module L = Dlist
module StringMap = Map.Make(String)

type error =
  | Redefined of string
  | Unimplemented of string

type state = {
    ty_gen : UnionFind.gen;
    funcs : (string, Type.t) Hashtbl.t;
  }

type 'a payload = {
    data : 'a;
    ex : Type.t L.t; (** Existential variables *)
    c : Constraint.t L.t; (** Constraints *)
  }

(* In the paper "Hindley-Milner Elaboration in Applicative Style," the wrapped
   data 'a is embedded inside a continuation of type env -> 'a. The paper notes
   that the presence of the continuation prevents the type from having a monad
   instance; it only has an applicative instance. Because I do not wrap the data
   in a continuation, I can have a monad.

   This type is equivalent to the Haskell monad transformer stack

   WriterT (ExceptT error (State state))
   = WriterT (ExceptT error (state -> (_ * state)))
   = WriterT (state -> ((Either error _) * state))
   = state -> (Either error (payload _) * state)
*)
type 'a t = state -> ('a payload, error) result * state

let throw e s = (Error e, s)

let init_state = {
    ty_gen = UnionFind.init_gen;
    funcs = Hashtbl.create 20;
  }

let run m =
  let r, _ = m init_state in
  match r with
  | Error e -> Error e
  | Ok w -> Ok (w.data, L.to_list w.c)

module Mon : Monad.MONAD with type 'a t = 'a t = struct
  type nonrec 'a t = 'a t

  let return a s = (Ok { data = a; ex = L.empty; c = L.empty }, s)

  let ( let+ ) t f s =
    let r, s = t s in
    match r with
    | Error e -> (Error e, s)
    | Ok w -> (Ok { w with data = f w.data }, s)

  let ( and+ ) t1 t2 s =
    let r1, s = t1 s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok w1 ->
       let r2, s = t2 s in
       match r2 with
       | Error e -> (Error e, s)
       | Ok w2 ->
          ( Ok {
                data = (w1.data, w2.data);
                ex = L.append w1.ex w2.ex;
                c = L.append w1.c w2.c;
              }
          , s )

  let ( and* ) = ( and+ )

  let ( let* ) t f s =
    let r1, s = t s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok w1 ->
       let r2, s = f w1.data s in
       match r2 with
       | Error e -> (Error e, s)
       | Ok w2 ->
          ( Ok {
                data = w2.data;
                ex = L.append w1.ex w2.ex;
                c = L.append w1.c w2.c;
              }
          , s )
end

open Mon
open Monad.List(Mon)

let constrain c s =
  (Ok { data = (); ex = L.empty; c = L.singleton c }, s)

let in_scope scope m s =
  let (r, s) = m s in
  match r with
  | Error e -> (Error e, s)
  | Ok w ->
     ( Ok { w with c = L.singleton (Constraint.Let_mono(scope, L.to_list w.c)) }
     , s )

let fresh_var s =
  let (ty, ty_gen) = UnionFind.fresh s.ty_gen in
  (Ok { data = ty; ex = L.singleton ty; c = L.empty }, { s with ty_gen })

let create_ty ty s =
  let (ty, ty_gen) = UnionFind.wrap s.ty_gen ty in
  (Ok { data = ty; ex = L.singleton ty; c = L.empty }, { s with ty_gen })

let rec read_ty = function
  | Ast.Unit -> create_ty (Type.Prim Type.Unit)
  | Ast.Arrow(dom, codom) ->
     let* dom = mapM (fun x -> read_ty x.Ast.annot_item) dom in
     let* codom = read_ty codom.Ast.annot_item in
     create_ty (Type.Fun { dom; codom })

let decl_fun name ty s =
  if Hashtbl.mem s.funcs name then
    (Error (Redefined name), s)
  else (
    Hashtbl.add s.funcs name ty;
    (Ok { data = (); ex = L.empty; c = L.empty }, s)
  )

let get_fun name s =
  (Ok { data = Hashtbl.find_opt s.funcs name; ex = L.empty; c = L.empty }, s)

let lit_has_ty lit ty =
  match lit with
  | Ast.Int_lit _ -> constrain (Constraint.Nat ty)
  | Ast.Str_lit _ ->
     let* cstr = create_ty (Type.Prim Type.Cstr) in
     constrain (Constraint.Eq(ty, cstr))
  | Ast.Unit_lit ->
     let* unit = create_ty (Type.Prim Type.Unit) in
     constrain (Constraint.Eq(ty, unit))

let pat_has_ty pat ty =
  match pat with
  | Ast.Var_pat var -> return (Typed.Wild_pat, StringMap.singleton var ty)
  | Ast.Wild_pat -> return (Typed.Wild_pat, StringMap.empty)
  | Ast.Lit_pat lit ->
     let+ () = lit_has_ty lit ty in
     ( (match lit with
        | Ast.Int_lit n -> Typed.Int_pat(ty, n)
        | Ast.Str_lit s -> Typed.Str_pat s
        | Ast.Unit_lit -> Typed.Wild_pat)
     , StringMap.empty )

exception String of string

let pats_have_tys pats =
  fold_rightM (fun (pats, map) (pat, ty) ->
      (* Raise exception to break out *)
      let f k _ _ = raise (String k) in
      let* pat, map' = pat_has_ty pat.Ast.annot_item ty in
      try return (pat :: pats, StringMap.union f map map') with
      | String k -> throw (Redefined k)
    ) ([], StringMap.empty) pats

let rec expr_has_ty expr ty =
  match expr with
  | Ast.Apply_expr(f, args) ->
     let* tys, args =
       fold_rightM (fun (tys, args) arg ->
           let* ty = fresh_var in
           let+ arg = expr_has_ty arg.Ast.annot_item ty in
           ty :: tys, arg :: args)
         ([], []) args
     in
     let* arrow = create_ty (Type.Fun { dom = tys; codom = ty }) in
     let+ f = expr_has_ty f.annot_item arrow in
     Typed.Apply_expr(f, args)
  | Ast.Seq_expr(e1, e2) ->
     let* unit = create_ty (Type.Prim Type.Unit) in
     let* e1 = expr_has_ty e1.annot_item unit in
     let+ e2 = expr_has_ty e2.annot_item ty in
     Typed.Seq_expr(e1, e2)
  | Ast.Var_expr var ->
     let+ () = constrain (Constraint.Inst(var, ty)) in
     Typed.Var_expr var
  | Ast.Lit_expr lit ->
     let+ () = lit_has_ty lit ty in
     match lit with
     | Ast.Int_lit n -> Typed.Int_expr(ty, n)
     | Ast.Str_lit s -> Typed.Str_expr s
     | Ast.Unit_lit -> Typed.Unit_expr

let clause_has_ty clause ty =
  let* lhs =
    mapM (fun lhs ->
        let+ ty = fresh_var in
        (lhs, ty)
      ) clause.Ast.clause_lhs
  in
  let dom = List.map (fun (_, ty) -> ty) lhs in
  let* lhs, map = pats_have_tys lhs in
  let* codom = fresh_var in
  let* rhs = in_scope map (expr_has_ty clause.clause_rhs.annot_item codom) in
  let* arrow = create_ty (Type.Fun({ dom; codom })) in
  let+ () = constrain (Constraint.Eq(ty, arrow)) in
  Typed.{ clause_lhs = lhs; clause_vars = map; clause_rhs = rhs }

let fun_has_ty func ty =
  let+ clauses =
    mapM (fun clause -> clause_has_ty clause ty) func.Ast.fun_clauses
  in
  Typed.{
      fun_name = func.Ast.fun_name;
      fun_ty = ty;
      fun_clauses = clauses;
  }

let elab prog =
  let+ decls =
    fold_leftM (fun decls next ->
        match next.Ast.annot_item with
        | Ast.Extern -> return decls
        | Ast.Forward_decl(name, ty) ->
           let* ty = read_ty ty.Ast.annot_item in
           let+ () = decl_fun name ty in
           decls
        | Ast.Fun fun_def ->
           let* ty =
             let* opt = get_fun fun_def.Ast.fun_name in
             match opt with
             | Some ty -> return ty
             | None ->
                let* ty = fresh_var in
                let+ () = decl_fun fun_def.Ast.fun_name ty in
                ty
           in
           let+ fun_def = fun_has_ty fun_def ty in
           Typed.Fun fun_def :: decls
      ) [] prog.Ast.decls
  in
  Typed.{ decls = List.rev decls }
