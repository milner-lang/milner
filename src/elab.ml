module L = Dlist
module StringMap = Map.Make(String)
module Symtable = ScopedMap.Make(String)

type error =
  | Redefined of string
  | Undefined of string
  | Undefined_tvar of string
  | Unification
  | Unimplemented of string

let string_of_error = function
  | Redefined s -> "Elab: Redefined " ^ s
  | Undefined s -> "Elab: Undefined " ^ s
  | Undefined_tvar s -> "Elab: Undefined type variable " ^ s
  | Unification -> "Elab: Unification"
  | Unimplemented s -> "Elab: Unimplemented " ^ s

type state = {
    tycons : (string, Type.t) Hashtbl.t;
    datacons : (string, Type.adt * int) Hashtbl.t;
    funcs : (string, Type.forall) Hashtbl.t;
    ty_gen : UnionFind.gen;
    var_gen : Typed.ns Var.gen;
  }

type 'a payload = {
    data : 'a;
    ex : Type.t L.t; (** Existential variables *)
    c : Type.constraints L.t; (** Constraints *)
  }

(* In the paper "Hindley-Milner Elaboration in Applicative Style," the wrapped
   data 'a is embedded inside a continuation of type env -> 'a. The paper notes
   that the presence of the continuation prevents the type from having a monad
   instance; it only has an applicative instance. Because I do not wrap the
   data in a continuation, I can have a monad. *)
type 'a t =
  Typed.ns Var.t Symtable.t -> state -> ('a payload, error) result * state

let throw e _ s = (Error e, s)

let init_state () =
  let tycons = Hashtbl.create 20 in
  Hashtbl.add tycons "Cstring" (UnionFind.wrap (Type.Prim Type.Cstr));
  Hashtbl.add tycons "Int32"
    (UnionFind.wrap (Type.Prim (Type.Num(Type.Signed, Type.Sz32))));
  { ty_gen = UnionFind.init_gen;
    var_gen = Var.init_gen;
    datacons = Hashtbl.create 20;
    funcs = Hashtbl.create 20;
    tycons }

let run m =
  let r, _ = m Symtable.empty (init_state ()) in
  match r with
  | Error e -> Error e
  | Ok w -> Ok w.data

module Mon : Monad.MONAD with type 'a t = 'a t = struct
  type nonrec 'a t = 'a t

  let return a _env s = (Ok { data = a; ex = L.empty; c = L.empty }, s)

  let ( let+ ) t f env s =
    let r, s = t env s in
    match r with
    | Error e -> (Error e, s)
    | Ok w -> (Ok { w with data = f w.data }, s)

  let ( and+ ) t1 t2 env s =
    let r1, s = t1 env s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok w1 ->
       let r2, s = t2 env s in
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

  let ( let* ) t f env s =
    let r1, s = t env s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok w1 ->
       let r2, s = f w1.data env s in
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

let constrain c _ s =
  (Ok { data = (); ex = L.empty; c = L.singleton c }, s)

let in_scope scope m env s =
  let (r, s) = m (Symtable.extend scope env) s in
  match r with
  | Error e -> (Error e, s)
  | Ok w -> (Ok w, s)

let poly m env s =
  let (r, s) = m env s in
  match r with
  | Error e -> (Error e, s)
  | Ok w ->
     let data = (w.data, L.to_list w.ex, L.to_list w.c) in
     (Ok { data; ex = L.empty; c = L.empty }, s)

type var_kind =
  | Local of Typed.ns Var.t
  | Global of Type.forall

let find name env s =
  match Symtable.find name env with
  | Some var -> (Ok { data = Local var; ex = L.empty; c = L.empty }, s)
  | None ->
     match Hashtbl.find_opt s.funcs name with
     | Some ty -> (Ok { data = Global ty; ex = L.empty; c = L.empty }, s)
     | None -> (Error (Undefined name), s)

let declare_ty name ty _ s =
  Hashtbl.add s.tycons name ty;
  (Ok { data = (); ex = L.empty; c = L.empty }, s)

let find_tcon name _ s =
  match Hashtbl.find_opt s.tycons name with
  | None -> (Error (Undefined name), s)
  | Some ty -> (Ok { data = ty; ex = L.empty; c = L.empty }, s)

let fresh_tvar _ s =
  let (ty, ty_gen) = UnionFind.fresh s.ty_gen in
  (Ok { data = ty; ex = L.singleton ty; c = L.empty }, { s with ty_gen })

let create_ty ty _ s =
  let ty = UnionFind.wrap ty in
  (Ok { data = ty; ex = L.singleton ty; c = L.empty }, s)

let fresh_var ty _ s =
  let (var, var_gen) = Var.fresh s.var_gen ty in
  (Ok { data = var; ex = L.empty; c = L.empty }, { s with var_gen })


let declare_datacon name idx adt _ s =
  Hashtbl.add s.datacons name (idx, adt);
  (Ok { data = (); ex = L.empty; c = L.empty }, s)

let find_datacon name _ s =
  match Hashtbl.find_opt s.datacons name with
  | Some data -> (Ok { data; ex = L.empty; c = L.empty }, s)
  | None -> Error (Undefined name), s

let rec read_ty tvars = function
  | Ast.Unit -> create_ty (Type.Prim Type.Unit)
  | Ast.Ty_con tycon -> find_tcon tycon
  | Ast.Arrow(dom, codom) ->
     let* dom = mapM (fun x -> read_ty tvars x.Ast.annot_item) dom in
     let* codom = read_ty tvars codom.Ast.annot_item in
     create_ty (Type.Fun { dom; codom })
  | Ast.Ty_var name ->
     match StringMap.find_opt name tvars with
     | Some v -> create_ty (Type.Rigid v)
     | None -> throw (Undefined_tvar name)

let read_ty_scheme tvars ty =
  let len, tvar_map =
    List.fold_left
      (fun (i, tvars) next -> i + 1, StringMap.add next i tvars)
      (0, StringMap.empty) tvars
  in
  let+ ty = read_ty tvar_map ty in
  len, ty

let read_adt adt =
  let constrs = Array.make (List.length adt.Ast.adt_constrs) ("", []) in
  let* _ =
    fold_leftM (fun i (name, tys) ->
        let+ tys =
          mapM (fun ann -> read_ty StringMap.empty ann.Ast.annot_item) tys
        in
        constrs.(i) <- (name, tys);
        i + 1)
      0 adt.Ast.adt_constrs
  in
  let adt' = Type.{ adt_name = adt.Ast.adt_name; adt_constrs = constrs } in
  let* _ =
    fold_leftM (fun i (name, _) ->
        let+ () = declare_datacon name adt' i in
        i + 1)
      0 adt.Ast.adt_constrs in
  let+ () = declare_ty adt.Ast.adt_name (UnionFind.wrap (Type.Constr adt')) in
  adt'

let inst n ty _ s =
  let ty_args, ty, ty_gen = Type.inst s.ty_gen n ty in
  (Ok { data = (ty_args, ty); ex = L.empty; c = L.empty }, { s with ty_gen })

let decl_fun name ty _ s =
  if Hashtbl.mem s.funcs name then
    (Error (Redefined name), s)
  else (
    Hashtbl.add s.funcs name ty;
    (Ok { data = (); ex = L.empty; c = L.empty }, s)
  )

let get_fun name _ s =
  (Ok { data = Hashtbl.find_opt s.funcs name; ex = L.empty; c = L.empty }, s)

let lit_has_ty lit ty =
  match lit with
  | Ast.Int_lit _ -> constrain (Type.Nat ty)
  | Ast.Int32_lit _ ->
     let* int32 = create_ty (Type.Prim (Type.Num(Type.Signed, Type.Sz32))) in
     constrain (Type.Eq(ty, int32))
  | Ast.Str_lit _ ->
     let* cstr = create_ty (Type.Prim Type.Cstr) in
     constrain (Type.Eq(ty, cstr))
  | Ast.Unit_lit ->
     let* unit = create_ty (Type.Prim Type.Unit) in
     constrain (Type.Eq(ty, unit))

exception String of string

let rec pat_has_ty vars pat ty =
  match pat with
  | Ast.As_pat(pat, name) ->
     let* var = fresh_var ty in
     Var.add_name var name;
     let* pat, map = pat_has_ty (var :: vars) pat.Ast.annot_item ty in
     if StringMap.mem name map then
       throw (Redefined name)
     else
       return (pat, StringMap.add name var map)
  | Ast.Constr_pat(name, pats) ->
     let* adt, idx = find_datacon name in
     let* pats_tys =
       mapM (fun pat ->
           let+ ty = fresh_tvar in
           pat, ty
         ) pats
     in
     let+ pats, varmap = pats_have_tys pats_tys in
     ( Typed.{
         pat_node = Constr_pat(ty, adt, idx, pats);
         pat_vars = vars
       }
     , varmap )
  | Ast.Var_pat name ->
     let+ var = fresh_var ty in
     Var.add_name var name;
     ( Typed.{ pat_node = Wild_pat; pat_vars = var :: vars }
     , StringMap.singleton name var )
  | Ast.Wild_pat ->
     return
       ( Typed.{ pat_node = Wild_pat; pat_vars = vars }
       , StringMap.empty )
  | Ast.Lit_pat lit ->
     let+ () = lit_has_ty lit ty in
     ( Typed.{
         pat_vars = vars;
         pat_node =
           match lit with
           | Ast.Int_lit n -> Typed.Int_pat(ty, n)
           | Ast.Int32_lit n -> Typed.Int_pat(ty, n)
           | Ast.Str_lit s -> Typed.Str_pat s
           | Ast.Unit_lit -> Typed.Wild_pat
       }
     , StringMap.empty )

and pats_have_tys pats =
  fold_rightM (fun (pats, map) (pat, ty) ->
      (* Raise exception to break out *)
      let f k _ _ = raise (String k) in
      let* pat, map' = pat_has_ty [] pat.Ast.annot_item ty in
      try return (pat :: pats, StringMap.union f map map') with
      | String k -> throw (Redefined k)
    ) ([], StringMap.empty) pats

let rec expr_has_ty expr ty =
  match expr with
  | Ast.Apply_expr(f, args) ->
     let* tys, args =
       fold_rightM (fun (tys, args) arg ->
           let* ty = fresh_tvar in
           let+ arg = expr_has_ty arg.Ast.annot_item ty in
           ty :: tys, arg :: args)
         ([], []) args
     in
     let* arrow = create_ty (Type.Fun { dom = tys; codom = ty }) in
     let+ f = expr_has_ty f.annot_item arrow in
     Typed.Apply_expr(ty, f, args)
  | Ast.Constr_expr(name, args) ->
     let* adt, idx = find_datacon name in
     let+ args =
       let rec loop acc args tys =
         match args, tys with
         | [], [] -> return (List.rev acc)
         | arg :: args, ty :: tys ->
            let* arg = expr_has_ty arg.Ast.annot_item ty in
            loop (arg :: acc) args tys
         | _ :: _, [] | [], _ :: _ -> failwith "mismatch"
       in
       let _, tys = adt.Type.adt_constrs.(idx) in
       loop [] args tys
     in
     let ty = UnionFind.wrap (Type.Constr adt) in
     Typed.Constr_expr(ty, idx, args)
  | Ast.Seq_expr(e1, e2) ->
     let* unit = create_ty (Type.Prim Type.Unit) in
     let* e1 = expr_has_ty e1.annot_item unit in
     let+ e2 = expr_has_ty e2.annot_item ty in
     Typed.Seq_expr(e1, e2)
  | Ast.Var_expr name ->
     let* var = find name in
     begin match var with
     | Global (Type.Forall(poly, ty')) ->
        let* ty_args, inst'ed = inst poly ty' in
        let+ () = constrain (Type.Eq(inst'ed, ty)) in
        Typed.Global_expr(name, ty_args)
     | Local var ->
        let+ () = constrain (Type.Eq(Var.ty var, ty)) in
        Typed.Var_expr var
     end
  | Ast.Lit_expr lit ->
     let+ () = lit_has_ty lit ty in
     match lit with
     | Ast.Int_lit n -> Typed.Int_expr(ty, n)
     | Ast.Int32_lit n -> Typed.Int_expr(ty, n)
     | Ast.Str_lit s -> Typed.Str_expr s
     | Ast.Unit_lit -> Typed.Unit_expr

let clause_has_ty clause ty =
  let* lhs =
    mapM (fun lhs ->
        let+ ty = fresh_tvar in
        (lhs, ty)
      ) clause.Ast.clause_lhs
  in
  let dom = List.map (fun (_, ty) -> ty) lhs in
  let* lhs, map = pats_have_tys lhs in
  let* codom = fresh_tvar in
  let* rhs = in_scope map (expr_has_ty clause.clause_rhs.annot_item codom) in
  let* arrow = create_ty (Type.Fun({ dom; codom })) in
  let+ () = constrain (Type.Eq(ty, arrow)) in
  Typed.{ clause_lhs = lhs; clause_vars = map; clause_rhs = rhs }

let fun_has_ty func ty =
  let* clauses, ex, cs =
    poly (mapM (fun clause -> clause_has_ty clause ty) func.Ast.fun_clauses)
  in
  match Solve.solve_many cs with
    | Error _ -> throw Unification
    | Ok () ->
       let+ ty_scheme =
         let+ opt = get_fun func.Ast.fun_name in
         match opt with
         | Some ty_scheme -> ty_scheme
         | None -> Type.gen ex ty
       in
       Typed.{
           fun_name = func.Ast.fun_name;
           fun_ty = ty_scheme;
           fun_clauses = clauses;
       }

let elab_program prog =
  let+ decls =
    fold_leftM (fun decls next ->
        match next.Ast.annot_item with
        | Ast.External(name, ty) ->
           let* ty = read_ty StringMap.empty ty.Ast.annot_item in
           let+ () = decl_fun name (Type.Forall(0, ty)) in
           Typed.External(name, ty) :: decls
        | Ast.Forward_decl(name, tvars, ty) ->
           let* n, ty = read_ty_scheme tvars ty.Ast.annot_item in
           let+ () = decl_fun name (Type.Forall(n, ty)) in
           decls
        | Ast.Fun fun_def ->
           let* ty, declared =
             let* opt = get_fun fun_def.Ast.fun_name in
             match opt with
             | Some (Type.Forall(_, ty)) -> return (ty, true)
             | None -> let+ ty = fresh_tvar in ty, false
           in
           let* fun_def = fun_has_ty fun_def ty in
           let+ () =
             if declared then
               return ()
             else
               decl_fun fun_def.Typed.fun_name fun_def.Typed.fun_ty
           in
           Typed.Fun fun_def :: decls
        | Ast.Adt adt ->
           let+ _ = read_adt adt in
           decls
      ) [] prog.Ast.decls
  in
  Typed.{ decls = List.rev decls }

let elab prog = run (elab_program prog)
