module StringMap = Map.Make(String)
module Symtable = ScopedMap.Make(String)

type error =
  | Redefined of string
  | Not_enough_params of int
  | Too_many_params of int
  | Unbound of string
  | Unimplemented of string

type state = {
    genvar : UnionFind.gen;
    constraints : Constraint.t;
    tctx : Type.t Symtable.t;
  }

type 'a t = state -> ('a, error) result * state

let return a s = (Ok a, s)

let throw e s = (Error e, s)

let init_state = {
    genvar = UnionFind.init_gen;
    constraints = Constraint.True;
    tctx = Symtable.empty;
  }

let run m =
  let a, _ = m init_state in
  a

module BindingOps = struct
  let ( let+ ) t f s =
    let r, s = t s in
    (Result.map f r, s)

  let ( and+ ) t1 t2 s =
    let r1, s = t1 s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok a ->
       let r2, s = t2 s in
       match r2 with
       | Error e -> (Error e, s)
       | Ok b -> (Ok (a, b), s)

  let ( and* ) = ( and+ )

  let ( let* ) t f s =
    let r, s = t s in
    match r with
    | Error e -> (Error e, s)
    | Ok a -> f a s
end

open BindingOps

let rec mapM f = function
  | [] -> return []
  | x :: xs ->
     let+ y = f x
     and+ ys = mapM f xs in
     y :: ys

let rec fold_rightM f acc = function
  | [] -> return acc
  | x :: xs ->
     let* acc = fold_rightM f acc xs in
     f acc x

let get s = (Ok s, s)

let put s' _ = (Ok (), s')

let in_scope scope m =
  let* old_s = get in
  let* () = put { old_s with tctx = Symtable.extend scope old_s.tctx } in
  let* a = m in
  let+ () = put old_s in
  a

let find_var v =
  let* s = get in
  match Symtable.find v s.tctx with
  | None -> throw (Unbound v)
  | Some t -> return t

let fresh_var s =
  let (ty, genvar) = UnionFind.fresh s.genvar in
  (Ok ty, { s with genvar })

let ty ty s =
  let (ty, genvar) = UnionFind.wrap s.genvar ty in
  (Ok ty, { s with genvar })

let add_constraint c s =
  (Ok (), { s with constraints = Constraint.Conj(s.constraints, c) })

let infer_lit = function
  | Ast.Int_lit _ ->
     let* ty = fresh_var in
     let+ () = add_constraint (Constraint.Nat ty) in
     ty
  | Ast.Str_lit _ -> ty (Type.Prim Type.Cstr)
  | Ast.Unit_lit -> ty (Type.Prim Type.Unit)

let infer_pat = function
  | Ast.Lit_pat lit ->
     let+ ty = infer_lit lit in
     (ty, StringMap.empty)
  | Ast.Var_pat var ->
     let+ ty = fresh_var in
     (ty, StringMap.singleton var ty)
  | Ast.Wild_pat ->
     let+ ty = fresh_var in
     (ty, StringMap.empty)

exception String of string

let infer_pats pats =
  fold_rightM (fun (tys, map) pat ->
      let f k _ _ = raise (String k) in
      let* ty, map' = infer_pat pat.Ast.annot_item in
      try return (ty :: tys, StringMap.union f map map') with
      | String k -> throw (Redefined k)
    ) ([], StringMap.empty) pats

let rec infer_expr = function
  | Ast.Apply_expr(f, args) ->
     let* f_ty = infer_expr f.annot_item
     and* arg_tys = mapM (fun arg -> infer_expr arg.Ast.annot_item) args
     and* ret_ty = fresh_var in
     let* arrow = ty (Type.Fun { dom = arg_tys; codom = ret_ty }) in
     let+ () = add_constraint (Constraint.Eq(f_ty, arrow)) in
     ret_ty
  | Ast.Lit_expr lit -> infer_lit lit
  | Ast.Seq_expr(e1, e2) ->
     let* t1 = infer_expr e1.annot_item
     and* unit = ty (Type.Prim Type.Unit) in
     let* () = add_constraint (Constraint.Eq(t1, unit)) in
     infer_expr e2.annot_item
  | Ast.Var_expr var -> find_var var

let infer_clause clause =
  let* tys, map = infer_pats clause.Ast.clause_lhs in
  let+ ty = in_scope map (infer_expr clause.Ast.clause_rhs.annot_item) in
  (tys, ty)

let unify_clauses (lhs_tys, lhs_ty) (rhs_tys, rhs_ty) =
  let rec loop idx lhs rhs = match lhs, rhs with
    | [], [] -> return ()
    | x :: xs, y :: ys ->
       let* () = add_constraint (Constraint.Eq(x, y)) in
       loop (idx + 1) xs ys
    | [], _ :: _ -> throw (Too_many_params idx)
    | _ :: _, [] -> throw (Not_enough_params idx)
  in
  let* () = loop 1 lhs_tys rhs_tys in
  add_constraint (Constraint.Eq(lhs_ty, rhs_ty))

let infer_fun func =
  let* list = mapM infer_clause func.Ast.fun_clauses in
  match list with
  | [] -> throw (Unimplemented "Todo")
  | first :: rest ->
     fold_rightM (fun () clause -> unify_clauses first clause) () rest
