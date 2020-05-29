module StringMap = Map.Make(String)

type error =
  | Redefined of string
  | Unimplemented of string

type state = {
    genvar : UnionFind.gen;
    funcs : (string, Type.t) Hashtbl.t;
  }

type 'a t = state -> ('a * Constraint.t list, error) result * state

let return a s = (Ok (a, []), s)

let throw e s = (Error e, s)

let init_state = {
    genvar = UnionFind.init_gen;
    funcs = Hashtbl.create 20;
  }

let run m =
  let a, _ = m init_state in
  a

module BindingOps = struct
  let ( let+ ) t f s =
    let r, s = t s in
    match r with
    | Error e -> (Error e, s)
    | Ok (a, c) -> (Ok (f a, c), s)

  let ( and+ ) t1 t2 s =
    let r1, s = t1 s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok (a, c1) ->
       let r2, s = t2 s in
       match r2 with
       | Error e -> (Error e, s)
       | Ok (b, c2) -> (Ok ((a, b), List.append c1 c2), s)

  let ( and* ) = ( and+ )

  let ( let* ) t f s =
    let r1, s = t s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok (a, c1) ->
       let r2, s = f a s in
       match r2 with
       | Error e -> (Error e, s)
       | Ok (b, c2) -> (Ok (b, List.append c1 c2), s)
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

let constrain c s =
  (Ok ((), [c]), s)

let in_scope scope m s =
  let (r, s) = m s in
  match r with
  | Error e -> (Error e, s)
  | Ok (a, c) -> (Ok (a, [Constraint.Let_mono(scope, c)]), s)

let fresh_var s =
  let (ty, genvar) = UnionFind.fresh s.genvar in
  (Ok (ty, []), { s with genvar })

let create_ty ty s =
  let (ty, genvar) = UnionFind.wrap s.genvar ty in
  (Ok (ty, []), { s with genvar })

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
    (Ok ((), []), s)
  )

let get_fun name s =
  (Ok (Hashtbl.find_opt s.funcs name, []), s)

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
  | Ast.Lit_pat lit ->
     let+ () = lit_has_ty lit ty in
     StringMap.empty
  | Ast.Var_pat var -> return (StringMap.singleton var ty)
  | Ast.Wild_pat -> return (StringMap.empty)

exception String of string

let pats_have_tys pats =
  fold_rightM (fun map (pat, ty) ->
      let f k _ _ = raise (String k) in
      let* map' = pat_has_ty pat.Ast.annot_item ty in
      try return (StringMap.union f map map') with
      | String k -> throw (Redefined k)
    ) StringMap.empty pats

let rec expr_has_ty expr ty =
  match expr with
  | Ast.Apply_expr(f, args) ->
     let* arg_tys =
       mapM (fun arg ->
           let* ty = fresh_var in
           let+ () = expr_has_ty arg.Ast.annot_item ty in
           ty
         ) args in
     let* arrow = create_ty (Type.Fun { dom = arg_tys; codom = ty }) in
     expr_has_ty f.annot_item arrow
  | Ast.Lit_expr lit -> lit_has_ty lit ty
  | Ast.Seq_expr(e1, e2) ->
     let* unit = create_ty (Type.Prim Type.Unit) in
     let* () = expr_has_ty e1.annot_item unit in
     expr_has_ty e2.annot_item ty
  | Ast.Var_expr var -> constrain (Constraint.Inst(var, ty))

let clause_has_ty clause ty =
  let* lhs =
    mapM (fun lhs ->
        let+ ty = fresh_var in
        (lhs, ty)
      ) clause.Ast.clause_lhs
  in
  let dom = List.map (fun (_, ty) -> ty) lhs in
  let* map = pats_have_tys lhs in
  let* codom = fresh_var in
  let* () = in_scope map (expr_has_ty clause.Ast.clause_rhs.annot_item codom) in
  let* arrow = create_ty (Type.Fun({ dom; codom })) in
  constrain (Constraint.Eq(ty, arrow))

let fun_has_ty func ty =
  fold_rightM (fun () clause -> clause_has_ty clause ty) () func.Ast.fun_clauses

let infer_decl = function
  | Ast.Extern -> return ()
  | Ast.Forward_decl(name, ty) ->
     let* ty = read_ty ty.Ast.annot_item in
     decl_fun name ty
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
     fun_has_ty fun_def ty
