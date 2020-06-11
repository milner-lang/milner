type prim =
  | Cstr
  | Int8
  | Nat8
  | Int16
  | Nat16
  | Int32
  | Nat32
  | Int64
  | Nat64
  | Unit

type ty =
  | Fun of fun_ty
  | Pointer of t
  | Prim of prim
  | Rigid of int

and t = ty UnionFind.t

and fun_ty = {
    dom : t list;
    codom : t;
  }

type constraints =
  | Eq of t * t
  | Nat of t

type forall = Forall of t list * constraints list * t

let prim_eq lhs rhs = match lhs, rhs with
  | Cstr, Cstr -> true
  | Int8, Int8 -> true
  | Nat8, Nat8 -> true
  | Int16, Int16 -> true
  | Nat16, Nat16 -> true
  | Int32, Int32 -> true
  | Nat32, Nat32 -> true
  | Int64, Int64 -> true
  | Nat64, Nat64 -> true
  | Unit, Unit -> true
  | _, _ -> false

let rec unify lhs rhs = match lhs, rhs with
  | Fun lhs, Fun rhs -> unify_fun lhs rhs
  | Pointer lhs, Pointer rhs -> UnionFind.union unify (Ok ()) lhs rhs
  | Prim lhs, Prim rhs ->
     if prim_eq lhs rhs then
       Ok ()
     else
       Error "Unification fail"
  | Rigid id, Rigid id' ->
     if id = id' then
       Ok ()
     else
       Error "Unification fail"
  | _, _ -> Error "Unification fail"

and unify_fun lhs rhs =
  let rec loop lhs rhs = match lhs, rhs with
    | [], [] -> Ok ()
    | [], _ :: _ -> Error "Too many"
    | _ :: _, [] -> Error "Too few"
    | x :: xs, y :: ys ->
       match UnionFind.union unify (Ok ()) x y with
       | Ok () -> loop xs ys
       | Error e -> Error e
  in
  match loop lhs.dom rhs.dom with
  | Ok () -> UnionFind.union unify (Ok ()) lhs.codom rhs.codom
  | Error e -> Error e

let rec rename namegen ty =
  match UnionFind.find ty with
  | Value (Fun fun_ty) ->
     let namegen = List.fold_right (Fun.flip rename) fun_ty.dom namegen in
     rename namegen fun_ty.codom
  | Value (Prim _) -> namegen
  | Value (Pointer ty) -> rename namegen ty
  | Value (Rigid _) -> namegen (* Already renamed *)
  | Root(_, tvar) ->
     ignore (
         UnionFind.union unify (Ok ()) tvar (UnionFind.wrap (Rigid namegen))
       );
     namegen

let gen tvs ty =
  let n = rename 0 ty in
  List.iter (fun tv ->
      match UnionFind.find tv with
      | UnionFind.Value _ -> ()
      | Root (_, node) ->
         match
           UnionFind.union unify (Ok ()) node (UnionFind.wrap (Prim Unit))
         with
         | Ok () -> ()
         | Error _ -> assert false
    ) tvs;
  n, ty

let inst gen n ty =
  let gen = ref gen in
  let arr =
    Array.init n (fun _ ->
        let ty, newgen = UnionFind.fresh !gen in
        gen := newgen;
        ty)
  in
  let rec loop ty = match UnionFind.find ty with
    | Value (Fun fun_ty) ->
       UnionFind.wrap
         (Fun { dom = List.map loop fun_ty.dom; codom = loop fun_ty.codom})
    | Value (Prim p) -> UnionFind.wrap (Prim p)
    | Value (Pointer ty) -> UnionFind.wrap (Pointer (loop ty))
    | Value (Rigid r) -> arr.(r)
    | Root _ -> assert false
  in
  loop ty, !gen
