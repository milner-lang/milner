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

and t = ty UnionFind.t

and fun_ty = {
    dom : t list;
    codom : t;
  }

type prelude = {
    int32 : t;
  }

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

let init =
  let ty_gen = UnionFind.init_gen in
  let int32, ty_gen = UnionFind.wrap ty_gen (Prim Int32) in
  { int32 }, ty_gen
