type ns

module Subst = Map.Make(Int)

type size = Sz8 | Sz16 | Sz32 | Sz64
type sign = Signed | Unsigned

type prim =
  | Cstr
  | Num of sign * size
  | Unit

type t =
  | Constr of adt
  | Fun of fun_ty
  | Pointer of t
  | Prim of prim
  | Univ
  | Rigid of int
  | Var of int

and fun_ty = {
    dom : t list;
    codom : t;
  }

and adt = {
    adt_name : string;
    adt_constrs : (string * t list) array;
  }

type forall = Forall of int * t

let rec subst s = function
  | Constr adt -> Constr adt
  | Fun fn -> Fun { dom = List.map (subst s) fn.dom; codom = subst s fn.codom }
  | Pointer ty -> Pointer (subst s ty)
  | Prim p -> Prim p
  | Univ -> Univ
  | Rigid id -> Rigid id
  | Var id ->
     match Subst.find_opt id s with
     | Some ty -> ty
     | None -> Var id

let rec unify lhs rhs = match lhs, rhs with
  | Constr adt, Constr adt' ->
     if adt.adt_name = adt'.adt_name then
       Ok Subst.empty
     else
       Error "Unification fail"
  | Fun lhs, Fun rhs -> unify_fun lhs rhs
  | Pointer lhs, Pointer rhs -> unify lhs rhs
  | Prim lhs, Prim rhs ->
     if lhs = rhs then
       Ok Subst.empty
     else
       Error "Unification fail"
  | Univ, Univ -> Ok Subst.empty
  | Rigid id, Rigid id' when id = id' -> Ok Subst.empty
  | Var id, Var id' when id = id' -> Ok Subst.empty
  | Var id, ty | ty, Var id -> Ok (Subst.singleton id ty)
  | _, _ -> Error "Unification fail"

and unify_fun lhs rhs =
  let rec loop s lhs rhs = match lhs, rhs with
    | [], [] -> Ok s
    | [], _ :: _ -> Error "Too many"
    | _ :: _, [] -> Error "Too few"
    | x :: xs, y :: ys ->
       match unify (subst s x) (subst s y) with
       | Ok s' -> loop (Subst.union (fun _ a _ -> Some a) s s') xs ys
       | Error e -> Error e
  in
  match loop Subst.empty lhs.dom rhs.dom with
  | Ok s -> unify (subst s lhs.codom) (subst s rhs.codom)
  | Error e -> Error e

let rec inst tyargs = function
  | Constr name-> Constr name
  | Fun fun_ty ->
     Fun
       { dom = List.map (inst tyargs) fun_ty.dom
       ; codom = inst tyargs fun_ty.codom }
  | Prim p -> Prim p
  | Pointer ty -> Pointer (inst tyargs ty)
  | Rigid r -> tyargs.(r)
  | Univ -> Univ
  | Var id -> Var id
