type ns

module Subst = Map.Make(Int)

type size = Sz8 | Sz16 | Sz32 | Sz64
type sign = Signed | Unsigned

type tycon =
  | Cstr
  | Num of sign * size
  | Adt of adt * t list

and t =
  | Constr of tycon
  | Fun of fun_ty
  | Pointer of t
  | KArrow of t * t
  | Unit
  | Univ
  | Rigid of int
  | Var of int

and fun_ty = {
    dom : t list;
    codom : t;
  }

and adt = {
    adt_name : string;
    adt_params : int;
    adt_kind : t;
    adt_constrs : (string * t list) array;
  }

type forall = Forall of t list * t

let rec subst s = function
  | Constr (Adt(adt, spine)) ->
     Constr(Adt(adt, List.map (subst s) spine))
  | Constr head -> Constr head
  | Fun fn -> Fun { dom = List.map (subst s) fn.dom; codom = subst s fn.codom }
  | KArrow(t1, t2) -> KArrow(subst s t1, subst s t2)
  | Pointer ty -> Pointer (subst s ty)
  | Unit -> Unit
  | Univ -> Univ
  | Rigid id -> Rigid id
  | Var id ->
     match Subst.find_opt id s with
     | Some ty -> ty
     | None -> Var id

let rec unify lhs rhs = match lhs, rhs with
  | Constr (Adt(adt, _spine)), Constr (Adt(adt', _spine')) ->
     if adt.adt_name = adt'.adt_name then
       Ok Subst.empty
     else
       Error "Unification fail"
  | Constr Cstr, Constr Cstr -> Ok Subst.empty
  | Constr (Num(a, b)), Constr (Num(c, d)) ->
     if a = c && b = d then
       Ok Subst.empty
     else
       Error "Unification fail"
  | Fun lhs, Fun rhs -> unify_fun lhs rhs
  | Pointer lhs, Pointer rhs -> unify lhs rhs
  | Unit, Unit -> Ok Subst.empty
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
  | Constr (Adt(adt, spine)) -> Constr (Adt(adt, List.map (inst tyargs) spine))
  | Constr Cstr -> Constr Cstr
  | Constr (Num(a, b)) -> Constr (Num(a, b))
  | Fun fun_ty ->
     Fun
       { dom = List.map (inst tyargs) fun_ty.dom
       ; codom = inst tyargs fun_ty.codom }
  | KArrow(t1, t2) -> KArrow(inst tyargs t1, inst tyargs t2)
  | Pointer ty -> Pointer (inst tyargs ty)
  | Rigid r -> tyargs.(r)
  | Unit -> Unit
  | Univ -> Univ
  | Var id -> Var id
