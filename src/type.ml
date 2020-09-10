type ns

module Subst = Map.Make(Int)

type size = Sz8 | Sz16 | Sz32 | Sz64
type sign = Signed | Unsigned

type head =
  | Cstr
  | Num of sign * size
  | Adt of adt

and t =
  | Neu of head * t list
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
    adt_constr_names : (string, int) Hashtbl.t;
    adt_constrs : datacon array;
  }

and datacon = {
    datacon_name : string;
    datacon_inputs : t list;
    datacon_output : t;
  }

type forall = Forall of t list * t

let rec subst s = function
  | Neu(head, spine) -> Neu(head, List.map (subst s) spine)
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

let union s s' =
  Subst.union (fun _ a _ -> Some a) s s'

type fun_error = Too_many | Too_few | Unify of (t * t)

let unify_head lhs rhs = match lhs, rhs with
  | Adt ladt, Adt radt when ladt.adt_name = radt.adt_name -> Ok ()
  | Cstr, Cstr -> Ok ()
  | Num(a, b), Num(c, d) when a = c && b = d -> Ok ()
  | _, _ -> Error (Neu(lhs, []), Neu(rhs, []))

let rec unify lhs rhs = match lhs, rhs with
  | Neu (head, spine), Neu (head', spine') ->
     unify_neu head spine head' spine'
  | Fun lhs', Fun rhs' ->
     begin match unify_fun lhs' rhs' with
     | Ok s -> Ok s
     | Error Too_many -> Error (lhs, rhs)
     | Error Too_few -> Error (lhs, rhs)
     | Error (Unify e) -> Error e
     end
  | Pointer lhs, Pointer rhs -> unify lhs rhs
  | Unit, Unit -> Ok Subst.empty
  | Univ, Univ -> Ok Subst.empty
  | Rigid id, Rigid id' when id = id' -> Ok Subst.empty
  | Var id, Var id' when id = id' -> Ok Subst.empty
  | Var id, ty | ty, Var id -> Ok (Subst.singleton id ty)
  | _, _ -> Error (lhs, rhs)

and unify_neu head spine head' spine' =
  match spine, spine' with
  | [], [] ->
     begin match unify_head head head' with
     | Ok () -> Ok Subst.empty
     | Error e -> Error e
     end
  | ty :: spine, ty' :: spine' ->
     begin match unify ty ty' with
     | Ok _ -> unify_neu head spine head' spine'
     | Error e -> Error e
     end
  | _, _ -> Error (Neu(head, spine), Neu(head', spine'))

and unify_fun lhs rhs =
  let rec loop s lhs rhs = match lhs, rhs with
    | [], [] -> Ok s
    | [], _ :: _ -> Error Too_many
    | _ :: _, [] -> Error Too_few
    | x :: xs, y :: ys ->
       match unify (subst s x) (subst s y) with
       | Ok s' -> loop (Subst.union (fun _ a _ -> Some a) s s') xs ys
       | Error e -> Error (Unify e)
  in
  match loop Subst.empty lhs.dom rhs.dom with
  | Error e -> Error e
  | Ok s ->
     match unify (subst s lhs.codom) (subst s rhs.codom) with
     | Error e -> Error (Unify e)
     | Ok s -> Ok s

let rec inst tyargs = function
  | Neu(head, spine) -> Neu(head, List.map (inst tyargs) spine)
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
