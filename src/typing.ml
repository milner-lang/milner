type ns

module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)
module Subst = IntMap

type size = Sz8 | Sz16 | Sz32 | Sz64
type sign = Signed | Unsigned

type _ var = {
    id : int;
    ty : ty;
    mutable names : string list;
  }

and head =
  | Cstr
  | Num of sign * size
  | Adt of adt

and ty =
  | Neu of head * ty list
  | Fun_ty of fun_ty
  | Pointer of ty
  | KArrow of ty * ty
  | Unit
  | Univ
  | Rigid of int
  | Var of int
  | Const of expr

and fun_ty = {
    dom : ty list;
    codom : ty;
  }

and adt = {
    adt_name : string;
    adt_params : int;
    adt_kind : ty;
    adt_constr_names : (string, int) Hashtbl.t;
    adt_constrs : datacon array;
  }

and datacon = {
    datacon_name : string;
    datacon_inputs : ty list;
    datacon_output : ty;
  }

and expr =
  | Apply_expr of ty * expr * expr list
  | Constr_expr of ty * int * expr list
  | Global_expr of string * ty array
  | Int_expr of ty * int
  | Str_expr of string
  | Seq_expr of expr * expr
  | Unit_expr
  | Var_expr of ns var

type forall = Forall of ty list * ty

type case_tree =
  | Leaf of int * (ns var * string) list
  | Split of adt * ns var * (ns var list * case_tree) list
  | Split_int of ns var * case_tree IntMap.t * case_tree
  | Split_str of ns var * case_tree StringMap.t * case_tree

type pat = {
    pat_node : pat_node;
    pat_vars : ns var list
  }

and pat_node =
  | Constr_pat of ty * adt * int * pat list
  | Int_pat of ty * int
  | Str_pat of string
  | Wild_pat

type clause = {
    clause_lhs : pat list;
    clause_vars : ns var StringMap.t;
    clause_rhs : expr;
  }

type fun_def = {
    fun_name : string;
    fun_ty : fun_ty;
    fun_typarams : ty list;
    fun_params : ns var list;
    fun_tree : case_tree;
    fun_clauses : (ns var StringMap.t * expr) list;
  }

type decl =
  | External of string * ty
  | Fun of fun_def

type program = {
    decls : decl list;
  }


let rec subst s = function
  | Neu(head, spine) -> Neu(head, List.map (subst s) spine)
  | Fun_ty fn ->
     Fun_ty { dom = List.map (subst s) fn.dom; codom = subst s fn.codom }
  | KArrow(t1, t2) -> KArrow(subst s t1, subst s t2)
  | Pointer ty -> Pointer (subst s ty)
  | Unit -> Unit
  | Univ -> Univ
  | Rigid id -> Rigid id
  | Var id ->
     begin match Subst.find_opt id s with
     | Some ty -> ty
     | None -> Var id
     end
  | expr -> expr

let union s s' =
  Subst.union (fun _ a _ -> Some a) s s'

type fun_error = Too_many | Too_few | Unify of (ty * ty)

let unify_head lhs rhs = match lhs, rhs with
  | Adt ladt, Adt radt when ladt.adt_name = radt.adt_name -> Ok ()
  | Cstr, Cstr -> Ok ()
  | Num(a, b), Num(c, d) when a = c && b = d -> Ok ()
  | _, _ -> Error (Neu(lhs, []), Neu(rhs, []))

let rec unify lhs rhs = match lhs, rhs with
  | Neu (head, spine), Neu (head', spine') ->
     unify_neu head spine head' spine'
  | Fun_ty lhs', Fun_ty rhs' ->
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
  | Fun_ty fun_ty ->
     Fun_ty
       { dom = List.map (inst tyargs) fun_ty.dom
       ; codom = inst tyargs fun_ty.codom }
  | KArrow(t1, t2) -> KArrow(inst tyargs t1, inst tyargs t2)
  | Pointer ty -> Pointer (inst tyargs ty)
  | Rigid r -> tyargs.(r)
  | Unit -> Unit
  | Univ -> Univ
  | Var id -> Var id
  | expr -> expr
