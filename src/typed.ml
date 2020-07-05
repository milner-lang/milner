module StringMap = Map.Make(String)

(** [ns] is type-level data intended to index [Var.t] *)
type ns

type pat = {
    pat_node : pat_node;
    pat_vars : ns Var.t list;
  }

and pat_node =
  | Constr_pat of Type.t * Type.adt * int * pat list
  | Int_pat of Type.t * int
  | Str_pat of string
  | Wild_pat

type expr =
  | Apply_expr of Type.t * expr * expr list
  | Global_expr of string * Type.t array
  | Int_expr of Type.t * int
  | Str_expr of string
  | Seq_expr of expr * expr
  | Unit_expr
  | Var_expr of ns Var.t

type clause = {
    clause_lhs : pat list;
    clause_vars : ns Var.t StringMap.t;
    clause_rhs : expr;
  }

type fun_def = {
    fun_name : string;
    fun_ty : Type.forall;
    fun_clauses : clause list;
  }

type decl =
  | External of string * Type.t
  | Fun of fun_def

type program = {
    decls : decl list;
  }
