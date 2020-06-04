module StringMap = Map.Make(String)

type pat = {
    pat_node : pat_node;
    pat_vars : Var.t list;
  }

and pat_node =
  | Int_pat of Type.t * int
  | Str_pat of string
  | Wild_pat

type expr =
  | Apply_expr of expr * expr list
  | Int_expr of Type.t * int
  | Str_expr of string
  | Seq_expr of expr * expr
  | Unit_expr
  | Var_expr of Var.t

type clause = {
    clause_lhs : pat list;
    clause_vars : (Var.t * Type.t) StringMap.t;
    clause_rhs : expr;
  }

type fun_def = {
    fun_name : string;
    fun_ty : Type.t;
    fun_clauses : clause list;
  }

type decl =
  | Fun of fun_def

type program = {
    decls : decl list;
  }
