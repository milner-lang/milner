type ns

module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)

type case_tree =
  | Leaf of int * (ns Var.t * string) list
  | Split of Type.adt * ns Var.t * (ns Var.t list * case_tree) list
  | Split_int of ns Var.t * case_tree IntMap.t * case_tree
  | Split_str of ns Var.t * case_tree StringMap.t * case_tree

type 'a pat = {
    pat_node : 'a pat_node;
    pat_vars : 'a
  }

and 'a pat_node =
  | Constr_pat of Type.t * Type.adt * int * 'a pat list
  | Int_pat of Type.t * int
  | Str_pat of string
  | Wild_pat

type expr =
  | Apply_expr of Type.t * expr * expr list
  | Constr_expr of Type.t * int * expr list
  | Global_expr of string * Type.t array
  | Int_expr of Type.t * int
  | Str_expr of string
  | Seq_expr of expr * expr
  | Unit_expr
  | Var_expr of ns Var.t

type clause = {
    clause_lhs : Type.ns Var.t list pat list;
    clause_vars : Type.ns Var.t StringMap.t;
    clause_rhs : expr;
  }

type fun_def = {
    fun_name : string;
    fun_ty : Type.fun_ty;
    fun_typarams : int;
    fun_params : ns Var.t list;
    fun_tree : case_tree;
    fun_clauses : (ns Var.t StringMap.t * expr) list;
  }

type decl =
  | External of string * Type.t
  | Fun of fun_def

type program = {
    decls : decl list;
  }
