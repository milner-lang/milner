type 'a annot = {
    annot_item : 'a;
    annot_begin : Lexing.position;
    annot_end : Lexing.position;
  }

type ty =
  | Arrow of ty annot list * ty annot
  | Ty_con of string
  | Ty_var of string
  | Unit
  | Univ

type adt = {
    adt_name : string;
    adt_params : string list;
    adt_constrs : (string * ty annot list) list;
  }

type literal =
  | Int_lit of int
  | Int32_lit of int
  | Str_lit of string
  | Unit_lit

type pat =
  | As_pat of pat annot * string
  | Constr_pat of string * pat annot list
  | Lit_pat of literal
  | Var_pat of string
  | Wild_pat

type expr =
  | Apply_expr of expr annot * expr annot list
  | Constr_expr of string * expr annot list
  | Lit_expr of literal
  | Seq_expr of expr annot * expr annot
  | Var_expr of string
  | Generic_expr of string * ty annot list

type clause = {
    clause_lhs : pat annot list;
    clause_rhs : expr annot;
  }

type fun_def = {
    fun_name : string;
    fun_clauses : clause list;
  }

type decl =
  | External of string * ty annot
  | Forward_decl of string * string list * ty annot
  | Fun of fun_def
  | Adt of adt

type program = {
    decls : decl annot list;
  }
