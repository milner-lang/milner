type 'a annot = {
    annot_item : 'a;
    annot_begin : Lexing.position;
    annot_end : Lexing.position;
  }

type literal =
  | Int_lit of int
  | Str_lit of string
  | Unit_lit

type pat =
  | Lit_pat of literal
  | Var_pat of string
  | Wild_pat

type expr =
  | Apply_expr of expr annot * expr annot list
  | Lit_expr of literal
  | Seq_expr of expr annot * expr annot
  | Var_expr of string

type clause = {
    clause_lhs : pat annot list;
    clause_rhs : expr annot;
  }

type fun_def = {
    fun_name : string;
    fun_clauses : clause list;
  }

type decl =
  | Extern
  | Fun of fun_def

type program = {
    decls : decl annot list;
  }
