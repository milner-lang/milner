%{
%}

%token COMMA
%token EQUALS
%token LPAREN
%token RPAREN
%token SEMICOLON
%token UNDERSCORE
%token EXTERN
%token FUN
%token <int> INT_LIT
%token <string> STRING_LIT
%token <string> LIDENT
%token EOF

%start <Ast.program> program

%%

let program := decls = list(decl); EOF; { { decls } }

let decl :=
  | extern_decl; {
      Ast.{
        annot_item = Ast.Extern;
        annot_begin = $symbolstartpos;
        annot_end = $endpos;
      }
    }
  | ~ = fun_decl; {
      Ast.{
        annot_item = Ast.Fun fun_decl;
        annot_begin = $symbolstartpos;
        annot_end = $endpos
      }
    }

let extern_decl :=
  | EXTERN; {
      ()
    }

let fun_decl :=
  | FUN; name = LIDENT; clauses = list(clause); {
        Ast.{
          fun_name = name;
          fun_clauses = clauses;
        }
      }

let lit :=
  | int = INT_LIT; { Ast.Int_lit int }
  | str = STRING_LIT; { Ast.Str_lit str }
  | LPAREN; RPAREN; { Ast.Unit_lit }

let pat :=
  | pat_atom

let pat_atom :=
  | id = LIDENT; {
      Ast.{
        annot_item = Var_pat id;
        annot_begin = $symbolstartpos;
        annot_end = $endpos;
      }
    }
  | UNDERSCORE; {
      Ast.{
        annot_item = Wild_pat;
        annot_begin = $symbolstartpos;
        annot_end = $endpos;
      }
    }
  | LPAREN; ~ = pat; RPAREN; { pat }

let clause :=
  | LPAREN; pats = separated_list(COMMA, pat); RPAREN; EQUALS; ~ = expr; {
        Ast.{
          clause_lhs = pats;
          clause_rhs = expr;
        }
      }

let expr :=
  | seq_expr

let seq_expr :=
  | exp1 = seq_expr; SEMICOLON; exp2 = atom_expr; {
        Ast.{
          annot_item = Ast.Seq_expr(exp1, exp2);
          annot_begin = $symbolstartpos;
          annot_end = $endpos;
        }
      }
  | atom_expr

let atom_expr :=
  | ~ = lit; {
      Ast.{
        annot_item = Lit_expr lit;
        annot_begin = $symbolstartpos;
        annot_end = $endpos;
      }
  }
  | id = LIDENT; {
      Ast.{
        annot_item = Var_expr id;
        annot_begin = $symbolstartpos;
        annot_end = $endpos;
      }
    }
  | LPAREN; ~ = expr; RPAREN; { expr }
