%{
%}

%token ARROW
%token BAR
%token COLON
%token COMMA
%token EQUALS
%token LPAREN
%token RPAREN
%token SEMICOLON
%token UNDERSCORE
%token AS
%token EXTERN
%token FUN
%token VAL
%token <int> INT_LIT
%token <int> INT32_LIT
%token <string> STRING_LIT
%token <string> LIDENT
%token <string> UIDENT
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
  | ~ = forward_decl; {
        let a, b = forward_decl in
        Ast.{
            annot_item = Forward_decl(a, b);
            annot_begin = $symbolstartpos;
            annot_end = $endpos;
        }
      }
  | ~ = fun_def; {
      Ast.{
        annot_item = Ast.Fun fun_def;
        annot_begin = $symbolstartpos;
        annot_end = $endpos
      }
    }

let extern_decl := EXTERN; {
    ()
  }

let forward_decl := VAL; name = LIDENT; COLON; ~ = ty; {
        (name, ty)
      }

let fun_def :=
  | FUN; name = LIDENT; BAR?; clauses = separated_list(BAR, clause); {
        Ast.{
          fun_name = name;
          fun_clauses = clauses;
        }
      }

let ty := arrow_ty

let arrow_ty :=
  | FUN; LPAREN; dom = separated_list(COMMA, ty); RPAREN; ARROW; codom = ty;
    {
      Ast.{
        annot_item = Arrow(dom, codom);
        annot_begin = $symbolstartpos;
        annot_end = $endpos;
      }
    }
  | atom_ty

let atom_ty :=
  | id = UIDENT; {
    Ast.{
      annot_item = TyCon id;
      annot_begin = $symbolstartpos;
      annot_end = $endpos;
    }
  }
  | LPAREN; RPAREN; {
        Ast.{
          annot_item = Unit;
          annot_begin = $symbolstartpos;
          annot_end = $endpos;
        }
      }
  | LPAREN; ~ = ty; RPAREN; { ty }

let lit :=
  | int = INT_LIT; { Ast.Int_lit int }
  | int = INT32_LIT; { Ast.Int32_lit int }
  | str = STRING_LIT; { Ast.Str_lit str }
  | LPAREN; RPAREN; { Ast.Unit_lit }

let pat :=
  | pat = pat_atom; AS; id = LIDENT; {
        Ast.{
          annot_item = As_pat(pat, id);
          annot_begin = $symbolstartpos;
          annot_end = $endpos;
        }
      }
  | pat_atom

let pat_atom :=
  | id = LIDENT; {
    Ast.{
      annot_item = Var_pat id;
      annot_begin = $symbolstartpos;
      annot_end = $endpos;
    }
  }
  | ~ = lit; {
      Ast.{
        annot_item = Lit_pat lit;
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

let expr := seq_expr

let seq_expr :=
  | exp1 = seq_expr; SEMICOLON; exp2 = apply_expr; {
        Ast.{
          annot_item = Seq_expr(exp1, exp2);
          annot_begin = $symbolstartpos;
          annot_end = $endpos;
        }
      }
  | apply_expr

let apply_expr :=
  | f = apply_expr; LPAREN; args = separated_list(COMMA, apply_expr); RPAREN; {
        Ast.{
          annot_item = Apply_expr(f, args);
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
