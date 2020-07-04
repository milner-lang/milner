type error =
  | Redefined of string
  | Undefined of string
  | Undefined_tvar of string
  | Unification
  | Unimplemented of string

val string_of_error : error -> string

val elab : Ast.program -> (Typed.program, error) result
