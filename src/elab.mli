type error =
  | Redefined of string
  | Undefined of string
  | Unimplemented of string

val string_of_error : error -> string

val elab :
  Ast.program
  -> (Typed.program * Constraint.t list * Type.prelude, error) result
