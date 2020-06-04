type error =
  | Redefined of string
  | Undefined of string
  | Unimplemented of string

val elab : Ast.program -> (Typed.program * Constraint.t list, error) result
