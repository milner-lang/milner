type error

val string_of_error : error -> string

val elab : Ast.program -> (Typed.program, error) result
