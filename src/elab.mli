module StringMap : Map.S with type key = string

type error =
  | Redefined of string
  | Unimplemented of string

type 'a t

val run : 'a t -> ('a * Constraint.t list, error) result

module Mon : Monad.MONAD with type 'a t = 'a t

val pat_has_ty : Ast.pat -> Type.t -> (Typed.pat * Type.t StringMap.t) t
val pats_have_tys :
  (Ast.pat Ast.annot * Type.t) list -> (Typed.pat list * Type.t StringMap.t) t
val expr_has_ty : Ast.expr -> Type.t -> Typed.expr t
val clause_has_ty : Ast.clause -> Type.t -> Typed.clause t
val fun_has_ty : Ast.fun_def -> Type.t -> Typed.fun_def t
val elab : Ast.program -> Typed.program t
