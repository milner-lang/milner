module StringMap : Map.S with type key = string

type error =
  | Redefined of string
  | Unimplemented of string

type 'a t

val return : 'a -> 'a t

val run : 'a t -> ('a * Constraint.t list, error) result

module BindingOps : sig
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
end

val pat_has_ty : Ast.pat -> Type.t -> Type.t StringMap.t t
val pats_have_tys : (Ast.pat Ast.annot * Type.t) list -> Type.t StringMap.t t
val expr_has_ty : Ast.expr -> Type.t -> unit t
val clause_has_ty : Ast.clause -> Type.t -> unit t
val fun_has_ty : Ast.fun_def -> Type.t -> unit t
val infer_decl : Ast.decl -> unit t
