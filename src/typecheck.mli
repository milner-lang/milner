module StringMap : Map.S with type key = string

type error =
  | Redefined of string
  | Not_enough_params of int
  | Too_many_params of int
  | Unbound of string
  | Unimplemented of string

type 'a t

val return : 'a -> 'a t

val run : 'a t -> ('a, error) result

module BindingOps : sig
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
end

val infer_pat : Ast.pat -> (Type.t * Type.t StringMap.t) t
val infer_pats : Ast.pat Ast.annot list -> (Type.t list * Type.t StringMap.t) t
val infer_expr : Ast.expr -> Type.t t
val infer_clause : Ast.clause -> (Type.t list * Type.t) t
val infer_fun : Ast.fun_def -> unit t
