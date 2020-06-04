(** [t] is intended to be indexed by a phantom type indicating its namespace. *)
type _ t

val add_name : _ t -> string -> unit

val compare : 'namespace t -> 'namespace t -> int

val hash : _ t -> int

val to_string : _ t -> string

(** The fresh variable generator ['ns gen] is tied to namespace ['ns]. *)
type _ gen

val init_gen : _ gen

val fresh : 'namespace gen -> 'namespace t * 'namespace gen
