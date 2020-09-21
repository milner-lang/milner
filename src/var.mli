(** [t] is intended to be indexed by a phantom type indicating its namespace. *)
type 'a t = 'a Typing.var

val ty : _ t -> Typing.ty

val add_name : _ t -> string -> unit

val compare : 'ns t -> 'ns t -> int

val equal : 'ns t -> 'ns t -> bool

val hash : _ t -> int

val to_string : _ t -> string

(** The fresh variable generator ['ns gen] is tied to namespace ['ns]. *)
type _ gen

val init_gen : _ gen

val fresh : 'ns gen -> Typing.ty -> 'ns t * 'ns gen
