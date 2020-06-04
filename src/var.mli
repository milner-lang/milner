type t

val add_name : t -> string -> unit

val compare : t -> t -> int

val hash : t -> int

val to_string : t -> string

type gen

val init_gen : gen

val fresh : gen -> t * gen
