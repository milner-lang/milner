type t

val compare : t -> t -> int

val hash : t -> int

type gen

val init_gen : gen

val fresh : gen -> t * gen

val gensym : string -> gen -> t * gen
