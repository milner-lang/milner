type 'a t

type 'a representative =
  | Value of 'a
  | Root of int * 'a t

val find : 'a t -> 'a representative

val union : ('a -> 'a -> 'b) -> 'b -> 'a t -> 'a t -> 'b

type gen

val init_gen : gen

val fresh : gen -> 'a t * gen

val wrap : 'a -> 'a t
