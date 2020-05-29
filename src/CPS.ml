type cont =
  | Return
  | Block of int

type aexp =
  | String of string
  | Unit

type expr =
  | Let_cont of cont * Var.t * expr * expr
  | Apply of aexp * aexp list
  | Case_num of (int * expr) list * expr
  | Case_str of (string * expr) list * expr
  | Continue of cont * aexp

type state = {
    var_gen : Var.gen;
  }

type 'a t = state -> 'a * state

module Mon : Monad.MONAD = struct
  type nonrec 'a t = 'a t

  let return a s = (a, s)

  let ( let+ ) m f s =
    let a, s = m s in
    (f a, s)

  let ( and+ ) m1 m2 s =
    let a, s = m1 s in
    let b, s = m2 s in
    (a, b), s

  let ( and* ) = ( and+ )

  let ( let* ) m f s =
    let a, s = m s in
    f a s
end
