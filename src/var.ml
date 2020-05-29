type t = {
    id : int;
    names : string list;
  }

type gen = int

let init_gen = 0

let fresh gen =
  ({ id = gen; names = [] }, gen + 1)

let gensym name gen =
  ({ id = gen; names = [name] }, gen + 1)
