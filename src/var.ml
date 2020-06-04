type _ t = {
    id : int;
    mutable names : string list;
  }

let add_name t name =
  t.names <- name :: t.names

let compare lhs rhs = compare lhs.id rhs.id

let hash t = t.id

let to_string t =
  let rec loop acc = function
    | [] -> acc
    | str :: strs -> loop (str ^ "," ^ acc) strs
  in (Int.to_string t.id) ^ "@" ^ loop "" t.names

type _ gen = int

let init_gen = 0

let fresh gen =
  ({ id = gen; names = [] }, gen + 1)
