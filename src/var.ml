type 'a t = 'a Typing.var

let ty t = t.Typing.ty

let add_name t name =
  t.Typing.names <- name :: t.Typing.names

let compare lhs rhs = compare lhs.Typing.id rhs.Typing.id

let equal lhs rhs = compare lhs rhs = 0

let hash t = t.Typing.id

let to_string t =
  let rec loop acc = function
    | [] -> acc
    | str :: strs -> loop (str ^ "," ^ acc) strs
  in (Int.to_string t.Typing.id) ^ "@" ^ loop "" t.names

type _ gen = int

let init_gen = 0

let fresh gen ty =
  (Typing.{ id = gen; ty; names = [] }, gen + 1)
