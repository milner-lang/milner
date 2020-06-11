type 'a t = {
    mutable parent : 'a parent;
  }

and 'a parent =
  | PValue of 'a
  | PRoot of int
  | PNode of 'a t

type 'a representative =
  | Value of 'a
  | Root of int * 'a t

(** Implements the path-halving find algorithm *)
let rec find node = match node.parent with
  | PValue a -> Value a
  | PRoot id -> Root(id, node)
  | PNode node' ->
     node.parent <- node'.parent;
     find node'

let union unify ok lhs rhs =
  match find lhs, find rhs with
  | Root (_, lhs), Root (_, rhs) ->
     rhs.parent <- PNode lhs;
     ok
  | Value a, Root (_, node) | Root (_, node), Value a ->
     node.parent <- PValue a;
     ok
  | Value a, Value b -> unify a b

type gen = int

let init_gen = 0

let fresh gen =
  ({ parent = PRoot gen }, gen + 1)

let wrap a =
  { parent = PValue a }
