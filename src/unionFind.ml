type 'a t = {
    id : int;
    mutable parent : 'a parent;
  }

and 'a parent =
  | PValue of 'a
  | PRoot
  | PNode of 'a t

type 'a representative =
  | Value of 'a
  | Root of 'a t

let id t = t.id

(** Implements the path-halving find algorithm *)
let rec find node = match node.parent with
  | PValue a -> Value a
  | PRoot -> Root node
  | PNode node' ->
     node.parent <- node'.parent;
     find node'

let union unify ok lhs rhs =
  match find lhs, find rhs with
  | Root lhs, Root rhs ->
     rhs.parent <- PNode lhs;
     ok
  | Value a, Root node | Root node, Value a ->
     node.parent <- PValue a;
     ok
  | Value a, Value b -> unify a b

type gen = int

let init_gen = 0

let fresh gen =
  ({ id = gen; parent = PRoot }, gen + 1)

let wrap gen a =
  ({ id = gen; parent = PValue a }, gen + 1)
