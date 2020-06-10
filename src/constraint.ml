type t =
  | Eq of Type.t * Type.t
  | Inst of string * Type.t
  | Nat of Type.t

type forall = Forall of Type.t list * t list * Type.t
