type t =
  | Conj of t * t
  | Eq of Type.t * Type.t
  | Exists of int * t
  | Nat of Type.t
  | True
