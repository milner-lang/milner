type term =
  |

type prim =
  | Cstr
  | Int8
  | Uint8
  | Int16
  | Uint16
  | Int32
  | Uint32
  | Int64
  | Uint64
  | Unit

type ty =
  | Prim of prim
  | Pi of ty list * ty
  | Var of int
