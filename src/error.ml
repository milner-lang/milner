type type_mismatch = {
    actual_mismatch : Typing.ty;
    expected_mismatch : Typing.ty;
    actual : Typing.ty;
    expected : Typing.ty;
  }

type t =
  | Expected_function_type
  | Incomplete_match
  | Not_enough_arguments
  | Not_enough_patterns
  | Not_enough_typeargs
  | Redefined of string
  | Syntax
  | Too_many_arguments
  | Too_many_patterns
  | Too_many_typeargs
  | Undefined of string
  | Undefined_tvar of string
  | Unify of type_mismatch
  | Unimplemented of string
