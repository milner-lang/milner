type calling_conv =
  | Milner
  | C

type fun_attrs = {
    is_entry : bool;
    calling_conv : calling_conv;
  }
