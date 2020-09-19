let parens level prec fmt f =
  if prec > level then (
    Format.pp_print_char fmt '(';
    f ();
    Format.pp_print_char fmt ')';
  ) else (
    f ()
  )

let pp_head fmt = function
  | Type.Cstr -> Format.pp_print_string fmt "Cstring"
  | Num(sign, size) ->
     begin match sign with
     | Type.Signed -> Format.pp_print_string fmt "Int"
     | Unsigned -> Format.pp_print_string fmt "Nat"
     end;
     begin match size with
     | Type.Sz8 -> Format.pp_print_string fmt "8"
     | Type.Sz16 -> Format.pp_print_string fmt "16"
     | Type.Sz32 -> Format.pp_print_string fmt "32"
     | Type.Sz64 -> Format.pp_print_string fmt "64"
     end
  | Adt adt -> Format.pp_print_string fmt adt.Type.adt_name

let rec pp_type prec fmt = function
  | Type.Neu(head, tys) ->
     parens 4 prec fmt (fun () ->
         pp_head fmt head;
         Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.pp_print_string fmt " ")
           (pp_type 0) fmt tys
       )
  | Fun { dom; codom } ->
     parens 0 prec fmt (fun () ->
         Format.pp_print_string fmt "fun(";
         Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
           (pp_type 0) fmt dom;
         Format.pp_print_string fmt ") -> ";
         pp_type 0 fmt codom
       )
  | Pointer _ -> ()
  | KArrow(dom, codom) ->
     parens 2 prec fmt (fun () ->
         pp_type 3 fmt dom;
         Format.pp_print_string fmt " -> ";
         pp_type 2 fmt codom
       )
  | Unit -> Format.pp_print_string fmt "()"
  | Univ -> Format.pp_print_string fmt "type"
  | Rigid _ -> ()
  | Var _ -> ()

let pp_with_vbox n fmt f =
  Format.pp_open_vbox fmt n;
  f fmt;
  Format.pp_close_box fmt ()

let pp_elab_error fmt = function
  | Error.Expected_function_type ->
     Format.pp_print_string fmt "Expected a function type"
  | Incomplete_match ->
     Format.pp_print_string fmt "Incomplete match"
  | Not_enough_arguments ->
     Format.pp_print_string fmt "Not enough arguments"
  | Not_enough_patterns ->
     Format.pp_print_string fmt "Not enough patterns"
  | Not_enough_typeargs ->
     Format.pp_print_string fmt "Not enough typeargs"
  | Redefined s ->
     Format.pp_print_string fmt "Redefined ";
     Format.pp_print_string fmt s
  | Syntax ->
     Format.pp_print_string fmt "Syntax error"
  | Too_many_arguments ->
     Format.pp_print_string fmt "Too many arguments"
  | Too_many_patterns ->
     Format.pp_print_string fmt "Too many patterns"
  | Too_many_typeargs ->
     Format.pp_print_string fmt "Too many typeargs"
  | Undefined s ->
     Format.pp_print_string fmt "Undefined ";
     Format.pp_print_string fmt s
  | Undefined_tvar s ->
     Format.pp_print_string fmt "Undefined type variable ";
     Format.pp_print_string fmt s
  | Unify { actual_mismatch; expected_mismatch; expected; actual } ->
     pp_with_vbox 0 fmt (fun fmt ->
         Format.pp_print_string fmt "Cannot unify ";
         pp_type 0 fmt actual_mismatch;
         Format.pp_print_string fmt " and ";
         pp_type 0 fmt expected_mismatch;
         Format.pp_print_break fmt 1 0;
         Format.pp_print_string fmt "Expected type: ";
         pp_type 0 fmt expected;
         Format.pp_print_break fmt 1 0;
         Format.pp_print_string fmt "Actual type: ";
         pp_type 0 fmt actual
       )
  | Unimplemented s ->
     Format.pp_print_string fmt "Unimplemented ";
     Format.pp_print_string fmt s
