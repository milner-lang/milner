let parens level buf prec f =
  if prec > level then (
    Buffer.add_char buf '(';
    f ();
    Buffer.add_char buf ')';
  ) else (
    f ()
  )

let pp_head buf = function
  | Type.Cstr ->
     Buffer.add_string buf "Cstring"
  | Num(sign, size) ->
     begin match sign with
     | Type.Signed ->
        Buffer.add_string buf "Int"
     | Unsigned ->
        Buffer.add_string buf "Nat"
     end;
     begin match size with
     | Type.Sz8 ->
        Buffer.add_string buf "8"
     | Type.Sz16 ->
        Buffer.add_string buf "16"
     | Type.Sz32 ->
        Buffer.add_string buf "32"
     | Type.Sz64 ->
        Buffer.add_string buf "64"
     end
  | Adt adt ->
     Buffer.add_string buf adt.Type.adt_name

let rec pp_type buf prec = function
  | Type.Neu(head, []) -> pp_head buf head
  | Type.Neu(head, ty :: tys) ->
     parens 0 buf prec (fun () ->
         pp_head buf head;
         Buffer.add_string buf " ";
         pp_type buf prec ty;
         List.iter (fun ty ->
             Buffer.add_char buf ' ';
             pp_type buf prec ty
           ) tys
       )
  | Fun { dom = []; codom } ->
     parens 0 buf prec (fun () ->
         Buffer.add_string buf "fun() -> ";
         pp_type buf prec codom
       )
  | Fun { dom = ty :: tys; codom } ->
     parens 0 buf prec (fun () ->
         Buffer.add_string buf "fun(";
         pp_type buf prec ty;
         List.iter (fun ty ->
             Buffer.add_string buf ", ";
             pp_type buf prec ty
           ) tys;
         Buffer.add_string buf ") -> ";
         pp_type buf prec codom
       )
  | Pointer _ -> ()
  | KArrow(dom, codom) ->
     parens 0 buf prec (fun () ->
         pp_type buf 1 dom;
         Buffer.add_string buf " -> ";
         pp_type buf 0 codom
       )
  | Unit -> Buffer.add_string buf "()"
  | Univ -> Buffer.add_string buf "type"
  | Rigid _ -> ()
  | Var _ -> ()

let string_of_type ty =
  let buf = Buffer.create 10 in
  pp_type buf 0 ty;
  Buffer.contents buf
