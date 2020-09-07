open Parser

exception Unexpected_EOF

let digit = [%sedlex.regexp? '0'..'9']
let upper = [%sedlex.regexp? 'A'..'Z']
let lower = [%sedlex.regexp? 'a'..'z']
let alphanum = [%sedlex.regexp? upper | lower | digit | '_' | '\'']

let base10_int = [%sedlex.regexp? Plus digit]
let lident = [%sedlex.regexp? lower, Star alphanum]
let uident = [%sedlex.regexp? upper, Star alphanum]

let keywords = Hashtbl.create 23

let () =
  Hashtbl.add keywords "as" AS;
  Hashtbl.add keywords "datatype" DATATYPE;
  Hashtbl.add keywords "external" EXTERNAL;
  Hashtbl.add keywords "forall" FORALL;
  Hashtbl.add keywords "fun" FUN;
  Hashtbl.add keywords "val" VAL

let rec tokenize lexbuf = match%sedlex lexbuf with
  | '|' -> BAR
  | ':' -> COLON
  | ',' -> COMMA
  | '.' -> DOT
  | '=' -> EQUALS
  | '(' -> LPAREN
  | ')' -> RPAREN
  | '<' -> LANGLE
  | '>' -> RANGLE
  | ';' -> SEMICOLON
  | '_' -> UNDERSCORE
  | '"' -> string (Buffer.create 17) lexbuf
  | 0x2192 (* → *) -> ARROW
  | 0x2200 (* ∀ *) -> FORALL
  | "->" -> ARROW
  | base10_int, "i32" ->
     let str = Sedlexing.Utf8.lexeme lexbuf in
     INT32_LIT (int_of_string (String.sub str 0 (String.length str - 3)))
  | base10_int ->
     let str = Sedlexing.Utf8.lexeme lexbuf in
     INT_LIT (int_of_string str)
  | lident ->
     let str = Sedlexing.Utf8.lexeme lexbuf in
     begin match Hashtbl.find_opt keywords str with
     | Some kw -> kw
     | None -> LIDENT str
     end
  | uident ->
     let str = Sedlexing.Utf8.lexeme lexbuf in
     UIDENT str
  | eof -> EOF
  | white_space -> tokenize lexbuf
  | _ -> failwith "Lexer failure"

and string buffer lexbuf = match%sedlex lexbuf with
  | '"' -> STRING_LIT (Buffer.contents buffer)
  | eof -> raise Unexpected_EOF
  | any ->
     let str = Sedlexing.Utf8.lexeme lexbuf in
     Buffer.add_string buffer str;
     string buffer lexbuf
  (* Escape sequences *)
  | "\\\"" ->
     Buffer.add_char buffer '"';
     string buffer lexbuf
  | "\\n" ->
     Buffer.add_char buffer '\n';
     string buffer lexbuf
  | "\\t" ->
     Buffer.add_char buffer '\t';
     string buffer lexbuf
  | _ -> failwith ""

module I = Parser.MenhirInterpreter

let rec loop lexbuf checkpoint = match checkpoint with
  | I.InputNeeded _env ->
     let token = tokenize lexbuf in
     let startp, endp = Sedlexing.lexing_positions lexbuf in
     loop lexbuf (I.offer checkpoint (token, startp, endp))
  | I.Shifting _ | I.AboutToReduce _ ->
     loop lexbuf (I.resume checkpoint)
  | I.HandlingError _ -> Result.Error "Syntax error"
  | I.Accepted v -> Ok v
  | I.Rejected -> assert false

let read lexbuf =
  let start, _ = Sedlexing.lexing_positions lexbuf in
  loop lexbuf (Parser.Incremental.program start)
