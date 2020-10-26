open Parser

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
  Hashtbl.add keywords "boxed" BOXED;
  Hashtbl.add keywords "datatype" DATATYPE;
  Hashtbl.add keywords "external" EXTERNAL;
  Hashtbl.add keywords "fun" FUN;
  Hashtbl.add keywords "type" TYPE;
  Hashtbl.add keywords "val" VAL

let rec tokenize lexbuf = match%sedlex lexbuf with
  | '@' -> Ok AMP
  | '|' -> Ok BAR
  | ':' -> Ok COLON
  | ',' -> Ok COMMA
  | '.' -> Ok DOT
  | '=' -> Ok EQUALS
  | '(' -> Ok LPAREN
  | ')' -> Ok RPAREN
  | '<' -> Ok LANGLE
  | '>' -> Ok RANGLE
  | ']' -> Ok RSQR
  | ';' -> Ok SEMICOLON
  | '_' -> Ok UNDERSCORE
  | '"' -> string (Buffer.create 17) lexbuf
  | 0x2192 (* → *) -> Ok ARROW
  | "->" -> Ok ARROW
  | "[@" -> Ok LSQRAT
  | base10_int ->
     let str = Sedlexing.Utf8.lexeme lexbuf in
     Ok (INT_LIT (int_of_string str))
  | lident ->
     let str = Sedlexing.Utf8.lexeme lexbuf in
     Ok (match Hashtbl.find_opt keywords str with
         | Some kw -> kw
         | None -> LIDENT str)
  | uident ->
     let str = Sedlexing.Utf8.lexeme lexbuf in
     Ok (UIDENT str)
  | eof -> Ok EOF
  | white_space -> tokenize lexbuf
  | _ -> Error Error.Syntax

and string buffer lexbuf = match%sedlex lexbuf with
  | '"' -> Ok (STRING_LIT (Buffer.contents buffer))
  | eof -> Error Error.Syntax
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
  | _ -> Error Error.Syntax

module I = Parser.MenhirInterpreter

let rec loop lexbuf checkpoint = match checkpoint with
  | I.Shifting _ | I.AboutToReduce _ -> loop lexbuf (I.resume checkpoint)
  | I.HandlingError _ -> Result.Error Error.Syntax
  | I.Accepted v -> Ok v
  | I.Rejected -> assert false
  | I.InputNeeded _env ->
     Result.bind (tokenize lexbuf) (fun token ->
         let startp, endp = Sedlexing.lexing_positions lexbuf in
         loop lexbuf (I.offer checkpoint (token, startp, endp))
       )

let read lexbuf =
  let start, _ = Sedlexing.lexing_positions lexbuf in
  loop lexbuf (Parser.Incremental.program start)
