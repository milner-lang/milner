open Milner

let () =
  List.iter (fun str ->
      let chan = open_in ("runpass/" ^ str) in
      Fun.protect (fun () ->
          let lexbuf = Sedlexing.Utf8.from_channel chan in
          let start, _ = Sedlexing.lexing_positions lexbuf in
          ignore (Lexer.loop lexbuf (Parser.Incremental.program start))
        ) ~finally:(fun () -> close_in chan)
    ) ["fun.ml"]
