open Milner

let () =
  List.iter (fun str ->
      let chan = open_in ("runpass/" ^ str) in
      Fun.protect (fun () ->
          let lexbuf = Sedlexing.Utf8.from_channel chan in
          match Lexer.read lexbuf with
          | Error _ -> failwith "Test failed: Parse error"
          | Ok program ->
             List.iter (fun a ->
                 match a.Ast.annot_item with
                 | Ast.Extern -> ()
                 | Ast.Fun fun_def ->
                    match Typecheck.run (Typecheck.infer_fun fun_def) with
                    | Error _ -> failwith "Test failed: Type error"
                    | Ok () -> ()
               ) program.Ast.decls
        ) ~finally:(fun () -> close_in chan)
    ) ["fun.ml"]
