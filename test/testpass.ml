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
                 match
                   Typecheck.run (Typecheck.infer_decl a.Ast.annot_item)
                 with
                 | Error _ -> failwith "Test failed: Constraints"
                 | Ok ((), cs) ->
                    match
                      Constraint.solve_many Constraint.Symtable.empty cs
                    with
                    | Error e ->
                       (* Constraint solver not complete yet *)
                       failwith e
                    | Ok () -> ()
               ) program.Ast.decls
        ) ~finally:(fun () -> close_in chan)
    ) ["fun.ml"]
