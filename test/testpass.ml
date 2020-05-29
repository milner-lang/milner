open Milner

let () =
  List.iter (fun str ->
      let chan = open_in ("runpass/" ^ str) in
      Fun.protect (fun () ->
          let lexbuf = Sedlexing.Utf8.from_channel chan in
          match Lexer.read lexbuf with
          | Error _ -> failwith "Test failed: Parse error"
          | Ok program ->
             match Elab.run (Elab.elab program) with
             | Error _ -> failwith "Test failed: Constraints"
             | Ok (_, cs) ->
                match Constraint.solve_many Constraint.Symtable.empty cs with
                | Error e ->
                   (* Constraint solver not complete yet *)
                   failwith e
                | Ok () -> ()
        ) ~finally:(fun () -> close_in chan)
    ) ["fun.ml"]
