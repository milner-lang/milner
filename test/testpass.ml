open Milner

let () =
  List.iter (fun str ->
      let chan = open_in ("runpass/" ^ str) in
      Fun.protect (fun () ->
          let lexbuf = Sedlexing.Utf8.from_channel chan in
          match Lexer.read lexbuf with
          | Error _ -> failwith "Test failed: Parse error"
          | Ok program ->
             match Elab.elab program with
             | Error _ -> failwith "Test failed: Constraints"
             | Ok (prog, cs) ->
                match Constraint.solve_many (Hashtbl.create 100) cs with
                | Error e ->
                   (* Constraint solver not complete yet *)
                   failwith e
                | Ok () ->
                   match ANF.compile prog with
                   | Error e -> failwith ("Test failed: ANF: " ^ e)
                   | Ok _ -> ()
        ) ~finally:(fun () -> close_in chan)
    ) ["fun.ml"]
