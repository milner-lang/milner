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
             | Error _ -> failwith "Test failed: Constraint gen"
             | Ok (prog, cs, tys) ->
                match
                  Constraint.solve_many (Constraint.Vartbl.create 100) cs
                with
                | Error e ->
                   (* Constraint solver not complete yet *)
                   failwith ("Test failed: Solver: " ^ e)
                | Ok () ->
                   match ANF.compile tys prog with
                   | Error e -> failwith ("Test failed: ANF: " ^ e)
                   | Ok prog ->
                      let llctx = Llvm.global_context () in
                      let llmod = Llvmgen.emit_module llctx "main" prog in
                      Fun.protect (fun () ->
                          match Llvm_analysis.verify_module llmod with
                          | None -> Llvm.dump_module llmod
                          | Some err ->
                             Llvm.dump_module llmod;
                             print_endline err;
                             failwith "Error"
                        ) ~finally:(fun () -> Llvm.dispose_module llmod)
        ) ~finally:(fun () -> close_in chan)
    ) ["fun.ml"]
