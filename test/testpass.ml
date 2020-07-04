open Milner

let test_dir dir =
  let handle = Unix.opendir dir in
  Fun.protect (fun () ->
      let rec loop () =
          let str = Unix.readdir handle in
          if str <> "." && str <> ".." then (
            let chan = open_in (dir ^ "/" ^ str) in
            Fun.protect (fun () ->
                let lexbuf = Sedlexing.Utf8.from_channel chan in
                match Lexer.read lexbuf with
                | Error _ -> failwith "Test failed: Parse error"
                | Ok program ->
                   match
                     Elab.elab program |> Result.map_error Elab.string_of_error
                   with
                   | Error e -> failwith ("Test failed: Constraint gen " ^ e)
                   | Ok prog ->
                      match Ir.compile prog with
                      | Error e -> failwith ("Test failed: ANF: " ^ e)
                      | Ok prog ->
                         let llctx = Llvm.global_context () in
                         let llmod = Llvmgen.emit_module llctx "main" prog in
                         Fun.protect (fun () ->
                             Llvm_analysis.assert_valid_module llmod
                           ) ~finally:(fun () -> Llvm.dispose_module llmod)
              ) ~finally:(fun () -> close_in chan)
          );
          loop ()
      in try loop () with End_of_file -> ()
    ) ~finally:(fun () -> Unix.closedir handle)

let () =
  test_dir "runpass";
  test_dir "../examples"
