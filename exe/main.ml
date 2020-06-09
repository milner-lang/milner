open Cmdliner
open Milner

let ( let+ ) m f = Result.map f m
let ( let* ) = Result.bind

let in_files =
  Arg.(non_empty @@ pos_all string [] @@ info [])

let out_file =
  Arg.(value @@ opt string "a.o" @@ info ["o"; "out"])

let compile out_file = function
  | [] -> failwith ""
  | file :: _files ->
     let* prog = Driver.read_file file in
     let+ llmod = Driver.compile prog in
     Llvm_all_backends.initialize ();
     let open Llvm_target in
     print_endline (Target.default_triple ());
     let target = Target.by_triple (Target.default_triple ()) in
     let mach =
       TargetMachine.create ~triple:(Target.default_triple ()) target
     in
     TargetMachine.emit_to_file llmod CodeGenFileType.ObjectFile out_file mach

let cmd =
  Term.(eval (const compile $ out_file $ in_files, info ""))

let () =
  Term.(exit @@ cmd)
