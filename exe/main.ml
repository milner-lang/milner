open Cmdliner
open Milner

let ( let+ ) m f = Result.map f m
let ( let* ) = Result.bind

let emit_llvm =
  Arg.(value @@ flag @@ info ["emit-llvm"])

let triple =
  let open Llvm_target in
  Arg.(value @@ opt string (Target.default_triple ()) @@ info ["target"])

let in_files =
  Arg.(non_empty @@ pos_all string [] @@ info [])

let out_file =
  Arg.(value @@ opt string "a.o" @@ info ["o"; "out"])

let compile triple emit_llvm out_file = function
  | [] -> assert false
  | file :: _files ->
     match
       let open Llvm_target in
       let* prog = Driver.read_file file in
       let+ llmod = Driver.compile prog in
       if emit_llvm then (
         Llvm.dump_module llmod
       ) else (
         Llvm_all_backends.initialize ();
         let target = Target.by_triple triple in
         let mach = TargetMachine.create ~triple target in
         TargetMachine.emit_to_file
           llmod CodeGenFileType.ObjectFile out_file mach
       )
     with
     | Error e -> failwith e
     | Ok () -> ()

let cmd =
  Term.(const compile $ triple $ emit_llvm $ out_file $ in_files, info "")

let () =
  Term.exit @@ Term.eval cmd
