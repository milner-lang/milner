open Cmdliner
open Milner

let ( let+ ) m f = Result.map f m
let ( let* ) = Result.bind

let emit_llvm =
  Arg.(value @@ flag @@ info ["emit-llvm"])

let triple =
  let open Llvm_target in
  let doc = "The target triple" in
  Arg.(value @@ opt string (Target.default_triple ())
       @@ info ~docv:"TARGET" ~doc ["target"])

let in_files =
  let doc = "The file to compile" in
  Arg.(non_empty @@ pos_all string [] @@ info ~docv:"FILE" ~doc [])

let out_file =
  Arg.(value @@ opt string "a.o" @@ info ["o"; "output"])

let compile triple emit_llvm out_file = function
  | [] -> assert false
  | file :: _files ->
     match
       let open Llvm_target in
       let* prog = Driver.read_file file in
       let+ llmod = Driver.compile prog in
       if emit_llvm then (
         Llvm.dump_module llmod;
         ignore (Llvm_bitwriter.write_bitcode_file llmod out_file)
       ) else (
         Llvm_all_backends.initialize ();
         let target = Target.by_triple triple in
         let mach =
           TargetMachine.create ~triple ~reloc_mode:RelocMode.PIC target
         in
         TargetMachine.emit_to_file
           llmod CodeGenFileType.ObjectFile out_file mach
       )
     with
     | Ok () -> ()
     | Error e -> output_string stderr (e ^ "\n")

let cmd =
  Term.(const compile $ triple $ emit_llvm $ out_file $ in_files, info "")

let () =
  Term.exit @@ Term.eval cmd
