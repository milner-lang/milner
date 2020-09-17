open Cmdliner
open Llvm_target
open Milner

let emit_llvm =
  let doc = "Emit LLVM IR." in
  Arg.(value @@ flag @@ info ~doc ["emit-llvm"])

let triple =
  let open Llvm_target in
  let doc = "The target triple." in
  Arg.(value @@ opt string (Target.default_triple ())
       @@ info ~docv:"TARGET" ~doc ["target"])

let in_files =
  let doc = "The file to compile" in
  Arg.(non_empty @@ pos_all string [] @@ info ~docv:"FILE" ~doc [])

let out_file =
  let doc = "Place the output into $(docv)." in
  Arg.(value @@ opt (some string) None
       @@ info ~docv:"output_file" ~doc ["o"; "output"])

let codegen_filetype =
  let flags =
    [ ( CodeGenFileType.ObjectFile
      , Arg.info ~doc:"Compile only; do not assemble or link." ["c"] )
    ; ( CodeGenFileType.AssemblyFile
      , Arg.info ~doc:"Compile and assemble, but do not link." ["S"] ) ]
  in
  Arg.(value @@ vflag CodeGenFileType.ObjectFile flags)

type reloc =
  | Static
  | Pic
  | Dynamic_no_pic

let reloc_model =
  let doc = "Choose relocation model" in
  let converter =
    Arg.conv
      ((function
        | "static" -> Ok Static
        | "pic" -> Ok Pic
        | "dynamic-no-pic" -> Ok Dynamic_no_pic
        | s -> Error (`Msg s)),
       fun fmt s ->
       match s with
       | Static -> Format.pp_print_string fmt "static"
       | Pic -> Format.pp_print_string fmt "pic"
       | Dynamic_no_pic -> Format.pp_print_string fmt "dynamic-no-pic")
  in
  Arg.(value @@ opt converter Pic @@ info ~doc ["relocation-model"])

let compile triple reloc_model emit_llvm codegen_filetype out_file = function
  | [] -> assert false
  | file :: _files ->
     let mach, layout =
       if triple = "wasm32-unknown-unknown" then
         ( None
         , Llvm_target.DataLayout.of_string "e-m:e-p:32:32-i64:64-n32:64-S128"
         )
       else (
         Llvm_all_backends.initialize ();
         let target = Target.by_triple triple in
         let reloc_mode = match reloc_model with
           | Static -> RelocMode.Static
           | Pic -> RelocMode.PIC
           | Dynamic_no_pic -> RelocMode.DynamicNoPIC
         in
         let mach = TargetMachine.create ~triple ~reloc_mode target in
         Some mach, Llvm_target.TargetMachine.data_layout mach
       ) in
     match
       let ( let* ) = Result.bind in
       let* out_file = match out_file with
         | Some name -> Ok name
         | None ->
            match Filename.chop_suffix_opt ~suffix:".ml" file with
            | None -> Error (Error.Unimplemented "Unknown file extension.")
            | Some base ->
               let s = match emit_llvm, codegen_filetype with
                 | false, CodeGenFileType.ObjectFile -> ".o"
                 | false, CodeGenFileType.AssemblyFile -> ".s"
                 | true, CodeGenFileType.ObjectFile -> ".bc"
                 | true, CodeGenFileType.AssemblyFile -> ".ll"
               in Ok (base ^ s)
       in
       let* prog = Driver.read_file file in
       let* llmod = Driver.compile layout prog in
       Llvm.set_target_triple triple llmod;
       if emit_llvm then (
         begin match codegen_filetype with
         | CodeGenFileType.ObjectFile ->
            ignore (Llvm_bitwriter.write_bitcode_file llmod out_file)
         | CodeGenFileType.AssemblyFile ->
            Llvm.print_module out_file llmod
         end;
         Ok ()
       ) else
         match mach with
         | Some mach ->
            TargetMachine.emit_to_file llmod codegen_filetype out_file mach;
            Ok ()
         | None -> Error (Error.Unimplemented "Wasm target not supported.")
     with
     | Ok () -> ()
     | Error e ->
        Pretty.pp_elab_error Format.err_formatter e;
        Format.pp_print_newline Format.err_formatter ();
        exit 2

let cmd =
  let ( let+ ) tm f = Term.(const f $ tm) in
  let ( and+ ) a b = Term.(const (fun a b -> (a, b)) $ a $ b) in
  ( (let+ triple = triple
     and+ reloc_model = reloc_model
     and+ emit_llvm = emit_llvm
     and+ codegen_filetype = codegen_filetype
     and+ out_file = out_file
     and+ in_files = in_files in
     compile triple reloc_model emit_llvm codegen_filetype out_file in_files)
  , Term.info "milner" )

let () =
  Printexc.record_backtrace true;
  Term.exit @@ Term.eval cmd
