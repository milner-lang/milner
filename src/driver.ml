let ( let+ ) m f = Result.map f m

let compile layout prog =
  let+ prog = Elab.elab prog in
  let prog = Ir.compile prog in
  Llvmgen.emit_module layout (Llvm.global_context ()) "main" prog

let read_file path =
  let chan = open_in path in
  Fun.protect (fun () -> Lexer.read (Sedlexing.Utf8.from_channel chan))
    ~finally:(fun () -> close_in chan)
