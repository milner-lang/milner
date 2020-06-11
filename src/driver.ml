let ( let+ ) m f = Result.map f m
let ( let* ) = Result.bind

let compile prog =
  let* prog = Elab.elab prog |> Result.map_error Elab.string_of_error in
  let+ prog = Ir.compile prog in
  Llvmgen.emit_module (Llvm.global_context ()) "main" prog

let read_file path =
  let chan = open_in path in
  Fun.protect (fun () -> Lexer.read (Sedlexing.Utf8.from_channel chan))
    ~finally:(fun () -> close_in chan)
