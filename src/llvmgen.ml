let with_module llctx name f =
  let llmod = Llvm.create_module llctx name in
  Fun.protect (fun () -> f llmod) ~finally:(fun () -> Llvm.dispose_module llmod)
