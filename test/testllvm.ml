open Milner

let () =
  let llctx = Llvm.global_context () in
  Llvmgen.with_module llctx "main" (fun llmod ->
      let ty = Llvm.function_type (Llvm.i32_type llctx) [||] in
      let main = Llvm.declare_function "main" ty llmod in
      let bb = Llvm.append_block llctx "entry" main in
      let builder = Llvm.builder llctx in
      Llvm.position_at_end bb builder;
      ignore (Llvm.build_ret (Llvm.const_int (Llvm.i32_type llctx) 0) builder);
      Llvm_analysis.assert_valid_module llmod
    )
