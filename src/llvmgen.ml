type t = {
    llctx : Llvm.llcontext;
    llmod : Llvm.llmodule;
    llbuilder : Llvm.llbuilder;
    llvals : (ANF.ns Var.t, Llvm.llvalue) Hashtbl.t;
    llfun : Llvm.llvalue;
    bbs : (int, Llvm.llbasicblock) Hashtbl.t;
    strcmp : Llvm.llvalue;
  }

let with_module llctx name f =
  let llmod = Llvm.create_module llctx name in
  Fun.protect (fun () -> f llmod) ~finally:(fun () -> Llvm.dispose_module llmod)

let remove_nones list = List.filter_map Fun.id list

(** The unit type does not translate into a machine type. *)
let rec transl_ty t ty =
  match UnionFind.find ty with
  | UnionFind.Value (Type.Prim prim) ->
     begin match prim with
     | Type.Cstr -> Some (Llvm.pointer_type (Llvm.i8_type t.llctx))
     | Type.Nat8 | Type.Int8 -> Some (Llvm.i8_type t.llctx)
     | Type.Nat16 | Type.Int16 -> Some (Llvm.i16_type t.llctx)
     | Type.Nat32 | Type.Int32 -> Some (Llvm.i32_type t.llctx)
     | Type.Nat64 | Type.Int64 -> Some (Llvm.i64_type t.llctx)
     | Type.Unit -> None
     end
  | UnionFind.Value (Type.Fun fun_ty) ->
     let params, ret = transl_fun_ty t fun_ty in
     let params = params |> remove_nones |> Array.of_list in
     Some (Llvm.function_type ret params)
  | UnionFind.Value (Type.Pointer _) ->
     Some (Llvm.pointer_type (Llvm.i8_type t.llctx))
  | UnionFind.Root _ -> failwith ""

(** In the parameter type list, the unit type translates to None. In the return
    type, the unit type translates to Some void. *)
and transl_fun_ty t fun_ty =
  let params = List.map (transl_ty t) fun_ty.Type.dom in
  let ret =
    match transl_ty t fun_ty.Type.codom with
    | None -> Llvm.void_type t.llctx
    | Some ty -> ty
  in
  (params, ret)

let emit_aexp t = function
  | ANF.Param idx -> Llvm.param t.llfun idx
  | ANF.Int32 n -> Llvm.const_int (Llvm.i32_type t.llctx) n
  | ANF.String s -> Llvm.const_stringz t.llctx s
  | ANF.Var v -> Hashtbl.find t.llvals v
  | ANF.Unit -> failwith "Unimplemented"

let rec emit_expr t = function
  | ANF.Switch(scrut, cases, Block default) ->
     let scrut = emit_aexp t scrut in
     let default = Hashtbl.find t.bbs default in
     let sw =
       Llvm.build_switch scrut default (ANF.IntMap.cardinal cases) t.llbuilder
     in
     ANF.IntMap.iter (fun idx (ANF.Block bb) ->
         let idx = Llvm.const_int (Llvm.i32_type t.llctx) idx in
         let bb = Hashtbl.find t.bbs bb in
         Llvm.add_case sw idx bb) cases
  | ANF.Continue (Block bb) ->
     let bb = Hashtbl.find t.bbs bb in
     ignore (Llvm.build_br bb t.llbuilder)
  | ANF.Let_app(dest, f, args, next) ->
     let f = emit_aexp t f in
     let args = List.map (emit_aexp t) args |> Array.of_list in
     let llval = Llvm.build_call f args "" t.llbuilder in
     Hashtbl.add t.llvals dest llval;
     emit_expr t next
  | ANF.Let_strcmp(dest, lhs, rhs, next) ->
     let lhs = emit_aexp t lhs in
     let rhs = emit_aexp t rhs in
     let llval = Llvm.build_call t.strcmp [|lhs; rhs|] "" t.llbuilder in
     Hashtbl.add t.llvals dest llval;
     emit_expr t next
  | ANF.Let_cont(bbname, cont, next) ->
     let bb = Llvm.append_block t.llctx (Int.to_string bbname) t.llfun in
     Hashtbl.add t.bbs bbname bb;
     let curr_bb = Llvm.insertion_block t.llbuilder in
     Llvm.position_at_end bb t.llbuilder;
     emit_expr t cont;
     Llvm.position_at_end curr_bb t.llbuilder;
     emit_expr t next
  | ANF.Return aexp ->
     let llval = emit_aexp t aexp in
     ignore (Llvm.build_ret llval t.llbuilder)

let emit_fun t fun_def =
  let param_tys, ret_ty = transl_fun_ty t fun_def.ANF.fun_ty in
  let param_tys = param_tys |> remove_nones |> Array.of_list in
  let lltype = Llvm.function_type ret_ty param_tys in
  let llfun = Llvm.define_function fun_def.fun_name lltype t.llmod in
  let entry = Llvm.entry_block llfun in
  Llvm.position_at_end entry t.llbuilder;
  emit_expr t fun_def.ANF.fun_body
