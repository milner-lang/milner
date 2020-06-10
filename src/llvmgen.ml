module Vartbl =
  Hashtbl.Make(
      struct
        type t = ANF.ns Var.t
        let hash = Var.hash
        let equal lhs rhs = Var.compare lhs rhs = 0
      end)

type prelude = {
    strcmp : Llvm.llvalue;
  }

type t = {
    llctx : Llvm.llcontext;
    llmod : Llvm.llmodule;
    llbuilder : Llvm.llbuilder;
    llvals : Llvm.llvalue Vartbl.t;
    llfun : Llvm.llvalue;
    bbs : (int, Llvm.llbasicblock) Hashtbl.t;
    real_params : Llvm.lltype option list;
    prelude : prelude;
  }

let with_module llctx name f =
  let llmod = Llvm.create_module llctx name in
  Fun.protect (fun () -> f llmod) ~finally:(fun () -> Llvm.dispose_module llmod)

let remove_nones list = List.filter_map Fun.id list

(** The unit type does not translate into a machine type. *)
let rec transl_ty llctx ty =
  match UnionFind.find ty with
  | UnionFind.Value (Type.Prim prim) ->
     begin match prim with
     | Type.Cstr -> Some (Llvm.pointer_type (Llvm.i8_type llctx))
     | Type.Nat8 | Type.Int8 -> Some (Llvm.i8_type llctx)
     | Type.Nat16 | Type.Int16 -> Some (Llvm.i16_type llctx)
     | Type.Nat32 | Type.Int32 -> Some (Llvm.i32_type llctx)
     | Type.Nat64 | Type.Int64 -> Some (Llvm.i64_type llctx)
     | Type.Unit -> None
     end
  | UnionFind.Value (Type.Fun fun_ty) ->
     let params, ret = transl_fun_ty llctx fun_ty in
     let params = params |> remove_nones |> Array.of_list in
     Some (Llvm.function_type ret params)
  | UnionFind.Value (Type.Pointer _) ->
     Some (Llvm.pointer_type (Llvm.i8_type llctx))
  | UnionFind.Root _ -> failwith "Unsolved type"

(** In the parameter type list, the unit type translates to None. In the return
    type, the unit type translates to Some void. *)
and transl_fun_ty llctx fun_ty =
  let params = List.map (transl_ty llctx) fun_ty.Type.dom in
  let ret =
    match transl_ty llctx fun_ty.Type.codom with
    | None -> Llvm.void_type llctx
    | Some ty -> ty
  in
  (params, ret)

let real_param_idx idx list =
  let rec loop i acc list =
    match list, i = idx with
    | [], _ -> failwith "Param index out of bounds"
    | None :: _, true -> None
    | None :: xs, false -> loop (i + 1) acc xs
    | Some _ :: _, true -> Some idx
    | Some _ :: xs, false -> loop (i + 1) (acc + 1) xs
  in loop 0 0 list

(** The unit type is erased. *)
let emit_aexp t = function
  | ANF.Param idx ->
     (* If the variable does not map to anything, it must have an erased type *)
     Option.map (Llvm.param t.llfun) (real_param_idx idx t.real_params)
  | ANF.Global name ->
     begin match Llvm.lookup_function name t.llmod with
     | None -> assert false
     | Some func -> Some func
     end
  | ANF.Int32 n -> Some (Llvm.const_int (Llvm.i32_type t.llctx) n)
  | ANF.String s ->
     Some (Llvm.build_global_stringptr s "" t.llbuilder)
  | ANF.Var v ->
     Option.map (fun llval -> Llvm.build_load llval "" t.llbuilder)
       (Vartbl.find_opt t.llvals v)
  | ANF.Unit -> None

let rec emit_expr t = function
  | ANF.Switch(scrut, cases, Block default) ->
     let default = Hashtbl.find t.bbs default in
     begin match emit_aexp t scrut with
     | None -> ignore (Llvm.build_br default t.llbuilder)
     | Some scrut ->
        let sw =
          Llvm.build_switch scrut default
            (ANF.IntMap.cardinal cases) t.llbuilder
        in
        ANF.IntMap.iter (fun idx (ANF.Block bb) ->
            let idx = Llvm.const_int (Llvm.i32_type t.llctx) idx in
            let bb = Hashtbl.find t.bbs bb in
            Llvm.add_case sw idx bb) cases
     end
  | ANF.Continue (Block bb) ->
     let bb = Hashtbl.find t.bbs bb in
     ignore (Llvm.build_br bb t.llbuilder)
  | ANF.Let_app(dest, f, args, next) ->
     begin match emit_aexp t f with
     | None -> failwith "Unreachable: Function is not erased"
     | Some f ->
        let args =
          List.map (emit_aexp t) args |> remove_nones |> Array.of_list
        in
        let llval = Llvm.build_call f args "" t.llbuilder in
        begin match transl_ty t.llctx (Var.ty dest) with
        | None -> ()
        | Some _ ->
           let loc = Vartbl.find t.llvals dest in
           ignore (Llvm.build_store llval loc t.llbuilder);
        end;
        emit_expr t next
     end
  | ANF.Let_strcmp(dest, lhs, rhs, next) ->
     begin match emit_aexp t lhs, emit_aexp t rhs with
     | None, None -> failwith "Unreachable: lhs and rhs cannot be unit"
     | None, Some _ -> failwith "Unreachable: lhs cannot be unit"
     | Some _, None -> failwith "Unreachable: rhs cannot be unit"
     | Some lhs, Some rhs ->
        let llval =
          Llvm.build_call t.prelude.strcmp [|lhs; rhs|] "" t.llbuilder
        in
        let loc = Vartbl.find t.llvals dest in
        ignore (Llvm.build_store llval loc t.llbuilder);
        emit_expr t next
     end
  | ANF.Let_cont(bbname, cont, next) ->
     let bb = Llvm.append_block t.llctx (Int.to_string bbname) t.llfun in
     Hashtbl.add t.bbs bbname bb;
     emit_expr t next;
     let curr_bb = Llvm.insertion_block t.llbuilder in
     Llvm.position_at_end bb t.llbuilder;
     emit_expr t cont;
     Llvm.position_at_end curr_bb t.llbuilder
  | ANF.Return aexp ->
     match emit_aexp t aexp with
     | None -> ignore (Llvm.build_ret_void t.llbuilder)
     | Some llval -> ignore (Llvm.build_ret llval t.llbuilder)

let emit_fun prelude llmod fun_def =
  let llctx = Llvm.module_context llmod in
  let real_params, ret_ty = transl_fun_ty llctx fun_def.ANF.fun_ty in
  let param_tys = real_params |> remove_nones |> Array.of_list in
  let lltype = Llvm.function_type ret_ty param_tys in
  let llfun = Llvm.define_function fun_def.fun_name lltype llmod in
  let entry = Llvm.entry_block llfun in
  let llbuilder = Llvm.builder_at_end llctx entry in
  let t = {
      llctx;
      llmod;
      llbuilder;
      llfun;
      llvals = Vartbl.create (List.length fun_def.fun_vars);
      bbs = Hashtbl.create 10;
      real_params;
      prelude;
    }
  in
  (* Allocate stack space for all local variables *)
  List.iter (fun var ->
      match transl_ty t.llctx (Var.ty var) with
      | None -> ()
      | Some mach_ty ->
         let llval = Llvm.build_alloca mach_ty "" llbuilder in
         Vartbl.add t.llvals var llval
    ) fun_def.ANF.fun_vars;
  emit_expr t fun_def.ANF.fun_body

let emit_module llctx name prog =
  let llmod = Llvm.create_module llctx name in
  try
    let cstr_ty = Llvm.pointer_type (Llvm.i8_type llctx) in
    let strcmp =
      let ty = Llvm.function_type (Llvm.i32_type llctx) [| cstr_ty; cstr_ty |]
      in Llvm.declare_function "strcmp" ty llmod
    in
    let prelude = {
        strcmp
      }
    in
    List.iter (function
        | ANF.External(name, ty) ->
           begin match transl_ty llctx ty with
           | Some ty ->
              ignore (Llvm.declare_function name ty llmod)
           | None -> failwith "External symbol not a function!"
           end
        | ANF.Fun fun_def ->
           emit_fun prelude llmod fun_def
      ) prog.ANF.decls;
    llmod
  with
  | e ->
     Llvm.dispose_module llmod;
     raise e
