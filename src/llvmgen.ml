module Vartbl =
  Hashtbl.Make(
      struct
        type t = Ir.ns Var.t
        let hash = Var.hash
        let equal lhs rhs = Var.compare lhs rhs = 0
      end)

type datacon =
  | Tag_Uninhabited
  | Tag_Zero
  | Tag_Type of Llvm.lltype

type datatype =
  | Uninhabited
  | Zero
  | Product of Llvm.lltype
  | Sum of Llvm.lltype * datacon array

type prelude = {
    strcmp : Llvm.llvalue;
  }

type status =
  | External of Type.t
  | Internal of Ir.fun_def

(** The state associated with the entire codegen phase *)
type global = {
    llmod : Llvm.llmodule;
    llctx : Llvm.llcontext;
    prelude : prelude;
    types : (string, datatype) Hashtbl.t;
    poly_funs : (string, status) Hashtbl.t;
    layout : Llvm_target.DataLayout.t;
  }

(** The state associated with the instantiation of a function *)
type t = {
    llbuilder : Llvm.llbuilder;
    llvals : Llvm.llvalue Vartbl.t;
    llfun : Llvm.llvalue;
    bbs : (int, Llvm.llbasicblock) Hashtbl.t;
    regs : (int, Llvm.llvalue) Hashtbl.t;
    real_params : Llvm.lltype option list;
    ty_args : Type.t array;
  }

let with_module llctx name f =
  let llmod = Llvm.create_module llctx name in
  Fun.protect (fun () -> f llmod)
    ~finally:(fun () -> Llvm.dispose_module llmod)

let remove_nones list = List.filter_map Fun.id list

let rec mangle_ty type_args ty =
  match UnionFind.find ty with
  | UnionFind.Value (Type.Constr adt) -> adt.Type.adt_name
  | UnionFind.Value (Type.Prim prim) ->
     (* Ints and nats share the same machine representation, so instantiations
        for ints and nats can share the same code *)
     begin match prim with
     | Type.Cstr -> "cstr"
     | Type.Num(_, Type.Sz8) -> "int8"
     | Type.Num(_, Type.Sz16) -> "int16"
     | Type.Num(_, Type.Sz32) -> "int32"
     | Type.Num(_, Type.Sz64) -> "int64"
     | Type.Unit -> "unit"
     end
  | UnionFind.Value (Type.Fun _fun_ty) -> ""
  | UnionFind.Value (Type.Pointer _) -> "pointer"
  | UnionFind.Value (Type.Rigid v) -> mangle_ty type_args type_args.(v)
  | UnionFind.Root _ -> failwith "Unsolved type"

let mangle_fun type_args name fun_ty =
  let buf = Buffer.create 32 in
  Buffer.add_string buf name;
  List.iter (fun ty ->
      let s = mangle_ty type_args ty in
      Buffer.add_string buf (Int.to_string (String.length s));
      Buffer.add_string buf s
    ) fun_ty.Type.dom;
  Buffer.contents buf

let transl_size llctx = function
  | Type.Sz8 -> Llvm.i8_type llctx
  | Type.Sz16 -> Llvm.i16_type llctx
  | Type.Sz32 -> Llvm.i32_type llctx
  | Type.Sz64 -> Llvm.i64_type llctx

(** The unit type does not translate into a machine type. *)
let rec transl_ty global ty_args ty =
  let llctx = global.llctx in
  match UnionFind.find ty with
  | UnionFind.Value (Type.Constr _adt) ->
     let mangled = mangle_ty [||] ty in
     begin match Hashtbl.find global.types mangled with
     | Uninhabited -> None
     | Zero -> None
     | Product ty -> Some ty
     | Sum(ty, _) -> Some ty
     end
  | UnionFind.Value (Type.Prim prim) ->
     begin match prim with
     | Type.Cstr -> Some (Llvm.pointer_type (Llvm.i8_type llctx))
     | Type.Num(_, sz) -> Some (transl_size llctx sz)
     | Type.Unit -> None
     end
  | UnionFind.Value (Type.Fun fun_ty) ->
     let params, ret = transl_fun_ty global ty_args fun_ty in
     let params = params |> remove_nones |> Array.of_list in
     Some (Llvm.function_type ret params)
  | UnionFind.Value (Type.Pointer _) ->
     Some (Llvm.pointer_type (Llvm.i8_type llctx))
  | UnionFind.Value (Type.Rigid v) -> transl_ty global ty_args ty_args.(v)
  | UnionFind.Root _ -> failwith "Unsolved type"

(** In the parameter type list, the unit type translates to None. In the return
    type, the unit type translates to Some void. *)
and transl_fun_ty global ty_args fun_ty =
  let params = List.map (transl_ty global ty_args) fun_ty.Type.dom in
  let ret =
    match transl_ty global ty_args fun_ty.Type.codom with
    | None -> Llvm.void_type global.llctx
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
let rec emit_aexp global t = function
  | Ir.Param idx ->
     (* If the variable doesn't map to anything, it must have an erased type *)
     Option.map (Llvm.param t.llfun) (real_param_idx idx t.real_params)
  | Ir.Global(name, targs) ->
     begin match Hashtbl.find global.poly_funs name with
     | External _ ->
        begin match Llvm.lookup_function name global.llmod with
        | None -> assert false
        | Some func -> Some func
        end
     | Internal fun_def ->
        let mangled_name = mangle_fun targs name fun_def.Ir.fun_ty in
        begin match Llvm.lookup_function mangled_name global.llmod with
        | None -> Some (emit_fun global targs fun_def)
        | Some func -> Some func
        end
     end
  | Ir.Int32 n -> Some (Llvm.const_int (Llvm.i32_type global.llctx) n)
  | Ir.String s ->
     Some (Llvm.build_global_stringptr s "" t.llbuilder)
  | Ir.Var v ->
     Option.map (fun llval -> Llvm.build_load llval "" t.llbuilder)
       (Vartbl.find_opt t.llvals v)
  | Ir.Reg n -> Some (Hashtbl.find t.regs n)
  | Ir.Unit -> None

and emit_cmp kind global t dest lhs rhs =
  match emit_aexp global t lhs, emit_aexp global t rhs with
  | None, None -> failwith "Unreachable: lhs and rhs cannot be unit"
  | None, Some _ -> failwith "Unreachable: lhs cannot be unit"
  | Some _, None -> failwith "Unreachable: rhs cannot be unit"
  | Some lhs, Some rhs ->
     let llval =
       Llvm.build_icmp kind lhs rhs ("r" ^ Int.to_string dest) t.llbuilder
     in
     Hashtbl.add t.regs dest llval

and emit_expr global t = function
  | Ir.Switch(ty, scrut, cases, default) ->
     let size = match UnionFind.find ty with
       | UnionFind.Value (Type.Prim (Type.Num(_, sz))) -> sz
       | _ -> failwith "Unreachable: Not an int"
     in
     let default = match default with
       | Some (Block default) -> Hashtbl.find t.bbs default
       | None ->
          let bb = Llvm.append_block global.llctx "" t.llfun in
          let curr_bb = Llvm.insertion_block t.llbuilder in
          Llvm.position_at_end bb t.llbuilder;
          ignore (Llvm.build_unreachable t.llbuilder);
          Llvm.position_at_end curr_bb t.llbuilder;
          bb
     in
     begin match emit_aexp global t scrut with
     | None -> ignore (Llvm.build_br default t.llbuilder)
     | Some scrut ->
        let sw =
          Llvm.build_switch scrut default
            (Ir.IntMap.cardinal cases) t.llbuilder
        in
        Ir.IntMap.iter (fun idx (Ir.Block bb) ->
            let idx = Llvm.const_int (transl_size global.llctx size) idx in
            let bb = Hashtbl.find t.bbs bb in
            Llvm.add_case sw idx bb) cases
     end
  | Ir.Continue (Block bb) ->
     let bb = Hashtbl.find t.bbs bb in
     ignore (Llvm.build_br bb t.llbuilder)
  | Ir.If(test, Block then_, Block else_) ->
     begin match emit_aexp global t test with
     | None -> failwith "Unreachable: Test is erased"
     | Some test ->
        let then_ = Hashtbl.find t.bbs then_ in
        let else_ = Hashtbl.find t.bbs else_ in
        ignore (Llvm.build_cond_br test then_ else_ t.llbuilder)
     end
  | Ir.Let_aexp(dest, aexp, next) ->
     begin match emit_aexp global t aexp with
     | None -> ()
     | Some llval ->
        let loc = Vartbl.find t.llvals dest in
        ignore (Llvm.build_store llval loc t.llbuilder)
     end;
     emit_expr global t next
  | Ir.Let_app(dest, f, args, next) ->
     begin match emit_aexp global t f with
     | None -> failwith "Unreachable: Function is not erased"
     | Some f ->
        let args =
          List.map (emit_aexp global t) args |> remove_nones |> Array.of_list
        in
        let llval = Llvm.build_call f args "" t.llbuilder in
        begin match transl_ty global t.ty_args (Var.ty dest) with
        | None -> ()
        | Some _ ->
           let loc = Vartbl.find t.llvals dest in
           ignore (Llvm.build_store llval loc t.llbuilder);
        end;
        emit_expr global t next
     end
  | Ir.Let_get_tag(tag_reg, scrut, next) ->
     let scrut_llval = Vartbl.find t.llvals scrut in
     let tagval = Llvm.build_gep scrut_llval [||] "" t.llbuilder in
     Hashtbl.add t.regs tag_reg tagval;
     emit_expr global t next
  | Ir.Let_get_member(dest, reg, idx, next) ->
     let casted = Hashtbl.find t.regs reg in
     let llval =
       Llvm.build_gep casted
         [|Llvm.const_int (Llvm.i32_type global.llctx) idx|] "" t.llbuilder
     in
     Vartbl.add t.llvals dest llval;
     emit_expr global t next
  | Ir.Let_select_tag(reg, v, constr, next) ->
     let llval = Vartbl.find t.llvals v in
     let mangled = mangle_ty t.ty_args (Var.ty v) in
     begin match Hashtbl.find_opt global.types mangled with
     | Some (Sum(_, constrs)) ->
        begin match constrs.(constr) with
        | Tag_Type llty ->
           let casted = Llvm.build_bitcast llval llty "" t.llbuilder in
           Hashtbl.add t.regs reg casted;
           emit_expr global t next
        | Tag_Zero -> emit_expr global t next
        | Tag_Uninhabited -> ignore (Llvm.build_unreachable t.llbuilder)
        end
     | Some _ -> failwith "Not a sum type"
     | None -> failwith "Mangled type not found"
     end
  | Ir.Let_eqint32(dest, lhs, rhs, next) ->
     emit_cmp Llvm.Icmp.Eq global t dest lhs rhs;
     emit_expr global t next
  | Ir.Let_gtint32(dest, lhs, rhs, next) ->
     emit_cmp Llvm.Icmp.Sgt global t dest lhs rhs;
     emit_expr global t next
  | Ir.Let_strcmp(dest, lhs, rhs, next) ->
     begin match emit_aexp global t lhs, emit_aexp global t rhs with
     | None, None -> failwith "Unreachable: lhs and rhs cannot be unit"
     | None, Some _ -> failwith "Unreachable: lhs cannot be unit"
     | Some _, None -> failwith "Unreachable: rhs cannot be unit"
     | Some lhs, Some rhs ->
        let llval =
          Llvm.build_call global.prelude.strcmp [|lhs; rhs|]
            ("tmp" ^ Int.to_string dest) t.llbuilder
        in
        Hashtbl.add t.regs dest llval;
        emit_expr global t next
     end
  | Ir.Let_cont(bbname, cont, next) ->
     let bb = Llvm.append_block global.llctx (Int.to_string bbname) t.llfun in
     Hashtbl.add t.bbs bbname bb;
     (* Important: Must visit [next] FIRST because it may define registers used
        in the continuation *)
     emit_expr global t next;
     let curr_bb = Llvm.insertion_block t.llbuilder in
     Llvm.position_at_end bb t.llbuilder;
     emit_expr global t cont;
     Llvm.position_at_end curr_bb t.llbuilder
  | Ir.Return aexp ->
     match emit_aexp global t aexp with
     | None -> ignore (Llvm.build_ret_void t.llbuilder)
     | Some llval -> ignore (Llvm.build_ret llval t.llbuilder)

and emit_fun global ty_args fun_def =
  let mangled = mangle_fun ty_args fun_def.Ir.fun_name fun_def.Ir.fun_ty in
  match Llvm.lookup_function mangled global.llmod with
  | Some func -> func
  | None ->
     let llctx = Llvm.module_context global.llmod in
     let real_params, ret_ty =
       transl_fun_ty global ty_args fun_def.Ir.fun_ty in
     let param_tys = real_params |> remove_nones |> Array.of_list in
     let lltype = Llvm.function_type ret_ty param_tys in
     let llfun = Llvm.define_function mangled lltype global.llmod in
     let entry = Llvm.entry_block llfun in
     let llbuilder = Llvm.builder_at_end llctx entry in
     let t = {
         llbuilder;
         llfun;
         llvals = Vartbl.create (List.length fun_def.fun_vars);
         bbs = Hashtbl.create 10;
         regs = Hashtbl.create 10;
         real_params;
         ty_args;
       }
     in
     (* Allocate stack space for all local variables *)
     List.iter (fun var ->
         match transl_ty global ty_args (Var.ty var) with
         | None -> ()
         | Some mach_ty ->
            let llval = Llvm.build_alloca mach_ty "" llbuilder in
            Vartbl.add t.llvals var llval
       ) fun_def.fun_vars;
     emit_expr global t fun_def.fun_body;
     llfun

let emit_module llctx name prog =
  let llmod = Llvm.create_module llctx name in
  try
    let poly_funs = Hashtbl.create 33 in
    let cstr_ty = Llvm.pointer_type (Llvm.i8_type llctx) in
    let strcmp =
      let ty = Llvm.function_type (Llvm.i32_type llctx) [| cstr_ty; cstr_ty |]
      in Llvm.declare_function "strcmp" ty llmod
    in
    let global = {
        llctx;
        llmod;
        prelude = { strcmp };
        types = Hashtbl.create 33;
        poly_funs;
        layout = Llvm_target.DataLayout.of_string (Llvm.data_layout llmod)
      }
    in
    List.iter (function
        | Ir.External(name, ty) ->
           Hashtbl.add poly_funs name (External ty)
        | Ir.Fun fun_def ->
           Hashtbl.add poly_funs fun_def.Ir.fun_name (Internal fun_def)
      ) prog.Ir.decls;
    List.iter (function
        | Ir.External(name, ty) ->
           begin match transl_ty global [||] ty with
           | Some ty ->
              ignore (Llvm.declare_function name ty llmod)
           | None -> failwith "External symbol not a function!"
           end
        | Ir.Fun fun_def ->
           if fun_def.Ir.fun_poly = 0 then
             ignore (emit_fun global [||] fun_def)
      ) prog.Ir.decls;
    llmod
  with
  | e ->
     Llvm.dispose_module llmod;
     raise e
