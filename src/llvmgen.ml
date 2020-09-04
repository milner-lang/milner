module Vartbl =
  Hashtbl.Make(
      struct
        type t = Ir.ns Var.t
        let hash = Var.hash
        let equal lhs rhs = Var.compare lhs rhs = 0
      end)

type datacon =
  | Tag_uninhabited
  | Tag_type of Llvm.lltype

type datatype =
  | Uninhabited (** A type that cannot be constructed. *)
  | Zero (** An erased type. *)
  | Product of int * Llvm.lltype (** A type with no tag. *)
  | Basic_sum of Llvm.lltype * Llvm.lltype option array
    (** The basic tagged union representation where the first member is the tag
        and the subsequent members are the product type for each constructor,
        and the tags are numbered starting from 0. *)

type transl_ty =
  | Uninhabited_ty
  | Zero_ty
  | Ll_ty of Llvm.lltype

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

type translated_constr =
  | No_constrs
  | One_constr of string * int * Llvm.lltype option list
  | Many_constrs of (string * int * Llvm.lltype option list) list

let with_module llctx name f =
  let llmod = Llvm.create_module llctx name in
  Fun.protect (fun () -> f llmod)
    ~finally:(fun () -> Llvm.dispose_module llmod)

let remove_nones list = List.filter_map Fun.id list

let rec erase_types = function
  | [] -> Some []
  | Uninhabited_ty :: _ -> None
  | Zero_ty :: tys -> Option.map (fun tys -> None :: tys) (erase_types tys)
  | Ll_ty llty :: tys ->
     Option.map (fun tys -> Some llty :: tys) (erase_types tys)

let rec mangle_ty global type_args ty =
  match UnionFind.find ty with
  | UnionFind.Value (Type.Constr adt) ->
     ignore (compile_datatype global adt);
     adt.Type.adt_name
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
  | UnionFind.Value (Type.Rigid v) -> mangle_ty global type_args type_args.(v)
  | UnionFind.Root _ -> failwith "Unsolved type"

and compile_datatype global adt =
  let rec classify_datatype idx = function
    | [] -> No_constrs
    | (name, datacon) :: datacons ->
       match classify_datatype (idx + 1) datacons with
       | No_constrs -> One_constr(name, idx, datacon)
       | One_constr(name', idx', tys') ->
          Many_constrs((name, idx, datacon) :: [name', idx', tys'])
       | Many_constrs datacons ->
          Many_constrs((name, idx, datacon) :: datacons)
  in
  match Hashtbl.find_opt global.types adt.Type.adt_name with
  | Some ty -> ty
  | None ->
     let datacons =
       Array.fold_right (fun (name, tys) acc ->
           match List.map (transl_ty global [||]) tys |> erase_types with
           | None -> acc
           | Some tys -> (name, tys) :: acc
         ) adt.Type.adt_constrs []
     in
     let datatype =
       match classify_datatype 0 datacons with
       | No_constrs -> Uninhabited
       | One_constr(_name, idx, tys) ->
          let ty = Llvm.named_struct_type global.llctx adt.Type.adt_name in
          let tys = tys |> remove_nones |> Array.of_list in
          Llvm.struct_set_body ty tys false;
          Product(idx, ty)
       | Many_constrs datacons ->
          let datacon_arr = Array.make (List.length datacons) None in
          List.iter (fun (name, idx, tys) ->
              let name = adt.Type.adt_name ^ "__" ^ name in
              let ty = Llvm.named_struct_type global.llctx name in
              let tys =
                (Llvm.i8_type global.llctx :: (tys |> remove_nones))
                |> Array.of_list
              in
              Llvm.struct_set_body ty tys false;
              datacon_arr.(idx) <- Some ty
            ) datacons;
          let size =
            Array.fold_left (fun size ty ->
                match ty with
                | None -> size
                | Some ty ->
                   let n = Llvm_target.DataLayout.abi_size ty global.layout in
                   if Int64.compare size n = -1 then
                     n
                   else
                     size)
              Int64.zero datacon_arr
          in
          let ty = Llvm.named_struct_type global.llctx adt.Type.adt_name in
          Llvm.struct_set_body ty
            [| Llvm.i8_type global.llctx
             ; Llvm.array_type
                 (Llvm.i8_type global.llctx)
                 ((Int64.to_int size) - 1) |]
            false;
          Basic_sum(ty, datacon_arr)
     in
     Hashtbl.add global.types adt.Type.adt_name datatype;
     datatype

and mangle_fun global type_args name fun_ty =
  let buf = Buffer.create 32 in
  Buffer.add_string buf name;
  List.iter (fun ty ->
      let s = mangle_ty global type_args ty in
      Buffer.add_string buf (Int.to_string (String.length s));
      Buffer.add_string buf s
    ) fun_ty.Type.dom;
  Buffer.contents buf

and transl_size llctx = function
  | Type.Sz8 -> Llvm.i8_type llctx
  | Type.Sz16 -> Llvm.i16_type llctx
  | Type.Sz32 -> Llvm.i32_type llctx
  | Type.Sz64 -> Llvm.i64_type llctx

(** The unit type does not translate into a machine type. *)
and transl_ty global ty_args ty : transl_ty =
  let llctx = global.llctx in
  match UnionFind.find ty with
  | UnionFind.Value (Type.Constr _adt) ->
     let mangled = mangle_ty global [||] ty in
     begin match Hashtbl.find global.types mangled with
     | Uninhabited -> Uninhabited_ty
     | Zero -> Zero_ty
     | Product(_, ty) -> Ll_ty ty
     | Basic_sum(ty, _) -> Ll_ty ty
     end
  | UnionFind.Value (Type.Prim prim) ->
     begin match prim with
     | Type.Cstr -> Ll_ty (Llvm.pointer_type (Llvm.i8_type llctx))
     | Type.Num(_, sz) -> Ll_ty (transl_size llctx sz)
     | Type.Unit -> Zero_ty
     end
  | UnionFind.Value (Type.Fun fun_ty) ->
     begin match transl_fun_ty global ty_args fun_ty with
     | None -> Uninhabited_ty
     | Some (params, ret) ->
        let params = params |> remove_nones |> Array.of_list in
        Ll_ty (Llvm.function_type ret params)
     end
  | UnionFind.Value (Type.Pointer _) ->
     Ll_ty (Llvm.pointer_type (Llvm.i8_type llctx))
  | UnionFind.Value (Type.Rigid v) -> transl_ty global ty_args ty_args.(v)
  | UnionFind.Root _ -> failwith "Unsolved type"

(** In the parameter type list, the unit type translates to None. In the return
    type, the unit type translates to Some void. *)
and transl_fun_ty global ty_args fun_ty
    : (Llvm.lltype option list * Llvm.lltype) option =
  let params =
    List.map (transl_ty global ty_args) fun_ty.Type.dom |> erase_types
  in
  let ret =
    match transl_ty global ty_args fun_ty.Type.codom with
    | Uninhabited_ty -> None
    | Zero_ty -> Some (Llvm.void_type global.llctx)
    | Ll_ty ty -> Some ty
  in
  match params, ret with
  | Some params, Some ret -> Some (params, ret)
  | _, _ -> None

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
        let mangled_name = mangle_fun global targs name fun_def.Ir.fun_ty in
        begin match Llvm.lookup_function mangled_name global.llmod with
        | None -> emit_fun global targs fun_def
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
  | Ir.Continue(Block bb, args) ->
     let bb = Hashtbl.find t.bbs bb in
     Ir.VarMap.iter (fun k v ->
         match transl_ty global t.ty_args (Var.ty k) with
         | Uninhabited_ty -> failwith "Unreachable"
         | Zero_ty -> ()
         | Ll_ty _ ->
            let phi = Vartbl.find t.llvals k in
            let var = Vartbl.find t.llvals v in
            Llvm.add_incoming (var, Llvm.insertion_block t.llbuilder) phi
       ) args;
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
        match transl_ty global t.ty_args (Var.ty dest) with
        | Uninhabited_ty -> ignore (Llvm.build_unreachable t.llbuilder)
        | Zero_ty -> emit_expr global t next
        | Ll_ty _ ->
           let loc = Vartbl.find t.llvals dest in
           ignore (Llvm.build_store llval loc t.llbuilder);
           emit_expr global t next
     end
  | Ir.Let_constr(dest, constr, args, next) ->
     let args = List.map (emit_aexp global t) args |> remove_nones in
     let mangled = mangle_ty global t.ty_args (Var.ty dest) in
     begin match Hashtbl.find_opt global.types mangled with
     | Some (Basic_sum (_, constrs)) ->
        begin match constrs.(constr) with
        | Some casted_ty ->
           let llval = Vartbl.find t.llvals dest in
           let casted =
             Llvm.build_bitcast llval (Llvm.pointer_type casted_ty) ""
               t.llbuilder
           in
           let tag = Llvm.build_struct_gep casted 0 "" t.llbuilder in
           ignore
             (Llvm.build_store
                (Llvm.const_int (Llvm.i8_type global.llctx) constr) tag
                t.llbuilder);
           List.iteri (fun i llval ->
               let ptr = Llvm.build_struct_gep casted (i + 1) "" t.llbuilder in
               ignore (Llvm.build_store llval ptr t.llbuilder)
             ) args;
           emit_expr global t next
        | None -> ignore (Llvm.build_unreachable t.llbuilder)
        end
     | Some Uninhabited -> ignore (Llvm.build_unreachable t.llbuilder)
     | Some Zero -> emit_expr global t next
     | Some (Product(n, _)) ->
        if constr = n then
          let struct_ = Vartbl.find t.llvals dest in
          List.iteri (fun i llval ->
              let ptr = Llvm.build_struct_gep struct_ i "" t.llbuilder in
              ignore (Llvm.build_store llval ptr t.llbuilder)
            ) args;
          emit_expr global t next
        else
          ignore (Llvm.build_unreachable t.llbuilder)
     | None -> failwith "datatype not found"
     end
  | Ir.Let_get_tag(tag_reg, scrut, next) ->
     let mangled = mangle_ty global t.ty_args (Var.ty scrut) in
     begin match Hashtbl.find_opt global.types mangled with
     | Some(Basic_sum(_, _)) ->
        let scrut_llval = Vartbl.find t.llvals scrut in
        let ptr = Llvm.build_struct_gep scrut_llval 0 "" t.llbuilder in
        let tag = Llvm.build_load ptr "" t.llbuilder in
        Hashtbl.add t.regs tag_reg tag;
        emit_expr global t next
     | Some(Product(idx, _)) ->
        Hashtbl.add t.regs tag_reg
          (Llvm.const_int (Llvm.i8_type global.llctx) idx);
        emit_expr global t next
     | Some _ -> failwith "Not a sum type"
     | None -> failwith "Mangled type not found"
     end
  | Ir.Let_get_member(dest, scrut, reg, idx, next) ->
     let mangled = mangle_ty global t.ty_args (Var.ty scrut) in
     begin match Hashtbl.find_opt global.types mangled with
     | Some(Basic_sum _) ->
        let casted = Hashtbl.find t.regs reg in
        let llval =
          Llvm.build_struct_gep casted (idx + 1) "" t.llbuilder
        in
        Vartbl.add t.llvals dest llval;
        emit_expr global t next
     | Some(Product _) ->
        let scrut = Vartbl.find t.llvals scrut in
        let llval = Llvm.build_struct_gep scrut idx "" t.llbuilder in
        Vartbl.add t.llvals dest llval;
        emit_expr global t next
     | Some _ -> failwith "Not a sum type"
     | None -> failwith "Mangled type not found!"
     end
  | Ir.Let_select_tag(reg, v, constr, next) ->
     let llval = Vartbl.find t.llvals v in
     let mangled = mangle_ty global t.ty_args (Var.ty v) in
     begin match Hashtbl.find_opt global.types mangled with
     | Some (Basic_sum(_, constrs)) ->
        begin match constrs.(constr) with
        | Some llty ->
           let casted =
             Llvm.build_bitcast llval (Llvm.pointer_type llty) "" t.llbuilder
           in
           Hashtbl.add t.regs reg casted;
           emit_expr global t next
        | None -> ignore (Llvm.build_unreachable t.llbuilder)
        end
     | Some(Product(_, _)) -> emit_expr global t next
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
  | Ir.Let_cont(bbname, params, cont, next) ->
     let curr_bb = Llvm.insertion_block t.llbuilder in
     let bb = Llvm.append_block global.llctx (Int.to_string bbname) t.llfun in
     Llvm.position_at_end bb t.llbuilder;
     List.iter (fun cont_param ->
         match transl_ty global t.ty_args (Var.ty cont_param) with
         | Uninhabited_ty -> ()
         | Zero_ty -> ()
         | Ll_ty llty ->
            let phi =
              Llvm.build_empty_phi (Llvm.pointer_type llty) "" t.llbuilder
            in
            Vartbl.add t.llvals cont_param phi
       ) params;
     Hashtbl.add t.bbs bbname bb;
     Llvm.position_at_end curr_bb t.llbuilder;
     (* Important: Must visit [next] FIRST because it may define registers used
        in the continuation *)
     emit_expr global t next;
     Llvm.position_at_end bb t.llbuilder;
     emit_expr global t cont;
     Llvm.position_at_end curr_bb t.llbuilder
  | Ir.Return aexp ->
     match emit_aexp global t aexp with
     | None -> ignore (Llvm.build_ret_void t.llbuilder)
     | Some llval -> ignore (Llvm.build_ret llval t.llbuilder)

and emit_fun global ty_args fun_def : Llvm.llvalue option =
  let mangled =
    mangle_fun global ty_args fun_def.Ir.fun_name fun_def.Ir.fun_ty
  in
  match Llvm.lookup_function mangled global.llmod with
  | Some func -> Some func
  | None ->
     let llctx = Llvm.module_context global.llmod in
     match transl_fun_ty global ty_args fun_def.Ir.fun_ty with
     | None -> None
     | Some (real_params, ret_ty) ->
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
            | Uninhabited_ty -> ()
            | Zero_ty -> ()
            | Ll_ty mach_ty ->
               let llval = Llvm.build_alloca mach_ty "" llbuilder in
               Vartbl.add t.llvals var llval
          ) fun_def.fun_vars;
        emit_expr global t fun_def.fun_body;
        Some llfun

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
           | Ll_ty ty ->
              ignore (Llvm.declare_function name ty llmod)
           | _ -> failwith "External symbol not a function!"
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
