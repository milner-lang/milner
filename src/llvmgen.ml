module Vartbl =
  Hashtbl.Make(struct
    type t = Ir.ns Var.t
    let hash = Var.hash
    let equal lhs rhs = Var.compare lhs rhs = 0
  end)

type datatype =
  | Uninhabited (** A type that cannot be constructed. *)
  | Zero (** An erased type. *)
  | Product of int * Llvm.lltype (** A type with no tag. *)
  | Basic_sum of Llvm.lltype * Llvm.lltype option array
    (** The basic tagged union representation where the first member is the tag
        and the subsequent members are the product type for each constructor,
        and the tags are numbered starting from 0.

        In the list of product types, [None] means that the product type is
        uninhabited and [Some llty] means that [llty] is the castable struct
        for the corresponding variant. *)

type transl_ty =
  | Uninhabited_ty
  | Zero_ty
  | Ll_ty of Llvm.lltype

type status =
  | External of Typing.ty
  | Internal of Ir.fun_def

(** The state associated with the entire codegen phase *)
type global = {
  llmod : Llvm.llmodule;
  llctx : Llvm.llcontext;
  gc_alloca : Llvm.llvalue;
  gc_malloc : Llvm.llvalue;
  gc_push : Llvm.llvalue;
  strcmp : Llvm.llvalue;
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
  ty_args : Typing.ty array;
  phis : (string, Llvm.llvalue) Hashtbl.t;
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

(** This function returns:

    - [None] if the list of types contains an uninhabited type.
    - [Some tys] otherwise, where an element of [tys] is:
      - [None] if it is erased
      - [Some llty] otherwise *)
let rec erase_types = function
  | [] -> Some []
  | Uninhabited_ty :: _ -> None
  | Zero_ty :: tys -> Option.map (fun tys -> None :: tys) (erase_types tys)
  | Ll_ty llty :: tys ->
     Option.map (fun tys -> Some llty :: tys) (erase_types tys)

let rec mangle_ty global type_args = function
  | Typing.Neu_ty(Typing.Adt adt, tyargs) ->
     let name = mangle_datatype global type_args adt tyargs in
     ignore (compile_datatype global type_args adt tyargs);
     name
  | Typing.Neu_ty(Typing.Cstr, _) -> "cstr"
  | Typing.Neu_ty(Typing.Num(_, sz), _) ->
     (* Ints and nats share the same machine representation, so instantiations
        for ints and nats can share the same code *)
     begin match sz with
     | Typing.Sz8 -> "int8"
     | Typing.Sz16 -> "int16"
     | Typing.Sz32 -> "int32"
     | Typing.Sz64 -> "int64"
     end
  | Typing.Neu_ty(Typing.Unit, _) -> "unit"
  | Typing.Fun_ty _fun_ty -> ""
  | Typing.Ptr_ty _ -> "pointer"
  | Typing.Staticvar_ty v -> mangle_ty global type_args type_args.(v)
  | Typing.Univ_ty -> failwith "univ"
  | Typing.KArrow_ty _ -> failwith "Unreachable"
  | Typing.Const_ty _ -> failwith "Const unimplemented"

and mangle_datatype global type_args adt adt_args =
  let mangled_adt_args = List.rev_map (mangle_ty global type_args) adt_args in
  let rec loop mangled n mangled_adt_args =
    if n = 0 then
      mangled
    else
      match mangled_adt_args with
      | [] -> failwith "Unreachable"
      | x :: xs -> loop (mangled ^ x) (n - 1) xs
  in loop adt.Typing.adt_name adt.Typing.adt_params mangled_adt_args

and compile_datatype global type_args adt adt_tyargs =
  let adt_name = mangle_datatype global type_args adt adt_tyargs in
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
  match Hashtbl.find_opt global.types adt_name with
  | Some ty -> ty
  | None ->
     let datacons =
       Array.fold_right (fun datacon acc ->
           let tyargs = Array.of_list (List.rev adt_tyargs) in
           let tys =
             List.map (Typing.inst tyargs) datacon.Typing.datacon_inputs
           in
           match List.map (transl_ty global type_args) tys |> erase_types with
           | None -> acc
           | Some tys -> (datacon.datacon_name, tys) :: acc)
         adt.Typing.adt_constrs []
     in
     let datatype =
       match classify_datatype 0 datacons with
       | No_constrs -> Uninhabited
       | One_constr(_name, idx, tys) ->
          let ty = Llvm.named_struct_type global.llctx adt.Typing.adt_name in
          let tys = tys |> remove_nones |> Array.of_list in
          Llvm.struct_set_body ty tys false;
          Product(idx, ty)
       | Many_constrs datacons ->
          let datacon_arr = Array.make (List.length datacons) None in
          List.iter (fun (name, idx, tys) ->
              let name = adt_name ^ "__" ^ name in
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
          let ty = Llvm.named_struct_type global.llctx adt.Typing.adt_name in
          Llvm.struct_set_body ty
            [| Llvm.i8_type global.llctx
             ; Llvm.array_type
                 (Llvm.i8_type global.llctx) ((Int64.to_int size) - 1) |]
            false;
          Basic_sum(ty, datacon_arr)
     in
     Hashtbl.add global.types adt_name datatype;
     datatype

and mangle_fun global type_args name fun_ty =
  let buf = Buffer.create 32 in
  Buffer.add_string buf "__milner_";
  Buffer.add_string buf name;
  List.iter (fun ty ->
      let s = mangle_ty global type_args ty in
      Buffer.add_string buf (Int.to_string (String.length s));
      Buffer.add_string buf s
    ) fun_ty.Typing.dom;
  Buffer.contents buf

and transl_size llctx = function
  | Typing.Sz8 -> Llvm.i8_type llctx
  | Typing.Sz16 -> Llvm.i16_type llctx
  | Typing.Sz32 -> Llvm.i32_type llctx
  | Typing.Sz64 -> Llvm.i64_type llctx

(** The unit type does not translate into a machine type. *)
and transl_ty global type_args ty : transl_ty =
  let llctx = global.llctx in
  match ty with
  | Typing.Neu_ty(Typing.Adt adt, adt_args) ->
     let mangled = mangle_datatype global type_args adt adt_args in
     begin match Hashtbl.find global.types mangled with
     | Uninhabited -> Uninhabited_ty
     | Zero -> Zero_ty
     | Product(_, ty) | Basic_sum(ty, _) ->
       match adt.adt_boxing with
       | Boxed -> Ll_ty (Llvm.pointer_type ty)
       | Unboxed -> Ll_ty ty
     end
  | Typing.Neu_ty(Typing.Cstr, _) ->
     Ll_ty (Llvm.pointer_type (Llvm.i8_type llctx))
  | Typing.Neu_ty(Typing.Num(_, sz), _) -> Ll_ty (transl_size llctx sz)
  | Typing.Neu_ty(Typing.Unit, _) -> Zero_ty
  | Typing.Fun_ty fun_ty ->
     begin match transl_fun_ty global type_args fun_ty with
     | None -> Uninhabited_ty
     | Some (params, ret) ->
        let params = params |> remove_nones |> Array.of_list in
        Ll_ty (Llvm.function_type ret params)
     end
  | Typing.Ptr_ty _ -> Ll_ty (Llvm.pointer_type (Llvm.i8_type llctx))
  | Typing.Staticvar_ty v -> transl_ty global type_args type_args.(v)
  | Typing.Univ_ty -> Zero_ty
  | Typing.KArrow_ty _ -> failwith "Unreachable"
  | Typing.Const_ty _ -> failwith "Const unimplemented"

(** In the parameter type list, the unit type translates to None. In the return
    type, the unit type translates to Some void. *)
and transl_fun_ty global ty_args fun_ty =
  match
    List.map (transl_ty global ty_args) fun_ty.Typing.dom |> erase_types
  with
  | None -> None
  | Some params ->
     let ret =
       match transl_ty global ty_args fun_ty.Typing.codom with
       (* The uninhabited type may still be inhabited by nonterminating
          computations, so map it to the void type *)
       | Uninhabited_ty | Zero_ty -> Llvm.void_type global.llctx
       | Ll_ty ty -> ty
     in Some (params, ret)

(** Maps the parameter index of the logical type system's function type to
    the corresponding index of the machine type's function type, for which
    parameters of erased types aren't counted *)
let real_param_idx idx list =
  let rec loop i acc list =
    match list, i = idx with
    | [], _ -> failwith "Param index out of bounds"
    | None :: _, true -> None
    | None :: xs, false -> loop (i + 1) acc xs
    | Some _ :: _, true -> Some acc
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
  | Ir.Switch((_, size), scrut, cases, default) ->
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
     let with_tys =
       List.fold_left (fun acc (var, name) ->
           match acc with
           | None -> None
           | Some ls ->
              match transl_ty global t.ty_args (Var.ty var) with
              | Uninhabited_ty -> None
              | Zero_ty -> Some ((var, name, false) :: ls)
              | Ll_ty _ -> Some ((var, name, true) :: ls))
         (Some []) args
     in
     begin match with_tys with
     | None -> ignore (Llvm.build_unreachable t.llbuilder);
     | Some ls ->
        let bb = Hashtbl.find t.bbs bb in
        List.iter (fun (var, name, b) ->
            if b then
              let phi = Hashtbl.find t.phis name in
              let var = Vartbl.find t.llvals var in
              Llvm.add_incoming (var, Llvm.insertion_block t.llbuilder) phi
          ) ls;
        ignore (Llvm.build_br bb t.llbuilder)
     end
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
     let f = match f with
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
       | _ -> failwith "Unreachable: Function call head"
     in
     begin match f with
       | None -> ignore (Llvm.build_unreachable t.llbuilder)
       | Some f ->
         let args =
           List.map (emit_aexp global t) args
           |> remove_nones
           |> Array.of_list
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
          Llvm.build_call global.strcmp [|lhs; rhs|]
            ("tmp" ^ Int.to_string dest) t.llbuilder
        in
        Hashtbl.add t.regs dest llval;
        emit_expr global t next
    end
  | Ir.Let_cont(bbname, params, cont, next) ->
    let curr_bb = Llvm.insertion_block t.llbuilder in
    let bb = Llvm.append_block global.llctx (Int.to_string bbname) t.llfun in
    Llvm.position_at_end bb t.llbuilder;
    let with_tys =
      List.fold_left (fun acc (name, var) ->
          match acc with
          | None -> None
          | Some ls ->
            match transl_ty global t.ty_args (Var.ty var) with
            | Uninhabited_ty -> None
            | Zero_ty -> Some ((name, var, None) :: ls)
            | Ll_ty ty -> Some ((name, var, Some ty) :: ls))
        (Some []) params
    in
    begin match with_tys with
      | None -> ignore (Llvm.build_unreachable t.llbuilder)
      | Some tys ->
        List.iter (function
            | (_, _, None) -> ()
            | (name, var, Some llty) ->
              let phi =
                Llvm.build_empty_phi (Llvm.pointer_type llty) "" t.llbuilder
              in
              Hashtbl.add t.phis name phi;
              Vartbl.add t.llvals var phi;
          ) tys;
        Hashtbl.add t.bbs bbname bb;
        Llvm.position_at_end curr_bb t.llbuilder;
        (* Important: Must visit [next] FIRST because it may define registers
           used in the continuation *)
        emit_expr global t next;
        Llvm.position_at_end bb t.llbuilder;
        emit_expr global t cont
    end
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
      let llvals = Vartbl.create (List.length fun_def.fun_vars) in
      (* Tell the GC to register a new stack frame *)
      ignore (Llvm.build_call global.gc_push [||] "" llbuilder);
      (* Allocate stack space for all local variables *)
      List.iter (fun var ->
          match transl_ty global ty_args (Var.ty var) with
          | Uninhabited_ty -> ()
          | Zero_ty -> ()
          | Ll_ty mach_ty ->
            let llval = match Var.ty var with
              | Neu_ty(Adt { adt_boxing = Boxed; _ }, _) ->
                Llvm.build_call global.gc_alloca [||] "" llbuilder
              | _ -> Llvm.build_alloca mach_ty "" llbuilder
            in
            Vartbl.add llvals var llval;
        ) fun_def.fun_vars;
      (*let stack_map =
        let prev = Llvm.param llfun 0 in
        (* Alloca the stack map *)
        let stack_map =
          Llvm.build_alloca global.stack_map_ty "" llbuilder in
        let size = Llvm.const_int (Llvm.i32_type global.llctx) num_roots in
        (* Alloca the array of roots *)
        let roots_arr =
          Llvm.build_array_alloca global.root_ty size "" llbuilder
        in
        let prev_member = Llvm.build_struct_gep stack_map 0 "" llbuilder in
        ignore (Llvm.build_store prev prev_member llbuilder);
        let size_member = Llvm.build_struct_gep stack_map 1 "" llbuilder in
        ignore (Llvm.build_store size size_member llbuilder);
        let ptr_member = Llvm.build_struct_gep stack_map 2 "" llbuilder in
        ignore (Llvm.build_store roots_arr ptr_member llbuilder);
        List.iteri (fun idx root ->
            let off =
              Llvm.build_gep roots_arr
                [|Llvm.const_int (Llvm.i64_type global.llctx) idx|] ""
                llbuilder
            in
            (* Set the root to null *)
            ignore
              (Llvm.build_store
                 (Llvm.const_null (Llvm.type_of root)) root llbuilder);
            (* Store the root in the root array *)
            let root_member = Llvm.build_struct_gep off 0 "" llbuilder in
            ignore (Llvm.build_store root root_member llbuilder)
          ) roots;
        stack_map
      in*)
      let t = {
        llbuilder;
        llfun;
        llvals;
        bbs = Hashtbl.create 10;
        regs = Hashtbl.create 10;
        real_params;
        ty_args;
        phis = Hashtbl.create 21;
      }
      in
      emit_expr global t fun_def.fun_body;
      begin
        if fun_def.fun_attrs.is_entry then (
          let ty = Llvm.function_type (Llvm.i32_type llctx) [||] in
          let main = Llvm.define_function "main" ty global.llmod in
          let entry = Llvm.entry_block main in
          let llbuilder = Llvm.builder_at_end llctx entry in
          let ret =
            Llvm.build_call llfun [||]
              "" llbuilder
          in
          ignore (Llvm.build_ret ret llbuilder)
        )
      end;
      Some llfun

let emit_module datalayout llctx name prog =
  let llmod = Llvm.create_module llctx name in
  try
    let poly_funs = Hashtbl.create 33 in
    let cstr_ty = Llvm.pointer_type (Llvm.i8_type llctx) in
    let gc_alloca =
      let ty =
        Llvm.function_type (Llvm.pointer_type (Llvm.void_type llctx)) [||]
      in Llvm.declare_function "gc_alloca" ty llmod
    in
    let gc_malloc =
      let ty =
        Llvm.function_type (Llvm.pointer_type (Llvm.void_type llctx))
          [| Llvm.i32_type llctx |]
      in Llvm.declare_function "gc_malloc" ty llmod
    in
    let gc_push =
      let ty = Llvm.function_type (Llvm.void_type llctx) [||] in
      Llvm.declare_function "gc_push" ty llmod
    in
    let strcmp =
      let ty =
        Llvm.function_type (Llvm.i32_type llctx) [| cstr_ty; cstr_ty |]
      in Llvm.declare_function "strcmp" ty llmod
    in
    let global = {
      llctx;
      llmod;
      gc_alloca;
      gc_malloc;
      gc_push;
      strcmp;
      types = Hashtbl.create 33;
      poly_funs;
      layout = datalayout
    }
    in
    List.iter (function
        | Ir.External(name, ty) ->
          Hashtbl.add poly_funs name (External ty)
        | Ir.Fun fun_def ->
          Hashtbl.add poly_funs fun_def.Ir.fun_name (Internal fun_def)
      ) prog.Ir.decls;
    List.iter (function
        | Ir.External(name, Typing.Fun_ty ty) ->
          begin match transl_fun_ty global [||] ty with
            | None -> failwith "C function has uninhabited type"
            | Some (params, ret) ->
              let params = params |> remove_nones |> Array.of_list in
              let llty = Llvm.function_type ret params in
              ignore (Llvm.declare_function name llty llmod)
          end
        | Ir.External(_name, _) ->
          failwith "External symbol not a function!"
        | Ir.Fun fun_def ->
          if fun_def.Ir.fun_poly = [] then
            ignore (emit_fun global [||] fun_def)
      ) prog.Ir.decls;
    Llvm.set_data_layout
      (Llvm_target.DataLayout.as_string global.layout) llmod;
    llmod
  with
  | e ->
    Llvm.dispose_module llmod;
    raise e
