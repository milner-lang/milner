module Vartbl =
  Hashtbl.Make(
      struct
        type t = Ir.ns Var.t
        let hash = Var.hash
        let equal lhs rhs = Var.compare lhs rhs = 0
      end)

type prelude = {
    strcmp : Llvm.llvalue;
  }

type status =
  | External of Type.t
  | Internal of Ir.fun_def

type t = {
    llctx : Llvm.llcontext;
    llmod : Llvm.llmodule;
    llbuilder : Llvm.llbuilder;
    llvals : Llvm.llvalue Vartbl.t;
    llfun : Llvm.llvalue;
    bbs : (int, Llvm.llbasicblock) Hashtbl.t;
    regs : (int, Llvm.llvalue) Hashtbl.t;
    real_params : Llvm.lltype option list;
    prelude : prelude;
    poly_funs : (string, status) Hashtbl.t;
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
     | Type.Nat8 | Type.Int8 -> "int8"
     | Type.Nat16 | Type.Int16 -> "int16"
     | Type.Nat32 | Type.Int32 -> "int32"
     | Type.Nat64 | Type.Int64 -> "int64"
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

(** The unit type does not translate into a machine type. *)
let rec transl_ty llctx ty_args ty =
  match UnionFind.find ty with
  | UnionFind.Value (Type.Constr _) -> failwith "TODO"
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
     let params, ret = transl_fun_ty llctx ty_args fun_ty in
     let params = params |> remove_nones |> Array.of_list in
     Some (Llvm.function_type ret params)
  | UnionFind.Value (Type.Pointer _) ->
     Some (Llvm.pointer_type (Llvm.i8_type llctx))
  | UnionFind.Value (Type.Rigid v) -> transl_ty llctx ty_args ty_args.(v)
  | UnionFind.Root _ -> failwith "Unsolved type"

(** In the parameter type list, the unit type translates to None. In the return
    type, the unit type translates to Some void. *)
and transl_fun_ty llctx ty_args fun_ty =
  let params = List.map (transl_ty llctx ty_args) fun_ty.Type.dom in
  let ret =
    match transl_ty llctx ty_args fun_ty.Type.codom with
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
let rec emit_aexp t = function
  | Ir.Param idx ->
     (* If the variable doesn't map to anything, it must have an erased type *)
     Option.map (Llvm.param t.llfun) (real_param_idx idx t.real_params)
  | Ir.Global(name, targs) ->
     begin match Hashtbl.find t.poly_funs name with
     | External _ ->
        begin match Llvm.lookup_function name t.llmod with
        | None -> assert false
        | Some func -> Some func
        end
     | Internal fun_def ->
        let mangled_name = mangle_fun targs name fun_def.Ir.fun_ty in
        begin match Llvm.lookup_function mangled_name t.llmod with
        | None -> Some (emit_fun t.prelude t.poly_funs t.llmod targs fun_def)
        | Some func -> Some func
        end
     end
  | Ir.Int32 n -> Some (Llvm.const_int (Llvm.i32_type t.llctx) n)
  | Ir.String s ->
     Some (Llvm.build_global_stringptr s "" t.llbuilder)
  | Ir.Var v ->
     Option.map (fun llval -> Llvm.build_load llval "" t.llbuilder)
       (Vartbl.find_opt t.llvals v)
  | Ir.Reg n -> Some (Hashtbl.find t.regs n)
  | Ir.Unit -> None

and emit_cmp kind t dest lhs rhs =
  match emit_aexp t lhs, emit_aexp t rhs with
  | None, None -> failwith "Unreachable: lhs and rhs cannot be unit"
  | None, Some _ -> failwith "Unreachable: lhs cannot be unit"
  | Some _, None -> failwith "Unreachable: rhs cannot be unit"
  | Some lhs, Some rhs ->
     let llval =
       Llvm.build_icmp kind lhs rhs ("r" ^ Int.to_string dest) t.llbuilder
     in
     Hashtbl.add t.regs dest llval

and emit_expr t = function
  | Ir.Switch(scrut, cases, Block default) ->
     let default = Hashtbl.find t.bbs default in
     begin match emit_aexp t scrut with
     | None -> ignore (Llvm.build_br default t.llbuilder)
     | Some scrut ->
        let sw =
          Llvm.build_switch scrut default
            (Ir.IntMap.cardinal cases) t.llbuilder
        in
        Ir.IntMap.iter (fun idx (Ir.Block bb) ->
            let idx = Llvm.const_int (Llvm.i32_type t.llctx) idx in
            let bb = Hashtbl.find t.bbs bb in
            Llvm.add_case sw idx bb) cases
     end
  | Ir.Continue (Block bb) ->
     let bb = Hashtbl.find t.bbs bb in
     ignore (Llvm.build_br bb t.llbuilder)
  | Ir.If(test, Block then_, Block else_) ->
     begin match emit_aexp t test with
     | None -> failwith "Unreachable: Test is erased"
     | Some test ->
        let then_ = Hashtbl.find t.bbs then_ in
        let else_ = Hashtbl.find t.bbs else_ in
        ignore (Llvm.build_cond_br test then_ else_ t.llbuilder)
     end
  | Ir.Let_aexp(dest, aexp, next) ->
     begin match emit_aexp t aexp with
     | None -> ()
     | Some llval ->
        let loc = Vartbl.find t.llvals dest in
        ignore (Llvm.build_store llval loc t.llbuilder)
     end;
     emit_expr t next
  | Ir.Let_app(dest, f, args, next) ->
     begin match emit_aexp t f with
     | None -> failwith "Unreachable: Function is not erased"
     | Some f ->
        let args =
          List.map (emit_aexp t) args |> remove_nones |> Array.of_list
        in
        let llval = Llvm.build_call f args "" t.llbuilder in
        begin match transl_ty t.llctx t.ty_args (Var.ty dest) with
        | None -> ()
        | Some _ ->
           let loc = Vartbl.find t.llvals dest in
           ignore (Llvm.build_store llval loc t.llbuilder);
        end;
        emit_expr t next
     end
  | Ir.Let_get_tag(_, _, _) ->
     failwith "TODO"
  | Ir.Let_get_member(_, _, _, _) ->
     failwith "TODO"
  | Ir.Let_select_tag _ -> failwith "TODO"
  | Ir.Let_eqint32(dest, lhs, rhs, next) ->
     emit_cmp Llvm.Icmp.Eq t dest lhs rhs;
     emit_expr t next
  | Ir.Let_gtint32(dest, lhs, rhs, next) ->
     emit_cmp Llvm.Icmp.Sgt t dest lhs rhs;
     emit_expr t next
  | Ir.Let_strcmp(dest, lhs, rhs, next) ->
     begin match emit_aexp t lhs, emit_aexp t rhs with
     | None, None -> failwith "Unreachable: lhs and rhs cannot be unit"
     | None, Some _ -> failwith "Unreachable: lhs cannot be unit"
     | Some _, None -> failwith "Unreachable: rhs cannot be unit"
     | Some lhs, Some rhs ->
        let llval =
          Llvm.build_call t.prelude.strcmp [|lhs; rhs|]
            ("tmp" ^ Int.to_string dest) t.llbuilder
        in
        Hashtbl.add t.regs dest llval;
        emit_expr t next
     end
  | Ir.Let_cont(bbname, cont, next) ->
     let bb = Llvm.append_block t.llctx (Int.to_string bbname) t.llfun in
     Hashtbl.add t.bbs bbname bb;
     (* Important: Must visit [next] FIRST because it may define registers used
        in the continuation *)
     emit_expr t next;
     let curr_bb = Llvm.insertion_block t.llbuilder in
     Llvm.position_at_end bb t.llbuilder;
     emit_expr t cont;
     Llvm.position_at_end curr_bb t.llbuilder
  | Ir.Return aexp ->
     match emit_aexp t aexp with
     | None -> ignore (Llvm.build_ret_void t.llbuilder)
     | Some llval -> ignore (Llvm.build_ret llval t.llbuilder)

and emit_fun prelude poly_funs llmod ty_args fun_def =
  let mangled = mangle_fun ty_args fun_def.Ir.fun_name fun_def.Ir.fun_ty in
  match Llvm.lookup_function mangled llmod with
  | Some func -> func
  | None ->
     let llctx = Llvm.module_context llmod in
     let real_params, ret_ty = transl_fun_ty llctx ty_args fun_def.Ir.fun_ty in
     let param_tys = real_params |> remove_nones |> Array.of_list in
     let lltype = Llvm.function_type ret_ty param_tys in
     let llfun = Llvm.define_function mangled lltype llmod in
     let entry = Llvm.entry_block llfun in
     let llbuilder = Llvm.builder_at_end llctx entry in
     let t = {
         llctx;
         llmod;
         llbuilder;
         llfun;
         llvals = Vartbl.create (List.length fun_def.fun_vars);
         bbs = Hashtbl.create 10;
         regs = Hashtbl.create 10;
         real_params;
         prelude;
         poly_funs;
         ty_args;
       }
     in
     (* Allocate stack space for all local variables *)
     List.iter (fun var ->
         match transl_ty t.llctx ty_args (Var.ty var) with
         | None -> ()
         | Some mach_ty ->
            let llval = Llvm.build_alloca mach_ty "" llbuilder in
            Vartbl.add t.llvals var llval
       ) fun_def.fun_vars;
     emit_expr t fun_def.fun_body;
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
    let prelude = {
        strcmp
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
           begin match transl_ty llctx [||] ty with
           | Some ty ->
              ignore (Llvm.declare_function name ty llmod)
           | None -> failwith "External symbol not a function!"
           end
        | Ir.Fun fun_def ->
           if fun_def.Ir.fun_poly = 0 then
             ignore (emit_fun prelude poly_funs llmod [||] fun_def)
      ) prog.Ir.decls;
    llmod
  with
  | e ->
     Llvm.dispose_module llmod;
     raise e
