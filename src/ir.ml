module L = Dlist
module IntMap = Map.Make(Int)
module StrMap = Map.Make(String)
module VarHash = struct
  type t = Typed.ns Var.t
  let hash = Var.hash
  let equal x y = Var.compare x y = 0
end
module Vartbl = Hashtbl.Make(VarHash)

(** [ns] is type-level data intended to index [Var.t] *)
type ns

module VarCmp = struct
  type t = ns Var.t
  let compare = Var.compare
end
module VarMap = Map.Make(VarCmp)

type reg = int

type aexp =
  | Param of int
  | Global of string * Type.t array
  | Int32 of int
  | String of string
  | Var of ns Var.t
  | Reg of reg
  | Unit

type cont = Block of int

type expr =
  | Switch of Type.t * aexp * cont IntMap.t * cont option
  | Continue of cont * (ns Var.t * string) list
  | If of aexp * cont * cont
  | Let_aexp of ns Var.t * aexp * expr
  | Let_app of ns Var.t * aexp * aexp list * expr
  | Let_constr of ns Var.t * int * aexp list * expr
  | Let_get_member of ns Var.t * ns Var.t * reg * int * expr
  | Let_get_tag of int * ns Var.t * expr
  | Let_select_tag of reg * ns Var.t * int * expr
  (** [Let_select_tag(reg, v, c, k)] casts tagged union [v] to case [c]
      and stores result in register [reg] before continuing to [k] *)
  | Let_eqint32 of int * aexp * aexp * expr
  | Let_gtint32 of int * aexp * aexp * expr
  | Let_strcmp of int * aexp * aexp * expr
  | Let_cont of int * (string * ns Var.t) list * expr * expr
  | Return of aexp

type fun_def = {
    fun_name : string;
    fun_ty : Type.fun_ty;
    fun_poly : int;
    fun_vars : ns Var.t list;
    fun_body : expr;
  }

type decl =
  | External of string * Type.t
  | Fun of fun_def

type program = {
    decls : decl list;
  }

type state = {
    var_gen : ns Var.gen;
    reg_gen : int;
    block_gen : int;
    var_map : ns Var.t Vartbl.t;
  }

type 'a t = state -> ('a * ns Var.t L.t, string) result * state

let init_state () = {
    var_gen = Var.init_gen;
    reg_gen = 0;
    block_gen = 0;
    var_map = Vartbl.create 100;
  }

let run action =
  let r, _ = action (init_state ()) in
  match r with
  | Error e -> Error e
  | Ok (a, _) -> Ok a

module Mon : Monad.MONAD with type 'a t = 'a t = struct
  type nonrec 'a t = 'a t

  let return a s = (Ok (a, L.empty), s)

  let ( let+ ) m f s =
    let r, s = m s in
    match r with
    | Error e -> (Error e, s)
    | Ok (a, l) -> (Ok (f a, l), s)

  let ( and+ ) m1 m2 s =
    let r1, s = m1 s in
    match r1 with
    | Error e -> Error e, s
    | Ok (a, l1) ->
       let r2, s = m2 s in
       match r2 with
       | Error e -> Error e, s
       | Ok (b, l2) -> Ok ((a, b), L.append l1 l2), s

  let ( and* ) = ( and+ )

  let ( let* ) m f s =
    let r, s = m s in
    match r with
    | Error e -> Error e, s
    | Ok (a, l1) ->
       match f a s with
       | Error e, s -> Error e, s
       | Ok (b, l2), s -> Ok (b, L.append l1 l2), s
end

open Mon
open Monad.List(Mon)

let throw e s = (Error e, s)

let fresh ty s =
  let v, var_gen = Var.fresh s.var_gen ty in
  (Ok (v, L.singleton v), { s with var_gen })

(** Phi variables don't get allocated on the stack, so don't add them to the
    list of variables *)
let fresh_phi ty s =
  let v, var_gen = Var.fresh s.var_gen ty in
  (Ok (v, L.empty), { s with var_gen })

let fresh_reg s =
  let r = s.reg_gen in
  Ok (r, L.empty), { s with reg_gen = r + 1 }

let get_state s = (Ok (s, L.empty), s)

let get_vars m s =
  match m s with
  | Error e, s -> Error e, s
  | Ok (a, l), s -> Ok ((a, l), l), s

let refresh var =
  let+ var' = fresh (Var.ty var)
  and+ s = get_state in
  Vartbl.add s.var_map var var';
  var'

let refresh_phi var =
  let+ var' = fresh_phi (Var.ty var)
  and+ s = get_state in
  Vartbl.add s.var_map var var';
  var'

let find_var var s =
  match Vartbl.find_opt s.var_map var with
  | Some aexp -> (Ok (aexp, L.empty), s)
  | None -> failwith ("Unreachable: var not found " ^ Var.to_string var)

let fresh_block s =
  (Ok (s.block_gen, L.empty), { s with block_gen = s.block_gen + 1 })

let rec compile_case_tree rhs = function
  | Typed.Leaf(idx, params) ->
     let action, _, _ = rhs.(idx) in
     let+ params =
       mapM (fun (var, name) ->
           let+ var = find_var var in
           (var, name)
         ) params
     in
     Continue(Block action, params)
  | Split(_, scrut, cases) ->
     let* tag_reg = fresh_reg (* Register to store the tag *)
     and* scrut = find_var scrut in
     let+ _, blocks, jumptable =
       List.fold_left (fun acc (vars, tree) ->
           let* i, blocks, map = acc
           and* vars = mapM refresh vars
           and* casted_reg = fresh_reg in
           let+ branch = compile_case_tree rhs tree
           and+ block_id = fresh_block in
           let rec get_members j = function
             | [] -> branch
             | var :: vars ->
                Let_get_member
                  (var, scrut, casted_reg, j, get_members (j + 1) vars)
           in
           ( i + 1
           , ( block_id
             , Let_select_tag(casted_reg, scrut, i, get_members 0 vars)
             ) :: blocks
           , IntMap.add i (Block block_id) map )
         ) (return (0, [], IntMap.empty)) cases
     in
     let expr =
       let ty = Type.Prim (Type.Num(Type.Unsigned, Type.Sz8)) in
       Let_get_tag(
           tag_reg, scrut,
           Switch(ty, Reg tag_reg, jumptable, None))
     in
     List.fold_right (fun (block_id, branch) expr ->
         Let_cont(block_id, [], branch, expr)
       ) blocks expr
  | Split_int(scrut, cases, otherwise) ->
     let+ scrut = find_var scrut
     and+ blocks, jumptable =
       IntMap.fold (fun n tree acc ->
           let* blocks, map = acc in
           let+ branch = compile_case_tree rhs tree
           and+ block_id = fresh_block in
           ((block_id, branch) :: blocks, IntMap.add n (Block block_id) map)
         ) cases (return ([], IntMap.empty))
     and+ default_id = fresh_block
     and+ default = compile_case_tree rhs otherwise in
     let ty = Type.Prim (Type.Num(Type.Unsigned, Type.Sz32)) in
     let expr =
       Let_cont(default_id, [], default,
                Switch(ty, Var scrut, jumptable, Some (Block default_id)))
     in
     List.fold_right (fun (block_id, branch) expr ->
         Let_cont(block_id, [], branch, expr)
       ) blocks expr
  | Split_str(scrut, cases, otherwise) ->
     let* scrut = find_var scrut in
     (* When pattern matching on a string, use a binary search *)
     let rec make_binary_search default array lo hi =
       if lo = hi then
         return default
       else
         let pivot = lo + (hi - lo) / 2 in
         let test_str, cont = array.(pivot) in
         let+ strtest_result = fresh_reg
         and+ eq_result = fresh_reg
         and+ gt_result = fresh_reg
         and+ left_id = fresh_block
         and+ right_id = fresh_block
         and+ gt_id = fresh_block
         and+ left = make_binary_search default array lo pivot
         and+ right = make_binary_search default array (pivot + 1) hi in
         Let_cont(
             left_id, [], left,
             Let_cont(
                 right_id, [], right,
                 Let_cont(
                     gt_id, [],
                     Let_gtint32(
                         gt_result, Reg strtest_result, Int32 0,
                         If(Reg gt_result, Block right_id, Block left_id)),
                     Let_strcmp(
                         strtest_result, Var scrut, String test_str,
                         Let_eqint32(
                                eq_result, Reg strtest_result, Int32 0,
                                If(Reg eq_result, cont, Block gt_id))))))
     in
     let* blocks, jumptable =
       StrMap.fold (fun str tree acc ->
           let* blocks, map = acc in
           let+ branch = compile_case_tree rhs tree
           and+ block_id = fresh_block in
           ((block_id, branch) :: blocks, StrMap.add str (Block block_id) map)
         ) cases (return ([], StrMap.empty))
     and* default_id = fresh_block
     and* default = compile_case_tree rhs otherwise in
     let array = Array.of_list (StrMap.bindings jumptable) in
     let+ search =
       make_binary_search (Continue(Block default_id, []))
         array 0 (Array.length array)
     in
     List.fold_right (fun (block_id, branch) expr ->
         Let_cont(block_id, [], branch, expr)
       ) blocks (Let_cont(default_id, [], default, search))

let rec compile_expr exp k =
  match exp with
  | Typed.Apply_expr(ty, f, args) ->
     compile_expr f (fun f ->
         List.fold_left (fun k arg args ->
             compile_expr arg (fun arg -> k (arg :: args))
           ) (fun args ->
             let* v = fresh ty in
             let+ body = k (Var v) in
             Let_app(v, f, args, body)
           ) args []
       )
  | Typed.Constr_expr(ty, idx, args) ->
     List.fold_left (fun k arg args ->
         compile_expr arg (fun arg -> k (arg :: args))
       ) (fun args ->
         let* v = fresh ty in
         let+ body = k (Var v) in
         Let_constr(v, idx, args, body)
       ) args []
  | Typed.Global_expr(name, targs) -> k (Global(name, targs))
  | Typed.Int_expr(_, n) -> k (Int32 n) (* Treat all ints as int32 for now *)
  | Typed.Str_expr s -> k (String s)
  | Typed.Seq_expr(e1, e2) ->
     compile_expr e1 (fun _ -> compile_expr e2 (fun e2 -> k e2))
  | Typed.Unit_expr -> k Unit
  | Typed.Var_expr var ->
     let* var = find_var var in
     k (Var var)

let compile_fun fun_def =
  let n = List.length fun_def.Typed.fun_ty.dom in
  let compile_body =
    (* Everything needs to be inside the action [compile_body] so that
       all generated variables can be collected by [get_vars] *)
    let* params = mapM refresh fun_def.Typed.fun_params in
    let* exprs =
      mapM (fun (cont_params, expr) ->
          let+ cont_id = fresh_block
          and+ cont_params =
            StrMap.fold (fun string var acc ->
                let+ ls = acc
                and+ var = refresh_phi var in
                (string, var) :: ls
              ) cont_params (return [])
          and+ expr = compile_expr expr (fun x -> return (Return x)) in
          cont_id, cont_params, expr) fun_def.Typed.fun_clauses
    in
    let block_mapping = Array.of_list exprs in
    let+ entry = compile_case_tree block_mapping fun_def.Typed.fun_tree in
    let expr =
      List.fold_right (fun (cont_id, cont_params, expr) next ->
          Let_cont(cont_id, cont_params, expr, next)
        ) exprs entry
    in
    let _, body =
      List.fold_right (fun var (i, expr) ->
          i - 1, Let_aexp(var, Param (i - 1), expr))
        params (n, expr)
    in body
  in
  let+ (body, vars) = get_vars compile_body in
  { fun_name = fun_def.Typed.fun_name;
    fun_ty = fun_def.Typed.fun_ty;
    fun_poly = fun_def.fun_typarams;
    fun_vars = L.to_list vars;
    fun_body = body }

let compile_decl = function
  | Typed.External(name, ty) -> return (External(name, ty))
  | Typed.Fun fun_def ->
     let+ fun_def = compile_fun fun_def in
     Fun fun_def

let compile_program program =
  let+ decls = mapM compile_decl program.Typed.decls in
  { decls }

let compile program = run (compile_program program)
