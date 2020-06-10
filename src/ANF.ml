module L = Dlist
module IntMap = Map.Make(Int)
module StrMap = Map.Make(String)

(** [ns] is type-level data intended to index [Var.t] *)
type ns

type aexp =
  | Param of int
  | Global of string
  | Int32 of int
  | String of string
  | Var of ns Var.t
  | Unit

type cont = Block of int

type expr =
  | Switch of aexp * cont IntMap.t * cont
  | Continue of cont
  | Let_aexp of ns Var.t * aexp * expr
  | Let_app of ns Var.t * aexp * aexp list * expr
  | Let_strcmp of ns Var.t * aexp * aexp * expr
  | Let_cont of int * expr * expr
  | Return of aexp

type fun_def = {
    fun_name : string;
    fun_ty : Type.fun_ty;
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
    block_gen : int;
    var_map : (Typed.ns Var.t, ns Var.t) Hashtbl.t;
    prelude_tys : Type.prelude;
  }

type 'a t = state -> ('a * ns Var.t L.t, string) result * state

let init_state prelude_tys = {
    var_gen = Var.init_gen;
    block_gen = 0;
    var_map = Hashtbl.create 100;
    prelude_tys;
  }

let run prelude_tys action =
  let r, _ = action (init_state prelude_tys) in
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

let get_state s = (Ok (s, L.empty), s)

let get_vars m s =
  match m s with
  | Error e, s -> Error e, s
  | Ok (a, l), s -> Ok ((a, l), l), s

let add_var v s =
  Ok ((), L.singleton v), s

let refresh = function
  | [] -> return None
  | (var :: _) as vars ->
     let* var' = fresh (Var.ty var)
     and* s = get_state in
     let+ () = add_var var'
     and+ () =
       iterM (fun var -> return (Hashtbl.add s.var_map var var')) vars
     in
     Some var'

let find_var var s =
  match Hashtbl.find_opt s.var_map var with
  | Some aexp -> (Ok (aexp, L.empty), s)
  | None -> failwith ("Unreachable: var not found " ^ Var.to_string var)

let fresh_block s =
  (Ok (s.block_gen, L.empty), { s with block_gen = s.block_gen + 1 })

let prelude_tys s = (Ok (s.prelude_tys, L.empty), s)

(** The following pattern matching compilation code uses the algorithm from
    Maranget 2008:

    Luc Maranget, Compiling Pattern Matching to Good Decision Trees
    http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf *)

type row = {
    pats : (Typed.pat * ns Var.t option) list;
    action : cont;
  }

type matrix = row list

type refutability =
  | Irrefutable of ns Var.t option list
  | Int_pat of ns Var.t option * int
  | Str_pat of ns Var.t option * int

let find_refutable_pat =
  let rec loop idx wilds = function
    | [] -> Irrefutable(List.rev wilds)
    | (Typed.{ pat_node = Int_pat _; _ }, var) :: _ ->
       Int_pat(var, idx)
    | (Typed.{ pat_node = Str_pat _; _ }, var) :: _ ->
       Str_pat(var, idx)
    | (Typed.{ pat_node = Wild_pat; _ }, var) :: pats ->
       loop (idx + 1) (var :: wilds) pats
  in loop 0 []

(** [split idx list] splits [list] at position [idx] if [idx] is in bounds,
    returning [(ls, x, rs)] where [List.rev_append ls (x :: rs)] = [list]. *)
let split idx =
  let rec loop acc i = function
    | [] -> assert false
    | x :: xs ->
       if i = idx then
         (acc, x, xs)
       else
         loop (x :: acc) (i + 1) xs
  in loop [] 0

let specialize_int idx occs mat =
  let loccs, occ, roccs = split idx occs in
  let occs = List.rev_append loccs roccs in
  let+ map, otherwise =
    fold_leftM (fun (map, otherwise) row ->
        let lpats, (pat, _), rpats = split idx row.pats in
        match pat.Typed.pat_node with
        | Typed.Int_pat(_, n) ->
           let row = { row with pats = List.rev_append lpats rpats } in
           begin match IntMap.find_opt n map with
           | None -> return (IntMap.add n [row] map, otherwise)
           | Some rows -> return (IntMap.add n (row :: rows) map, otherwise)
           end
        | Typed.Wild_pat -> return (map, row :: otherwise)
        | _ -> assert false
      ) (IntMap.empty, []) mat
  in
  (occ, occs, map, List.rev otherwise)

let specialize_str idx occs mat =
  let loccs, occ, roccs = split idx occs in
  let occs = List.rev_append loccs roccs in
  let+ map, otherwise =
    fold_leftM (fun (map, otherwise) row ->
        let lpats, (pat, _), rpats = split idx row.pats in
        match pat.Typed.pat_node with
        | Typed.Str_pat s ->
           let row = { row with pats = List.rev_append lpats rpats } in
           begin match StrMap.find_opt s map with
           | None -> return (StrMap.add s [row] map, otherwise)
           | Some rows -> return (StrMap.add s (row :: rows) map, otherwise)
           end
        | Typed.Wild_pat -> return (map, row :: otherwise)
        | _ -> assert false
      ) (StrMap.empty, []) mat
  in
  (occ, occs, map, List.rev otherwise)

let compile_irrefutable expr occs wilds =
  let rec loop expr = function
    | [], [] -> expr
    | occ :: occs, Some var :: wilds ->
       loop (Let_aexp(var, occ, expr)) (occs, wilds)
    | _ :: occs, None :: wilds -> loop expr (occs, wilds)
    | _ :: _, [] -> assert false
    | [], _ :: _ -> assert false
  in
  loop expr (occs, wilds)

let rec compile_matrix occs mat =
  match mat with
  | [] -> throw "Incomplete pattern match"
  | row :: mat' ->
     match find_refutable_pat row.pats with
     | Irrefutable wilds ->
        begin match mat' with
        | [] -> return (compile_irrefutable (Continue row.action) occs wilds)
        | _ :: _ -> throw "Unreachable code"
        end
     | Int_pat(pat_var, idx) ->
        let* occ, occs', map, otherwise = specialize_int idx occs mat in
        let+ blocks, jumptable =
          IntMap.fold (fun n mat acc ->
              let+ blocks, map = acc
              and+ branch = compile_matrix occs' (List.rev mat)
              and+ block_id = fresh_block in
              ((block_id, branch) :: blocks, IntMap.add n (Block block_id) map)
            ) map (return ([], IntMap.empty))
        and+ default_id = fresh_block
        and+ default = compile_matrix occs otherwise in
        let expr =
          List.fold_right (fun (block_id, branch) expr ->
              Let_cont(block_id, branch, expr)
            ) blocks
            (Let_cont(default_id, default,
                      Switch(occ, jumptable, Block default_id)))
        in
        begin match pat_var with
        | None -> expr
        | Some var -> Let_aexp(var, occ, expr)
        end

     | Str_pat(pat_var, idx) ->
        (* When pattern matching on a string, use a binary search *)
        let rec make_binary_search occ default array lo hi =
          if lo = hi then
            return default
          else
            let pivot = lo + (hi - lo) / 2 in
            let test_str, cont = array.(pivot) in
            let* prelude = prelude_tys in
            let+ test_result = fresh prelude.Type.int32
            and+ left_id = fresh_block
            and+ right_id = fresh_block
            and+ left = make_binary_search occ default array lo pivot
            and+ right = make_binary_search occ default array (pivot + 1) hi in
            let jumptable =
              (* 0 = equals, 1 = greater *)
              IntMap.singleton 0 cont |> IntMap.add 1 (Block right_id)
            in
            Let_strcmp(
                test_result, occ, String test_str,
                Let_cont(
                    left_id, left,
                    Let_cont(
                        right_id, right,
                        (* default branch = less *)
                        Switch(Var test_result, jumptable, Block left_id))))
        in
        let* occ, occs', map, otherwise = specialize_str idx occs mat in
        let* blocks, jumptable =
          StrMap.fold (fun n mat acc ->
              let+ blocks, map = acc
              and+ branch = compile_matrix occs' (List.rev mat)
              and+ block_id = fresh_block in
              ((block_id, branch) :: blocks, StrMap.add n (Block block_id) map)
            ) map (return ([], StrMap.empty))
        and* default_id = fresh_block
        and* default = compile_matrix occs otherwise in
        let array = Array.of_list (StrMap.bindings jumptable) in
        let+ search =
          make_binary_search occ (Continue (Block default_id))
            array 0 (Array.length array)
        in
        let expr =
          List.fold_right (fun (block_id, branch) expr ->
              Let_cont(block_id, branch, expr)
            ) blocks (Let_cont(default_id, default, search))
        in
        begin match pat_var with
        | None -> expr
        | Some var -> Let_aexp(var, occ, expr)
        end

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
  | Typed.Global_expr name -> k (Global name)
  | Typed.Int_expr(_, n) -> k (Int32 n) (* Treat all ints as int32 for now *)
  | Typed.Str_expr s -> k (String s)
  | Typed.Seq_expr(e1, e2) ->
     compile_expr e1 (fun _ -> compile_expr e2 (fun e2 -> k e2))
  | Typed.Unit_expr -> k Unit
  | Typed.Var_expr var ->
     let* var = find_var var in
     k (Var var)

let compile_fun fun_def =
  let Constraint.Forall(_, _, ty) = fun_def.Typed.fun_ty in
  let arity = match UnionFind.find ty with
    | UnionFind.Value (Type.Fun fun_ty) -> fun_ty
    | _ -> assert false
  in
  let params = List.mapi (fun i _ -> Param i) arity.Type.dom in
  let rec create_matrix mat exprs = function
    | [] -> return (List.rev mat, List.rev exprs)
    | clause :: clauses ->
       let* cont_id = fresh_block in
       let* pats =
         mapM (fun pat ->
             let+ var = refresh pat.Typed.pat_vars in
             (pat, var)
           ) clause.Typed.clause_lhs
       in
       create_matrix
         ({ pats; action = Block cont_id } :: mat)
         ((cont_id, clause.Typed.clause_rhs) :: exprs)
         clauses
  in
  let compile_body =
    let* mat, exprs = create_matrix [] [] fun_def.Typed.fun_clauses in
    let* entry = compile_matrix params mat in
    let+ exprs =
      mapM (fun (cont_id, expr) ->
          let+ expr = compile_expr expr (fun x -> return (Return x))
          in cont_id, expr) exprs
    in
    List.fold_right (fun (cont_id, expr) next ->
        Let_cont(cont_id, expr, next)
      ) exprs entry
  in
  let+ (body, vars) = get_vars compile_body in
  { fun_name = fun_def.fun_name;
    fun_ty = arity;
    fun_vars = L.to_list vars;
    fun_body = body }

let compile_decl = function
  | Typed.External(name, ty) ->
     return (External(name, ty))
  | Typed.Fun fun_def ->
     let+ fun_def = compile_fun fun_def in
     Fun fun_def

let compile_program program =
  let+ decls = mapM compile_decl program.Typed.decls in
  { decls }

let compile prelude_tys program = run prelude_tys (compile_program program)
