module L = Dlist
module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)
module Symtable = ScopedMap.Make(String)

type state = {
    tycons : (string, Typing.head * Typing.ty) Hashtbl.t;
    funcs : (string, Typing.forall) Hashtbl.t;
    metavar_gen : int;
    var_gen : Typing.ns Var.gen;
  }

type 'a payload = {
    data : 'a;
  }

type var_kind =
  | Local of Typing.ns Var.t
  | Global of Typing.forall
  | Type of Typing.ty * Typing.ty

type 'a t =
  var_kind Symtable.t -> state -> ('a payload, Error.t) result * state

let throw e _ s = (Error e, s)

let init_state () =
  let tycons = Hashtbl.create 20 in
  Hashtbl.add tycons "Cstring" (Typing.Cstr, Typing.Univ);
  Hashtbl.add tycons "Int32"
    (Typing.Num(Typing.Signed, Typing.Sz32), Typing.Univ);
  { var_gen = Var.init_gen;
    metavar_gen = 0;
    funcs = Hashtbl.create 20;
    tycons }

let run m =
  let r, _ = m Symtable.empty (init_state ()) in
  match r with
  | Error e -> Error e
  | Ok w -> Ok w.data

module Mon : Monad.MONAD with type 'a t = 'a t = struct
  type nonrec 'a t = 'a t

  let return a _env s = (Ok { data = a }, s)

  let ( let+ ) t f env s =
    let r, s = t env s in
    match r with
    | Error e -> (Error e, s)
    | Ok w -> (Ok { data = f w.data }, s)

  let ( and+ ) t1 t2 env s =
    let r1, s = t1 env s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok w1 ->
       let r2, s = t2 env s in
       match r2 with
       | Error e -> (Error e, s)
       | Ok w2 ->
          ( Ok {
                data = (w1.data, w2.data);
              }
          , s )

  let ( and* ) = ( and+ )

  let ( let* ) t f env s =
    let r1, s = t env s in
    match r1 with
    | Error e -> (Error e, s)
    | Ok w1 ->
       let r2, s = f w1.data env s in
       match r2 with
       | Error e -> (Error e, s)
       | Ok w2 ->
          ( Ok {
                data = w2.data;
              }
          , s )
end

open Mon
open Monad.List(Mon)

let in_scope scope m env s =
  let (r, s) = m (Symtable.extend scope env) s in
  match r with
  | Error e -> (Error e, s)
  | Ok w -> (Ok w, s)

let find name env s =
  match Symtable.find name env with
  | Some var -> (Ok { data = var }, s)
  | None -> (Error (Error.Undefined name), s)

let declare_tycon name tycon kind _ s =
  Hashtbl.add s.tycons name (tycon, kind);
  (Ok { data = () }, s)

let find_tcon name _ s =
  match Hashtbl.find_opt s.tycons name with
  | None -> (Error (Error.Undefined name), s)
  | Some ty -> (Ok { data = ty }, s)

let fresh_var ty _ s =
  let (var, var_gen) = Var.fresh s.var_gen ty in
  (Ok { data = var }, { s with var_gen })

let unify ~expected ~actual =
  match Typing.unify expected actual with
  | Ok s -> return s
  | Error (lhs, rhs) ->
     throw
       (Error.Unify
          { expected_mismatch = lhs
          ; actual_mismatch = rhs
          ; expected
          ; actual })

(** Infer the kind of a type. *)
let rec ty_infer = function
  | Ast.Unit -> return (Typing.Unit, Typing.Univ)
  | Ast.Univ -> return (Typing.Univ, Typing.Univ)
  | Ast.Ty_app(f, x) ->
     let* pair = ty_infer f.Ast.annot_item in
     begin match pair with
     | Typing.Neu(Adt(adt), spine), Typing.KArrow(dom, cod) ->
        let+ x = ty_check x.Ast.annot_item dom in
        Typing.Neu(Adt(adt), x :: spine), cod
     | _ -> throw (Error.Unimplemented "Ty infer app")
     end
  | Ast.Constr_expr(tycon, []) ->
     let+ ty, kind = find_tcon tycon in
     Typing.Neu(ty, []), kind
  | Ast.Arrow(dom, codom) ->
     let+ dom = mapM (fun x -> ty_check x.Ast.annot_item Typing.Univ) dom
     and+ codom, _ = ty_infer codom.Ast.annot_item in
     (Typing.Fun_ty { dom; codom }, Typing.Univ)
  | Ast.Var_expr name ->
     let* x = find name in
     begin match x with
     | Type (v, kind) -> return (v, kind)
     | _ -> throw (Error.Unimplemented "")
     end
  | _ -> throw (Error.Unimplemented "Dependent types")

and ty_check ast_ty kind =
  let* ty, kind' = ty_infer ast_ty in
  let+ _ = unify ~expected:kind ~actual:kind' in
  ty

let read_ty_scheme tvars ty =
  let* _, tvar_map, kinds =
    fold_leftM
      (fun (i, tvars, kinds) (tvar, kind) ->
        let+ kind = ty_check kind.Ast.annot_item Typing.Univ in
        ( i + 1
        , StringMap.add tvar (Type(Typing.Rigid i, kind)) tvars
        , Typing.Univ :: kinds ))
      (0, StringMap.empty, []) tvars
  in
  let+ ty, _ = in_scope tvar_map (ty_infer ty) in
  Typing.Forall(List.rev kinds, ty)

let read_adt adt =
  let constrs =
    (* Dummy values; these should all be replaced *)
    Array.make (List.length adt.Ast.adt_constrs)
      { Typing.datacon_name = ""
      ; datacon_inputs = []
      ; datacon_output = Typing.Univ }
  in
  let* param_count, params, kinds, tparams =
    fold_leftM (fun (i, params, kinds, map) (name, kind) ->
        let+ kind = ty_check kind.Ast.annot_item Typing.Univ in
        let ty = Typing.Rigid i in
        ( i + 1
        , ty :: params
        , kind :: kinds
        , StringMap.add name (Type(ty, kind)) map ))
      (0, [], [], StringMap.empty) adt.Ast.adt_params
  in
  let datacons = Hashtbl.create (Array.length constrs) in
  let rec loop = function
    | [] -> Typing.Univ
    | kind :: kinds -> Typing.KArrow(kind, loop kinds)
  in
  let adt' =
    Typing.{
        adt_name = adt.Ast.adt_name;
        adt_params = param_count;
        adt_kind = loop kinds;
        adt_constr_names = datacons;
        adt_constrs = constrs;
    }
  in
  let* _ =
    fold_leftM (fun i (name, tys) ->
        let+ tys =
          mapM (fun ann -> in_scope tparams (ty_check ann.Ast.annot_item Typing.Univ)) tys
        in
        let datacon =
          { Typing.datacon_name = name
          ; datacon_inputs = tys
          ; datacon_output = Typing.Neu(Typing.Adt(adt'), params) }
        in
        constrs.(i) <- datacon;
        Hashtbl.add datacons name i;
        i + 1)
      0 adt.Ast.adt_constrs
  in
  let+ () =
    declare_tycon adt.Ast.adt_name (Typing.Adt adt') adt'.Typing.adt_kind
  in
  adt'

let decl_fun name ty _ s =
  if Hashtbl.mem s.funcs name then
    (Error (Error.Redefined name), s)
  else (
    Hashtbl.add s.funcs name ty;
    (Ok { data = () }, s)
  )

let get_fun name _ s =
  (Ok { data = Hashtbl.find_opt s.funcs name }, s)

exception String of string

let rec check_pat pat ty =
  match pat with
  | Ast.As_pat(pat, name) ->
     let* var = fresh_var ty in
     Var.add_name var name;
     let* map = check_pat pat.Ast.annot_item ty in
     if StringMap.mem name map then
       throw (Error.Redefined name)
     else
       return (StringMap.add name var map)
  | Ast.Constr_pat(name, pats) ->
     begin match ty with
     | Typing.Neu(Typing.Adt adt, tyargs) ->
        let idx = Hashtbl.find adt.Typing.adt_constr_names name in
        let datacon = adt.adt_constrs.(idx) in
        let tyargs = Array.of_list (List.rev tyargs) in
        let tys =
          List.map (Typing.inst tyargs) datacon.Typing.datacon_inputs
        in
        check_pats pats tys
     | _ -> throw (Error.Unimplemented "")
     end
  | Ast.Var_pat name ->
     let+ var = fresh_var ty in
     Var.add_name var name;
     StringMap.singleton name var
  | Ast.Wild_pat -> return StringMap.empty
  | Ast.Lit_pat lit ->
     match lit, ty with
     | Ast.Int_lit _, Typing.Neu(Typing.Num(Typing.Signed, Typing.Sz32), []) ->
        return StringMap.empty
     | Ast.Str_lit _, Typing.Neu(Typing.Cstr, []) -> return StringMap.empty
     | Ast.Unit_lit, Typing.Unit -> return StringMap.empty
     | _, _ -> throw (Error.Unimplemented "Checking lit pat")

and check_pats pats tys =
  let rec tie acc = function
    | [], [] -> return (List.rev acc)
    | pat :: pats, ty :: tys ->
       tie ((pat, ty) :: acc) (pats, tys)
    | _ :: _, [] -> throw Error.Too_many_patterns
    | [], _ :: _ -> throw Error.Not_enough_patterns
  in
  let* tied = tie [] (pats, tys) in
  fold_rightM (fun map (pat, ty) ->
      (* Raise exception to break out *)
      let f s _ _ = raise (String s) in
      let* map' = check_pat pat.Ast.annot_item ty in
      try return (StringMap.union f map map') with
      | String k -> throw (Error.Redefined k)
    ) StringMap.empty tied

let rec infer subst = function
  | Ast.Apply_expr(f, args) ->
     let* typed_f, f_ty, subst = infer subst f.Ast.annot_item in
     begin match f_ty with
     | Typing.Fun_ty { dom; codom } ->
        let rec loop subst typed_args args dom = match args, dom with
          | [], [] ->
             return
               ( Typing.Apply_expr(codom, typed_f, List.rev typed_args)
               , codom
               , subst )
          | arg :: args, ty :: dom ->
             let* typed_arg, subst = check subst arg.Ast.annot_item ty in
             loop subst (typed_arg :: typed_args) args dom
          | _ :: _, [] -> throw Error.Too_many_arguments
          | [], _ :: _ -> throw Error.Not_enough_arguments
        in loop subst [] args dom
     | _ -> throw Error.Expected_function_type
     end
  | Ast.Constr_expr _ ->
     throw (Error.Unimplemented "Cannot infer data constructor")
  | Ast.Lit_expr (Ast.Int_lit _) ->
     throw (Error.Unimplemented "Cannot infer int lit")
  | Ast.Lit_expr (Ast.Str_lit s) ->
     return (Typing.Str_expr s, Typing.Neu(Typing.Cstr, []), subst)
  | Ast.Lit_expr Ast.Unit_lit ->
     return (Typing.Unit_expr, Typing.Unit, subst)
  | Ast.Seq_expr(e1, e2) ->
     let* typed_e1, subst = check subst e1.Ast.annot_item Typing.Unit in
     let+ typed_e2, ty, subst = infer subst e2.Ast.annot_item in
     (Typing.Seq_expr(typed_e1, typed_e2), ty, subst)
  | Ast.Var_expr name ->
     let* var = find name in
     begin match var with
     | Global (Typing.Forall([], ty)) ->
        return (Typing.Global_expr(name, [||]), ty, subst)
     | Global (Typing.Forall(_, _)) -> throw (Error.Unimplemented "Global")
     | Local var -> return (Typing.Var_expr var, Var.ty var, subst)
     | Type _ -> throw (Error.Unimplemented "First-class types")
     end
  | Ast.Generic_expr(name, tyargs) ->
     let* var = find name in
     begin match var with
     | Global (Typing.Forall(kinds, ty)) ->
        let rec loop = function
          | [], [] -> return []
          | ty :: tys, kind :: kinds ->
             let+ ty = ty_check ty.Ast.annot_item kind
             and+ rest = loop (tys, kinds) in
             ty :: rest
          | [], _ :: _ -> throw Error.Not_enough_typeargs
          | _ :: _, [] -> throw Error.Too_many_typeargs
        in
        let* tyargs = loop (tyargs, kinds) in
        let tyargs = Array.of_list tyargs in
        return (Typing.Global_expr(name, tyargs), Typing.inst tyargs ty, subst)
     | Local _ -> throw (Error.Unimplemented "Local with generics")
     | Type _ -> throw (Error.Unimplemented "First-class types")
     end
  | _ -> throw (Error.Unimplemented "First-class types")

and check subst expr ty = match expr, ty with
  | Ast.Constr_expr(name, args), Typing.Neu(Typing.Adt adt, tyargs) ->
     let idx = Hashtbl.find adt.Typing.adt_constr_names name in
     let datacon = adt.Typing.adt_constrs.(idx) in
     let tyargs = Array.of_list (List.rev tyargs) in
     let* subst, args =
       let rec loop subst typed_args args tys =
         match args, tys with
         | [], [] -> return (subst, List.rev typed_args)
         | arg :: args, ty :: tys ->
            let ty = Typing.inst tyargs ty in
            let* typed_arg, subst = check subst arg.Ast.annot_item ty in
            loop subst (typed_arg :: typed_args) args tys
         | _ :: _, [] -> throw Error.Too_many_arguments
         | [], _ :: _ -> throw Error.Not_enough_arguments
       in
       loop subst [] args datacon.Typing.datacon_inputs
     in
     let ty' = Typing.inst tyargs datacon.Typing.datacon_output in
     let+ _ = unify ~expected:ty ~actual:ty' in
     (Typing.Constr_expr(ty, idx, args), subst)
  | Ast.Lit_expr (Ast.Int_lit n), Typing.Neu (Num(_, _), []) ->
     return (Typing.Int_expr(ty, n), subst)
  | Ast.Seq_expr(e1, e2), ty ->
     let* typed_e1, subst = check subst e1.Ast.annot_item Typing.Unit in
     let+ typed_e2, subst = check subst e2.Ast.annot_item ty in
     (Typing.Seq_expr(typed_e1, typed_e2), subst)
  | expr, ty ->
     let* typed_expr, ty', subst = infer subst expr in
     let+ subst' = unify ~expected:ty' ~actual:(Typing.subst subst ty) in
     (typed_expr, Typing.Subst.union (fun _ a _ -> Some a) subst subst')

type constrain = Typing.ns Var.t * Ast.pat Ast.annot

type clause = {
    constraints : constrain list;
    pat_vars : (Typing.ns Var.t * string) list;
    rhs : int
  }

type refutability =
  | Refut of Typing.ns Var.t
  | Irrefut of (Typing.ns Var.t * string) list

let rec find_refut acc = function
  | [] -> Irrefut acc
  | (_, Ast.{ annot_item = Wild_pat | Lit_pat Unit_lit; _ }) :: rest ->
     find_refut acc rest
  | (var, Ast.{ annot_item = As_pat(pat, name); _ }) :: rest ->
     find_refut ((var, name) :: acc) ((var, pat) :: rest)
  | (var, Ast.{ annot_item = Constr_pat(_, _) | Lit_pat _; _ }) :: _ ->
     Refut var
  | (var, Ast.{ annot_item = Var_pat name; _ }) :: rest ->
     find_refut ((var, name) :: acc) rest

let rec tie acc vars pats = match vars, pats with
  | [], [] -> return (List.rev acc)
  | var :: vars, pat :: pats -> tie ((var, pat) :: acc) vars pats
  | _ :: _, [] -> throw Error.Not_enough_patterns
  | [], _ :: _ -> throw Error.Too_many_patterns

let rec filter pat_vars acc var vars datacon = function
  | [] -> return (Some (pat_vars, List.rev acc))
  | ((var', pat) as c) :: constraints when Var.equal var var' ->
     let rec normalize pat_vars' pat =
       match pat.Ast.annot_item with
       | Ast.Constr_pat(datacon', pats) ->
          if datacon = datacon' then
            let+ tied = tie [] vars pats in
            Some
              (pat_vars', List.rev_append acc (List.append tied constraints))
          else
            return None
       | Var_pat _ ->
          (* Return the original pat-vars *)
          return (Some (pat_vars, List.rev_append acc (c :: constraints)))
       | Wild_pat ->
          (* Return the original pat-vars *)
          return (Some (pat_vars, List.rev_append acc (c :: constraints)))
       | As_pat(pat, name) -> normalize ((var, name) :: pat_vars') pat
       | Lit_pat _ -> failwith "Unreachable: Lit pat"
     in normalize pat_vars pat
  | c :: constraints -> filter pat_vars (c :: acc) var vars datacon constraints

let rec filter_str pat_vars acc var = function
  | [] -> return (None, pat_vars, List.rev acc)
  | ((var', pat) as c) :: constraints when Var.equal var var' ->
     let rec normalize pat_vars' pat =
       match pat.Ast.annot_item with
       | Ast.Lit_pat(Ast.Str_lit str) ->
          return (Some str, pat_vars', List.rev_append acc constraints)
       | Var_pat _ ->
          (* Return the original pat-vars *)
          return (None, pat_vars, List.rev_append acc (c :: constraints))
       | Wild_pat ->
          (* Return the original pat-vars *)
          return (None, pat_vars, List.rev_append acc (c :: constraints))
       | As_pat(pat, name) -> normalize ((var, name) :: pat_vars') pat
       | Constr_pat _ -> failwith "Unreachable: Constr pt"
       | Lit_pat _ -> failwith "Unreachable: Lit pat"
     in normalize pat_vars pat
  | c :: constraints -> filter_str pat_vars (c :: acc) var constraints

let rec filter_int pat_vars acc var = function
  | [] -> return (None, pat_vars, List.rev acc)
  | ((var', pat) as c) :: constraints when Var.equal var var' ->
     let rec normalize pat_vars' pat =
       match pat.Ast.annot_item with
       | Ast.Lit_pat(Ast.Int_lit n) ->
          return (Some n, pat_vars', List.rev_append acc constraints)
       | Var_pat _ ->
          (* Return the original pat-vars *)
          return (None, pat_vars, List.rev_append acc (c :: constraints))
       | Wild_pat ->
          (* Return the original pat-vars *)
          return (None, pat_vars, List.rev_append acc (c :: constraints))
       | As_pat(pat, name) -> normalize ((var, name) :: pat_vars') pat
       | Constr_pat _ -> failwith "Unreachable: Constr pt"
       | Lit_pat _ -> failwith "Unreachable: Lit pat"
     in normalize pat_vars pat
  | c :: constraints -> filter_int pat_vars (c :: acc) var constraints

let rec elab_clauses clauses dom codom = match clauses with
  | [] -> throw Error.Incomplete_match
  | clause :: _ ->
     match find_refut clause.pat_vars clause.constraints with
     | Irrefut pat_vars -> return (Typing.Leaf(clause.rhs, pat_vars))
     | Refut var ->
        match Var.ty var with
        | Typing.Neu (Typing.Adt adt, tyargs) ->
           let tyargs = Array.of_list (List.rev tyargs) in
           let+ cases =
             Array.fold_right (fun datacon acc ->
                 let* cases = acc in
                 let+ case = refine datacon tyargs var clauses dom codom in
                 case :: cases
               ) adt.Typing.adt_constrs (return [])
           in
           Typing.Split(adt, var, cases)
        | Typing.Neu(Typing.Cstr, []) ->
           let+ strmap, otherwise = refine_str var clauses dom codom in
           Typing.Split_str(var, strmap, otherwise)
        | Typing.Neu(Typing.Num(Typing.Signed, Typing.Sz32), []) ->
           let+ intmap, otherwise = refine_int var clauses dom codom in
           Typing.Split_int(var, intmap, otherwise)
        | Typing.Rigid _ -> throw (Error.Unimplemented "Rigid")
        | _ -> throw (Error.Unimplemented "Not a pattern-matchable type")

and refine datacon tyargs var clauses dom codom =
  let tys = List.map (Typing.inst tyargs) datacon.Typing.datacon_inputs in
  let* fresh_vars = mapM fresh_var tys in
  let* clauses =
    fold_rightM (fun acc clause ->
        let+ opt =
          filter clause.pat_vars [] var fresh_vars datacon.Typing.datacon_name
            clause.constraints
        in
        match opt with
        | None -> acc
        | Some (pat_vars, constraints) ->
           { clause with pat_vars; constraints } :: acc
      ) [] clauses
  in
  let+ tree = elab_clauses clauses dom codom in
  (fresh_vars, tree)

and refine_str var clauses dom codom =
  let* strs, otherwise =
    fold_rightM (fun (strs, otherwise) clause ->
        let+ (str_opt, pat_vars, constraints) =
          filter_str clause.pat_vars [] var clause.constraints
        in
        let clause = { clause with pat_vars; constraints } in
        match str_opt with
        | None ->
           ( StringMap.map (fun clauses -> clause :: clauses) strs
           , clause :: otherwise )
        | Some str ->
           let clauses = match StringMap.find_opt str strs with
             | None -> otherwise
             | Some clauses -> clauses
           in
           (StringMap.add str (clause :: clauses) strs, otherwise)
      ) (StringMap.empty, []) clauses
  in
  let+ strs =
    StringMap.fold (fun str clauses acc ->
        let+ strmap = acc
        and+ tree = elab_clauses clauses dom codom in
        StringMap.add str tree strmap
      ) strs (return StringMap.empty)
  and+ otherwise = elab_clauses otherwise dom codom in
  (strs, otherwise)

and refine_int var clauses dom codom =
  let* intmap, otherwise =
    fold_rightM (fun (intmap, otherwise) clause ->
        let+ (int_opt, pat_vars, constraints) =
          filter_int clause.pat_vars [] var clause.constraints
        in
        let clause = { clause with pat_vars; constraints } in
        match int_opt with
        | None ->
           ( IntMap.map (fun clauses -> clause :: clauses) intmap
           , clause :: otherwise )
        | Some int ->
           let clauses = match IntMap.find_opt int intmap with
             | None -> otherwise
             | Some clauses -> clauses
           in
           (IntMap.add int (clause :: clauses) intmap, otherwise)
      ) (IntMap.empty, []) clauses
  in
  let+ intmap =
    IntMap.fold (fun n clauses acc ->
        let+ strmap = acc
        and+ tree = elab_clauses clauses dom codom in
        IntMap.add n tree strmap
      ) intmap (return IntMap.empty)
  and+ otherwise = elab_clauses otherwise dom codom in
  (intmap, otherwise)

let check_fun func fun_typarams Typing.{ dom; codom } =
  let* rhs =
    mapM (fun clause ->
        let* map = check_pats clause.Ast.clause_lhs dom in
        let map' = StringMap.map (fun x -> Local x) map in
        let+ expr, _ =
          in_scope map'
            (check Typing.Subst.empty clause.Ast.clause_rhs.annot_item codom)
        in (map, expr)
      ) func.Ast.fun_clauses
  in
  let* vars = mapM fresh_var dom in
  let* _, clauses =
    fold_leftM (fun (i, clauses) clause ->
        let rec loop = function
          | [], [] -> return []
          | _ :: _, [] -> throw Error.Too_many_patterns
          | [], _ :: _ -> throw Error.Not_enough_patterns
          | pat :: pats, var :: vars->
             let+ constraints = loop (pats, vars) in
             (var, pat) :: constraints
        in
        let+ constraints = loop (clause.Ast.clause_lhs, vars) in
        (i + 1, { constraints; pat_vars = []; rhs = i } :: clauses)
      ) (0, []) func.Ast.fun_clauses
  in
  let+ tree = elab_clauses (List.rev clauses) dom codom in
  Typing.{
      fun_name = func.Ast.fun_name;
      fun_ty = Typing.{ dom; codom };
      fun_typarams;
      fun_params = vars;
      fun_tree = tree;
      fun_clauses = rhs;
  }

let elab_program prog =
  let+ decls =
    let rec loop = function
      | [] -> return []
      | next :: decls ->
         match next.Ast.annot_item with
         | Ast.External(name, ty) ->
            let* ty, _ = ty_infer ty.Ast.annot_item in
            let* () = decl_fun name (Typing.Forall([], ty)) in
            let+ decls =
              in_scope
                (StringMap.singleton name (Global (Forall([], ty))))
                (loop decls)
            in
            Typing.External(name, ty) :: decls
         | Ast.Forward_decl(name, tvars, ty) ->
            let* forall = read_ty_scheme tvars ty.Ast.annot_item in
            let* () = decl_fun name forall in
            in_scope (StringMap.singleton name (Global forall)) (loop decls)
         | Ast.Fun fun_def ->
            let* opt = get_fun fun_def.Ast.fun_name in
            begin match opt with
            | None -> throw (Error.Undefined fun_def.Ast.fun_name)
            | Some (Typing.Forall(kinds, Typing.Fun_ty ty))->
               let* fun_def = check_fun fun_def kinds ty in
               let+ decls = loop decls in
               Typing.Fun fun_def :: decls
            | Some _ -> throw Error.Expected_function_type
            end
         | Ast.Adt adt ->
            let* _ = read_adt adt in
            loop decls
    in
    loop prog.Ast.decls
  in
  Typing.{ decls }

let elab prog = run (elab_program prog)
