module L = Dlist
module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)
module Symtable = ScopedMap.Make(String)

type error =
  | Expected_function_type
  | Incomplete_match
  | Not_enough_arguments
  | Not_enough_patterns
  | Not_enough_typeargs
  | Redefined of string
  | Too_many_arguments
  | Too_many_patterns
  | Too_many_typeargs
  | Undefined of string
  | Undefined_tvar of string
  | Unify of Type.t * Type.t * Type.t * Type.t
  | Unimplemented of string

let string_of_error = function
  | Expected_function_type -> "Expected a function type"
  | Incomplete_match -> "Incomplete match"
  | Not_enough_arguments -> "Not enough arguments"
  | Not_enough_patterns -> "Not enough patterns"
  | Not_enough_typeargs -> "Not enough typeargs"
  | Redefined s -> "Redefined " ^ s
  | Too_many_arguments -> "Too manu arguments"
  | Too_many_patterns -> "Too many patterns"
  | Too_many_typeargs -> "Too many typeargs"
  | Undefined s -> "Undefined " ^ s
  | Undefined_tvar s -> "Undefined type variable " ^ s
  | Unify _ -> "Unify"
  | Unimplemented s -> "Unimplemented " ^ s

type state = {
    tycons : (string, Type.head * Type.t) Hashtbl.t;
    funcs : (string, Type.forall) Hashtbl.t;
    metavar_gen : int;
    var_gen : Typed.ns Var.gen;
  }

type 'a payload = {
    data : 'a;
  }

type 'a t =
  Typed.ns Var.t Symtable.t -> state -> ('a payload, error) result * state

let throw e _ s = (Error e, s)

let init_state () =
  let tycons = Hashtbl.create 20 in
  Hashtbl.add tycons "Cstring" (Type.Cstr, Type.Univ);
  Hashtbl.add tycons "Int32" (Type.Num(Type.Signed, Type.Sz32), Type.Univ);
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

type var_kind =
  | Local of Typed.ns Var.t
  | Global of Type.forall

let find name env s =
  match Symtable.find name env with
  | Some var -> (Ok { data = Local var }, s)
  | None ->
     match Hashtbl.find_opt s.funcs name with
     | Some ty -> (Ok { data = Global ty }, s)
     | None -> (Error (Undefined name), s)

let declare_tycon name tycon kind _ s =
  Hashtbl.add s.tycons name (tycon, kind);
  (Ok { data = () }, s)

let find_tcon name _ s =
  match Hashtbl.find_opt s.tycons name with
  | None -> (Error (Undefined name), s)
  | Some ty -> (Ok { data = ty }, s)

let fresh_var ty _ s =
  let (var, var_gen) = Var.fresh s.var_gen ty in
  (Ok { data = var }, { s with var_gen })

let unify ty ty' =
  match Type.unify ty ty' with
  | Ok s -> return s
  | Error (lhs, rhs) -> throw (Unify(lhs, rhs, ty, ty'))

(** Infer the kind of a type. *)
let rec ty_infer tvars = function
  | Ast.Unit -> return (Type.Unit, Type.Univ)
  | Ast.Univ -> return (Type.Univ, Type.Univ)
  | Ast.Ty_app(f, x) ->
     let* pair = ty_infer tvars f.Ast.annot_item in
     begin match pair with
     | Type.Neu(Adt(adt), spine), Type.KArrow(dom, cod) ->
        let+ x = ty_check tvars x.Ast.annot_item dom in
        Type.Neu(Adt(adt), x :: spine), cod
     | _ -> throw (Unimplemented "Ty infer app")
     end
  | Ast.Ty_con tycon ->
     let+ ty, kind = find_tcon tycon in
     Type.Neu(ty, []), kind
  | Ast.Arrow(dom, codom) ->
     let+ dom = mapM (fun x -> ty_check tvars x.Ast.annot_item Type.Univ) dom
     and+ codom, _ = ty_infer tvars codom.Ast.annot_item in
     (Type.Fun { dom; codom }, Type.Univ)
  | Ast.Ty_var name ->
     match StringMap.find_opt name tvars with
     | Some (v, kind) -> return (v, kind)
     | None -> throw (Undefined_tvar name)

and ty_check tvars ast_ty kind =
  let* ty, kind' = ty_infer tvars ast_ty in
  let+ _ = unify kind' kind in
  ty

let read_ty_scheme tvars ty =
  let* _, tvar_map, kinds =
    fold_leftM
      (fun (i, tvars, kinds) (tvar, kind) ->
        let+ kind = ty_check StringMap.empty kind.Ast.annot_item Type.Univ in
        ( i + 1
        , StringMap.add tvar (Type.Rigid i, kind) tvars
        , Type.Univ :: kinds ))
      (0, StringMap.empty, []) tvars
  in
  let+ ty, _ = ty_infer tvar_map ty in
  Type.Forall(List.rev kinds, ty)

let read_adt adt =
  let constrs =
    (* Dummy values; these should all be replaced *)
    Array.make (List.length adt.Ast.adt_constrs)
      { Type.datacon_name = ""
      ; datacon_inputs = []
      ; datacon_output = Type.Univ }
  in
  let* param_count, params, kinds, tparams =
    fold_leftM (fun (i, params, kinds, map) (name, kind) ->
        let+ kind = ty_check StringMap.empty kind.Ast.annot_item Type.Univ in
        let ty = Type.Rigid i in
        i + 1, ty :: params, kind :: kinds, StringMap.add name (ty, kind) map)
      (0, [], [], StringMap.empty) adt.Ast.adt_params
  in
  let datacons = Hashtbl.create (Array.length constrs) in
  let rec loop = function
    | [] -> Type.Univ
    | kind :: kinds -> Type.KArrow(kind, loop kinds)
  in
  let adt' =
    Type.{
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
          mapM (fun ann -> ty_check tparams ann.Ast.annot_item Type.Univ) tys
        in
        let datacon =
          { Type.datacon_name = name
          ; datacon_inputs = tys
          ; datacon_output = Type.Neu(Type.Adt(adt'), params) }
        in
        constrs.(i) <- datacon;
        Hashtbl.add datacons name i;
        i + 1)
      0 adt.Ast.adt_constrs
  in
  let+ () =
    declare_tycon adt.Ast.adt_name (Type.Adt adt') adt'.Type.adt_kind
  in
  adt'

let decl_fun name ty _ s =
  if Hashtbl.mem s.funcs name then
    (Error (Redefined name), s)
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
       throw (Redefined name)
     else
       return (StringMap.add name var map)
  | Ast.Constr_pat(name, pats) ->
     begin match ty with
     | Type.Neu(Type.Adt adt, tyargs) ->
        let idx = Hashtbl.find adt.Type.adt_constr_names name in
        let datacon = adt.Type.adt_constrs.(idx) in
        let tyargs = Array.of_list (List.rev tyargs) in
        let tys = List.map (Type.inst tyargs) datacon.Type.datacon_inputs in
        check_pats pats tys
     | _ -> throw (Unimplemented "")
     end
  | Ast.Var_pat name ->
     let+ var = fresh_var ty in
     Var.add_name var name;
     StringMap.singleton name var
  | Ast.Wild_pat -> return StringMap.empty
  | Ast.Lit_pat lit ->
     match lit, ty with
     | Ast.Int_lit _, Type.Neu(Type.Num(Type.Signed, Type.Sz32), []) ->
        return StringMap.empty
     | Ast.Str_lit _, Type.Neu(Type.Cstr, []) -> return StringMap.empty
     | Ast.Unit_lit, Type.Unit -> return StringMap.empty
     | _, _ -> throw (Unimplemented "Checking lit pat")

and check_pats pats tys =
  let rec tie acc = function
    | [], [] -> return (List.rev acc)
    | pat :: pats, ty :: tys ->
       tie ((pat, ty) :: acc) (pats, tys)
    | _ :: _, [] -> throw Too_many_patterns
    | [], _ :: _ -> throw Not_enough_patterns
  in
  let* tied = tie [] (pats, tys) in
  fold_rightM (fun map (pat, ty) ->
      (* Raise exception to break out *)
      let f s _ _ = raise (String s) in
      let* map' = check_pat pat.Ast.annot_item ty in
      try return (StringMap.union f map map') with
      | String k -> throw (Redefined k)
    ) StringMap.empty tied

let rec infer subst = function
  | Ast.Apply_expr(f, args) ->
     let* typed_f, f_ty, subst = infer subst f.Ast.annot_item in
     begin match f_ty with
     | Type.Fun { dom; codom } ->
        let rec loop subst typed_args args dom = match args, dom with
          | [], [] ->
             return
               ( Typed.Apply_expr(codom, typed_f, List.rev typed_args)
               , codom
               , subst )
          | arg :: args, ty :: dom ->
             let* typed_arg, subst = check subst arg.Ast.annot_item ty in
             loop subst (typed_arg :: typed_args) args dom
          | _ :: _, [] -> throw Too_many_arguments
          | [], _ :: _ -> throw Not_enough_arguments
        in loop subst [] args dom
     | _ -> throw Expected_function_type
     end
  | Ast.Constr_expr _ -> throw (Unimplemented "Cannot infer data constructor")
  | Ast.Lit_expr (Ast.Int_lit _) ->
     throw (Unimplemented "Cannot infer int lit")
  | Ast.Lit_expr (Ast.Str_lit s) ->
     return (Typed.Str_expr s, Type.Neu(Type.Cstr, []), subst)
  | Ast.Lit_expr Ast.Unit_lit ->
     return (Typed.Unit_expr, Type.Unit, subst)
  | Ast.Seq_expr(e1, e2) ->
     let* typed_e1, subst = check subst e1.Ast.annot_item Type.Unit in
     let+ typed_e2, ty, subst = infer subst e2.Ast.annot_item in
     (Typed.Seq_expr(typed_e1, typed_e2), ty, subst)
  | Ast.Var_expr name ->
     let* var = find name in
     begin match var with
     | Global (Type.Forall([], ty)) ->
        return (Typed.Global_expr(name, [||]), ty, subst)
     | Global (Type.Forall(_, _)) -> throw (Unimplemented "Global")
     | Local var -> return (Typed.Var_expr var, Var.ty var, subst)
     end
  | Ast.Generic_expr(name, tyargs) ->
     let* var = find name in
     match var with
     | Global (Type.Forall(kinds, ty)) ->
        let rec loop = function
          | [], [] -> return []
          | ty :: tys, kind :: kinds ->
             let+ ty = ty_check StringMap.empty ty.Ast.annot_item kind
             and+ rest = loop (tys, kinds) in
             ty :: rest
          | [], _ :: _ -> throw Not_enough_typeargs
          | _ :: _, [] -> throw Too_many_typeargs
        in
        let* tyargs = loop (tyargs, kinds) in
        let tyargs = Array.of_list tyargs in
        return (Typed.Global_expr(name, tyargs), Type.inst tyargs ty, subst)
     | Local _ -> throw (Unimplemented "Local with generics")

and check subst expr ty = match expr, ty with
  | Ast.Constr_expr(name, args), Type.Neu(Type.Adt adt, tyargs) ->
     let idx = Hashtbl.find adt.Type.adt_constr_names name in
     let datacon = adt.Type.adt_constrs.(idx) in
     let tyargs = Array.of_list (List.rev tyargs) in
     let* subst, args =
       let rec loop subst typed_args args tys =
         match args, tys with
         | [], [] -> return (subst, List.rev typed_args)
         | arg :: args, ty :: tys ->
            let ty = Type.inst tyargs ty in
            let* typed_arg, subst = check subst arg.Ast.annot_item ty in
            loop subst (typed_arg :: typed_args) args tys
         | _ :: _, [] -> throw Too_many_arguments
         | [], _ :: _ -> throw Not_enough_arguments
       in
       loop subst [] args datacon.Type.datacon_inputs
     in
     let ty' = Type.inst tyargs datacon.Type.datacon_output in
     let+ _ = unify ty ty' in
     (Typed.Constr_expr(ty, idx, args), subst)
  | Ast.Lit_expr (Ast.Int_lit n), Type.Neu (Num(_, _), []) ->
     return (Typed.Int_expr(ty, n), subst)
  | Ast.Seq_expr(e1, e2), ty ->
     let* typed_e1, subst = check subst e1.Ast.annot_item Type.Unit in
     let+ typed_e2, subst = check subst e2.Ast.annot_item ty in
     (Typed.Seq_expr(typed_e1, typed_e2), subst)
  | expr, ty ->
     let* typed_expr, ty', subst = infer subst expr in
     let+ subst' = unify (Type.subst subst ty) ty' in
     (typed_expr, Type.Subst.union (fun _ a _ -> Some a) subst subst')

type constrain = Typed.ns Var.t * Ast.pat Ast.annot

type clause = {
    constraints : constrain list;
    pat_vars : (Typed.ns Var.t * string) list;
    rhs : int
  }

type refutability =
  | Refut of Typed.ns Var.t
  | Irrefut of (Typed.ns Var.t * string) list

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
  | _ :: _, [] -> throw Not_enough_patterns
  | [], _ :: _ -> throw Too_many_patterns

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
  | [] -> throw Incomplete_match
  | clause :: _ ->
     match find_refut clause.pat_vars clause.constraints with
     | Irrefut pat_vars -> return (Typed.Leaf(clause.rhs, pat_vars))
     | Refut var ->
        match Var.ty var with
        | Type.Neu (Type.Adt adt, tyargs) ->
           let tyargs = Array.of_list (List.rev tyargs) in
           let+ cases =
             Array.fold_right (fun datacon acc ->
                 let* cases = acc in
                 let+ case = refine datacon tyargs var clauses dom codom in
                 case :: cases
               ) adt.Type.adt_constrs (return [])
           in
           Typed.Split(adt, var, cases)
        | Type.Neu(Type.Cstr, []) ->
           let+ strmap, otherwise = refine_str var clauses dom codom in
           Typed.Split_str(var, strmap, otherwise)
        | Type.Neu(Type.Num(Type.Signed, Type.Sz32), []) ->
           let+ intmap, otherwise = refine_int var clauses dom codom in
           Typed.Split_int(var, intmap, otherwise)
        | Type.Rigid _ -> throw (Unimplemented "Rigid")
        | _ -> throw (Unimplemented "Not a pattern-matchable type")

and refine datacon tyargs var clauses dom codom =
  let tys = List.map (Type.inst tyargs) datacon.Type.datacon_inputs in
  let* fresh_vars = mapM fresh_var tys in
  let* clauses =
    fold_rightM (fun acc clause ->
        let+ opt =
          filter clause.pat_vars [] var fresh_vars datacon.Type.datacon_name
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

let check_fun func fun_typarams Type.{ dom; codom } =
  let* rhs =
    mapM (fun clause ->
        let* map = check_pats clause.Ast.clause_lhs dom in
        let+ expr, _ =
          in_scope map
            (check Type.Subst.empty clause.Ast.clause_rhs.annot_item codom)
        in (map, expr)
      ) func.Ast.fun_clauses
  in
  let* vars = mapM fresh_var dom in
  let* _, clauses =
    fold_leftM (fun (i, clauses) clause ->
        let rec loop = function
          | [], [] -> return []
          | _ :: _, [] -> throw Too_many_patterns
          | [], _ :: _ -> throw Not_enough_patterns
          | pat :: pats, var :: vars->
             let+ constraints = loop (pats, vars) in
             (var, pat) :: constraints
        in
        let+ constraints = loop (clause.Ast.clause_lhs, vars) in
        (i + 1, { constraints; pat_vars = []; rhs = i } :: clauses)
      ) (0, []) func.Ast.fun_clauses
  in
  let+ tree = elab_clauses (List.rev clauses) dom codom in
  Typed.{
      fun_name = func.Ast.fun_name;
      fun_ty = Type.{ dom; codom };
      fun_typarams;
      fun_params = vars;
      fun_tree = tree;
      fun_clauses = rhs;
  }

let elab_program prog =
  let+ decls =
    fold_leftM (fun decls next ->
        match next.Ast.annot_item with
        | Ast.External(name, ty) ->
           let* ty, _ = ty_infer StringMap.empty ty.Ast.annot_item in
           let+ () = decl_fun name (Type.Forall([], ty)) in
           Typed.External(name, ty) :: decls
        | Ast.Forward_decl(name, tvars, ty) ->
           let* forall = read_ty_scheme tvars ty.Ast.annot_item in
           let+ () = decl_fun name forall in
           decls
        | Ast.Fun fun_def ->
           let* opt = get_fun fun_def.Ast.fun_name in
           begin match opt with
           | None -> throw (Undefined fun_def.Ast.fun_name)
           | Some (Type.Forall(kinds, Type.Fun ty)) ->
              let+ fun_def = check_fun fun_def kinds ty in
              Typed.Fun fun_def :: decls
           | Some _ -> throw Expected_function_type
           end
        | Ast.Adt adt ->
           let+ _ = read_adt adt in
           decls
      ) [] prog.Ast.decls
  in
  Typed.{ decls = List.rev decls }

let elab prog = run (elab_program prog)
