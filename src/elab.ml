module L = Dlist
module IntMap = Map.Make(Int)
module StringMap = Map.Make(String)
module Symtable = ScopedMap.Make(String)

type error =
  | Incomplete_match
  | Not_enough_arguments
  | Not_enough_patterns
  | Redefined of string
  | Too_many_arguments
  | Too_many_patterns
  | Undefined of string
  | Undefined_tvar of string
  | Unimplemented of string

let string_of_error = function
  | Incomplete_match -> "Incomplete match"
  | Not_enough_arguments -> "Not enough arguments"
  | Not_enough_patterns -> "Not enough patterns"
  | Redefined s -> "Redefined " ^ s
  | Too_many_arguments -> "Too manu arguments"
  | Too_many_patterns -> "Too many patterns"
  | Undefined s -> "Undefined " ^ s
  | Undefined_tvar s -> "Undefined type variable " ^ s
  | Unimplemented s -> "Unimplemented " ^ s

type state = {
    tycons : (string, Type.tycon * Type.t) Hashtbl.t;
    datacons : (string, Type.adt * int) Hashtbl.t;
    funcs : (string, Type.forall) Hashtbl.t;
    metavar_gen : int;
    var_gen : Typed.ns Var.gen;
  }

type 'a payload = {
    data : 'a;
    ex : Type.t L.t; (** Existential variables *)
  }

(* In the paper "Hindley-Milner Elaboration in Applicative Style," the wrapped
   data 'a is embedded inside a continuation of type env -> 'a. The paper notes
   that the presence of the continuation prevents the type from having a monad
   instance; it only has an applicative instance. Because I do not wrap the
   data in a continuation, I can have a monad. *)
type 'a t =
  Typed.ns Var.t Symtable.t -> state -> ('a payload, error) result * state

let throw e _ s = (Error e, s)

let init_state () =
  let tycons = Hashtbl.create 20 in
  Hashtbl.add tycons "Cstring" (Type.Cstr, Type.Univ);
  Hashtbl.add tycons "Int32" (Type.Num(Type.Signed, Type.Sz32), Type.Univ);
  { var_gen = Var.init_gen;
    metavar_gen = 0;
    datacons = Hashtbl.create 20;
    funcs = Hashtbl.create 20;
    tycons }

let run m =
  let r, _ = m Symtable.empty (init_state ()) in
  match r with
  | Error e -> Error e
  | Ok w -> Ok w.data

module Mon : Monad.MONAD with type 'a t = 'a t = struct
  type nonrec 'a t = 'a t

  let return a _env s = (Ok { data = a; ex = L.empty }, s)

  let ( let+ ) t f env s =
    let r, s = t env s in
    match r with
    | Error e -> (Error e, s)
    | Ok w -> (Ok { w with data = f w.data }, s)

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
                ex = L.append w1.ex w2.ex;
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
                ex = L.append w1.ex w2.ex;
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
  | Some var -> (Ok { data = Local var; ex = L.empty }, s)
  | None ->
     match Hashtbl.find_opt s.funcs name with
     | Some ty -> (Ok { data = Global ty; ex = L.empty }, s)
     | None -> (Error (Undefined name), s)

let declare_tycon name tycon kind _ s =
  Hashtbl.add s.tycons name (tycon, kind);
  (Ok { data = (); ex = L.empty }, s)

let find_tcon name _ s =
  match Hashtbl.find_opt s.tycons name with
  | None -> (Error (Undefined name), s)
  | Some ty -> (Ok { data = ty; ex = L.empty }, s)

let fresh_var ty _ s =
  let (var, var_gen) = Var.fresh s.var_gen ty in
  (Ok { data = var; ex = L.empty }, { s with var_gen })

let declare_datacon name idx adt _ s =
  Hashtbl.add s.datacons name (idx, adt);
  (Ok { data = (); ex = L.empty }, s)

let find_datacon name _ s =
  match Hashtbl.find_opt s.datacons name with
  | Some data -> (Ok { data; ex = L.empty }, s)
  | None -> Error (Undefined name), s

(** Infer the kind of a type. *)
let rec ty_infer tvars = function
  | Ast.Unit -> return (Type.Unit, Type.Univ)
  | Ast.Univ -> return (Type.Univ, Type.Univ)
  | Ast.Ty_app(f, x) ->
     let* pair = ty_infer tvars f.Ast.annot_item in
     begin match pair with
     | Type.Constr(Adt(adt, spine)), Type.KArrow(dom, cod) ->
        let+ x = ty_check tvars x.Ast.annot_item dom in
        Type.Constr(Adt(adt, x :: spine)), cod
     | _ -> throw (Unimplemented "")
     end
  | Ast.Ty_con tycon ->
     let+ ty, kind = find_tcon tycon in
     Type.Constr ty, kind
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
  match Type.unify kind' kind with
  | Error _ -> throw (Unimplemented "")
  | Ok _ -> return ty

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
  List.rev kinds, ty

let read_adt adt =
  let constrs = Array.make (List.length adt.Ast.adt_constrs) ("", []) in
  let* _, tparams =
    fold_leftM (fun (i, map) (name, kind) ->
        let+ kind = ty_check StringMap.empty kind.Ast.annot_item Type.Univ in
        i + 1, StringMap.add name (Type.Rigid i, kind) map
      ) (0, StringMap.empty) adt.Ast.adt_params
  in
  let* _ =
    fold_leftM (fun i (name, tys) ->
        let+ tys =
          mapM (fun ann ->
              ty_check tparams ann.Ast.annot_item Type.Univ) tys
        in
        constrs.(i) <- (name, tys);
        i + 1)
      0 adt.Ast.adt_constrs
  in
  let adt' =
    Type.{
        adt_name = adt.Ast.adt_name;
        adt_params = 0;
        adt_kind = Type.Univ;
        adt_constrs = constrs
    }
  in
  let* _ =
    fold_leftM (fun i (name, _) ->
        let+ () = declare_datacon name adt' i in
        i + 1)
      0 adt.Ast.adt_constrs in
  let+ () =
    declare_tycon adt.Ast.adt_name (Type.Adt(adt', [])) adt'.Type.adt_kind
  in
  adt'

let decl_fun name ty _ s =
  if Hashtbl.mem s.funcs name then
    (Error (Redefined name), s)
  else (
    Hashtbl.add s.funcs name ty;
    (Ok { data = (); ex = L.empty }, s)
  )

let get_fun name _ s =
  (Ok { data = Hashtbl.find_opt s.funcs name; ex = L.empty }, s)

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
     let* adt, idx = find_datacon name in
     let _, tys = adt.Type.adt_constrs.(idx) in
     check_pats pats tys
  | Ast.Var_pat name ->
     let+ var = fresh_var ty in
     Var.add_name var name;
     StringMap.singleton name var
  | Ast.Wild_pat -> return StringMap.empty
  | Ast.Lit_pat lit ->
     match lit, ty with
     | Ast.Int32_lit _,
       Type.Constr(Type.Num(Type.Signed, Type.Sz32)) ->
        return StringMap.empty
     | Ast.Str_lit _, Type.Constr Type.Cstr ->
        return StringMap.empty
     | Ast.Unit_lit, Type.Unit ->
        return StringMap.empty
     | _, _ -> throw (Unimplemented "Checking int lit pat")

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
     | _ -> throw (Unimplemented "")
     end
  | Ast.Constr_expr(name, args) ->
     let* adt, idx = find_datacon name in
     let+ subst, args =
       let rec loop subst typed_args args tys =
         match args, tys with
         | [], [] -> return (subst, List.rev typed_args)
         | arg :: args, ty :: tys ->
            let* typed_arg, subst = check subst arg.Ast.annot_item ty in
            loop subst (typed_arg :: typed_args) args tys
         | _ :: _, [] -> throw Too_many_arguments
         | [], _ :: _ -> throw Not_enough_arguments
       in
       let _, tys = adt.Type.adt_constrs.(idx) in
       loop subst [] args tys
     in
     let ty = Type.Constr (Type.Adt(adt, [])) in
     (Typed.Constr_expr(ty, idx, args), ty, subst)
  | Ast.Lit_expr (Ast.Int_lit _) -> throw (Unimplemented "Int lit")
  | Ast.Lit_expr (Ast.Int32_lit n) ->
     let ty = Type.(Constr (Num(Signed, Sz32))) in
     return (Typed.Int_expr(ty, n), ty, subst)
  | Ast.Lit_expr (Ast.Str_lit s) ->
     return (Typed.Str_expr s, Type.Constr Type.Cstr, subst)
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
     | Global (Type.Forall(_, _)) ->
        throw (Unimplemented "Global")
     | Local var ->
        return (Typed.Var_expr var, Var.ty var, subst)
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
          | [], _ :: _ ->
             throw (Unimplemented "Not enough tyargs")
          | _ :: _, [] ->
             throw (Unimplemented "Too many tyargs")
        in
        let* tyargs = loop (tyargs, kinds) in
        let tyargs = Array.of_list tyargs in
        return (Typed.Global_expr(name, tyargs), Type.inst tyargs ty, subst)
     | Local _ ->
        throw (Unimplemented "")

and check subst expr ty = match expr, ty with
  | expr, ty ->
     let* typed_expr, ty', subst = infer subst expr in
     match Type.unify (Type.subst subst ty) ty' with
     | Error e -> throw (Unimplemented e)
     | Ok subst' ->
        return
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
       | As_pat(pat, name) ->
          normalize ((var, name) :: pat_vars') pat
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
       | As_pat(pat, name) ->
          normalize ((var, name) :: pat_vars') pat
       | Constr_pat _ -> failwith "Unreachable: Constr pt"
       | Lit_pat _ -> failwith "Unreachable: Lit pat"
     in normalize pat_vars pat
  | c :: constraints -> filter_str pat_vars (c :: acc) var constraints

let rec filter_int pat_vars acc var = function
  | [] -> return (None, pat_vars, List.rev acc)
  | ((var', pat) as c) :: constraints when Var.equal var var' ->
     let rec normalize pat_vars' pat =
       match pat.Ast.annot_item with
       | Ast.Lit_pat(Ast.Int32_lit n) ->
          return (Some n, pat_vars', List.rev_append acc constraints)
       | Var_pat _ ->
          (* Return the original pat-vars *)
          return (None, pat_vars, List.rev_append acc (c :: constraints))
       | Wild_pat ->
          (* Return the original pat-vars *)
          return (None, pat_vars, List.rev_append acc (c :: constraints))
       | As_pat(pat, name) ->
          normalize ((var, name) :: pat_vars') pat
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
        | Type.Constr (Type.Adt(adt, _)) ->
           let+ cases =
             Array.fold_right (fun datacon acc ->
                 let* cases = acc in
                 let+ case = refine datacon var clauses dom codom in
                 case :: cases
               ) adt.Type.adt_constrs (return [])
           in
           Typed.Split(adt, var, cases)
        | Type.Constr Type.Cstr ->
           let+ strmap, otherwise = refine_str var clauses dom codom in
           Typed.Split_str(var, strmap, otherwise)
        | Type.Constr (Type.Num(Type.Signed, Type.Sz32)) ->
           let+ intmap, otherwise = refine_int var clauses dom codom in
           Typed.Split_int(var, intmap, otherwise)
        | _ -> throw (Unimplemented "")

and refine (datacon_name, tys) var clauses dom codom =
  let* fresh_vars = mapM fresh_var tys in
  let* clauses =
    fold_rightM (fun acc clause ->
        let+ opt =
          filter clause.pat_vars [] var fresh_vars datacon_name
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
           let* kinds, ty = read_ty_scheme tvars ty.Ast.annot_item in
           let+ () = decl_fun name (Type.Forall(kinds, ty)) in
           decls
        | Ast.Fun fun_def ->
           let* opt = get_fun fun_def.Ast.fun_name in
           begin match opt with
           | None -> throw (Undefined fun_def.Ast.fun_name)
           | Some (Type.Forall(kinds, Type.Fun ty)) ->
              let+ fun_def = check_fun fun_def kinds ty in
              Typed.Fun fun_def :: decls
           | Some _ -> throw (Unimplemented "")
           end
        | Ast.Adt adt ->
           let+ _ = read_adt adt in
           decls
      ) [] prog.Ast.decls
  in
  Typed.{ decls = List.rev decls }

let elab prog = run (elab_program prog)
