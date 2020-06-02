module IntMap = Map.Make(Int)
module StrMap = Map.Make(String)

type aexp =
  | Int32 of int
  | String of string
  | Var of Var.t
  | Unit

type cont =
  | Return of aexp
  | Block of int

type expr =
  | Case_num of expr IntMap.t * expr
  | Case_str of expr StrMap.t * expr
  | Continue of cont
  | Let_app of Var.t * aexp * aexp list * expr
  | Let_cont of int * Var.t * expr * expr

type state = {
    var_gen : Var.gen;
  }

type 'a t = state -> ('a, string) result * state

module Mon : Monad.MONAD with type 'a t = 'a t = struct
  type nonrec 'a t = 'a t

  let return a s = (Ok a, s)

  let ( let+ ) m f s =
    let a, s = m s in
    (Result.map f a, s)

  let ( and+ ) m1 m2 s =
    let r1, s = m1 s in
    match r1 with
    | Error e -> Error e, s
    | Ok a ->
       let r2, s = m2 s in
       match r2 with
       | Error e -> Error e, s
       | Ok b -> Ok (a, b), s

  let ( and* ) = ( and+ )

  let ( let* ) m f s =
    let r, s = m s in
    match r with
    | Error e -> Error e, s
    | Ok a -> f a s
end

open Mon

let throw e s = (Error e, s)

let fresh s =
  let v, var_gen = Var.fresh s.var_gen in
  (Ok v, { var_gen })

(** The following pattern matching compilation code uses the algorithm from
    Maranget 2008:

    Luc Maranget, Compiling Pattern Matching to Good Decision Trees
    http://moscova.inria.fr/~maranget/papers/ml05e-maranget.pdf *)

type row = {
    pats : Typed.pat list;
    action : cont;
  }

type matrix = row list

type refutable_type = Int_pat | Str_pat

let rec find_refutable_pat idx = function
  | [] -> None
  | Typed.Int_pat _ :: _ -> Some (Int_pat, idx)
  | Typed.Str_pat _ :: _ -> Some (Str_pat, idx)
  | Typed.Wild_pat :: pats -> find_refutable_pat (idx + 1) pats

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

let specialize_int idx mat =
  List.fold_left (fun (map, otherwise) row ->
      let ls, x, rs = split idx row.pats in
      let row = { row with pats = List.rev_append ls rs } in
      match x with
      | Typed.Int_pat(_, n) ->
         begin match IntMap.find_opt n map with
         | None -> (IntMap.add n [row] map, otherwise)
         | Some rows -> (IntMap.add n (row :: rows) map, otherwise)
         end
      | Typed.Wild_pat -> (map, row :: otherwise)
      | _ -> assert false
    ) (IntMap.empty, []) mat

let specialize_str idx mat =
  List.fold_left (fun (map, otherwise) row ->
      let ls, x, rs = split idx row.pats in
      let row = { row with pats = List.rev_append ls rs } in
      match x with
      | Typed.Str_pat s ->
         begin match StrMap.find_opt s map with
         | None -> (StrMap.add s [row] map, otherwise)
         | Some rows -> (StrMap.add s (row :: rows) map, otherwise)
         end
      | Typed.Wild_pat -> (map, row :: otherwise)
      | _ -> assert false
    ) (StrMap.empty, []) mat

let rec compile_matrix mat =
  match mat with
  | [] -> throw "Incomplete pattern match"
  | row :: _ ->
     match find_refutable_pat 0 row.pats with
     | None -> return (Continue row.action)
     | Some (Int_pat, idx) ->
        let map, otherwise = specialize_int idx mat in
        let+ jumptable =
          IntMap.fold (fun n mat acc ->
              let+ map = acc
              and+ branch = compile_matrix (List.rev mat) in
              IntMap.add n branch map
            ) map (return IntMap.empty)
        and+ default = compile_matrix (List.rev otherwise) in
        Case_num(jumptable, default)
     | Some (Str_pat, idx) ->
        let map, otherwise = specialize_str idx mat in
        let+ jumptable =
          StrMap.fold (fun n mat acc ->
              let+ map = acc
              and+ branch = compile_matrix (List.rev mat) in
              StrMap.add n branch map
            ) map (return StrMap.empty)
        and+ default = compile_matrix (List.rev otherwise) in
        Case_str(jumptable, default)

let rec compile_expr exp k =
  match exp with
  | Typed.Apply_expr(f, args) ->
     compile_expr f (fun f ->
         List.fold_left (fun k arg args ->
             compile_expr arg (fun arg -> k (arg :: args))
           ) (fun args ->
             let* v = fresh in
             let+ body = k (Var v) in
             Let_app(v, f, args, body)
           ) args []
       )
  | Typed.Int_expr(_, n) -> k (Int32 n) (* Treat all ints as int32 for now *)
  | Typed.Str_expr s -> k (String s)
  | Typed.Seq_expr(e1, e2) ->
     compile_expr e1 (fun _ -> compile_expr e2 (fun e2 -> k e2))
  | Typed.Unit_expr -> k Unit
  | Typed.Var_expr _name -> failwith "Unimplemented"

let arity func =
  match UnionFind.find (func.Typed.fun_ty) with
  | UnionFind.Value (Type.Fun arity) -> arity
  | _ -> assert false
