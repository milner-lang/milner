module StringMap = Map.Make(String)
module Symtable = ScopedMap.Make(String)

type t =
  | Eq of Type.t * Type.t
  | Let_mono of Type.t StringMap.t * t list
  | Inst of string * Type.t
  | Nat of Type.t

type forall = Forall of t list * Type.t

type 'a solver = ('a, string) result

module Mon : Monad.MONAD with type 'a t = 'a solver = struct
  type 'a t = 'a solver

  let return a = Ok a

  let ( let+ ) m f =
    match m with
    | Error e -> Error e
    | Ok a -> Ok (f a)

  let ( and+ ) m1 m2 =
    match m1, m2 with
    | Ok a, Ok b -> Ok (a, b)
    | Error e, _ -> Error e
    | _, Error e -> Error e

  let ( and* ) = ( and+ )

  let ( let* ) m f =
    match m with
    | Ok a -> f a
    | Error e -> Error e
end

open Mon

let rec solve tctx = function
  | Eq(t1, t2) -> UnionFind.union Type.unify (Ok ()) t1 t2
  | Inst(var, t1) ->
     begin match Symtable.find var tctx with
     | None ->
        Symtable.iter (fun k _ -> print_endline k) tctx;
        Error "Var not found"
     | Some t2 -> UnionFind.union Type.unify (Ok ()) t1 t2
     end
  | Let_mono(bindings, cs) ->
     solve_many (Symtable.extend bindings tctx) cs
  | Nat _ -> Error "Unimplemented"

and solve_many tctx = function
  | [] -> Ok ()
  | c :: cs ->
     let* () = solve tctx c in
     solve_many tctx cs
