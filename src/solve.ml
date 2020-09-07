(*type 'a solver = ('a, string) result

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
open Monad.List(Mon)

let solve_constraints = function
  | Type.Eq(t1, t2) -> UnionFind.union Type.unify (Ok ()) t1 t2
  | Nat _ -> Error "Unimplemented"

let rec solve_many = function
  | [] -> Ok ()
  | c :: cs ->
     let* () = solve_constraints c in
     solve_many cs
*)
