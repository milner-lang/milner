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
open Monad.List(Mon)

let solve_constraints tctx = function
  | Constraint.Eq(t1, t2) -> UnionFind.union Type.unify (Ok ()) t1 t2
  | Inst(var, t) ->
     begin match Hashtbl.find_opt tctx var with
     | None -> Error ("Var not found " ^ var)
     | Some ty -> UnionFind.union Type.unify (Ok ()) ty t
     end
  | Nat _ -> Error "Unimplemented"

let rec solve_many tctx = function
  | [] -> Ok ()
  | c :: cs ->
     let* () = solve_constraints tctx c in
     solve_many tctx cs

let solve program =
  let tctx = Hashtbl.create 100 in
  iterM (fun next ->
      match next with
      | Typed.Fun fun_def ->
         let Forall(_, cs, ty) = fun_def.Typed.fun_ty in
         Hashtbl.add tctx fun_def.Typed.fun_name ty;
         solve_many tctx cs
      | Typed.External(name, ty) ->
         return (Hashtbl.add tctx name ty)
    ) program.Typed.decls
