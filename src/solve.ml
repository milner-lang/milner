type 'a solver = UnionFind.gen -> ('a, string) result * UnionFind.gen

module Mon : Monad.MONAD with type 'a t = 'a solver = struct
  type 'a t = 'a solver

  let return a gen = Ok a, gen

  let ( let+ ) m f gen =
    match m gen with
    | Error e, gen -> Error e, gen
    | Ok a, gen -> Ok (f a), gen

  let ( and+ ) m1 m2 gen =
    match m1 gen with
    | Error e, gen -> Error e, gen
    | Ok a, gen ->
       match m2 gen with
       | Error e, gen -> Error e, gen
       | Ok b, gen -> Ok (a, b), gen

  let ( and* ) = ( and+ )

  let ( let* ) m f gen =
    match m gen with
    | Ok a, gen -> f a gen
    | Error e, gen -> Error e, gen
end

open Mon
open Monad.List(Mon)

let throw e gen = Error e, gen

let lift r gen = r, gen

let solve_constraints tctx = function
  | Type.Eq(t1, t2) -> lift (UnionFind.union Type.unify (Ok ()) t1 t2)
  | Inst(var, t, _) ->
     begin match Hashtbl.find_opt tctx var with
     | None -> throw ("Var not found " ^ var)
     | Some ty -> lift (UnionFind.union Type.unify (Ok ()) ty t)
     end
  | Nat _ -> throw "Unimplemented"

let rec solve_many tctx = function
  | [] -> return ()
  | c :: cs ->
     let* () = solve_constraints tctx c in
     solve_many tctx cs

let solve gen program =
  let tctx = Hashtbl.create 100 in
  let r, _ =
    iterM (fun next ->
        match next with
        | Typed.Fun fun_def ->
           let Forall(_, cs, ty) = fun_def.Typed.fun_ty in
           Hashtbl.add tctx fun_def.Typed.fun_name ty;
           solve_many tctx cs
        | Typed.External(name, ty) ->
           return (Hashtbl.add tctx name ty)
      ) program.Typed.decls gen
  in
  r
