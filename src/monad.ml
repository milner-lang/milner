module type MONAD = sig
  type 'a t
  val return : 'a -> 'a t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
end

module List(M : MONAD) = struct
  open M

  let rec iterM f = function
    | [] -> return ()
    | x :: xs ->
       let+ () = f x
       and+ () = iterM f xs in
       ()

  let rec mapM f = function
    | [] -> return []
    | x :: xs ->
       let+ y = f x
       and+ ys = mapM f xs in
       y :: ys

  let rec fold_leftM f acc = function
    | [] -> return acc
    | x :: xs ->
       let* acc = f acc x in
       fold_leftM f acc xs

  let rec fold_rightM f acc = function
    | [] -> return acc
    | x :: xs ->
       let* acc = fold_rightM f acc xs in
       f acc x
end
