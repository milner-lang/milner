external puts : fun(Cstring) -> ()

datatype Bool = False | True

datatype Option (a : type) = None | Some(a)

datatype Pt = Pt(Int32, Int32)

val f: fun(Bool) -> Int32
fun f
  | (False) =
    puts("False");
    0i32
  | (True) =
    puts("True");
    1i32

val g: fun(Option Int32) -> Bool
fun g
  | (Some(5i32)) = False
  | (_) = True

val inv: fun(Pt) -> Pt
fun inv(Pt(x, y)) = Pt(y, x)

val foo: fun(Pt) -> ()
fun foo(Pt(0i32, _)) = puts("Touching the x-axis")
     | (Pt(_, _)) = ()

val main: fun() -> Int32
fun main() =
  puts("Booleans");
  foo(inv(Pt(1i32, 0i32)));
  f(g(Some(5i32)))
