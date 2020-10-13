external puts : fun(Cstring) -> Unit

datatype Bool = False | True

datatype Option (a : type) = None | Some(a)

datatype Point = Pt(Int32, Int32)

val f: fun(Bool) -> Int32
fun f
  | (False) =
    puts("False");
    0
  | (True) =
    puts("True");
    1

val g: fun(opt: Option @ Int32) -> Bool
fun g
  | (Some(5)) = False
  | (_) = True

val inv: fun(Point) -> Point
fun inv(Pt(x, y)) = Pt(y, x)

val foo: fun(Point) -> Unit
fun foo(Pt(0, _)) = puts("Touching the x-axis")
     | (Pt(_, _)) = ()

val main: fun() -> Int32
fun main() =
  puts("Booleans");
  foo(inv(Pt(1, 0)));
  f(g(Some(5)))
