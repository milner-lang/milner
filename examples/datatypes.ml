external puts : fun(Cstring) -> ()

datatype Bool = False | True

datatype IntOpt = None | Some(Int32)

val f: fun(Bool) -> Int32
fun f
  | (False) =
    puts("False");
    0i32
  | (True) =
    puts("True");
    1i32

val g: fun(IntOpt) -> Bool
fun g
  | (Some(5i32)) = False
  | (_) = True

val main: fun() -> Int32
fun main() =
  puts("Booleans");
  f(g(Some(5i32)))
