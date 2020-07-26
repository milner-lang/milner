external puts : fun(Cstring) -> ()

datatype Bool = False | True

val f: fun(Bool) -> Int32
fun f
  | (False) =
    puts("False");
    0i32
  | (True) =
    puts("True");
    1i32

val main: fun() -> Int32
fun main() =
  puts("Booleans");
  f(False)
