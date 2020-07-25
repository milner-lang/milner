external puts : fun(Cstring) -> ()

datatype Bool = False | True

fun bool_to_int
  | (False) = 0i32
  | (True) = 1i32

fun main() =
  puts("Booleans");
  0i32
