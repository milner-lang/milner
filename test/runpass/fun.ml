val foo : fun(Unit, Unit) -> Unit
fun foo(x as y, ()) = y; x

val bar : fun(Unit) -> Unit
fun bar(x as y) = x; (); x; y

val str : fun() -> Cstring
fun str() = "FOO BAR BAZ"

val str2 : fun() -> Cstring
fun str2() = " \" \n "

val nil : fun() -> Unit
fun nil() = ()

val str_fun : fun(Int32) -> Cstring
fun str_fun(0) = "foofoo"
  | (1) = "barbar"
  | (2) = "bazbaz"
  | (3) = "empty"
  | (n) = ""

val main : fun() -> Int32
[@entry] fun main() = 0
