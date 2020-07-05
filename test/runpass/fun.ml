val foo : fun((), ()) -> ()
fun foo(x as y, ()) = y; x

val bar : fun(()) -> ()
fun bar(x as y) = x; (); x; y

fun str() = "FOO BAR BAZ"

val str2 : fun() -> Cstring
fun str2() = " \" \n "

val nil : fun() -> ()
fun nil() = ()

fun str_fun(0i32) = "foofoo"
  | (1i32) = "barbar"
  | (2i32) = "bazbaz"
  | (3i32) = "empty"
  | (n) = ""

val main : fun() -> Int32
fun main() = 0i32
