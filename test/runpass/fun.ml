val foo : fun((), ()) -> ()
fun foo(x as y, ()) = y; x

val bar : fun(()) -> ()
fun bar(x as y) = x; (); x; y

fun str() = "FOO BAR BAZ"

fun str2() = " \" \n "

val nil : fun() -> ()
fun nil() = ()

fun str_fun("foo") = "foofoo"
  | ("bar") = "barbar"
  | ("baz") = "bazbaz"
  | ("") = "empty"
  | (s) = s
