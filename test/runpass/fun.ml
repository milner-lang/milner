val foo : fun((), ()) -> ()
fun foo(x, ()) = x
     | (x, y) = x; y

val bar : fun(()) -> ()
fun bar(x) = x; (); x

fun str() = "FOO BAR BAZ"

fun str2() = " \" \n "

val nil : fun() -> ()
fun nil() = ()
