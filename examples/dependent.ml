external puts : fun(Cstring) -> Unit

val dep<s : Cstring> : fun() -> Unit
fun dep() = ()

val main: fun() -> Int32
[@entry] fun main() =
  puts("Dependent");
  dep.<"Hello">();
  0
