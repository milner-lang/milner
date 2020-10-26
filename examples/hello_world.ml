external puts : fun(Cstring) -> Unit

val main : fun() -> Int32
[@entry] fun main() =
  puts("Hello world!");
  0
