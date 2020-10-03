external puts : fun(Cstring) -> Unit

val id<a : type> : fun(a) -> a
fun id(x) = x

val main : fun() -> Int32
fun main() =
  puts(id.<Cstring>("Hello polymorphic world!"));
  id.<Unit>(());
  id.<Int32>(0)
