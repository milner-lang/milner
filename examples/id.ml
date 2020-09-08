external puts : fun(Cstring) -> ()

val id<a : type> : fun(a) -> a
fun id(x) = x

val main : fun() -> Int32
fun main() =
  puts(id.<Cstring>("Hello polymorphic world!"));
  id.<()>(());
  id.<Int32>(0i32)
