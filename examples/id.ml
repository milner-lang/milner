external puts : fun(Cstring) -> ()

fun id(x) = x

fun main() =
  puts(id("Hello polymorphic world!"));
  id(());
  id(0i32)
