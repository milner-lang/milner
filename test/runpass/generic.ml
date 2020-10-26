val id<a : type> : fun(a) → a
fun id(x) = x

val main : fun() → Int32
[@entry] fun main() = id.<Int32>(0)
