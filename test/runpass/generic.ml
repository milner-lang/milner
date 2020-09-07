val id : ∀ a, fun(a) → a
fun id(x) = x

val main : fun() → Int32
fun main() = id.<Int32>(0i32)
