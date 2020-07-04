val id : ∀ a, fun(a) -> a
fun id(x) = x

val main : fun() -> Int32
fun main() = id(0i32)
