external puts : fun(Cstring) -> ()

val cases : fun(Int32) -> Cstring
fun cases(0i32) = "Hello world!"
  | (_) = "Goodbye world!"

fun str_cases("") = "Empty"
  | (s) = s

val main : fun() -> Int32
fun main() =
  puts(cases(0i32));
  puts(cases(1i32));
  puts(str_cases(""));
  puts(str_cases("Ichi ni san"));
  0i32
