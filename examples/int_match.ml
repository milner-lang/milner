external puts : fun(Cstring) -> ()

val cases : fun(Int32) -> Cstring
fun cases(0) = "Hello world!"
  | (_) = "Goodbye world!"

val str_cases : fun(Cstring) -> Cstring
fun str_cases("") = "Empty"
  | ("Foo") = "Foofoorian"
  | ("Bar") = "Barbarian"
  | ("Baz") = "Bazbazrian"
  | ("ML") = "MetaLanguage"
  | (s) = s

val main : fun() -> Int32
fun main() =
  puts(cases(0));
  puts(cases(1));
  puts(str_cases(""));
  puts(str_cases("Foo"));
  puts(str_cases("Bar"));
  puts(str_cases("Baz"));
  puts(str_cases("ML"));
  puts(str_cases("\tIchi ni san"));
  0
