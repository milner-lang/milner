let compile filename =
  let pid =
    Unix.create_process "../exe/main.exe"
      [|"../exe/main.exe"; "-o"; "a.o"; filename|]
      Unix.stdin Unix.stdout Unix.stderr
  in
  match Unix.waitpid [] pid with
  | _, Unix.WEXITED 0 -> ()
  | _, Unix.WEXITED n ->
    let msg =
      "Test " ^ filename ^ " failed with exit code "
      ^ Int.to_string n ^ " at compile-time"
    in failwith msg
  | _, Unix.WSIGNALED _ ->
    failwith ("Test " ^ filename ^ " signaled at compile-time")
  | _, Unix.WSTOPPED _ ->
    failwith ("Test " ^ filename ^ " stopped at compile-time")

let cc_compile filename =
  let pid =
    Unix.create_process "cc" [|"cc"; "a.o"; "../runtime/gc.c"|]
      Unix.stdin Unix.stdout Unix.stderr
  in
  match Unix.waitpid [] pid with
  | _, Unix.WEXITED 0 -> ()
  | _, Unix.WEXITED n ->
    let msg =
      "Test " ^ filename ^ " failed with exit code "
      ^ Int.to_string n ^ " at c compiler"
    in failwith msg
  | _, Unix.WSIGNALED _ ->
    failwith ("Test " ^ filename ^ " signaled at c compiler")
  | _, Unix.WSTOPPED _ ->
    failwith ("Test " ^ filename ^ " stopped at c compiler")

let run filename =
  let pid =
    Unix.create_process "./a.out" [|"./a.out"|]
      Unix.stdin Unix.stdout Unix.stderr
  in
  match Unix.waitpid [] pid with
  | _, Unix.WEXITED 0 -> ()
  | _, Unix.WEXITED n ->
    let msg =
      "Test " ^ filename ^ " failed with exit code "
      ^ Int.to_string n ^ " at runtime"
    in failwith msg
  | _, Unix.WSIGNALED _ ->
    failwith ("Test " ^ filename ^ " signaled at runtime")
  | _, Unix.WSTOPPED _ ->
    failwith ("Test " ^ filename ^ " stopped at runtime")

let test_dir dir =
  let handle = Unix.opendir dir in
  Fun.protect (fun () ->
      let rec loop () =
        let str = Unix.readdir handle in
        if str <> "." && str <> ".." then (
          let filename = dir ^ "/" ^ str in
          compile filename;
          cc_compile filename;
          run filename
        );
        loop ()
      in try loop () with End_of_file -> ()
    ) ~finally:(fun () -> Unix.closedir handle)

let () =
  test_dir "runpass";
  test_dir "../examples"
