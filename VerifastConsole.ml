open Verifast

let _ =
  let print_msg l msg =
    print_endline (string_of_loc l ^ ": " ^ msg)
  in
  let verify verbose path =
    try
      verify_program verbose path
    with
      ParseException (l, msg) -> print_msg l ("Parse error" ^ (if msg = "" then "." else ": " ^ msg))
    | StaticError (l, msg) -> print_msg l msg
    | SymbolicExecutionError (ctxts, phi, l, msg) ->
        let _ = print_endline "Trace:" in
        let _ = List.iter (fun c -> print_endline (string_of_context c)) (List.rev ctxts) in
        (*
        let _ = print_endline ("Heap: " ^ string_of_heap h) in
        let _ = print_endline ("Env: " ^ string_of_env env) in
        *)
        let _ = print_endline ("Failed query: " ^ simp phi) in
        let _ = print_msg l msg in
        ()
  in
  match Sys.argv with
    [| _; path |] -> verify false path
  | [| _; "-verbose"; path |] -> verify true path
  | _ ->
    print_endline "Verifast 0.2 for C";
    print_endline "Usage: verifast [-verbose] filepath";
    print_endline "Note: Requires z3.exe."
