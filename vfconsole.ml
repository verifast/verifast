open Verifast2


let _ =
  let print_msg l msg =
    print_endline (string_of_loc l ^ ": " ^ msg)
  in
  let verify stats verbose prover path =
    try
      let channel = open_in path in
      let stream = Stream.of_channel channel in
      verify_program prover stats verbose path stream (fun _ -> ()) (fun _ -> ());
      print_endline "0 errors found";
      exit 0
    with
      ParseException (l, msg) -> print_msg l ("Parse error" ^ (if msg = "" then "." else ": " ^ msg)); exit 1
    | StaticError (l, msg) -> print_msg l msg; exit 1
    | SymbolicExecutionError (ctxts, phi, l, msg) ->
        let _ = print_endline "Trace:" in
        let _ = List.iter (fun c -> print_endline (string_of_context c)) (List.rev ctxts) in
        (*
        let _ = print_endline ("Heap: " ^ string_of_heap h) in
        let _ = print_endline ("Env: " ^ string_of_env env) in
        *)
        let _ = print_endline ("Failed query: " ^ phi) in
        let _ = print_msg l msg in
        exit 1
  in
  let n = Array.length Sys.argv in
  if n = 1 then
  begin
    print_endline "Verifast 2.0 for C";
    print_endline "Usage: verifast [-stats] [-verbose] [-prover z3|redux] filepath"
  end
  else
  let rec iter stats verbose prover i : unit =
    if i < n then
      let arg = Sys.argv.(i) in
      if String.length arg > 0 && String.get arg 0 = '-' then
        match arg with
          "-stats" -> iter true verbose prover (i + 1)
        | "-verbose" -> iter stats true prover (i + 1)
        | "-prover" -> iter stats verbose (Some Sys.argv.(i + 1)) (i + 2)
        | _ -> failwith ("unknown command-line option '" ^ arg ^ "'")
      else
        if i + 1 = n then
          verify stats verbose prover arg
        else
          failwith "bad command line"
    else
      failwith "no path specified"
  in
  iter false false None 1; ()
