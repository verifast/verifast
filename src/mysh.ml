let match_start s0 s =
  if String.length s0 <= String.length s && String.sub s 0 (String.length s0) = s0 then
    Some (String.sub s (String.length s0) (String.length s - String.length s0))
  else
    None

let rec exec_lines lineno =
  try
    let line = read_line () in
    print_endline line;
    begin
      match match_start "cd " line with
        Some dir -> Sys.chdir dir
      | None ->
        let status = Sys.command line in
        print_newline ();
        if status <> 0 then
          failwith ("mysh: line " ^ string_of_int lineno ^ ": exit code " ^ string_of_int status)
    end;
    exec_lines (lineno + 1)
  with End_of_file -> ()

let () = exec_lines 1
