let push xs x = xs := x::!xs

let (|>) x f = f x

let remove_leading_whitespace s =
  let n = String.length s in
  let first_nonwhite =
    let rec iter k =
      if k = n then n else
      match s.[k] with
        ' '|'\012'|'\n'|'\r'|'\t' -> iter (k + 1)
      | _ -> k
    in
    iter 0
  in
  if first_nonwhite = 0 then s else String.sub s first_nonwhite (n - first_nonwhite)

let max_processes =
  match Sys.argv with
    [| _; "-cpus"; n |] -> int_of_string n
  | _ -> 1

let parse_cmdline line =
  if line <> "" && line.[0] = '#' then [""] else
  try
    let space = String.index line ' ' in
    [String.sub line 0 space; String.sub line (space + 1) (String.length line - space - 1)]
  with Not_found -> [line]

let read_line_canon file =
  let line = input_line file in
  let n = String.length line in
  if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line

let macros = ref []

let processes_started_count = ref 0
let active_processes_count = ref 0
let failed_processes_log: string list list ref = ref []
let queue = Queue.create ()
let queueNonempty = Condition.create ()
let queueMutex = Mutex.create ()

let enqueue x =
  Mutex.lock queueMutex;
  Queue.add x queue;
  Condition.signal queueNonempty;
  Mutex.unlock queueMutex

let do_print_line s =
  enqueue (fun () -> print_endline s)

(* Pump events until a process finishes *)
let pump_events () =
  let count0 = !active_processes_count in
  Mutex.lock queueMutex;
  let rec iter () =
    if !active_processes_count < count0 then
      ()
    else if Queue.is_empty queue then begin
      Condition.wait queueNonempty queueMutex;
      iter ()
    end else
      let event = Queue.take queue in
      begin
        try
          event ()
        with e -> Mutex.unlock queueMutex; raise e
      end;
      iter ()
  in
  iter ();
  Mutex.unlock queueMutex

let rec exec_lines filepath file lineno =
  if !failed_processes_log = [] then
  let error msg =
    failwith (Printf.sprintf "mysh: %s: line %d: %s" filepath lineno msg)
  in
  try
    let line = read_line_canon file in
    let rec exec_line line =
      if !failed_processes_log = [] then begin
      print_endline line;
      match parse_cmdline (remove_leading_whitespace line) with
        ["cd"; dir] -> Sys.chdir dir
      | ["del"; file] -> while !active_processes_count > 0 do pump_events() done; Sys.remove file
      | ["ifnotmac"; line] -> if not Fonts.is_macos then exec_line line
      | ["ifz3"; line] -> if Vfconfig.z3_present then exec_line line
      | [""] -> () (* Do not launch a process for empty lines. *)
      | ["let"; macroName] ->
        let lines =
          let rec read_macro_lines () =
            let line = read_line_canon file in
            if line = "in" then [] else line::read_macro_lines ()
          in
          read_macro_lines ()
        in
        macros := (macroName, lines)::!macros
      | ["include"; includepath] ->
        let file = try open_in includepath with Sys_error s -> error (Printf.sprintf "Could not open include file '%s': %s" includepath s) in
        exec_lines includepath file 1;
        close_in file
      | [cmdName; args] when List.mem_assoc cmdName !macros ->
        List.iter (fun line -> exec_line (Printf.sprintf "%s %s" line args)) (List.assoc cmdName !macros)
      | _ ->
        incr processes_started_count;
        let pid = !processes_started_count in
        Printf.printf "Starting process %d\n" pid;
        incr active_processes_count;
        let time0 = Unix.gettimeofday () in
        let cin = Unix.open_process_in line in
        let t = Thread.create
          begin fun () ->
            let output = ref [] in
            push output line;
            try
              while true do
                let line = input_line cin in
                push output line;
                do_print_line (Printf.sprintf "[%d]%s" pid line)
              done
            with End_of_file -> ();
            let status = Unix.close_process_in cin in
            let time1 = Unix.gettimeofday() in
            do_print_line (Printf.sprintf "[%d]%f seconds\n" pid (time1 -. time0));
            if status <> Unix.WEXITED 0 then begin
              let msg =
                match status with
                  Unix.WEXITED n -> Printf.sprintf "=== Process %d terminated with exit code %d ===" pid n
                | Unix.WSIGNALED n -> Printf.sprintf "=== Process %d terminated because of signal %d ===" pid n
                | Unix.WSTOPPED n -> Printf.sprintf "=== Process %d stopped because of signal %d ===" pid n
              in
              do_print_line msg;
              enqueue (fun () -> push failed_processes_log (msg::List.rev !output))
            end;
            enqueue (fun () -> decr active_processes_count)
          end
          ()
        in
        ignore t;
        if !active_processes_count = max_processes then pump_events ()
      end
    in
    exec_line line;
    exec_lines filepath file (lineno + 1)
  with End_of_file -> ()

let () =
  let time0 = Unix.gettimeofday() in
  exec_lines "standard input" stdin 1;
  while !active_processes_count > 0 do pump_events () done;
  let time1 = Unix.gettimeofday() in
  Printf.printf "Total execution time: %f seconds\n" (time1 -. time0);
  List.rev !failed_processes_log |> List.iter begin fun lines ->
    print_newline ();
    List.iter print_endline lines
  end;
  Printf.printf "\n%d failed processes\n" (List.length !failed_processes_log);
  if !failed_processes_log <> [] then exit 1
