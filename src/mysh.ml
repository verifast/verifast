let max_processes =
  match Sys.argv with
    [| _; "-cpus"; n |] -> int_of_string n
  | _ -> 1

let parse_cmdline line =
  try
    let space = String.index line ' ' in
    [String.sub line 0 space; String.sub line (space + 1) (String.length line - space - 1)]
  with Not_found -> [line]

let read_line_canon file =
  let line = input_line file in
  let n = String.length line in
  if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line

let macros = ref []

let pnos = ref 0
let processes = ref 0
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

let pump_events () =
  let processes0 = !processes in
  Mutex.lock queueMutex;
  let rec iter () =
    if !processes < processes0 then
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
  let error msg =
    failwith (Printf.sprintf "mysh: %s: line %d: %s" filepath lineno msg)
  in
  try
    let line = read_line_canon file in
    let rec exec_line line =
      print_endline line;
      match parse_cmdline line with
        ["cd"; dir] -> Sys.chdir dir
      | ["del"; file] -> while !processes > 0 do pump_events() done; Sys.remove file
      | ["ifnotmac"; line] -> if not Fonts.is_macos then exec_line line
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
        incr pnos;
        let pno = !pnos in
        Printf.printf "Starting process %d\n" pno;
        incr processes;
        let time0 = Unix.gettimeofday () in
        let cin = Unix.open_process_in line in
        let t = Thread.create
          begin fun () ->
            try
              while true do do_print_line (Printf.sprintf "[%d]%s" pno (input_line cin)) done
            with End_of_file -> ();
            let status = Unix.close_process_in cin in
            let time1 = Unix.gettimeofday() in
            do_print_line (Printf.sprintf "[%d]%f seconds\n" pno (time1 -. time0));
            if status <> Unix.WEXITED 0 then begin
              let msg =
                match status with
                  Unix.WEXITED n -> Printf.sprintf "Process %d terminated with exit code %d" pno n
                | Unix.WSIGNALED n -> Printf.sprintf "Process %d terminated because of signal %d" pno n
                | Unix.WSTOPPED n -> Printf.sprintf "Process %d stopped because of signal %d" pno n
              in
              enqueue (fun () -> error msg)
            end;
            enqueue (fun () -> decr processes)
          end
          ()
        in
        ignore t;
        if !processes = max_processes then pump_events ()
    in
    exec_line line;
    exec_lines filepath file (lineno + 1)
  with End_of_file ->
    while !processes > 0 do pump_events () done

let () =
  let time0 = Unix.gettimeofday() in
  exec_lines "standard input" stdin 1;
  let time1 = Unix.gettimeofday() in
  Printf.printf "Total execution time: %f seconds\n" (time1 -. time0)
