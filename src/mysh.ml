let push xs x = xs := x::!xs

let (|>) x f = f x

let string_of_status status =
  match status with
    Unix.WEXITED 0 -> "terminated successfully"
  | Unix.WEXITED n -> Printf.sprintf "terminated with exit code %d" n
  | Unix.WSIGNALED n -> Printf.sprintf "terminated because of signal %d" n
  | Unix.WSTOPPED n -> Printf.sprintf "stopped because of signal %d" n

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

let decompose_path s =
  let rec iter k =
    let rec iter' k' =
      if k' = String.length s then
        [String.sub s k (k' - k)]
      else
        match s.[k'] with
          '/'|'\\' -> String.sub s k (k' - k)::iter (k' + 1)
        | _ -> iter' (k' + 1)
    in
    iter' k
  in
  iter 0

let max_processes = ref 1
let dots = ref false  (* Print only a dot for successfully terminated processes. *)
let verbose = ref false
let main_filename = ref "standard input"
let main_file = ref stdin

let () =
  let rec iter args =
    match args with
      [] -> ()
    | "-cpus"::n::args ->
      max_processes := int_of_string n;
      iter args
    | "-dots"::args ->
      dots := true;
      iter args
    | "-verbose"::args ->
      verbose := true;
      iter args
    | filename::args when String.length filename > 0 && filename.[0] <> '-' ->
      main_filename := filename;
      let file = try open_in filename with Sys_error s -> failwith (Printf.sprintf "Could not open file '%s': %s" filename s) in
      main_file := file;
      iter args
    | arg::args ->
      Printf.printf "Invalid argument: %s\n" arg;
      print_endline "Usage: mysh [-cpus n] [-dots] [-verbose] [filename]";
      exit 1
  in
  iter (List.tl (Array.to_list Sys.argv))

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

let dots_printed = ref false

let print_dot () =
  print_char '.';
  flush stdout;
  dots_printed := true

let print_endline s =
  if !dots_printed then print_newline ();
  print_endline s;
  dots_printed := false

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
      Mutex.unlock queueMutex;
      event ();
      Mutex.lock queueMutex;
      iter ()
  in
  iter ();
  Mutex.unlock queueMutex

type alarm = {mutable alarm_prev: alarm; alarm_time: float; mutable alarm_handler: unit -> unit; mutable alarm_next: alarm}

let remove_alarm alarm =
  alarm.alarm_prev.alarm_next <- alarm.alarm_next;
  alarm.alarm_next.alarm_prev <- alarm.alarm_prev;
  (* Ensure that calling remove_alarm on an alarm that was already removed has no effect *)
  alarm.alarm_prev <- alarm;
  alarm.alarm_next <- alarm

let rec alarms = {alarm_prev=alarms; alarm_time=0.0; alarm_handler=(fun () -> ()); alarm_next=alarms}

let alarm_mutex = Mutex.create ()
let alarm_condition = Condition.create ()

let alarm_thread = Thread.create begin fun () ->
    Mutex.lock alarm_mutex;
    let rec iter () =
      let next = alarms.alarm_next in
      if next == alarms then begin
        Condition.wait alarm_condition alarm_mutex
      end else begin
        let tnow = Unix.gettimeofday () in
        let delta = next.alarm_time -. tnow in
        if delta <= 0.2 then begin
          remove_alarm next;
          enqueue begin fun () -> next.alarm_handler () end
        end else begin
          Mutex.unlock alarm_mutex;
          Thread.delay delta;
          Mutex.lock alarm_mutex
        end
      end;
      iter ()
    in
    iter ()
  end ()

let create_alarm t h =
  Mutex.lock alarm_mutex;
  let prev =
    let rec iter n =
      if n == alarms || n.alarm_time <= t then n else iter n.alarm_prev
    in
    iter alarms.alarm_prev
  in
  let alarm = {alarm_prev=prev; alarm_time=t; alarm_handler=h; alarm_next=prev.alarm_next} in
  prev.alarm_next <- alarm;
  alarm.alarm_next.alarm_prev <- alarm;
  Condition.signal alarm_condition;
  Mutex.unlock alarm_mutex;
  alarm

let cancel_alarm alarm =
  Mutex.lock alarm_mutex;
  remove_alarm alarm;
  alarm.alarm_handler <- (fun () -> ());
  Mutex.unlock alarm_mutex

let cwd = ref []

let has_char s c =
  try
    ignore (String.index s c); true
  with Not_found -> false

let getcwd () =
  match !cwd with
    [] -> "."
  | cs -> String.concat "/" (List.rev cs)

let rec exec_lines filepath file lineno =
  if !failed_processes_log = [] then
  let error msg =
    failwith (Printf.sprintf "mysh: %s: line %d: %s" filepath lineno msg)
  in
  let cd s =
    decompose_path s |> List.iter begin fun s ->
      if s = "." then
        ()
      else if s = ".." then
        match !cwd with
          _::cs -> cwd := cs
        | [] -> error "cd ..: already at script base directory"
      else begin
        if has_char s '/' || has_char s '\\' then error "cd: composite paths are not supported; split into multiple cd commands";
        push cwd s
      end;
      Sys.chdir s
    end
  in
  try
    let line = read_line_canon file in
    let rec exec_line line =
      let line = remove_leading_whitespace line in
      if !failed_processes_log = [] then begin
      if !verbose then print_endline line;
      match parse_cmdline line with
        ["cd"; dir] -> cd dir
      | ["del"; file] -> while !active_processes_count > 0 do pump_events() done; Sys.remove file
      | ["ifnotmac"; line] -> if not Fonts.is_macos then exec_line line
      | ["ifz3"; line] -> if Vfconfig.z3_present then exec_line line
      | ["ifdef"; line] ->
        let space = try String.index line ' ' with Not_found -> error "Syntax error: 'ifdef ENVVAR CMD' expected" in
        let var = String.sub line 0 space in
        let cmd = String.sub line (space + 1) (String.length line - space - 1) in
        if try ignore (Sys.getenv var); true with Not_found -> false then
          exec_line cmd
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
        if !verbose then Printf.printf "Starting process %d\n" pid;
        incr active_processes_count;
        let time0 = Unix.gettimeofday () in
        let cwd = getcwd () in
        let line' = if cwd = "." then line else cwd ^ "$ " ^ line in
        let cin = Unix.open_process_in (line ^ " 2>&1") in
        let current_alarm = ref None in
        let rec produce_alarm i =
          let runtime = i * 5 in
          let alarm = create_alarm (time0 +. float_of_int runtime) begin fun () ->
              print_endline (Printf.sprintf "SLOW: %s has been running for %ds" line' runtime);
              produce_alarm (i + 1)
            end
          in
          current_alarm := Some alarm
        in
        produce_alarm 1;
        let t = Thread.create
          begin fun () ->
            let output = ref [] in
            if !verbose then push output line';
            try
              while true do
                let line = input_line cin in
                push output line;
                if !verbose then do_print_line (Printf.sprintf "[%d]%s" pid line)
              done
            with End_of_file -> ();
            let status = Unix.close_process_in cin in
            let time1 = Unix.gettimeofday() in
            if !verbose then do_print_line (Printf.sprintf "[%d]%f seconds\n" pid (time1 -. time0));
            enqueue begin fun () ->
                let Some alarm = !current_alarm in
                cancel_alarm alarm
              end;
            if status <> Unix.WEXITED 0 then begin
              let msg =
                if !verbose then
                  Printf.sprintf "=== Process %d %s ===" pid (string_of_status status)
                else
                  Printf.sprintf "FAIL: %s %s" line' (string_of_status status)
              in
              let lines = msg::List.map (fun s -> "> " ^ s) (List.rev !output) in
              let msg = if !verbose then msg else String.concat "\n" lines in
              do_print_line msg;
              enqueue (fun () -> push failed_processes_log lines)
            end else begin
              if !dots then
                enqueue (fun () -> print_dot ())
              else
                do_print_line (Printf.sprintf "PASS: %s (%.2fs)" line' (time1 -. time0))
            end;
            enqueue (fun () -> decr active_processes_count)
          end
          ()
        in
        ignore t;
        if !active_processes_count = !max_processes then pump_events ()
      end
    in
    exec_line line;
    exec_lines filepath file (lineno + 1)
  with End_of_file -> ()

let () =
  let time0 = Unix.gettimeofday() in
  exec_lines !main_filename !main_file 1;
  while !active_processes_count > 0 do pump_events () done;
  let time1 = Unix.gettimeofday() in
  Printf.printf "Total execution time: %f seconds\n" (time1 -. time0);
  List.rev !failed_processes_log |> List.iter begin fun lines ->
    print_newline ();
    List.iter print_endline lines
  end;
  Printf.printf "\n%d failed processes\n" (List.length !failed_processes_log);
  if !failed_processes_log <> [] then exit 1
