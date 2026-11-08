type module_data = {
  file : string;
  points : (int * int * string) array;
  counters : int array;
}

let modules : module_data array ref = ref [||]
let next_module_id = ref 0

let register_module ~file ~points =
  let id = !next_module_id in
  incr next_module_id;
  let counters = Array.make (Array.length points) 0 in
  let data = { file; points; counters } in
  let cur_len = Array.length !modules in
  if id >= cur_len then begin
    let new_len = max (id + 1) (max 16 (cur_len * 2)) in
    let new_arr = Array.make new_len { file = ""; points = [||]; counters = [||] } in
    Array.blit !modules 0 new_arr 0 cur_len;
    modules := new_arr
  end;
  (!modules).(id) <- data;
  id

let[@inline] hit mod_id pt_id =
  let m = (!modules).(mod_id) in
  m.counters.(pt_id) <- m.counters.(pt_id) + 1

let get_registered_modules () =
  let count = !next_module_id in
  let res = ref [] in
  for i = count - 1 downto 0 do
    let m = (!modules).(i) in
    res := (m.file, m.points, m.counters) :: !res
  done;
  !res

let rec mkdir_p path =
  if path = "" || path = "." || Sys.file_exists path then ()
  else begin
    mkdir_p (Filename.dirname path);
    try Unix.mkdir path 0o755 with _ -> ()
  end

let dump_stats () =
  match Sys.getenv_opt "VF_COVERAGE_DIR" with
  | None -> ()
  | Some dir when String.trim dir = "" -> ()
  | Some dir ->
    let count = !next_module_id in
    if count > 0 then begin
      (try mkdir_p dir with _ -> ());
      let pid = Unix.getpid () in
      let r = Random.bits () land 0xFFFFFF in
      let filename = Printf.sprintf "%s/cov-%d-%06x.vfcov" dir pid r in
      (try
        let oc = open_out filename in
        for i = 0 to count - 1 do
          let m = (!modules).(i) in
          let num_points = Array.length m.points in
          Printf.fprintf oc "MODULE %s %d\n" m.file num_points;
          for p = 0 to num_points - 1 do
            let (line, col, kind) = m.points.(p) in
            let hits = m.counters.(p) in
            Printf.fprintf oc "%d %d %d %s %d\n" p line col kind hits
          done
        done;
        close_out oc
       with exn ->
         Printf.eprintf "vf_cov_runtime: failed to dump coverage to %s: %s\n%!"
           filename (Printexc.to_string exn))
    end

let () =
  Random.self_init ();
  Stdlib.at_exit dump_stats
