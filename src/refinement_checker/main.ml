open Refinement_checker

let memoize f =
  let cache = Hashtbl.create 100 in
  fun x ->
    match Hashtbl.find_opt cache x with
    | Some y -> y
    | None ->
        let y = f x in
        Hashtbl.add cache x y;
        y

let original_path, verified_path =
  match Sys.argv with
  | [| _; original_path; verified_path |] -> (original_path, verified_path)
  | _ ->
      print_endline
        "Usage: refinement_checker <original_path> <verified_path>\n\n\
         Checks that each behavior of each function in the original path is \
         also exhibited by the corresponding function in the verified path";
      exit 1

let () = Perf.init_windows_error_mode ()
let rustc_args = [ "--vf-rust-mir-exporter:no-preprocess" ]

let original_vf_mir =
  VfMirRd.VfMir.of_message @@ Frontend.get_vf_mir rustc_args original_path

let verified_vf_mir =
  VfMirRd.VfMir.of_message @@ Frontend.get_vf_mir rustc_args verified_path

(* Check, for each function body in original_vf_mir, that there is a matching function body in verified_vf_mir *)
let original_bodies = VfMirRd.VfMir.bodies_get_list original_vf_mir

let verified_bodies =
  VfMirRd.VfMir.bodies_get_list verified_vf_mir
  |> List.map (fun body -> (VfMirRd.Body.def_path_get body, body))

let get_line_offsets text =
  let rec get_line_offsets' text offset acc =
    match String.index_from_opt text offset '\n' with
    | None -> List.rev acc
    | Some i -> get_line_offsets' text (i + 1) ((i + 1) :: acc)
  in
  get_line_offsets' text 0 [ 0 ]

let load_file_core path =
  let chan = open_in path in
  let contents = Frontend.input_fully chan in
  close_in chan;
  let line_offsets = Array.of_list (get_line_offsets contents) in
  (contents, line_offsets)

let load_file = memoize load_file_core

let load_span_snippet span =
  let (path, start_line, start_col), (_, end_line, end_col) =
    decode_span span
  in
  let contents, line_offsets = load_file path in
  let start_offset = line_offsets.(start_line - 1) + start_col in
  let end_offset = line_offsets.(end_line - 1) + end_col in
  String.sub contents start_offset (end_offset - start_offset)

let bodies_are_identical body0 body1 =
  let body0_span = VfMirRd.Body.span_get body0 in
  let body1_span = VfMirRd.Body.span_get body1 in
  let snippet0 = load_span_snippet body0_span in
  let snippet1 = load_span_snippet body1_span in
  snippet0 = snippet1

let check_body_refines_body def_path body verified_body =
  if bodies_are_identical body verified_body then
    Printf.printf "Function bodies for %s are identical\n" def_path
  else (
    Printf.printf
      "Function bodies for %s are different; checking refinement...\n" def_path;
    check_body_refines_body def_path body verified_body)

let () =
  original_bodies
  |> List.iter @@ fun body ->
     let def_path = VfMirRd.Body.def_path_get body in
     match List.assoc_opt def_path verified_bodies with
     | None ->
         error
           (Printf.sprintf "Function body %s not found in verified path"
              def_path)
     | Some verified_body -> check_body_refines_body def_path body verified_body

let () = Printf.printf "No refinement errors found\n"
