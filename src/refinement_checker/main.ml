open Vf_mir_decoder
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

(** Ignore `/*@~mut@*/` directives *)
let ignore_directives = ref false
let push xs_ref x = xs_ref := x :: !xs_ref
let rustc_args = ref []

let original_path, verified_path =
  let rec process_args = function
    | flag :: args when String.starts_with ~prefix:"--" flag -> (
        match flag :: args with
        | "--" :: [ original_path; verified_path ] ->
            (original_path, verified_path)
        | "--ignore-directives" :: args ->
          ignore_directives := true;
          process_args args
        | "--verbose" :: value :: args ->
            verbosity :=
              begin match int_of_string_opt value with
                None -> failwith "--verbose expects an integer argument"
              | Some n -> n
              end;
            process_args args
        | "--rustc-args" :: value :: args ->
            rustc_args := !rustc_args @ String.split_on_char ' ' value;
            process_args args
        | _ -> failwith ("No such flag: " ^ flag))
    | [ original_path; verified_path ] -> (original_path, verified_path)
    | _ ->
        print_endline
          "Usage: refinement_checker [--ignore-directives] [--verbose N] [--rustc-args ARGS] [--] <original_path> \
           <verified_path>\n\n\
           Checks that each behavior of each function in the original path is \
           also exhibited by the corresponding function in the verified path\n\n
           Options:\n\
               --ignore-directives     Ignore /*@~mut@*/ directives";
        exit 1
  in
  process_args (List.tl (Array.to_list Sys.argv))

let () =
  if !ignore_directives then
    push rustc_args "--vf-rust-mir-exporter:no-preprocess"
  else
    push rustc_args "--vf-rust-mir-exporter:preprocess-readonly"

let () = Perf.init_windows_error_mode ()

let original_vf_mir =
  decode_vf_mir @@ VfMirRd.VfMir.of_message @@ Frontend.get_vf_mir !rustc_args original_path

let verified_vf_mir =
  decode_vf_mir @@ VfMirRd.VfMir.of_message @@ Frontend.get_vf_mir !rustc_args verified_path

(* Check, for each function body in original_vf_mir, that there is a matching function body in verified_vf_mir *)
let original_bodies =
  original_vf_mir.bodies
  |> List.map (fun body -> (canonicalize_def_path body.def_path, body))

let verified_bodies =
  verified_vf_mir.bodies
  |> List.map (fun body -> (canonicalize_def_path body.def_path, body))

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
let decode_body_span (body: body) = decode_span body.span

let load_span_snippet span =
  let (path, start_line, start_col), (_, end_line, end_col) = span in
  let contents, line_offsets = load_file path in
  let start_offset = line_offsets.(start_line - 1) + start_col in
  let end_offset = line_offsets.(end_line - 1) + end_col in
  String.sub contents start_offset (end_offset - start_offset)

let bodies_are_identical body0 body1 =
  let snippet0 = load_span_snippet (decode_body_span body0) in
  let snippet1 = load_span_snippet (decode_body_span body1) in
  snippet0 = snippet1

let wrapper_fn_spans =
  verified_bodies |> List.map (fun (fn, body) ->
    if String.ends_with ~suffix:"__VeriFast_wrapper" fn then
      [decode_body_span body]
    else []) |> List.flatten

let original_checked_spans = ref []
let verified_checked_spans = ref wrapper_fn_spans

let check_body_refines_body def_path body verified_body =
  if bodies_are_identical body verified_body then
    Printf.printf "Function bodies for %s are identical\n" def_path
  else (
    Printf.printf
      "Function bodies for %s are different; checking refinement...\n" def_path;
    check_body_refines_body original_bodies verified_bodies def_path body verified_body;
    push original_checked_spans (decode_body_span body);
    push verified_checked_spans (decode_body_span verified_body))

let skip_whitespace contents offset =
  let rec skip_whitespace' offset =
    if offset = String.length contents then offset
    else
      match contents.[offset] with
      | ' ' | '\t' | '\n' | '\r' -> skip_whitespace' (offset + 1)
      | '/' ->
          if offset + 1 < String.length contents then
            match contents.[offset + 1] with
            | '/' ->
                let rec skip_comment offset =
                  if offset = String.length contents then offset
                  else
                    match contents.[offset] with
                    | '\n' -> skip_whitespace' (offset + 1)
                    | _ -> skip_comment (offset + 1)
                in
                skip_comment (offset + 2)
            | '*' ->
                let rec skip_comment offset nesting_depth =
                  if offset = String.length contents then
                    failwith "Unexpected EOF in comment"
                  else
                    match contents.[offset] with
                    | '*' ->
                        if offset + 1 < String.length contents then
                          match contents.[offset + 1] with
                          | '/' ->
                              if nesting_depth = 1 then
                                skip_whitespace' (offset + 2)
                              else skip_comment (offset + 2) (nesting_depth - 1)
                          | _ -> skip_comment (offset + 1) nesting_depth
                        else failwith "Unexpected EOF in comment"
                    | '/' ->
                        (* Handle nested comments *)
                        if offset + 1 < String.length contents then
                          match contents.[offset + 1] with
                          | '*' -> skip_comment (offset + 2) (nesting_depth + 1)
                          | _ -> skip_comment (offset + 1) nesting_depth
                        else failwith "Unexpected EOF in comment"
                    | _ -> skip_comment (offset + 1) nesting_depth
                in
                skip_comment (offset + 2) 1
            | _ -> offset
          else offset
      | _ -> offset
  in
  skip_whitespace' offset

let rec skip_whitespace_and_checked_ranges contents offset checked_ranges =
  let offset = skip_whitespace contents offset in
  match checked_ranges with
  | (start, end_) :: checked_ranges when start = offset ->
    skip_whitespace_and_checked_ranges contents end_ checked_ranges
  | _ -> offset, checked_ranges

(* Checks that the two files are identical, after collapsing whitespace and spans checked by the refinement checker *)
let check_files_match (path0, path1) =
  Printf.printf "Checking that, apart from checked functions and comments, %s and %s are identical\n" path0 path1;
  let contents0, line_offsets0 = load_file path0 in
  let contents1, line_offsets1 = load_file path1 in
  let checked_ranges0 =
    List.filter
      (fun ((path, start_line, start_col), (_, end_line, end_col)) ->
        path = path0)
      !original_checked_spans
  in
  let checked_ranges1 =
    List.filter
      (fun ((path, start_line, start_col), (_, end_line, end_col)) ->
        path = path1)
      !verified_checked_spans
  in
  let checked_ranges0 =
    List.map
      (fun ((_, start_line, start_col), (_, end_line, end_col)) ->
        ( line_offsets0.(start_line - 1) + start_col,
          line_offsets0.(end_line - 1) + end_col ))
      checked_ranges0
  in
  let checked_ranges1 =
    List.map
      (fun ((_, start_line, start_col), (_, end_line, end_col)) ->
        ( line_offsets1.(start_line - 1) + start_col,
          line_offsets1.(end_line - 1) + end_col ))
      checked_ranges1
  in
  let checked_ranges0 = List.sort compare checked_ranges0 in
  let checked_ranges1 = List.sort compare checked_ranges1 in
  let rec iter offset0 offset1 checked_ranges0 checked_ranges1 =
    let offset0', checked_ranges0 = skip_whitespace_and_checked_ranges contents0 offset0 checked_ranges0 in
    let offset1', checked_ranges1 = skip_whitespace_and_checked_ranges contents1 offset1 checked_ranges1 in
    if offset0' = offset0 <> (offset1' = offset1) then
      failwith
        (Printf.sprintf
           "Comparing %s to %s: Whitespace mismatch at offset %d/%d" path0 path1
           offset0 offset1);
    let offset0, offset1 = (offset0', offset1') in
    if offset0 = String.length contents0 then
      if offset1 = String.length contents1 then (
        assert (checked_ranges0 = [] && checked_ranges1 = []);
        ())
      else
        failwith
          (Printf.sprintf "Comparing %s to %s: Unexpected EOF in %s"
              path0 path1 path1)
    else if offset1 = String.length contents1 then
      failwith
        (Printf.sprintf "Comparing %s to %s: Unexpected EOF in %s" path0
            path1 path0)
    else (
      if contents0.[offset0] <> contents1.[offset1] then
        failwith
          (Printf.sprintf
              "Comparing %s to %s: Mismatch at offset %d/%d: %c vs %c"
              path0 path1 offset0 offset1 contents0.[offset0]
              contents1.[offset1]);
      iter (offset0 + 1) (offset1 + 1) checked_ranges0 checked_ranges1)
  in
  iter 0 0 checked_ranges0 checked_ranges1

let check_files_match = memoize check_files_match

let rec check_module module0 module1 =
  let (path0, _, _), _ = decode_span module0.body_span in
  let (path1, _, _), _ = decode_span module1.body_span in
  check_files_match (path0, path1);
  let submodules0 = module0.submodules in
  let submodules1 = module1.submodules in
  List.iter2 check_module submodules0 submodules1

let check_bodies () =
  original_bodies
  |> List.iter @@ fun (def_path, body) ->
     match List.assoc_opt def_path verified_bodies with
     | None ->
        if body.visibility = Restricted then
          () (* If a private function of the original program does not appear in the verified program,
                it must be the case that all calls of that function were inlined. *)
        else
          error
            (Printf.sprintf "Function body %s not found in verified path"
               def_path)
     | Some verified_body -> check_body_refines_body def_path body verified_body

let check_modules () =
  check_files_match (original_path, verified_path);
  let modules0 = original_vf_mir.modules in
  let modules1 = verified_vf_mir.modules in
  List.iter2 check_module modules0 modules1

let () =
  try
    check_bodies ();
    check_modules ();
    Printf.printf "No refinement errors found\n"
  with RefinementCheckFailure msg ->
    print_endline msg;
    exit 1
    
