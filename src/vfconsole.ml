open Verifast

let _ =
  let print_msg l msg =
    print_endline (string_of_loc l ^ ": " ^ msg)
  in
  let verify stats options prover path emitHighlightedSourceFiles =
    let verify reportRange =
    try
      verify_program prover stats options path reportRange None;
      print_endline "0 errors found"
    with
      ParseException (l, msg) -> print_msg l ("Parse error" ^ (if msg = "" then "." else ": " ^ msg)); exit 1
    | StaticError (l, msg) -> print_msg l msg; exit 1
    | SymbolicExecutionError (ctxts, phi, l, msg) ->
        (*
        let _ = print_endline "Trace:" in
        let _ = List.iter (fun c -> print_endline (string_of_context c)) (List.rev ctxts) in
        let _ = print_endline ("Heap: " ^ string_of_heap h) in
        let _ = print_endline ("Env: " ^ string_of_env env) in
        let _ = print_endline ("Failed query: " ^ phi) in
        *)
        let _ = print_msg l msg in
        exit 1
    in
    if emitHighlightedSourceFiles then
    begin
      let sourceFiles = ref [] in
      let reportRange kind ((path1, line1, col1), (path2, line2, col2)) =
        assert (path1 = path2);
        let path = string_of_path path1 in
        let ranges =
          if List.mem_assoc path !sourceFiles then
            List.assoc path !sourceFiles
          else
          begin
            let ranges = ref [] in
            sourceFiles := (path, ranges)::!sourceFiles;
            ranges
          end
        in
        ranges := (((line1, col1), (line2, col2)), kind)::!ranges
      in
      verify reportRange;
      print_endline "Emitting highlighted source files...";
      let emit_source_file (path, ranges) =
        let text = readFile path in
        let n = String.length text in
        let outpath = path ^ ".html" in
        let outfile = open_out outpath in
        output_string outfile "<html><head><title>";
        output_string outfile (Filename.basename path);
        output_string outfile "</title>";
        let stylesheet =
          "<style>\n\
           .keyword {color: blue; font-weight: bold}\n\
           .ghostKeyword {color: #DB9900; font-weight: bold}\n\
           .ghostRange {color: #CC6600}\n\
           .ghostRangeDelimiter {color: gray}\n\
           .comment {color: #008000}\n\
           .error {color: red; text-decoration: underline}\n\
           </style>"
        in
        output_string outfile stylesheet;
        output_string outfile "</head><body><pre>";
        let ranges = !ranges in
        let lexico cx cy (x1, y1) (x2, y2) = let dx = cx x1 x2 in if dx = 0 then cy y1 y2 else dx in
        let compare_pos = lexico compare compare in
        let compare_loc = lexico compare_pos (fun pos1 pos2 -> - compare_pos pos1 pos2) in
        let compare_start_pos (l1, kind1) (l2, kind2) = compare_loc l1 l2 in
        let ranges = List.sort compare_start_pos ranges in
        let rec emit_postfix offset line col inside_ranges before_ranges =
          match inside_ranges with
            ((line0, col0), kind)::inside_ranges when line0 = line && col0 = col ->
            output_string outfile "</span>";
            emit_postfix offset line col inside_ranges before_ranges
          | _ ->
            if offset = n then
              ()
            else
              match before_ranges with
                (((line0, col0), pos1), kind)::before_ranges when line0 = line && col0 = col ->
                output_string outfile "<span class=\"";
                let kindClass =
                  match kind with
                    KeywordRange -> "keyword"
                  | GhostKeywordRange -> "ghostKeyword"
                  | GhostRange -> "ghostRange"
                  | GhostRangeDelimiter -> "ghostRangeDelimiter"
                  | CommentRange -> "comment"
                  | ErrorRange -> "error"
                in
                output_string outfile kindClass;
                output_string outfile "\">";
                begin
                match inside_ranges with
                  (pos2, _)::_ when compare_pos pos2 pos1 < 0 -> let ((l1, c1), (l2, c2)) = (pos1, pos2) in Printf.printf "%s (%d, %d) < (%d, %d)" path l1 c1 l2 c2; assert false
                | _ -> emit_postfix offset line col ((pos1, kind)::inside_ranges) before_ranges
                end
              | _ ->
                let c = text.[offset] in
                if c = '\r' && offset + 1 < n && text.[offset + 1] = '\n' then
                begin
                  output_string outfile "\r\n";
                  emit_postfix (offset + 2) (line + 1) 1 inside_ranges before_ranges
                end
                else if c = '\r' || c = '\n' then
                begin
                  output_byte outfile (int_of_char c);
                  emit_postfix (offset + 1) (line + 1) 1 inside_ranges before_ranges
                end
                else
                begin
                  if c = '<' || c = '&' then
                    output_string outfile (Printf.sprintf "&#%d;" (int_of_char c))
                  else
                    output_byte outfile (int_of_char c);
                  emit_postfix (offset + 1) line (col + 1) inside_ranges before_ranges
                end
        in
        emit_postfix 0 1 1 [] ranges;
        output_string outfile "</pre></body></html>";
        close_out outfile;
        print_endline ("Emitted " ^ outpath)
      in
      List.iter emit_source_file !sourceFiles
    end
    else
      verify (fun _ _ -> ())
  in
  let n = Array.length Sys.argv in
  if n = 1 then
  begin
    print_endline (Verifast.banner ());
    print_endline "Usage: verifast [-stats] [-verbose] [-disable_overflow_check] [-prover z3|redux] [-c] [-shared] [-allow_assume] [-emit_vfmanifest] [-emit_dll_vfmanifest] [-emit_highlighted_source_files] {sourcefile|objectfile} {-export exportmanifest}"
  end
  else
  let stats = ref false in
  let verbose = ref false in
  let disable_overflow_check = ref false in
  let prover: string option ref = ref None in
  let compileOnly = ref false in
  let isLibrary = ref false in
  let allowAssume = ref false in
  let allowShouldFail = ref false in
  let emitManifest = ref false in
  let emitDllManifest = ref false in
  let modules: string list ref = ref [] in
  let emitHighlightedSourceFiles = ref false in
  let exports: string list ref = ref [] in
  let i = ref 1 in
  while !i < n do
    let arg = Sys.argv.(!i) in
    i := !i + 1;
    if String.length arg > 0 && String.get arg 0 = '-' then
      match arg with
        "-stats" -> stats := true
      | "-verbose" -> verbose := true
      | "-disable_overflow_check" -> disable_overflow_check := true
      | "-prover" -> prover := Some Sys.argv.(!i); i := !i + 1
      | "-c" -> compileOnly := true
      | "-shared" -> isLibrary := true
      | "-allow_assume" -> allowAssume := true
      | "-allow_should_fail" -> allowShouldFail := true
      | "-emit_vfmanifest" -> emitManifest := true
      | "-emit_dll_vfmanifest" -> emitDllManifest := true
      | "-emit_highlighted_source_files" -> emitHighlightedSourceFiles := true
      | "-export" -> if !i = n then failwith "-export option requires an argument"; exports := Sys.argv.(!i)::!exports; i := !i + 1
      | _ -> failwith ("unknown command-line option '" ^ arg ^ "'")
    else
    begin
      if Filename.check_suffix arg ".c" || Filename.check_suffix arg ".java" || Filename.check_suffix arg ".scala" || Filename.check_suffix arg ".jarsrc" || Filename.check_suffix arg ".javaspec"
      then
      begin
        let options = {
          option_verbose = !verbose;
          option_disable_overflow_check = !disable_overflow_check;
          option_allow_should_fail = !allowShouldFail;
          option_emit_manifest = !emitManifest
        } in
        print_endline arg;
        verify !stats options !prover arg !emitHighlightedSourceFiles
      end;
      modules := arg::!modules
    end
  done;
  if not !compileOnly then
  begin
    try
      print_endline "Linking...";
      let mydir = Filename.dirname Sys.executable_name in
      let crt = Filename.concat mydir "crt.a" in
      let assume_lib = Filename.concat mydir "assume.a" in
      let modules = crt::List.rev !modules in
      let modules = if !allowAssume then assume_lib::modules else modules in
      link_program (!isLibrary) modules !emitDllManifest !exports; 
      print_endline "Program linked successfully."
    with
      LinkError msg -> print_endline msg; exit 1
  end
