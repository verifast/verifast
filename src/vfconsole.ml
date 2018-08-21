open Ast
open Lexer
open Parser
open Verifast0
open Verifast
open Arg

let _ =
  let print_msg l msg =
    print_endline (string_of_loc l ^ ": " ^ msg)
  in
  let verify ?(emitter_callback = fun _ -> ()) (print_stats : bool) (options : options) (prover : string) (path : string) (emitHighlightedSourceFiles : bool) (dumpPerLineStmtExecCounts : bool) =
    let verify range_callback =
    let exit l =
      Java_frontend_bridge.unload();
      exit l
    in
    try
      let reportStmt, reportStmtExec, dumpPerLineStmtExecCounts =
        if dumpPerLineStmtExecCounts then
          let hasStmts = Array.make 10000 false in
          let counts = Array.make 10000 0 in
          let reportStmt l =
            let ((lpath, line, col), _) = l in
            let line = line - 1 in
            if lpath == path then
              hasStmts.(line) <- true
          in
          let reportStmtExec l =
            let ((lpath, line, col), _) = l in
            let line = line - 1 in
            if lpath == path then
              counts.(line) <- counts.(line) + 1
          in
          let dumpPerLineStmtExecCounts () =
            let text = readFile path in
            let lines = String.split_on_char '\n' text in
            let rec iter k lines =
              match lines with
                [] -> ()
              | line::lines ->
                if hasStmts.(k) then
                  Printf.printf "%5dx %s\n" counts.(k) line
                else
                  Printf.printf "       %s\n" line;
                iter (k + 1) lines
            in
            iter 0 lines
          in
          reportStmt, reportStmtExec, dumpPerLineStmtExecCounts
        else
          (fun _ -> ()), (fun _ -> ()), (fun _ -> ())
      in
      let callbacks = {Verifast1.noop_callbacks with reportRange=range_callback; reportStmt; reportStmtExec} in
      let stats = verify_program ~emitter_callback:emitter_callback prover options path callbacks None None in
      dumpPerLineStmtExecCounts ();
      if print_stats then stats#printStats;
      print_endline ("0 errors found (" ^ (string_of_int (stats#getStmtExec)) ^ " statements verified)");
      Java_frontend_bridge.unload();
    with
      PreprocessorDivergence (l, msg) -> print_msg l msg; exit 1
    | ParseException (l, msg) -> print_msg l ("Parse error" ^ (if msg = "" then "." else ": " ^ msg)); exit 1
    | CompilationError(msg) -> print_endline (msg); exit 1
    | StaticError (l, msg, url) -> print_msg l msg; exit 1
    | SymbolicExecutionError (ctxts, l, msg, url) ->
        (*
        let _ = print_endline "Trace:" in
        let _ = List.iter (fun c -> print_endline (string_of_context c)) (List.rev ctxts) in
        let _ = print_endline ("Heap: " ^ string_of_heap h) in
        let _ = print_endline ("Env: " ^ string_of_env env) in
        *)
        let _ = print_msg l msg in
        exit 1
    in
    if emitHighlightedSourceFiles then
    begin
      let sourceFiles : (string * (((int * int) * (int * int)) * range_kind) list ref) list ref = ref [] in
      let range_callback kind ((path1, line1, col1), (path2, line2, col2)) =    
        assert (path1 = path2);
        let path = path1 in
        let ranges =
          if List.mem_assoc path !sourceFiles then
            List.assoc path !sourceFiles
          else
          begin
            let ranges : (((int * int) * (int * int)) * range_kind) list ref = ref [] in
            sourceFiles := (path, ranges)::!sourceFiles;
            ranges
          end
        in
        ranges := (((line1, col1), (line2, col2)), kind)::!ranges
      in
      verify range_callback;
      print_endline "Emitting highlighted source files...";
      let emit_source_file (path, ranges) =
        let text = readFile path in
        let n = String.length text in
        let outpath = path ^ ".html" in
        let outfile = open_out_bin outpath in
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
  let stats = ref false in
  let verbose = ref 0 in
  let disable_overflow_check = ref false in
  let prover: string ref = ref default_prover in
  let compileOnly = ref false in
  let isLibrary = ref false in
  let allowAssume = ref false in
  let simplifyTerms = ref false in
  let allowShouldFail = ref false in
  let emitManifest = ref false in
  let emitDllManifest = ref false in
  let allModules: string list ref = ref [] in
  let dllManifestName = ref None in
  let emitHighlightedSourceFiles = ref false in
  let dumpPerLineStmtExecCounts = ref false in
  let exports: string list ref = ref [] in
  let outputSExpressions : string option ref = ref None in
  let runtime: string option ref = ref None in
  let provides = ref [] in
  let keepProvideFiles = ref false in
  let include_paths: string list ref = ref [] in
  let define_macros: string list ref = ref [] in
  let library_paths: string list ref = ref ["CRT"] in
  let safe_mode = ref false in
  let header_whitelist: string list ref = ref [] in
  let linkShouldFail = ref false in
  let useJavaFrontend = ref false in
  let enforceAnnotations = ref false in
  let allowUndeclaredStructTypes = ref false in
  let dataModel = ref data_model_32bit in
  let vroots = ref [Util.crt_vroot Util.default_bindir] in
  let add_vroot vroot =
    let (root, expansion) = Util.split_around_char vroot '=' in
    let expansion = Util.abs_path expansion in
    if not (Sys.file_exists expansion) then
      failwith (Printf.sprintf "In definition of vroot '%s': bad expansion '%s': no such file" root expansion);
    if String.length root = 0 then
      failwith (Printf.sprintf "Bad root name '%s': should be nonempty" root);
    String.iter (function 'A'..'Z'|'_'|'0'..'9' -> () | _ -> failwith (Printf.sprintf "Bad root name '%s': should contain only uppercase letters, underscores, and digits" root)) root;
    begin match root.[0] with 'A'..'Z' -> () | _ -> failwith (Printf.sprintf "Bad root name '%s': should start with an uppercase letter" root) end;
    vroots := List.append (List.filter (fun (x, y) -> x <> root) !vroots) [(root, expansion)]
  in

  (* Explanations that are an empty string ("") become hidden in the
   * "--help" output. When adding options, you can consider writing an
   * explanation or just " " to prevent this, or document why the
   * new option should be hidden.
   *)
  let cla = [ "-stats", Set stats, " "
            ; "-verbose", Set_int verbose, "-1 = file processing; 1 = statement executions; 2 = produce/consume steps; 4 = prover queries."
            ; "-disable_overflow_check", Set disable_overflow_check, " "
            ; "-prover", String (fun str -> prover := str), "Set SMT prover (" ^ list_provers() ^ ")."
            ; "-c", Set compileOnly, "Compile only, do not perform link checking."
            ; "-shared", Set isLibrary, "The file is a library (i.e. no main function required)."
            ; "-allow_assume", Set allowAssume, "Allow assume(expr) annotations."
            ; "-runtime", String (fun path -> runtime := Some path), " "
            ; "-allow_should_fail", Set allowShouldFail, "Allow '//~' annotations that specify the line should fail."
            ; "-emit_vfmanifest", Set emitManifest, " "
            ; "-emit_dll_vfmanifest", Set emitDllManifest, " "
            ; "-emit_dll_vfmanifest_as", String (fun str -> dllManifestName := Some str), " "
            ; "-bindir", String (fun str -> let p = Util.abs_path str in Util.set_bindir p; add_vroot ("CRT=" ^ p)), "Set custom bindir with standard library"
            ; "-vroot", String (fun str -> add_vroot str), "Add a virtual root for include paths and, creating or linking vfmanifest files (e.g. MYLIB=../../lib). Ill-formed roots are ignored."
            ; "-emit_highlighted_source_files", Set emitHighlightedSourceFiles, " "
            ; "-dump_per_line_stmt_exec_counts", Set dumpPerLineStmtExecCounts, " "
            ; "-provides", String (fun path -> provides := !provides @ [path]), " "
            ; "-keep_provide_files", Set keepProvideFiles, " "
            ; "-emit_sexpr",
              String begin fun str ->
                outputSExpressions := Some str;
                SExpressionEmitter.unsupported_exception := false
              end,
              "Emits the AST as an s-expression to the specified file."
            ; "-emit_sexpr_fail",
              String begin fun str ->
                outputSExpressions := Some str;
                SExpressionEmitter.unsupported_exception := true
              end,
              "Emits the AST as an s-expression to the specified file; raises exception on unsupported constructs."
            ; "-export", String (fun str -> exports := str :: !exports), " "
            ; "-I", String (fun str -> include_paths := str :: !include_paths), "Add a directory to the list of directories to be searched for header files."
            ; "-D", String (fun str -> define_macros := str :: !define_macros), "Predefine name as a macro, with definition 1."
            ; "-L", String (fun str -> library_paths := str :: !library_paths), "Add a directory to the list of directories to be searched for manifest files during linking."
            ; "-safe_mode", Set safe_mode, "Safe mode (for use in CGI scripts)."
            ; "-allow_header", String (fun str -> header_whitelist := str::!header_whitelist), "Add the specified header to the whitelist."
            ; "-link_should_fail", Set linkShouldFail, "Specify that the linking phase is expected to fail."
            ; "-javac", Unit (fun _ -> (useJavaFrontend := true; Java_frontend_bridge.load ())), " "
            ; "-enforce_annotations", Unit (fun _ -> (enforceAnnotations := true)), " "
            ; "-allow_undeclared_struct_types", Unit (fun () -> (allowUndeclaredStructTypes := true)), " "
            ; "-target", String (fun s -> dataModel := data_model_of_string s), "Target platform of the program being verified. Determines the size of pointer and integer types. Supported targets: " ^ String.concat ", " (List.map fst data_models)
            ]
  in
  let process_file filename =
    if List.exists (Filename.check_suffix filename) [ ".c"; ".java"; ".scala"; ".jarsrc"; ".javaspec" ]
    then
      begin
        let options = {
          option_verbose = !verbose;
          option_disable_overflow_check = !disable_overflow_check;
          option_allow_should_fail = !allowShouldFail;
          option_emit_manifest = !emitManifest;
          option_vroots = !vroots;
          option_allow_assume = !allowAssume;
          option_simplify_terms = !simplifyTerms;
          option_runtime = !runtime;
          option_provides = !provides;
          option_keep_provide_files = !keepProvideFiles;
          option_include_paths = List.map (Util.replace_vroot !vroots) !include_paths;
          option_define_macros = !define_macros;
          option_safe_mode = !safe_mode;
          option_header_whitelist = !header_whitelist;
          option_use_java_frontend = !useJavaFrontend;
          option_enforce_annotations = !enforceAnnotations;
          option_allow_undeclared_struct_types = !allowUndeclaredStructTypes;
          option_data_model = !dataModel
        } in
        print_endline filename;
        let emitter_callback (packages : package list) =
          match !outputSExpressions with
            | Some target_file ->
              Printf.printf "Emitting s-expressions to %s\n" target_file;
              SExpressionEmitter.emit target_file packages          
            | None             -> ()
        in
        verify ~emitter_callback:emitter_callback !stats options !prover filename !emitHighlightedSourceFiles !dumpPerLineStmtExecCounts;
        allModules := ((Filename.chop_extension filename) ^ ".vfmanifest")::!allModules
      end
    else if Filename.check_suffix filename ".o" then
      allModules := ((Filename.chop_extension filename) ^ ".vfmanifest")::!allModules
    else if List.exists (Filename.check_suffix filename) [ ".so"; ".dll"; ".dll.vfmanifest" ] then
      begin
        let filename =
          if Filename.check_suffix filename ".so" then (Filename.chop_extension filename) ^ ".dll.vfmanifest"
          else if Filename.check_suffix filename ".dll" then (filename ^ ".vfmanifest") 
          else filename
        in
        allModules := filename::!allModules;
      end
    else if Filename.check_suffix filename ".vfmanifest" then
      allModules := filename::!allModules
    else
      begin
        print_endline ("Don't know what to do with file \'" ^ filename ^ "\'."); 
        exit 1
      end
  in
  let usage_string =
    Verifast.banner ()
    ^ "\nUsage: verifast [options] {sourcefile|objectfile}\n"
  in
  if Array.length Sys.argv = 1
  then usage cla usage_string
  else begin
    let process_file filename =
      if !verbose = -1 then Printf.printf "\n%10.6fs: processing file %s\n" (Perf.time()) filename;
      let result = process_file filename in
      if !verbose = -1 then Printf.printf "%10.6fs: done with file %s\n\n" (Perf.time()) filename;
      result
    in
    parse cla process_file usage_string;
    if not !compileOnly then
      begin
        try
          print_endline "Linking...";
          let library_paths = List.map (Util.replace_vroot !vroots) !library_paths in
          let libs = [Filename.concat !Util.bindir "crt.dll.vfmanifest"] in
          let assume_lib = Filename.concat !Util.bindir "assume.dll.vfmanifest" in
          let libs = if !allowAssume then libs @ [assume_lib] else libs in
          let allModules = libs @ List.rev !allModules in
          if !verbose = -1 then Printf.printf "\n%10.6fs: linking files: %s\n\n" (Perf.time()) (String.concat " " allModules);
          let dllManifest =
            if !emitDllManifest then Some (!dllManifestName) else None
          in
          link_program !vroots library_paths (!isLibrary) allModules dllManifest !exports;
          if (!linkShouldFail) then 
            (print_endline "Error: link phase succeeded, while expected to fail (option -link_should_fail)."; exit 1)
          else print_endline "Program linked successfully."
        with
            LinkError msg when (!linkShouldFail) -> print_endline msg; print_endline "Link phase failed as expected (option -link_should_fail)."
          | LinkError msg -> print_endline msg; exit 1
          | CompilationError msg -> print_endline ("error: " ^ msg); exit 1
      end
  end
