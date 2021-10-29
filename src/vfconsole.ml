open Util
open Ast
open Lexer
open Parser
open Verifast0
open Verifast
open Arg
open Json

let json_of_srcpos (path, line, col) = A [S path; I line; I col]

let json_of_loc0 (ls, le) = A [json_of_srcpos ls; json_of_srcpos le]

let rec json_of_loc l =
  match l with
    Lexed l -> A [S "Lexed"; json_of_loc0 l]
  | DummyLoc -> A [S "DummyLoc"]
  | MacroExpansion (l1, l2) -> A [S "MacroExpansion"; json_of_loc l1; json_of_loc l2]
  | MacroParamExpansion (l1, l2) -> A [S "MacroParamExpansion"; json_of_loc l1; json_of_loc l2]

let json_of_chunk (Chunk ((p, _), typeArgs, coef, args, _)) =
  let s =
    p ^
    (if typeArgs = [] then "" else "<" ^ String.concat ", " (List.map string_of_type typeArgs) ^ ">") ^
    "(" ^ String.concat ", " args ^ ")"
  in
  A [S coef; S s]
let json_of_heap heap = A (List.map json_of_chunk heap)
let json_of_env env = O (List.map (fun (k, v) -> (k, S v)) env)
let json_of_ctxt ctxt =
  match ctxt with
    Assuming cond -> A [S "Assuming"; S cond]
  | Executing (h, env, l, msg) -> A [S "Executing"; json_of_heap h; json_of_env env; json_of_loc l; S msg]
  | PushSubcontext -> A [S "PushSubcontext"]
  | PopSubcontext -> A [S "PopSubcontext"]
  | Branching b -> A [S "Branching"; S (match b with LeftBranch -> "LeftBranch" | RightBranch -> "RightBranch")]

module HashedLoc = struct
  type t = loc0
  let equal l1 l2 = l1 == l2
  let hash ((path, line, col), _) = line
end
module LocHashtbl = Hashtbl.Make(HashedLoc)

module HashedLine = struct
  type t = string * int
  let equal (p1, l1) (p2, l2) = p1 == p2 && l1 = l2
  let hash (path, line) = line
end
module LineHashtbl = Hashtbl.Make(HashedLine)

let _ =
  let verify ?(emitter_callback = fun _ -> ()) (print_stats : bool) (options : options) (prover : string) (path : string) (emitHighlightedSourceFiles : bool) (dumpPerLineStmtExecCounts : bool) allowDeadCode json mergeOptionsFromSourceFile =
    let exit l =
      Java_frontend_bridge.unload();
      exit l
    in
    let reportUseSite, get_use_sites_json =
      if not json then
        (fun _ _ _ -> ()), (fun _ -> Null)
      else
        let paths = Hashtbl.create 50 in
        let pathInfos = ref [] in
        let reportUseSite declarationKind locDecl locUse =
          let get_path_info path =
            match Hashtbl.find_opt paths path with
              Some info -> info
            | None ->
              let id = Hashtbl.length paths in
              let info = (id, path, ref []) in
              Hashtbl.add paths path info;
              push info pathInfos;
              info
          in
          let ((usePath, useLine, useCol), (usePath', useLine', useCol')) = locUse in
          assert (usePath' = usePath);
          let ((declPath, declLine, declCol), (declPath', declLine', declCol')) = locDecl in
          assert (declPath' = declPath);
          let (usePathId, _, useSites) = get_path_info usePath in
          let (declPathId, _, _) = get_path_info declPath in
          push ((useLine, useCol, useLine', useCol'), declPathId, (declLine, declCol, declLine', declCol')) useSites
        in
        let get_use_sites_json () =
          let pathInfos = List.rev (!pathInfos) |> List.map begin fun (_, path, useSites) ->
              let useSites = Array.of_list !useSites in
              useSites |> Array.sort begin fun ((line1, col1, _, _), _, _) ((line2, col2, _, _), _, _) ->
                if line1 < line2 then
                  -1
                else if line1 = line2 then
                  if col1 < col2 then -1 else if col1 = col2 then 0 else 1
                else
                  1
              end;
              let useSites = useSites |> Array.map begin fun (useRange, declPathId, declRange) ->
                  let json_of_range (line1, col1, line2, col2) =
                    if line1 = line2 then
                      A [I line1; I col1; I col2]
                    else
                      A [I line1; I col1; I line2; I col2]
                  in
                  A [json_of_range useRange; I declPathId; json_of_range declRange]
                end
              in
              A [S path; A (Array.to_list useSites)]
            end
          in
          A pathInfos
        in
        reportUseSite, get_use_sites_json
    in
    let exit_with_json_result resultJson =
      let majorVersion = 2 in
      let minorVersion = 0 in
      print_json_endline (A [S "VeriFast-Json"; I majorVersion; I minorVersion; O ["result", resultJson; "useSites", get_use_sites_json ()]])
    in
    let exit_with_msg l msg =
      if json then begin
        exit_with_json_result (A [S "StaticError"; json_of_loc l; S msg])
      end else begin
        print_endline (string_of_loc l ^ ": " ^ msg);
        exit 1
      end
    in
    let verify range_callback =
    try
      let allowDeadCodeLines = LineHashtbl.create 10 in
      let reportStmt, reportStmtExec, reportDeadCode =
        if allowDeadCode then
          (fun _ -> ()), (fun _ -> ()), (fun _ -> ())
        else
          let stmtLocs = LocHashtbl.create 10000 in
          let reportStmt l = LocHashtbl.replace stmtLocs l () in
          let reportStmtExec l = LocHashtbl.remove stmtLocs l in
          let reportDeadCode () =
            stmtLocs |> LocHashtbl.filter_map_inplace begin fun ((path, line, _), _) () ->
              if LineHashtbl.mem allowDeadCodeLines (path, line) then None else Some ()
            end;
            if LocHashtbl.length stmtLocs > 0 then begin
              stmtLocs |> LocHashtbl.iter begin fun l () ->
                Printf.printf "%s: dead code\n" (string_of_loc0 l)
              end;
              exit 1
            end
          in
          reportStmt, reportStmtExec, reportDeadCode
      in
      let reportStmt, reportStmtExec, dumpPerLineStmtExecCounts =
        if dumpPerLineStmtExecCounts then
          let hasStmts = Array.make 10000 false in
          let counts = Array.make 10000 0 in
          let reportStmt l =
            reportStmt l;
            let ((lpath, line, col), _) = l in
            let line = line - 1 in
            if lpath == path then
              hasStmts.(line) <- true
          in
          let reportStmtExec l =
            reportStmtExec l;
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
          reportStmt, reportStmtExec, (fun _ -> ())
      in
      let reportDirective directive l =
        match directive with
          "allow_dead_code" ->
          let ((path, line, _), _) = l in
          LineHashtbl.add allowDeadCodeLines (path, line) ();
          true
        | _ ->
          false
      in
      let callbacks = {Verifast1.noop_callbacks with reportRange=range_callback; reportStmt; reportStmtExec; reportDirective; reportUseSite} in
      let prover, options = 
        if mergeOptionsFromSourceFile then
          merge_options_from_source_file prover options path
        else
          prover, options
      in
      let stats = verify_program ~emitter_callback:emitter_callback prover options path callbacks None None in
      reportDeadCode ();
      dumpPerLineStmtExecCounts ();
      if print_stats then stats#printStats;
      let msg = "0 errors found (" ^ (string_of_int (stats#getStmtExec)) ^ " statements verified)" in
      if json then
        exit_with_json_result (A [S "success"; S msg])
      else
        print_endline msg;
      Java_frontend_bridge.unload();
    with
      PreprocessorDivergence (l, msg) ->
      exit_with_msg (Lexed l) msg
    | ParseException (l, msg) ->
      exit_with_msg l ("Parse error" ^ (if msg = "" then "." else ": " ^ msg))
    | CompilationError(msg) ->
      if json then begin
        exit_with_json_result (A [S "CompilationError"; S msg])
      end else begin
        print_endline msg; exit 1
      end
    | StaticError (l, msg, url) ->
      exit_with_msg l msg
    | SymbolicExecutionError (ctxts, l, msg, url) ->
      if json then begin
        exit_with_json_result (A [S "SymbolicExecutionError"; A (List.map json_of_ctxt ctxts); json_of_loc l; S msg; match url with None -> Null | Some s -> S s])
      end else
        exit_with_msg l msg
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
  let json = ref false in
  let verbose = ref 0 in
  let disable_overflow_check = ref false in
  let prover: string ref = ref default_prover in
  let compileOnly = ref false in
  let isLibrary = ref false in
  let allowAssume = ref false in
  let simplifyTerms = ref false in
  let allowShouldFail = ref false in
  let emitManifest = ref false in
  let checkManifest = ref false in
  let emitDllManifest = ref false in
  let allModules: string list ref = ref [] in
  let dllManifestName = ref None in
  let emitHighlightedSourceFiles = ref false in
  let dumpPerLineStmtExecCounts = ref false in
  let allowDeadCode = ref false in
  let readOptionsFromSourceFile = ref false in
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
  let dataModel = ref None in
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
            ; "-read_options_from_source_file", Set readOptionsFromSourceFile, "Retrieve disable_overflow_check, prover, target settings from first line of .c/.java file; syntax: //verifast_options{disable_overflow_check prover:z3v4.5 target:32bit}"
            ; "-json", Set json, "Report result as JSON"
            ; "-verbose", Set_int verbose, "-1 = file processing; 1 = statement executions; 2 = produce/consume steps; 4 = prover queries."
            ; "-disable_overflow_check", Set disable_overflow_check, " "
            ; "-prover", String (fun str -> prover := str), "Set SMT prover (" ^ list_provers() ^ ")."
            ; "-c", Set compileOnly, "Compile only, do not perform link checking."
            ; "-shared", Set isLibrary, "The file is a library (i.e. no main function required)."
            ; "-allow_assume", Set allowAssume, "Allow assume(expr) annotations."
            ; "-runtime", String (fun path -> runtime := Some path), " "
            ; "-allow_should_fail", Set allowShouldFail, "Allow '//~' annotations that specify the line should fail."
            ; "-emit_vfmanifest", Set emitManifest, " "
            ; "-check_vfmanifest", Set checkManifest, " "
            ; "-emit_dll_vfmanifest", Set emitDllManifest, " "
            ; "-emit_dll_vfmanifest_as", String (fun str -> dllManifestName := Some str), " "
            ; "-bindir", String (fun str -> let p = Util.abs_path str in Util.set_bindir p; add_vroot ("CRT=" ^ p)), "Set custom bindir with standard library"
            ; "-vroot", String (fun str -> add_vroot str), "Add a virtual root for include paths and, creating or linking vfmanifest files (e.g. MYLIB=../../lib). Ill-formed roots are ignored."
            ; "-emit_highlighted_source_files", Set emitHighlightedSourceFiles, " "
            ; "-dump_per_line_stmt_exec_counts", Set dumpPerLineStmtExecCounts, " "
            ; "-allow_dead_code", Set allowDeadCode, " "
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
            ; "-target", String (fun s -> dataModel := Some (data_model_of_string s)), "Target platform of the program being verified. Determines the size of pointer and integer types. Supported targets: " ^ String.concat ", " (List.map fst data_models)
            ]
  in
  let process_file filename =
    if List.exists (Filename.check_suffix filename) [ ".c"; ".cpp"; ".java"; ".scala"; ".jarsrc"; ".javaspec" ]
    then
      begin
        let options = {
          option_verbose = !verbose;
          option_disable_overflow_check = !disable_overflow_check;
          option_allow_should_fail = !allowShouldFail;
          option_emit_manifest = !emitManifest;
          option_check_manifest = !checkManifest;
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
          option_data_model = !dataModel;
          option_report_skipped_stmts = false;
        } in
        if not !json then print_endline filename;
        let emitter_callback (packages : package list) =
          match !outputSExpressions with
            | Some target_file ->
              Printf.printf "Emitting s-expressions to %s\n" target_file;
              SExpressionEmitter.emit target_file packages          
            | None             -> ()
        in
        verify ~emitter_callback:emitter_callback !stats options !prover filename !emitHighlightedSourceFiles !dumpPerLineStmtExecCounts !allowDeadCode !json !readOptionsFromSourceFile;
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
