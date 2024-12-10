open Util
open Ast
open Lexer
open Parser
open Verifast0
open Verifast
open Arg
open Json

let () = Register_provers.register_provers ()

let json_of_srcpos (path, line, col) = A [S path; I line; I col]

let json_of_loc0 (ls, le) = A [json_of_srcpos ls; json_of_srcpos le]

let rec json_of_loc l =
  match l with
    Lexed l -> A [S "Lexed"; json_of_loc0 l]
  | DummyLoc -> A [S "DummyLoc"]
  | MacroExpansion (l1, l2) -> A [S "MacroExpansion"; json_of_loc l1; json_of_loc l2]
  | MacroParamExpansion (l1, l2) -> A [S "MacroParamExpansion"; json_of_loc l1; json_of_loc l2]

module JsonOf(ARGS: sig
  val string_of_type: type_ -> string
end) = struct
  open ARGS

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

end

module HashedLoc = struct
  type t = loc0
  let equal l1 l2 = l1 == l2
  let hash ((path, line, col), _) = line
end
module LocHashtbl = Hashtbl.Make(HashedLoc)

module HashedLine = struct
  type t = string * int
  let equal (p1, l1) (p2, l2) = p1 = p2 && l1 = l2
  let hash (path, line) = line
end
module LineHashtbl = Hashtbl.Make(HashedLine)

let _ =
  let verify ?(emitter_callback = fun _ _ _ -> ()) (print_stats : bool) (options : options) (prover : string) (path : string) (emitHighlightedSourceFiles : bool) (dumpPerLineStmtExecCounts : bool) allowDeadCode json expectedJsonResult applyQuickFix mergeOptionsFromSourceFile breakpoint focus targetPath =
    let exit l =
      Java_frontend_bridge.unload();
      exit l
    in
    let reportExecutionForest, get_execution_forest_json =
      if not json then
        (fun _ -> ()), (fun _ -> Null)
      else
        let forest = ref None in
        let reportExecutionForest f = forest := Some f in
        let get_execution_forest_json () =
          let msgsTable = Hashtbl.create 10 in
          let msgs = ref [] in
          let get_msg_id msg =
            match Hashtbl.find_opt msgsTable msg with
              None ->
              msgs := msg::!msgs;
              let id = Hashtbl.length msgsTable in
              Hashtbl.add msgsTable msg id;
              id
            | Some id -> id
          in
          let Some forest = !forest in
          let buf = Buffer.create 10000 in
          let add_node_type = function
            ExecNode (msg, path) -> Printf.bprintf buf "#%d" (get_msg_id msg)
          | BranchNode -> Buffer.add_char buf 'B'
          | SuccessNode -> Buffer.add_char buf 'S'
          | ErrorNode -> Buffer.add_char buf 'E'
          in
          let rec add_node (Node (nodeType, children)) =
            add_node_type nodeType;
            match !children with
              [child] -> add_node child
            | children -> Buffer.add_char buf '['; List.iter add_node (List.rev children); Buffer.add_char buf ']'
          in
          List.iter add_node (List.rev !forest);
          O ["msgs", A (List.map (fun msg -> S msg) (List.rev !msgs)); "forest", S (Buffer.contents buf)]
        in
        reportExecutionForest, get_execution_forest_json
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
      match expectedJsonResult with
        Some path ->
        let expectedJson = readFile path in
        let resultJsonString = string_of_json resultJson in
        if resultJsonString = expectedJson then
          exit 0
        else begin
          print_endline ("Expected JSON result in file " ^ path ^ ":");
          print_endline expectedJson;
          print_endline "Actual JSON result:";
          print_endline resultJsonString;
          exit 1
        end
      | None ->
        let majorVersion = 2 in
        let minorVersion = 0 in
        print_json_endline (A [S "VeriFast-Json"; I majorVersion; I minorVersion; O ["result", resultJson; "useSites", get_use_sites_json (); "executionForest", get_execution_forest_json ()]])
    in
    let exit_with_msg l msg =
      if json then begin
        exit_with_json_result (A [S "StaticError"; json_of_loc l; S msg])
      end else begin
        print_endline (string_of_loc l ^ ": " ^ msg);
        exit 1
      end
    in
    let json_of_quick_fix_kind = function
      InsertTextAt (pos, text) -> A [S "InsertTextAt"; json_of_srcpos pos; S text]
    in
    let json_of_quick_fix (description, kind) =
      O ["description", S description; "kind", json_of_quick_fix_kind kind]
    in
    let json_of_error_attributes attrs =
      let {help_topic; quick_fixes} = parse_error_attributes attrs in
      let props =
        [
          "help_topic", (match help_topic with None -> None | Some topic -> Some (S topic));
          "quick_fixes", (match quick_fixes with [] -> None | _ -> Some (A (List.map json_of_quick_fix quick_fixes)))
        ]
      in
      O (flatmap (function (k, Some v) -> [k, v] | _ -> []) props)
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
      let callbacks = {Verifast1.reportRange=range_callback; reportStmt; reportStmtExec; reportDirective; reportUseSite; reportExecutionForest} in
      let prover, options = 
        if mergeOptionsFromSourceFile then
          merge_options_from_source_file prover options path
        else
          prover, options
      in
      let stats = verify_program ~emitter_callback:emitter_callback prover options path callbacks breakpoint focus targetPath in
      reportDeadCode ();
      dumpPerLineStmtExecCounts ();
      if print_stats then stats#printStats;
      let msg = stats#get_success_message in
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
    | CompilationErrorWithDetails (msg, details) ->
      if json then begin
        exit_with_json_result (A [S "CompilationErrorWithDetails"; S msg; S details])
      end else begin
        print_endline msg;
        print_endline "Details:";
        print_endline details;
        exit 1
      end
    | StaticError (l, msg, url) ->
      begin match applyQuickFix with
        None -> ()
      | Some file ->
        let QuickFix (descr, InsertTextAt ((insertPath, insertLine, insertCol), insertText))::_ = List.filter (function QuickFix (_, _) -> true | _ -> false) (Option.get url) in
        let text = readFile path in
        let lines = String.split_on_char '\n' text in
        let lines_before, line::lines_after = Util.take_drop (insertLine - 1) lines in
        let before = String.sub line 0 (insertCol - 1) in
        let after = String.sub line (insertCol - 1) (String.length line - insertCol + 1) in
        let lines = lines_before @ (before ^ insertText ^ after) :: lines_after in
        let text = String.concat "\n" lines in
        let outfile = open_out_bin file in
        output_string outfile text;
        close_out outfile;
        Printf.printf "Applied quick fix: %s\n" descr;
        exit 0
      end;
      if json then
        exit_with_json_result (A [S "StaticError"; json_of_loc l; S msg; json_of_error_attributes url])
      else
        exit_with_msg l msg
    | RustcErrors (l, msg, diagnostics) ->
      if json then
        exit_with_json_result (A [S "StaticError"; json_of_loc l; S msg; O ["rustc_diagnostics", A diagnostics]])
      else begin
        List.iter (fun d -> Printf.printf "%s" (o_assoc "rendered" d |> s_value)) diagnostics;
        exit 1
      end
    | SymbolicExecutionError (ctxts, l, msg, url) ->
      let language, dialect = file_specs path in
      let open JsonOf(struct let string_of_type = string_of_type language dialect end) in
      if json then begin
        exit_with_json_result (A [S "SymbolicExecutionError"; A (List.map json_of_ctxt ctxts); json_of_loc l; S msg; json_of_error_attributes url])
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
  let expected_json_result_file = ref None in
  let apply_quick_fix = ref None in
  let verbose = ref 0 in
  let verbose_flags = ref [] in
  let vfbindings = ref Vfbindings.default in
  let prover: string ref = ref default_prover in
  let compileOnly = ref false in
  let isLibrary = ref false in
  let allowAssume = ref false in
  let allowShouldFail = ref false in
  let emitManifest = ref false in
  let checkManifest = ref false in
  let emitDllManifest = ref false in
  let allModules: string list ref = ref [] in
  let dllManifestName = ref None in
  let emitHighlightedSourceFiles = ref false in
  let dumpPerLineStmtExecCounts = ref false in
  let allowDeadCode = ref false in
  let allowIgnoreRefCreation = ref false in
  let readOptionsFromSourceFile = ref false in
  let exports: string list ref = ref [] in
  let outputSExpressions : string option ref = ref None in
  let dumpAST: (bool * bool * string) option ref = ref None in
  let breakpoint: (string * int) option ref = ref None in
  let focus: (string * int) option ref  = ref None in
  let targetPath: int list option ref = ref None in
  let provides = ref [] in
  let keepProvideFiles = ref false in
  let library_paths: string list ref = ref ["CRT"] in
  let safe_mode = ref false in
  let header_whitelist: string list ref = ref [] in
  let linkShouldFail = ref false in
  let useJavaFrontend = ref false in
  let enforceAnnotations = ref false in
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

  let cla = vfparams |> List.map begin fun (paramName, (Vfparam vfparam, description)) ->
      let action =
        match vfparam_info_of vfparam with
          BoolParam -> Unit (fun () -> vfbindings := Vfbindings.set vfparam true !vfbindings)
        | ParsedParam (_, parseFunc, _) -> String (fun arg -> vfbindings := Vfbindings.set vfparam (parseFunc arg) !vfbindings)
      in
      "-" ^ paramName, action, description
    end
  in

  (* Explanations that are an empty string ("") become hidden in the
   * "--help" output. When adding options, you can consider writing an
   * explanation or just " " to prevent this, or document why the
   * new option should be hidden.
   *)
  let cla = cla @
            [ "-stats", Set stats, " "
            ; "-read_options_from_source_file", Set readOptionsFromSourceFile, "Retrieve disable_overflow_check, prover, target settings from first line of .c/.java file; syntax: //verifast_options{disable_overflow_check prover:z3v4.5 target:32bit}"
            ; "-json", Set json, "Report result as JSON"
            ; "-expect_json_result", String (fun file -> json := true; expected_json_result_file := Some file), "Expect JSON result from file"
            ; "-apply_quick_fix", String (fun file -> apply_quick_fix := Some file), "Apply the quick fix proposed by VeriFast and write the resulting source file to the specified file"
            ; "-verbose", Set_int verbose, "-1 = file processing; 1 = statement executions; 2 = produce/consume steps; 4 = prover queries."
            ; "-verbose_flag", String (fun flag -> verbose_flags := flag::!verbose_flags), "Enable particular verbose output. Flags: rust_exporter"
            ; "-prover", String (fun str -> prover := str), "Set SMT prover (" ^ list_provers() ^ ")."
            ; "-c", Set compileOnly, "Compile only, do not perform link checking."
            ; "-shared", Set isLibrary, "The file is a library (i.e. no main function required)."
            ; "-allow_assume", Set allowAssume, "Allow assume(expr) annotations."
            ; "-breakpoint", String (fun path_loc -> let [path; loc_string] = String.split_on_char ':' path_loc in breakpoint := Some (path, int_of_string loc_string)), "-breakpoint myfile.c:123 causes symbolic execution to fail when it reaches line 123 of file myfile.c"
            ; "-focus", String (fun path_loc -> let [path; loc_string] = String.split_on_char ':' path_loc in focus := Some (path, int_of_string loc_string)), "-focus myfile.c:123 causes VeriFast to verify only the function/method/constructor/destructor at the specified source line"
            ; "-break_at_node", String (fun path -> targetPath := Some (path |> String.split_on_char ',' |> List.map int_of_string)), "Break when symbolic execution reaches the specified node in the execution tree."
            ; "-allow_should_fail", Set allowShouldFail, "Allow '//~' annotations that specify the line should fail."
            ; "-allow_ignore_ref_creation", Set allowIgnoreRefCreation, "Allow //~ignore_ref_creation directives."
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
            ; "-dump_ast", String (fun str -> dumpAST := Some (false, true, str)), "Dumps the verified module's AST to the specified file."
            ; "-dump_ast_with_locs", String (fun str -> dumpAST := Some (false, false, str)), "Dumps the verified module's AST, including source locations, to the specified file."
            ; "-dump_asts", String (fun str -> dumpAST := Some (true, true, str)), "Dumps the the verified module's AST as well as all header files' ASTs to the specified directory."
            ; "-dump_asts_with_locs", String (fun str -> dumpAST := Some (true, false, str)), "Dumps the the verified module's AST as well as all header files' ASTs, including source locations, to the specified directory."
            ; "-export", String (fun str -> exports := str :: !exports), " "
            ; "-L", String (fun str -> library_paths := str :: !library_paths), "Add a directory to the list of directories to be searched for manifest files during linking."
            ; "-safe_mode", Set safe_mode, "Safe mode (for use in CGI scripts)."
            ; "-allow_header", String (fun str -> header_whitelist := str::!header_whitelist), "Add the specified header to the whitelist."
            ; "-link_should_fail", Set linkShouldFail, "Specify that the linking phase is expected to fail."
            ; "-javac", Unit (fun _ -> (useJavaFrontend := true; Java_frontend_bridge.load ())), " "
            ; "-enforce_annotations", Unit (fun _ -> (enforceAnnotations := true)), " "
            ]
  in
  let process_file filename =
    if List.exists (Filename.check_suffix filename) [ ".c"; ".h"; ".cpp"; ".hpp"; ".java"; ".scala"; ".jarsrc"; ".javaspec"; ".rs" ]
    then
      begin
        let vfbindings = !vfbindings in
        let includePaths = Vfbindings.get Vfparam_include_paths vfbindings in
        let includePaths = List.map (Util.replace_vroot !vroots) includePaths in
        let vfbindings = Vfbindings.set Vfparam_include_paths includePaths vfbindings in
        let options = {
          option_verbose = !verbose;
          option_verbose_flags = !verbose_flags;
          option_vfbindings = vfbindings;
          option_allow_should_fail = !allowShouldFail;
          option_allow_ignore_ref_creation = !allowIgnoreRefCreation;
          option_emit_manifest = !emitManifest;
          option_check_manifest = !checkManifest;
          option_vroots = !vroots;
          option_allow_assume = !allowAssume;
          option_provides = !provides;
          option_keep_provide_files = !keepProvideFiles;
          option_safe_mode = !safe_mode;
          option_header_whitelist = !header_whitelist;
          option_use_java_frontend = !useJavaFrontend;
          option_enforce_annotations = !enforceAnnotations;
          option_report_skipped_stmts = false;
        } in
        if not !json then print_endline filename;
        let emitter_callback (path : string) (dir : string) (packages : package list) =
          begin match !dumpAST with
            | Some (allASTs, noLocs, target_file) ->
              if allASTs then begin
                if not (Sys.file_exists target_file) then Sys.mkdir target_file 0o700;
                let target_file = Filename.concat target_file (String.map (function '/'|'\\' -> '-' | c -> c) (smart_compose dir path)) ^ ".ast.ml" in
                Ocaml_expr_formatter.print_ocaml_expr_to_file noLocs target_file (Ocaml_expr_of_ast.of_list Ocaml_expr_of_ast.of_package packages)
              end else if path = filename && dir = Filename.dirname filename then
                Ocaml_expr_formatter.print_ocaml_expr_to_file noLocs target_file (Ocaml_expr_of_ast.of_list Ocaml_expr_of_ast.of_package packages)
            | None -> ()
          end;
          if path = filename then
            match !outputSExpressions with
              | Some target_file ->
                Printf.printf "Emitting s-expressions to %s\n" target_file;
                SExpressionEmitter.emit target_file packages
              | None             -> ()
        in
        verify ~emitter_callback:emitter_callback !stats options !prover filename !emitHighlightedSourceFiles !dumpPerLineStmtExecCounts !allowDeadCode !json !expected_json_result_file !apply_quick_fix !readOptionsFromSourceFile !breakpoint !focus !targetPath;
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
    let all_files_are_dotrs_files = ref true in
    let process_file filename =
      if !verbose = -1 then Printf.printf "\n%10.6fs: processing file %s\n" (Perf.time()) filename;
      all_files_are_dotrs_files := !all_files_are_dotrs_files && Filename.check_suffix filename ".rs";
      let result = process_file filename in
      if !verbose = -1 then Printf.printf "%10.6fs: done with file %s\n\n" (Perf.time()) filename;
      result
    in
    parse cla process_file usage_string;
    if not !compileOnly && not !all_files_are_dotrs_files then
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
