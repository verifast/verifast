module VF = Ast
open Lexer

exception CxxAnnParseException of VF.loc * string

let error (loc: VF.loc) (msg: string) =
  raise @@ CxxAnnParseException (loc, msg)

type raw_annotation = VF.loc0 * string

module Make (Args: Cxx_fe_sig.CXX_TRANSLATOR_ARGS) = struct

  module AnnParser = Parser.Parser (
    struct
      let language = VF.CLang
      let enforce_annotations = Args.enforce_annotations
      let data_model = Args.data_model_opt
    end
  )

  (* 
  Needed to keep track of defined header guards during oarsing of ghost #include directives.
  Gets updated by the sound preprocessor of VeriFast.
  *)
  let ghost_macros = Hashtbl.create 10

  let make_lexer_token_stream_core (((start_loc, _), text): raw_annotation) =
    let loc, ignore_eol, token_stream, _, _ = Lexer.make_lexer_core
      (Parser.common_keywords @ Parser.c_keywords) Parser.ghost_keywords start_loc (text ^ "\n") (* append a newline to be able to parse //@ annotations *)
      Args.report_range false false true Args.report_should_fail Lexer.default_file_options.annot_char 
    in
    loc, ignore_eol, token_stream

  let make_lexer_token_stream (ann: raw_annotation) =
    let loc, _, token_stream = make_lexer_token_stream_core ann in
    loc, token_stream

  let try_parse_no_pp ann_parser (current_loc, token_stream) =
    try
      ann_parser @@ Parser.noop_preprocessor token_stream
    with
      Stream.Error msg -> error (VF.Lexed (current_loc ())) ("Stream error during parsing: " ^ msg)
    | Stream.Failure -> error (VF.Lexed (current_loc ())) "Parse error in ghost code."

  let try_parse_ghost_no_pp (ann: raw_annotation) ann_parser =
    make_lexer_token_stream ann |> try_parse_no_pp ann_parser

  let try_parse_ann_list_no_pp (anns: raw_annotation list) ann_parser =
    let lexers = anns |> List.map make_lexer_token_stream |> ref in
    let current_loc () =
      let (c_loc, _) :: _ = !lexers in c_loc
    in
    let rec next_token () =
      let (_, stream) :: rest = !lexers in
      match Lexer.Stream.peek stream with
        Some (_, Lexer.Eof) | None ->
          if rest = [] then None
          else begin
            lexers := rest; 
            next_token ()
          end
      | Some _ as tk -> Lexer.Stream.junk stream; tk 
    in
    let token_stream = Stream.from (fun _ -> next_token ()) in
    try_parse_no_pp ann_parser (current_loc (), token_stream)

  let parse_end = function%parser
    | [ [%l () = Lexer.Stream.empty] ] -> ()
    | [ (_, Lexer.Eof) ] -> ()

  let parse_spec_clauses_opt (anns: raw_annotation list): (bool * (string * VF.type_expr list * (VF.loc * string) list) option * (VF.asn * VF.asn) option * bool) option =
    match anns with
    | [] -> None
    | _ -> 
      let ann_parser = function%parser
      | [ [%l s = AnnParser.parse_spec_clauses]; [%l () = parse_end] ] -> s in
      Some (try_parse_ann_list_no_pp anns ann_parser)

  let parse_func_contract (loc: VF.loc) (anns: raw_annotation list): (bool * (string * VF.type_expr list * (VF.loc * string) list) option * (VF.asn * VF.asn) option * bool) =
    let ng_callers_only, ft, pre_post, terminates = 
      match parse_spec_clauses_opt anns with
      | Some s -> s
      | None -> false, None, None, false
    in
    let pre_post = AnnParser.check_for_contract pre_post loc "Function declaration should have a contract." (fun contract -> contract) in
    ng_callers_only, ft, Some pre_post, terminates

  let parse_functype_contract (loc: VF.loc) (anns: raw_annotation list): VF.asn * VF.asn * bool =
    match parse_spec_clauses_opt anns with
    | Some (ng_callers_only, ft, pre_post, terminates) ->
      begin match ng_callers_only, ft, pre_post with
      | false, None, None -> raise Stream.Failure
      | false, None, Some (pre, post) -> pre, post, terminates
      | _ -> raise (Stream.Error "Incorrect kind, number, or order of specification clauses. Expected: requires clause, ensures clause, terminates clause (optional).")
      end
    | None ->
      AnnParser.check_for_contract None loc "Function type declaration should have contract." (fun (pre, post) -> pre, post, false)

  let parse_loop_spec (loc: VF.loc) (anns: raw_annotation list): VF.loop_spec option * VF.asn option =
    match anns with
    | [] -> None, None
    | _ -> let ann_parser = AnnParser.parse_loop_core0 loc in
      try_parse_ann_list_no_pp anns ann_parser

  let parse_decls (ann: raw_annotation): VF.decl list =
    let ann_parser = function%parser
    | [ [%l d = AnnParser.parse_decls]; [%l () = parse_end] ] -> d in
    try_parse_ghost_no_pp ann ann_parser

  let parse_stmt (ann: raw_annotation): VF.stmt =
    let ann_parser = function%parser
    | [ [%l stmt = AnnParser.parse_stmt]; [%l () = parse_end] ] -> stmt in
    try_parse_ghost_no_pp ann ann_parser

  let parse_functype_ghost_params (ann: raw_annotation): string list * (VF.type_expr * string) list =
    let ann_parser = function%parser
    | [ 
        (_, Kwd "/*@");
        [%l functiontype_type_params = Parser.opt AnnParser.parse_type_params_free];
        [%l functiontype_params = Parser.opt AnnParser.parse_paramlist];
        (_, Kwd "@*/");
        [%l () = parse_end]
      ] ->
        let none_to_empty_list = function None -> [] | Some x -> x in
        none_to_empty_list functiontype_type_params, none_to_empty_list functiontype_params
    | [ [%l () = parse_end] ] -> [], []
    in
    try_parse_ghost_no_pp ann ann_parser

  let parse_struct_members (struct_name: string) (ann: raw_annotation): Cxx_fe_sig.struct_member_decl list =
    let parse_mem = function%parser
    | [ 
        (l, Kwd "predicate"); 
        (_, Ident g); 
        [%l ps = AnnParser.parse_paramlist];
        [%l
        body = begin function%parser
        | [ (_, Kwd "="); [%l p = AnnParser.parse_asn] ] -> Some p
        | [ ] -> None
        end
        ];
        (_, Kwd ";") 
      ] -> 
      let pred = VF.InstancePredDecl (l, g, ps, body) in
      Cxx_fe_sig.CxxInstPredMem pred
    | [ 
        (l, Kwd "lemma"); 
        [%l t = AnnParser.parse_return_type];
        [%l VF.Func (l, k, tparams, t, g, ps, nonghost_callers_only, ft, co, terminates, None, false, []) = AnnParser.parse_func_rest (VF.Lemma (false, None)) t] 
      ] ->
      let ps = (VF.PtrTypeExpr (l, VF.StructTypeExpr (l, Some struct_name, None, [])), "this") :: ps in
      let lem = VF.Func (l, k, tparams, t, g, ps, nonghost_callers_only, ft, co, terminates, None, false, []) in
      Cxx_fe_sig.CxxDeclMem lem
    | [ 
        [%l
        binding = begin function%parser
        | [ (_, Kwd "static") ] -> VF.Static
        | [  ] -> VF.Instance
        end
        ];
        [%l t = AnnParser.parse_type]; (l, Ident x); (_, Kwd ";")
      ] ->
      let field = VF.Field (l, VF.Ghost, t, x, binding, VF.Public, false, None) in
      Cxx_fe_sig.CxxFieldMem field
    in
    let rec parse_mems = function%parser
    | [ (_, Kwd "@*/") ] -> []
    | [ parse_mem as mem; parse_mems as mems ] -> mem :: mems
    in
    let ann_parser = function%parser
    | [ (_, Kwd "/*@"); parse_mems as mems; [%l () = parse_end] ] -> mems
    in
    try_parse_ghost_no_pp ann ann_parser

  (*
    parse_include_directives
    [path]            path of the file that contains the annotation
    [ann]             annotation
    [active_headers]  used to check include cycles
    [included_files]  used to detect secondary includes
  *)
  let parse_include_directives (path: string) (ann: raw_annotation) (active_headers: string list ref) (included_files: string list ref) =
    (* create a lexer for the annotation that is given *)
    let make_virtual_file_lexer ann =
      make_lexer_token_stream_core ann
    in
    (* create a lexer for an #include directive *)
    let make_real_file_lexer path include_paths ~inGhostRange =
      let text = Lexer.readFile path in
      Lexer.make_lexer (Parser.common_keywords @ Parser.c_keywords) Parser.ghost_keywords path text Args.report_range ~inGhostRange Args.report_should_fail
    in
    let make_lexer p include_paths ~inGhostRange =
      if p = path then make_virtual_file_lexer ann (* lex the 'virtual' file that contains the given annotation *)
      else make_real_file_lexer p include_paths ~inGhostRange (* lex real file at path 'p' *)
    in
    let result = 
      let loc, token_stream = make_sound_preprocessor_core Args.report_macro_call make_lexer path Args.verbose Args.include_paths Args.data_model_opt Args.define_macros ghost_macros included_files in
      let parse_virtual_c_file = function%parser
      [
        [%l headers, header_names = Parser.parse_include_directives_core Args.verbose Args.enforce_annotations Args.data_model_opt active_headers];
        [%l ds = Parser.parse_decls VF.CLang Args.data_model_opt Args.enforce_annotations ~inGhostHeader:false];
        [%l () = parse_end]
      ] -> 
        match ds with
        | [] -> headers, header_names
        | _ -> error (loc ()) "Expected only ghost #include directives."
      in
      try
        parse_virtual_c_file token_stream
      with
      | Stream.Error msg -> error (loc ()) ("Stream error during parsing of include directives: " ^ msg)
      | Stream.Failure -> error (loc ()) "Parse error during parsing of include directives."
    in
    result

end