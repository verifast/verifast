module type VF_MIR_ANNOT_PARSER_ARGS = sig
  val data_model_opt : Ast.data_model option
  val report_should_fail : string -> Ast.loc0 -> unit
  val report_range : Lexer.range_kind -> Ast.loc0 -> unit
end

module Make (Args : VF_MIR_ANNOT_PARSER_ARGS) = struct
  type src_pos = Ast.srcpos
  type src_span = Ast.loc0

  let token_stream_from_annot ((start_pos, text) : src_pos * string) =
    let get_current_loc, _, token_stream, _, _ =
      Lexer.make_lexer_core
        Parser.rust_keywords
        Parser.rust_ghost_keywords start_pos
        (* append a newline to be able to parse //@ annotations *)
        (text ^ "\n")
        Args.report_range (* inComment *) false (* inGhostRange *) false
        (* exceptionOnError *) true Args.report_should_fail
        Lexer.default_file_options.annot_char
    in
    (get_current_loc, token_stream)

  let token_stream_from_annots (annots : (src_pos * string) list) =
    let tk_strs_ref = annots |> List.map token_stream_from_annot |> ref in
    let get_current_loc () =
      let get_current_loc, _ = List.hd !tk_strs_ref in
      get_current_loc ()
    in
    let rec next_tk n =
      match !tk_strs_ref with
      | [] -> None
      | (_, current_tk_str) :: rest_strs -> (
          match Lexer.Stream.peek current_tk_str with
          | None | Some (_, Lexer.Eof) when rest_strs <> [] ->
              tk_strs_ref := rest_strs;
              next_tk n
          | Some _ as some_tk ->
              Lexer.Stream.junk current_tk_str;
              some_tk)
    in
    get_current_loc, Lexer.Stream.from next_tk

  let parse_fully parser_ stream =
    let v = parser_ stream in
    match Lexer.Stream.peek stream with
      None | Some (_, Lexer.Eof) -> v
    | Some (l, _) -> raise (Lexer.ParseException (l, "Parse error"))

  let parse_func_contract (func_loc : Ast.loc) (annots : (src_pos * string) list) =
    let loc, tk_stream = token_stream_from_annots annots in
    let tk_stream = Parser.noop_preprocessor tk_stream in
    try
      parse_fully (Rust_parser.parse_spec_clauses func_loc Regular) tk_stream
    with
      Lexer.Stream.Error msg -> raise (Lexer.ParseException (Lexed (loc()), msg))
    | Lexer.Stream.Failure -> raise (Lexer.ParseException (Lexed (loc()), "Parse error"))

  let parse_ghost_stmt (annot : src_pos * string) =
    let loc, ts = token_stream_from_annot annot in
    try
      ts |> Parser.noop_preprocessor |> Rust_parser.parse_stmt
    with
      Lexer.Stream.Error msg -> raise (Lexer.ParseException (Lexed (loc()), msg))
    | Lexer.Stream.Failure -> raise (Lexer.ParseException (Lexed (loc()), "Parse error"))
  (* Todo @Nima: This can parse all statements. Maybe we should rename this module to just a parser *)

  let parse_ghost_decl_batch (annot : src_pos * string) =
    let loc, ts = token_stream_from_annot annot in
    try
      ts |> Parser.noop_preprocessor |> parse_fully Rust_parser.parse_ghost_decl_block
    with
      Lexer.Stream.Error msg -> raise (Lexer.ParseException (Lexed (loc()), msg))
    | Lexer.Stream.Failure -> raise (Lexer.ParseException (Lexed (loc()), "Parse error"))
      
  let parse_ghost_use_decl_or_decl_batch (annot : src_pos * string) =
    let loc, ts = token_stream_from_annot annot in
    try
      ts |> Parser.noop_preprocessor |> parse_fully Rust_parser.parse_ghost_use_decl_or_decl_batch
    with
      Lexer.Stream.Error msg -> raise (Lexer.ParseException (Lexed (loc()), msg))
    | Lexer.Stream.Failure -> raise (Lexer.ParseException (Lexed (loc()), "Parse error"))
      
  let parse_ghost_generic_arg_list (annot : src_pos * string) =
    let loc, ts = token_stream_from_annot annot in
    try
      ts |> Parser.noop_preprocessor |> parse_fully Rust_parser.parse_ghost_generic_arg_list
    with
      Lexer.Stream.Error msg -> raise (Lexer.ParseException (Lexed (loc()), msg))
    | Lexer.Stream.Failure -> raise (Lexer.ParseException (Lexed (loc()), "Parse error"))
        
  let rec parse_rsspec_file path =
    let pos = (path, 1, 1) in
    let text = Lexer.readFile path in
    let loc, ts = token_stream_from_annot (pos, text) in
    let parse_rsspec_file l relpath =
      let abs_path = Util.concat (Filename.dirname path) relpath in
      if not (Sys.file_exists abs_path) then
        raise (Lexer.ParseException (l, "No such file"));
      parse_rsspec_file abs_path
    in
    try
      ts |> Parser.noop_preprocessor |> parse_fully (Rust_parser.parse_decls parse_rsspec_file)
    with
      Lexer.Stream.Error msg -> raise (Lexer.ParseException (Lexed (loc()), msg))
    | Lexer.Stream.Failure -> raise (Lexer.ParseException (Lexed (loc()), "Parse error"))

end
