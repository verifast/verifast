module type VF_MIR_ANNOT_PARSER_ARGS = sig
  val data_model_opt : Ast.data_model option

  val report_should_fail : string -> Ast.loc0 -> unit

  val report_range : Lexer.range_kind -> Ast.loc0 -> unit
end

module Make (Args : VF_MIR_ANNOT_PARSER_ARGS) = struct
  module VfParser = Parser.Parser (struct
    let language = Ast.CLang

    (* If it is false the parser adds "requires false" and "ensures true" as the contract to functions without one.
       It does not matter here because we are just parsing annotations *)
    let enforce_annotations = true

    let data_model = Args.data_model_opt
  end)

  type src_pos = Ast.srcpos

  type src_span = Ast.loc0

  let token_stream_from_annot ((start_pos, text) : src_pos * string) =
    let get_current_loc, _, token_stream, _, _ =
      Lexer.make_lexer_core
        (Parser.common_keywords @ Parser.c_keywords)
        Parser.ghost_keywords start_pos
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
          | None | Some (_, Lexer.Eof) ->
              tk_strs_ref := rest_strs;
              next_tk n
          | Some _ as some_tk ->
              Lexer.Stream.junk current_tk_str;
              some_tk)
    in
    Lexer.Stream.from next_tk

  let parse_func_contract (annots : string list) =
    let dpos = Ast.dummy_srcpos in
    let annots = List.map (fun annot -> (dpos, annot)) annots in
    let tk_stream = token_stream_from_annots annots in
    let tk_stream = Parser.noop_preprocessor tk_stream in
    VfParser.parse_spec_clauses tk_stream
end
