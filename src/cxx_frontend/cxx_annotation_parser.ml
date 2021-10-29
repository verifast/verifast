module VF = Ast
open Lexer

exception CxxAnnParseException of VF.loc * string

let error (loc: VF.loc) (msg: string) =
  raise @@ CxxAnnParseException (loc, msg)

type raw_annotation = VF.loc0 * string

module Make (Args: Cxx_fe_sig.CXX_TRANSLATOR_ARGS) = struct

  open Args

  module AnnParser = Parser.Parser (
    struct
      let language = VF.CLang
      let enforce_annotations = enforce_annotations
      let data_model = data_model_opt
    end
  )

  let make_lexer_token_stream (((start_loc, _), text): raw_annotation) =
    let loc, _, token_stream, _, _ = Lexer.make_lexer_core
      (Parser.common_keywords @ Parser.c_keywords) Parser.ghost_keywords start_loc (text ^ "\n") (* append a newline to be able to parse //@ annotations *)
      report_range false false true report_should_fail Lexer.default_file_options.annot_char 
    in
    loc, token_stream

  let try_parse ann_parser (current_loc, token_stream) =
    try
      ann_parser @@ Parser.noop_preprocessor token_stream
    with
      Stream.Error msg -> error (VF.Lexed (current_loc ())) ("Stream error during parsing: " ^ msg)
    | Stream.Failure -> error (VF.Lexed (current_loc ())) "Parse error in ghost code."

  let try_parse_ghost (ann: raw_annotation) ann_parser =
    try_parse ann_parser @@ make_lexer_token_stream ann

  let parse_ann_list (anns: raw_annotation list) ann_parser =
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
    try_parse ann_parser (current_loc (), token_stream)

  let parse_end = parser
    | [< _ = Lexer.Stream.empty >] -> ()
    | [< '(_, Lexer.Eof) >] -> ()

  let parse_spec_clauses (anns: raw_annotation list): bool * (string * VF.type_expr list * (VF.loc * string) list) option * (VF.asn * VF.asn) option * bool =
    match anns with
      [] -> false, None, None, false
    | _ -> let ann_parser = parser
        [< s = AnnParser.parse_spec_clauses; parse_end >] -> s in
        parse_ann_list anns ann_parser

  let parse_loop_spec (loc: VF.loc) (anns: raw_annotation list): VF.loop_spec option * VF.asn option =
    match anns with
      [] -> None, None
    | _ -> let ann_parser = AnnParser.parse_loop_core0 loc in
      parse_ann_list anns ann_parser

  let parse_decls (ann: raw_annotation): VF.decl list =
    let ann_parser = parser
      [< d = AnnParser.parse_decls; parse_end >] -> d in
    try_parse_ghost ann ann_parser

  let parse_stmt (ann: raw_annotation): VF.stmt =
    let ann_parser = parser
      [< stmt = AnnParser.parse_stmt; parse_end >] -> stmt in
    try_parse_ghost ann ann_parser

end