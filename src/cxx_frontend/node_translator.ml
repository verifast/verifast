module R = Reader.R
module N = R.Node
module L = R.Loc
module S = L.SrcPos

type 'a reader = 'a Reader.Stubs.reader_t

module type Translator = sig
  val translate_loc : L.t -> Ast.loc
  val decompose : N.t -> Ast.loc * 'a reader
  val map_expect_fail : f:(Ast.loc -> 'a reader -> 'b option) -> N.t -> 'b
  val map : f:(Ast.loc -> 'a reader -> 'b) -> N.t -> 'b
  val map_annotation : R.Clause.t -> Ast.loc0 * string

  module Annotation_parser : Annotation_parser.Parser
end

module Make (Args : sig
  include Sig.CXX_TRANSLATOR_ARGS

  val path_of_int : int -> string
end) : Translator = struct
  module Annotation_parser = Annotation_parser.Make (Args)

  let transl_srcpos srcpos =
    let l = S.l_get srcpos in
    let c = S.c_get srcpos in
    let fd = S.fd_get srcpos in
    let file_name = Args.path_of_int fd in
    (file_name, l, c)

  let rec translate_loc loc =
    match L.get loc with
    | UnionNotInitialized -> Error.union_no_init_err "location"
    | Lexed l ->
        let l_start =
          if L.Lexed.has_start l then L.Lexed.start_get l |> transl_srcpos
          else Ast.dummy_srcpos
        in
        let l_end =
          if L.Lexed.has_end l then L.Lexed.end_get l |> transl_srcpos
          else Ast.dummy_srcpos
        in
        Ast.Lexed (l_start, l_end)
    | MacroExp l ->
        let l_call_site =
          if L.MacroExp.has_call_site l then
            L.MacroExp.call_site_get l |> translate_loc
          else Ast.dummy_loc
        in
        let l_body_token =
          if L.MacroExp.has_body_token l then
            L.MacroExp.body_token_get l |> translate_loc
          else Ast.dummy_loc
        in
        Ast.MacroExpansion (l_call_site, l_body_token)
    | MacroParamExp l ->
        let l_param =
          if L.MacroParamExp.has_param l then
            L.MacroParamExp.param_get l |> translate_loc
          else Ast.dummy_loc
        in
        let l_arg_token =
          if L.MacroParamExp.has_arg_token l then
            L.MacroParamExp.arg_token_get l |> translate_loc
          else Ast.dummy_loc
        in
        Ast.MacroParamExpansion (l_param, l_arg_token)

  let map_annotation ann =
    let open R.Clause in
    let (Ast.Lexed a_loc) = loc_get ann |> translate_loc in
    let a_text = text_get ann in
    (a_loc, a_text)

  let decompose node =
    let loc =
      if N.has_loc node then N.loc_get node |> translate_loc else Ast.dummy_loc
    in
    let desc = N.desc_get node in
    (loc, R.of_pointer desc)

  let map_expect_fail ~f node =
    let loc, ptr = decompose node in
    match f loc ptr with
    | None -> failwith "Actual did not match expected."
    | Some result -> result

  let map ~f node =
    let loc, ptr = decompose node in
    f loc ptr
end
