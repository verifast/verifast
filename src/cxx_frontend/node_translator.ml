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

  let translate_loc loc =
    let l_start =
      if L.has_start loc then L.start_get loc |> transl_srcpos
      else Ast.dummy_srcpos
    in
    let l_end =
      if L.has_end loc then L.end_get loc |> transl_srcpos else Ast.dummy_srcpos
    in
    Ast.Lexed (l_start, l_end)

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
