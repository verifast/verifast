type header_type = Ast.loc * (Lexer.include_kind * string * string) * string list * Ast.package list

module type Cxx_Ast_Translator = sig
  val parse_cxx_file : unit -> header_type list * Ast.package list
  (**
    [parse_cxx_file path] parses the given C++ file and produces a VeriFast package.
  *)
end

type struct_member_decl =
  | CxxFieldMem of Ast.field
  | CxxInstPredMem of Ast.instance_pred_decl
  | CxxDeclMem of Ast.decl

module type CXX_TRANSLATOR_ARGS = sig
  val data_model_opt: Ast.data_model option
  val enforce_annotations: bool
  val report_should_fail: string -> Ast.loc0 -> unit
  val report_range: Lexer.range_kind -> Ast.loc0 -> unit
  val dialect_opt: Ast.dialect option
  val report_macro_call: Ast.loc0 -> Ast.loc0 -> unit
  val path: string
  val verbose: int
  val include_paths: string list
  val define_macros: string list
end