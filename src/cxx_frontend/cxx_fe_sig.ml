module VF = Ast

type header_type = VF.loc * (Lexer.include_kind * string * string) * string list * VF.package list

module type Cxx_Ast_Translator = sig
  val parse_cxx_file : string -> header_type list * VF.package list
  (**
    [parse_cxx_file path] parses the given C++ file and produces a VeriFast package.
  *)
end

type struct_member_decl =
  | CxxFieldMem of VF.field
  | CxxInstPredMem of VF.instance_pred_decl
  | CxxDeclMem of VF.decl

module type CXX_TRANSLATOR_ARGS = sig
  val data_model_opt: VF.data_model option
  val enforce_annotations: bool
  val report_should_fail: string -> VF.loc0 -> unit
  val report_range: Lexer.range_kind -> VF.loc0 -> unit
end