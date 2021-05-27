module VF = Ast

module type Cxx_Ast_Translator = sig
  val parse_cxx_file : string -> VF.package
  (**
    [parse_cxx_file path] parses the given C++ file and produces a VeriFast package.
  *)
end

module type CXX_TRANSLATOR_ARGS = sig
  val data_model_opt: VF.data_model option
  val enforce_annotations: bool
  val report_should_fail: string -> VF.loc0 -> unit
  val report_range: Lexer.range_kind -> VF.loc0 -> unit
end