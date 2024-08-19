module type RUST_FE_ARGS =
  sig
    val data_model_opt : Ast.data_model option
    val report_should_fail : string -> Ast.loc0 -> unit
    val report_range : Lexer.range_kind -> Ast.loc0 -> unit
    val report_macro_call : Ast.loc0 -> Ast.loc0 -> unit
    val verbose_flags : string list
  end
module Make :
  functor (_ : RUST_FE_ARGS) ->
    sig
      exception RustFrontend of string
      val parse_rs_file :
        string list ->
        string list ->
        string ->
        (Ast.loc * (Lexer.include_kind * string * string) * string list *
         Ast.package list)
        list * Ast.package list * Verifast0.debug_info option
    end
