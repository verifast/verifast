module VF = Ast

exception CxxAstTranslException of VF.loc * string

module Make(Args: Cxx_fe_sig.CXX_TRANSLATOR_ARGS) : Cxx_fe_sig.Cxx_Ast_Translator = struct
  let parse_cxx_file path =
    let p = path, 1, 1 in
    raise @@ CxxAstTranslException (VF.Lexed (p, p), "C++ verification is not supported on this platform.")
end