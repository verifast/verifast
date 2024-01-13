module R = Reader.R
module V = R.Decl.Var

module type Translator = sig
  val translate : V.t -> Ast.type_expr * string * Ast.expr option
end

module Make (Node_translator : Node_translator.Translator) : Translator = struct
  module Type_translator = Type_translator.Make (Node_translator)
  module Expr_translator = Expr_translator.Make (Node_translator)

  let transl_var_init (i : V.VarInit.t) : Ast.expr =
    let open V.VarInit in
    let init_expr = init_get i |> Expr_translator.translate in
    match style_get i with
    | V.InitStyle.ListInit ->
        Error.error (Ast.expr_loc init_expr)
          "List initialization is not supported yet."
    | _ -> init_expr

  let translate var =
    let open V in
    let name = name_get var in
    let init_opt =
      if has_init var then Some (init_get var |> transl_var_init) else None
    in
    let ty = Type_translator.translate @@ type_get var in
    (ty, name, init_opt)
end
