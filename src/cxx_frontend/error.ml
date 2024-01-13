let union_no_init_err kind =
  failwith @@ "Node of kind '" ^ kind ^ "' has no initialized union body (default case has been implicitly selected). Make sure that you serialize a description for all nodes in the C++ AST exporter tool."

exception CxxAstTranslException of Ast.loc * string

let error (loc: Ast.loc) (msg: string): 'a =
  raise @@ CxxAstTranslException (loc, msg)