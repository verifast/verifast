val unsupported_exception : bool ref

val emit : ?margin:int -> string -> Ast.package list -> unit

(*
  Made public for testing purposes
*)
val sexpr_of_type_ : Ast.type_ -> SExpressions.sexpression

val sexpr_of_type_expr : Ast.type_expr -> SExpressions.sexpression

val sexpr_of_decl : Ast.decl -> SExpressions.sexpression

val sexpr_of_package : Ast.package -> SExpressions.sexpression

val sexpr_of_expr : Ast.expr -> SExpressions.sexpression

val sexpr_of_func_kind : Ast.func_kind -> SExpressions.sexpression

val sexpr_of_ident_scope : Ast.ident_scope -> SExpressions.sexpression

val sexpr_of_operator : Ast.operator -> SExpressions.sexpression

val sexpr_of_constant_value : Ast.constant_value -> SExpressions.sexpression

val sexpr_of_method_binding : Ast.method_binding -> SExpressions.sexpression

val sexpr_of_pred_name : Ast.pred_name -> SExpressions.sexpression

val sexpr_of_pred : Ast.asn -> SExpressions.sexpression

val sexpr_of_stmt : Ast.stmt -> SExpressions.sexpression

val sexpr_of_import : Ast.import -> SExpressions.sexpression
