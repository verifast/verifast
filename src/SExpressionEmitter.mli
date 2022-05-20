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
