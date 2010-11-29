val emit : ?margin:int -> string -> Verifast.package list -> unit


(*
  Made public for testing purposes
*)
val sexpr_of_decl : Verifast.decl -> SExpressions.sexpression

val sexpr_of_package : Verifast.package -> SExpressions.sexpression
