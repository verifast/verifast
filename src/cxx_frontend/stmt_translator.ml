module R = Reader.R
module S = R.Stmt

module type Translator = sig
  val translate : R.Node.t -> Ast.stmt
  val expect_compund_stmt : R.Node.t -> Ast.stmt list * Ast.loc
end

module Make (Node_translator : Node_translator.Translator) : Translator = struct
  module Expr_translator = Expr_translator.Make (Node_translator)
  module Misc_translator = Var_translator.Make (Node_translator)
  module AP = Node_translator.Annotation_parser

  let rec translate_decomposed loc stmt_desc =
    match S.get stmt_desc with
    | UnionNotInitialized -> Error.union_no_init_err "statement"
    | Decl decls -> transl_decl_stmt loc decls
    | Ann a -> transl_stmt_ann loc a
    | Expr e -> transl_expr_stmt e
    | Return r -> transl_return_stmt loc r
    | If i -> transl_if_stmt loc i
    | Null -> transl_null_stmt loc
    | While w -> transl_while_stmt loc w
    | DoWhile w -> transl_do_while_stmt loc w
    | Break -> transl_break_stmt loc
    | Compound c -> transl_compound_stmt loc c
    (* TODO: check if this is translated correctly *)
    (* | Switch s            -> transl_switch_stmt loc s *)
    | Undefined _ -> failwith "Undefined statement."
    | _ -> Error.error loc "Unsupported statement."

  and translate stmt_node =
    Node_translator.map ~f:translate_decomposed stmt_node

  and expect_compund_stmt stmt_node =
    Node_translator.map_expect_fail
      ~f:(fun l s ->
        match S.get s with
        | Compound c ->
            let r_brace_loc =
              S.Compound.r_brace_get c |> Node_translator.translate_loc
            in
            let stmts =
              S.Compound.stmts_get c |> Capnp_util.arr_map translate
            in
            Some (stmts, r_brace_loc)
        | _ -> None)
      stmt_node

  (* TODO: redeclaration of function! *)
  and transl_decl_stmt (loc : Ast.loc) (decls : R.Node.t Capnp_util.capnp_arr) :
      Ast.stmt =
    let expect_var loc desc =
      match R.Decl.get desc with
      | R.Decl.Var v ->
          let ty, name, init_opt = Misc_translator.translate v in
          Some (loc, Some ty, name, init_opt, (ref false, ref None))
      | _ -> None
    in
    Ast.DeclStmt
      ( loc,
        decls
        |> Capnp_util.arr_map (Node_translator.map_expect_fail ~f:expect_var) )

  and transl_stmt_ann (loc : Ast.loc) (text : string) : Ast.stmt =
    let (Ast.Lexed l) = loc in
    AP.parse_stmt (l, text)

  and transl_compound_stmt (loc : Ast.loc) (c : R.Stmt.Compound.t) : Ast.stmt =
    let open R.Stmt.Compound in
    let stmts = stmts_get c |> Capnp_util.arr_map translate in
    Ast.BlockStmt
      (loc, [], stmts, Node_translator.translate_loc @@ r_brace_get c, ref [])

  and transl_expr_stmt (e : R.Node.t) : Ast.stmt =
    Ast.ExprStmt (Expr_translator.translate e)

  and transl_return_stmt (loc : Ast.loc) (r : R.Stmt.Return.t) : Ast.stmt =
    let open R.Stmt.Return in
    let expr_opt =
      if has_expr r then Some (Expr_translator.translate @@ expr_get r)
      else None
    in
    Ast.ReturnStmt (loc, expr_opt)

  and transl_if_stmt (loc : Ast.loc) (i : R.Stmt.If.t) : Ast.stmt =
    let open R.Stmt.If in
    let cond = Expr_translator.translate @@ cond_get i in
    let th =
      let stmts, _ = expect_compund_stmt @@ then_get i in
      stmts
    in
    let el =
      if has_else i then
        let stmts, _ = expect_compund_stmt @@ else_get i in
        stmts
      else []
    in
    Ast.IfStmt (loc, cond, th, el)

  and transl_null_stmt (loc : Ast.loc) : Ast.stmt = Ast.NoopStmt loc

  and transl_while_like (loc : Ast.loc) (w : R.Stmt.While.t) :
      Ast.loc * Ast.expr * Ast.stmt list * Ast.loop_spec option * Ast.asn option
      =
    let open R.Stmt.While in
    let while_loc = Node_translator.translate_loc @@ while_loc_get w in
    let cond = Expr_translator.translate @@ cond_get w in
    let body = [ translate @@ body_get w ] in
    let spec, decr =
      spec_get w
      |> Capnp_util.arr_map Node_translator.map_annotation
      |> AP.parse_loop_spec loc
    in
    (while_loc, cond, body, spec, decr)

  and transl_while_stmt (loc : Ast.loc) (w : R.Stmt.While.t) : Ast.stmt =
    let _, cond, body, spec, decr = transl_while_like loc w in
    Ast.WhileStmt (loc, cond, spec, decr, body, [])

  and transl_do_while_stmt (loc : Ast.loc) (w : R.Stmt.While.t) : Ast.stmt =
    let while_loc, cond, body, spec, decr = transl_while_like loc w in
    Ast.WhileStmt
      ( loc,
        Ast.True loc,
        spec,
        decr,
        body,
        [ Ast.IfStmt (while_loc, cond, [], [ Ast.Break while_loc ]) ] )

  and transl_break_stmt (loc : Ast.loc) : Ast.stmt = Ast.Break loc

  and transl_switch_stmt (loc : Ast.loc) (s : R.Stmt.Switch.t) : Ast.stmt =
    let open R.Stmt.Switch in
    let cond = Expr_translator.translate @@ cond_get s in
    let map_case case =
      case
      |> Node_translator.map_expect_fail ~f:(fun l c ->
             match R.Stmt.get c with
             | R.Stmt.Case c ->
                 let lhs = Expr_translator.translate @@ R.Stmt.Case.lhs_get c in
                 let stmts, _ =
                   if R.Stmt.Case.has_stmt c then
                     expect_compund_stmt @@ R.Stmt.Case.stmt_get c
                   else ([], Ast.dummy_loc)
                 in
                 Some (Ast.SwitchStmtClause (l, lhs, stmts))
             | R.Stmt.DefCase c ->
                 let stmts, _ =
                   if R.Stmt.DefCase.has_stmt c then
                     expect_compund_stmt @@ R.Stmt.DefCase.stmt_get c
                   else ([], Ast.dummy_loc)
                 in
                 Some (Ast.SwitchStmtDefaultClause (l, stmts))
             | _ -> None)
    in
    let cases = cases_get s |> Capnp_util.arr_map map_case in
    Ast.SwitchStmt (loc, cond, cases)
end
