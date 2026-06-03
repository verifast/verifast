module R = Reader.R
module S = R.Stmt

module type Translator = sig
  val translate : R.Node.t -> Ast.stmt
  val expect_compound_stmt : R.Node.t -> Ast.stmt list * Ast.loc
end

module Make (Node_translator : Node_translator.Translator) : Translator = struct
  module Expr_translator = Expr_translator.Make (Node_translator)
  module Var_translator = Var_translator.Make (Node_translator)
  module AP = Node_translator.Annotation_parser

  (* Desugar GCC statement expressions ({ stmts; expr; }). A statement
     expression's leading statements are hoisted out before the enclosing
     statement, and the expression is replaced by the value of its final
     expression statement. The hoisted statements' declarations harmlessly
     remain in the enclosing scope (sound for verification: it only adds names).
     Only the common statement-level positions are handled here (expression
     statement, initializer, assignment RHS, return, if-condition); a statement
     expression nested more deeply in an expression is left in place and
     rejected with a clean error by the verifier. The recursion descends into
     nested blocks, so desugaring a function body handles all of it. *)
  let rec desugar_stmts (ss : Ast.stmt list) : Ast.stmt list =
    List.concat_map desugar_stmt ss
  and desugar_stmt (s : Ast.stmt) : Ast.stmt list =
    let open Ast in
    (* Desugar an inner block and split off its final value expression. *)
    let split ss =
      match List.rev (desugar_stmts ss) with
      | ExprStmt efinal :: rev_init -> Some (List.rev rev_init, efinal)
      | _ -> None
    in
    match s with
    | ExprStmt (StmtExpr (_, ss)) ->
        (* value discarded: just inline the block's statements *)
        desugar_stmts ss
    | DeclStmt (l, [ (ld, ty, x, Some (StmtExpr (_, ss)), addr) ]) -> (
        match split ss with
        | Some (init, efinal) ->
            init @ [ DeclStmt (l, [ (ld, ty, x, Some efinal, addr) ]) ]
        | None -> [ s ])
    | ReturnStmt (l, Some (StmtExpr (_, ss))) -> (
        match split ss with
        | Some (init, efinal) -> init @ [ ReturnStmt (l, Some efinal) ]
        | None -> [ s ])
    | ExprStmt (AssignExpr (la, lhs, k, StmtExpr (_, ss))) -> (
        match split ss with
        | Some (init, efinal) ->
            init @ [ ExprStmt (AssignExpr (la, lhs, k, efinal)) ]
        | None -> [ s ])
    | IfStmt (l, StmtExpr (_, ss), t, e) -> (
        match split ss with
        | Some (init, efinal) ->
            init @ [ IfStmt (l, efinal, desugar_stmts t, desugar_stmts e) ]
        | None -> [ IfStmt (l, s_cond_unchanged ss l, desugar_stmts t, desugar_stmts e) ])
    | IfStmt (l, c, t, e) -> [ IfStmt (l, c, desugar_stmts t, desugar_stmts e) ]
    | BlockStmt (l, ds, ss, cb, lf) -> [ BlockStmt (l, ds, desugar_stmts ss, cb, lf) ]
    | WhileStmt (l, c, sp, d, body, fin) ->
        [ WhileStmt (l, c, sp, d, desugar_stmts body, desugar_stmts fin) ]
    | SwitchStmt (l, c, clauses) ->
        let dc = function
          | SwitchStmtClause (lc, e, ss) -> SwitchStmtClause (lc, e, desugar_stmts ss)
          | SwitchStmtDefaultClause (lc, ss) ->
              SwitchStmtDefaultClause (lc, desugar_stmts ss)
        in
        [ SwitchStmt (l, c, List.map dc clauses) ]
    | _ -> [ s ]
  and s_cond_unchanged ss l = Ast.StmtExpr (l, ss)

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
    | For f -> transl_for_stmt loc f
    | Break -> transl_break_stmt loc
    | Continue -> transl_continue_stmt loc
    | Compound c -> transl_compound_stmt loc c
    | Switch s -> transl_switch_stmt loc s
    | Asm a -> transl_asm_stmt loc a
    | Undefined _ -> failwith "Undefined statement."
    | _ -> Error.error loc "Unsupported statement."

  and translate stmt_node =
    Node_translator.map ~f:translate_decomposed stmt_node

  and transl_stmt_as_list stmt_node =
    Node_translator.map
      ~f:(fun _ d ->
        match S.get d with
        | Compound c -> S.Compound.stmts_get c |> Capnp_util.arr_map translate
        | _ -> [ translate stmt_node ])
      stmt_node

  and expect_compound_stmt stmt_node =
    Node_translator.map_expect_fail
      ~f:(fun l s ->
        match S.get s with
        | Compound c ->
            let r_brace_loc =
              S.Compound.r_brace_get c |> Node_translator.translate_loc
            in
            let stmts =
              S.Compound.stmts_get c |> Capnp_util.arr_map translate
              |> desugar_stmts
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
          let ty, name, init_opt = Var_translator.translate v in
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

  and transl_compound_stmt (loc : Ast.loc) (c : S.Compound.t) : Ast.stmt =
    let open S.Compound in
    let stmts = stmts_get c |> Capnp_util.arr_map translate |> desugar_stmts in
    Ast.BlockStmt
      (loc, [], stmts, Node_translator.translate_loc @@ r_brace_get c, ref [])

  and transl_expr_stmt (e : R.Node.t) : Ast.stmt =
    Ast.ExprStmt (Expr_translator.translate e)

  (* Inline asm: modelled by havocing its output operands. We emit a call to the
     recognized intrinsic __vf_asm_havoc(out0, out1, ...), which the verifier
     handles by assigning each output lvalue a fresh, unconstrained value. An asm
     with no outputs yields a no-op call (a pure barrier). See verify_stmt. *)
  and transl_asm_stmt (loc : Ast.loc) (a : S.Asm.t) : Ast.stmt =
    let open S.Asm in
    let outputs = outputs_get a |> Capnp_util.arr_map Expr_translator.translate in
    let args = List.map (fun e -> Ast.LitPat e) outputs in
    Ast.ExprStmt (Ast.CallExpr (loc, "__vf_asm_havoc", [], [], args, Ast.Static))

  and transl_return_stmt (loc : Ast.loc) (r : S.Return.t) : Ast.stmt =
    let open S.Return in
    let expr_opt =
      if has_expr r then Some (Expr_translator.translate @@ expr_get r)
      else None
    in
    Ast.ReturnStmt (loc, expr_opt)

  and transl_if_stmt (loc : Ast.loc) (i : S.If.t) : Ast.stmt =
    let open S.If in
    let cond = Expr_translator.translate @@ cond_get i in
    let th = [ then_get i |> translate ] in
    let el =
      if has_else i then
        let stmts = [ else_get i |> translate ] in
        stmts
      else []
    in
    Ast.IfStmt (loc, cond, th, el)

  and transl_null_stmt (loc : Ast.loc) : Ast.stmt = Ast.NoopStmt loc

  and transl_while_like (loc : Ast.loc) (w : S.While.t) :
      Ast.loc * Ast.expr * Ast.stmt list * Ast.loop_spec option * Ast.asn option
      =
    let open S.While in
    let while_loc = Node_translator.translate_loc @@ while_loc_get w in
    let cond = Expr_translator.translate @@ cond_get w in
    let body = [ translate @@ body_get w ] in
    let spec, decr =
      spec_get w
      |> Capnp_util.arr_map Node_translator.map_annotation
      |> AP.parse_loop_spec loc
    in
    (while_loc, cond, body, spec, decr)

  and transl_while_stmt (loc : Ast.loc) (w : S.While.t) : Ast.stmt =
    let _, cond, body, spec, decr = transl_while_like loc w in
    Ast.WhileStmt (loc, cond, spec, decr, body, [])

  and transl_do_while_stmt (loc : Ast.loc) (w : S.While.t) : Ast.stmt =
    let while_loc, cond, body, spec, decr = transl_while_like loc w in
    Ast.WhileStmt
      ( loc,
        Ast.True loc,
        spec,
        decr,
        body,
        [ Ast.IfStmt (while_loc, cond, [], [ Ast.Break while_loc ]) ] )

  and transl_for_stmt (loc : Ast.loc) (f : S.For.t) : Ast.stmt =
    let open S.For in
    let _, cond, body, spec, decr =
      transl_while_like loc (inside_while_get f)
    in
    let forStmt =
      Ast.WhileStmt
        ( loc,
          cond,
          spec,
          decr,
          body,
          [ Ast.ExprStmt (Expr_translator.translate @@ iteration_get f) ] )
    in
    Ast.BlockStmt (loc, [], [ translate @@ init_get f; forStmt ], loc, ref [])

  and transl_break_stmt (loc : Ast.loc) : Ast.stmt = Ast.Break loc
  and transl_continue_stmt (loc : Ast.loc) : Ast.stmt = Ast.Continue loc

  and transl_switch_stmt (loc : Ast.loc) (s : S.Switch.t) : Ast.stmt =
    let open S.Switch in
    let cond = Expr_translator.translate @@ cond_get s in
    let map_case case =
      case
      |> Node_translator.map_expect_fail ~f:(fun l c ->
             match S.get c with
             | S.Case c ->
                 let lhs = Expr_translator.translate @@ S.Case.lhs_get c in
                 let stmts =
                   if S.Case.has_stmts c then
                     S.Case.stmts_get c |> Capnp_util.arr_map translate
                   else []
                 in
                 Some (Ast.SwitchStmtClause (l, lhs, stmts))
             | S.DefCase c ->
                 let stmts =
                   if S.DefCase.has_stmts c then
                     S.DefCase.stmts_get c |> Capnp_util.arr_map translate
                   else []
                 in
                 Some (Ast.SwitchStmtDefaultClause (l, stmts))
             | _ -> None)
    in
    let cases = cases_get s |> Capnp_util.arr_map map_case in
    Ast.SwitchStmt (loc, cond, cases)

  (* Install the forward reference so Expr_translator can translate the
     sub-statements of a GCC statement expression. *)
  let () = Node_translator.translate_stmt_hook := translate
end
