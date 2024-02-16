module LocAux = Src_loc_aux
open Lexer
open Ast
open Parser
open Big_int

let is_expr_with_block = function
  IfExpr (_, _, _, _) -> true
| SwitchExpr (_, _, _, _) -> true
| _ -> false

let rec parse_simple_path_rest l x = function%parser
  [ (_, Kwd "::"); (ll, Ident xx);
  [%let l, x = parse_simple_path_rest (Lexed(Result.get_ok @@ LocAux.cover_loc0 (lexed_loc l) (lexed_loc ll))) (x ^ "::" ^ xx)] ] -> (l, x)
| [ ] -> (l, x)

let parse_right_angle_bracket stream = stream |> function%parser
  [ (_, Kwd ">") ] -> ()
| [ (Lexed ((path, line, col), (path', line', col')), Kwd ">>") ] ->
  Lexer.Stream.push (Some (Lexed ((path, line, col + 1), (path', line', col')), Kwd ">")) stream

let rec parse_type = function%parser
  [ (l, Ident "i8") ] -> ManifestTypeExpr (l, Int (Signed, FixedWidthRank 0))
| [ (l, Ident "i16") ] -> ManifestTypeExpr (l, Int (Signed, FixedWidthRank 1))
| [ (l, Ident "i32") ] -> ManifestTypeExpr (l, Int (Signed, FixedWidthRank 2))
| [ (l, Ident "i64") ] -> ManifestTypeExpr (l, Int (Signed, FixedWidthRank 3))
| [ (l, Ident "i128") ] -> ManifestTypeExpr (l, Int (Signed, FixedWidthRank 4))
| [ (l, Ident "isize") ] -> ManifestTypeExpr (l, Int (Signed, PtrRank))
| [ (l, Ident "u8") ] -> ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank 0))
| [ (l, Ident "u16") ] -> ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank 1))
| [ (l, Ident "u32") ] -> ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank 2))
| [ (l, Ident "u64") ] -> ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank 3))
| [ (l, Ident "u128") ] -> ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank 4))
| [ (l, Ident "usize") ] -> ManifestTypeExpr (l, Int (Unsigned, PtrRank))
| [ (l, Ident "bool") ] -> ManifestTypeExpr (l, Bool)
| [ (l, Ident x); [%let l, x = parse_simple_path_rest l x];
    [%let t = function%parser
      [ parse_type_args as targs ] -> ConstructedTypeExpr (l, x, targs)
    | [ ] -> IdentTypeExpr (l, None, x)
    ]
  ] -> t
| [ (l, Kwd "pred"); (_, Kwd "(");
    [%let ts = rep_comma parse_type_with_opt_name];
    [%let (ts, inputParamCount) = function%parser
       [ (_, Kwd ";"); [%let ts' = rep_comma parse_type_with_opt_name] ] -> (ts @ ts', Some (List.length ts))
     | [ ] -> (ts, None)
    ];
    (_, Kwd ")")
  ] -> PredTypeExpr (l, List.map snd ts, inputParamCount)
| [ (l, Kwd "*");
    [%let mutability = opt (function%parser [ (_, Kwd "const") ] -> () | [ (_, Kwd "mut") ] -> ()) ];
    parse_type as t
  ] -> ignore mutability; PtrTypeExpr (l, t)
| [ (l, Kwd "any") ] -> ManifestTypeExpr (l, AnyType)
| [ (l, Kwd "Self") ] -> IdentTypeExpr (l, None, "Self")
and parse_type_with_opt_name = function%parser
  [ parse_type as t;
    [%let (x, t) = function%parser
     | [ (_, Kwd ":"); parse_type as t1 ] ->
       begin match t with
         IdentTypeExpr (lt, None, x) -> (x, t1)
       | _ -> raise (ParseException (type_expr_loc t, "Identifier expected"))
       end
     | [ ] -> ("", t)
    ]
  ] -> (x, t)
and parse_type_args = function%parser
  [ (_, Kwd "<"); [%let targs = rep_comma parse_type]; parse_right_angle_bracket as dummy ] -> targs

let rec parse_expr_funcs allowStructExprs =

  let parse_expr stream = fst (parse_expr_funcs true) stream in
  let parse_pat stream = snd (parse_expr_funcs true) stream in
  let parse_expr_no_struct_expr stream = fst (parse_expr_funcs false) stream in

  let rec parse_sep_expr = function%parser
    [ parse_pointsto_expr as e0;
      [%let e = function%parser
        [ (l, Kwd "&*&"); parse_sep_expr as e1 ] -> Sep (l, e0, e1)
      | [ ] -> e0
      ]
    ] -> e
  and parse_pointsto_expr = function%parser
    [ parse_disj_expr as e;
      [%let e = match e with
        CallExpr (l, "#list", [], [], [coefPat], Static) ->
        begin function%parser
          [ parse_pointsto_expr as e ] -> CoefAsn (l, coefPat, e)
        | [ ] -> e
        end
      | _ ->
        begin function%parser
          [ (l, Kwd "|->");
            parse_pat0 as rhs
          ] -> PointsTo (l, e, rhs)
        | [ ] -> e
        end
      ]
    ] -> e
  and parse_disj_expr = function%parser
    [ parse_conj_expr as e; [%let e = parse_disj_rest e ] ] -> e
  and parse_disj_rest e = function%parser
    [ (l, Kwd "||"); parse_disj_expr as e1 ] -> Operation (l, Or, [e; e1])
  | [ ] -> e
  and parse_conj_expr = function%parser
    [ parse_rel_expr as e; [%let e = parse_conj_rest e ] ] -> e
  and parse_conj_rest e = function%parser
    [ (l, Kwd "&&"); parse_conj_expr as e1 ] -> Operation (l, And, [e; e1])
  | [ ] -> e
  and parse_rel_expr = function%parser
    [ parse_bitor_expr as e; [%let e = parse_rel_rest e ] ] -> e
  and parse_rel_rest e = function%parser
    [ (l, Kwd "=="); parse_bitor_expr as e1 ] -> Operation (l, Eq, [e; e1])
  | [ (l, Kwd "!="); parse_bitor_expr as e1 ] -> Operation (l, Neq, [e; e1])
  | [ (l, Kwd "<"); parse_bitor_expr as e1 ] -> Operation (l, Lt, [e; e1])
  | [ (l, Kwd ">"); parse_bitor_expr as e1 ] -> Operation (l, Gt, [e; e1])
  | [ (l, Kwd "<="); parse_bitor_expr as e1 ] -> Operation (l, Le, [e; e1])
  | [ (l, Kwd ">="); parse_bitor_expr as e1 ] -> Operation (l, Ge, [e; e1])
  | [ ] -> e
  and parse_bitor_expr = function%parser
    [ parse_bitxor_expr as e; [%let e = parse_bitor_rest e ] ] -> e
  and parse_bitor_rest e = function%parser
    [ (l, Kwd "|"); parse_bitxor_expr as e1; [%let e = parse_bitor_rest (Operation (l, BitOr, [e; e1])) ] ] -> e
  | [ ] -> e
  and parse_bitxor_expr = function%parser
    [ parse_bitand_expr as e; [%let e = parse_bitxor_rest e ] ] -> e
  and parse_bitxor_rest e = function%parser
    [ (l, Kwd "^"); parse_bitand_expr as e1; [%let e = parse_bitxor_rest (Operation (l, BitXor, [e; e1])) ] ] -> e
  | [ ] -> e
  and parse_bitand_expr = function%parser
    [ parse_shift_expr as e; [%let e = parse_bitand_rest e ] ] -> e
  and parse_bitand_rest e = function%parser
    [ (l, Kwd "&"); parse_shift_expr as e1; [%let e = parse_bitand_rest (Operation (l, BitAnd, [e; e1])) ] ] -> e
  | [ ] -> e
  and parse_shift_expr = function%parser
    [ parse_add_expr as e; [% let e = parse_shift_rest e ] ] -> e
  and parse_shift_rest e = function%parser
    [ (l, Kwd "<<"); parse_add_expr as e1; [%let e = parse_shift_rest (Operation (l, ShiftLeft, [e; e1])) ] ] -> e
  | [ (l, Kwd ">>"); parse_add_expr as e1; [%let e = parse_shift_rest (Operation (l, ShiftRight, [e; e1])) ] ] -> e
  | [ ] -> e
  and parse_add_expr = function%parser
    [ parse_mul_expr as e; [%let e = parse_add_rest e] ] -> e
  and parse_add_rest e = function%parser
    [ (l, Kwd "+"); parse_mul_expr as e1; [%let e = parse_add_rest (Operation (l, Add, [e; e1])) ] ] -> e
  | [ (l, Kwd "-"); parse_mul_expr as e1; [%let e = parse_add_rest (Operation (l, Sub, [e; e1])) ] ] -> e
  | [ ] -> e
  and parse_mul_expr = function%parser
    [ parse_as_expr as e; [%let e = parse_mul_rest e ] ] -> e
  and parse_mul_rest e = function%parser
    [ (l, Kwd "*"); parse_as_expr as e1; [%let e = parse_mul_rest (Operation (l, Mul, [e; e1])) ] ] -> e
  | [ (l, Kwd "/"); parse_as_expr as e1; [%let e = parse_mul_rest (Operation (l, Div, [e; e1])) ] ] -> e
  | [ (l, Kwd "%"); parse_as_expr as e1; [%let e = parse_mul_rest (Operation (l, Mod, [e; e1])) ] ] -> e
  | [ ] -> e
  and parse_as_expr = function%parser
    [ parse_prefix_expr as e; [%let e = parse_as_rest e ] ] -> e
  and parse_as_rest e = function%parser
    [ (l, Kwd "as"); parse_type as t; [%let e = parse_as_rest (CastExpr (l, t, e)) ] ] -> e
  | [ ] -> e
  and parse_prefix_expr = function%parser
    [ (l, Kwd "-"); parse_prefix_expr as e ] -> Operation (l, Sub, [IntLit (l, zero_big_int, true, false, NoLSuffix); e])
  | [ (l, Kwd "*"); parse_prefix_expr as e ] -> Deref (l, e)
  | [ (l, Kwd "!"); parse_prefix_expr as e ] -> Operation (l, Not, [e])
  | [ (l, Kwd "&"); [%let mutability = opt (function%parser [ (_, Kwd "mut") ] -> ()) ]; parse_prefix_expr as e ] -> ignore mutability; AddressOf (l, e)
  | [ parse_suffix_expr as e ] -> e
  and parse_suffix_expr = function%parser
    [ parse_primary_expr as e;
      [%let e = match e with
        CallExpr (_, "#list", [], [], pats, Static) -> fun s -> e
        | _ -> parse_suffix e
      ]
    ] -> e
  and parse_suffix e = function%parser
    [ (l, Kwd "."); (_, Ident f); [%let e = parse_suffix (Select (l, e, f)) ] ] -> e
  | [ (l, Kwd "("); [%let args0 = rep_comma parse_pat ]; (_, Kwd ")");
      [%let (indices, args) = function%parser
        [ (_, Kwd "("); [%let args = rep_comma parse_pat]; (_, Kwd ")") ] -> (args0, args)
      | [ ] -> ([], args0)
      ]
    ] ->
    begin match e with
      Var (_, x) -> CallExpr (l, x, [], indices, args, Static)
    | _ -> raise (ParseException (l, "Cannot call this expression form"))
    end
  | [] -> e
  and parse_struct_expr_field_rest lf f = function%parser
    [ (_, Kwd ":"); parse_expr as e ] -> (Some (lf, f), e)
  | [ ] -> (Some (lf, f), Var (lf, f))
  and parse_struct_expr_field = function%parser
    [ (lf, Ident f); [%let e = parse_struct_expr_field_rest lf f] ] -> e
  and parse_struct_expr_fields = function%parser
    [ parse_struct_expr_field as e; parse_struct_expr_fields_rest as es ] -> e::es
  | [ ] -> []
  and parse_struct_expr_fields_rest = function%parser
    [ (_, Kwd ","); parse_struct_expr_fields as es ] -> es
  | [ ] -> []
  and parse_struct_expr_rest e = function%parser
    [ (_, Kwd "{"); parse_struct_expr_fields as es; (_, Kwd "}") ] when allowStructExprs ->
    begin match e with
      Var (l, x) -> CastExpr (l, StructTypeExpr (l, Some x, None, [], []), InitializerList (l, es))
    | _ -> raise (ParseException (expr_loc e, "This expression form is not supported in this position"))
    end
  | [ ] -> e
  and parse_primary_expr = function%parser
    [ (l, Ident x); [%let e = parse_path_rest l x];
      [%let e = parse_struct_expr_rest e] ] -> e
  | [ (l, Kwd "self") ] -> Var (l, "self")
  | [ (l, Int (i, dec, usuffix, lsuffix, _)) ] -> IntLit (l, i, dec, usuffix, lsuffix)
  | [ (l, String s) ] -> StringLit (l, s)
  | [ (l, Kwd "true") ] -> True l
  | [ (l, Kwd "false") ] -> False l
  | [ (l, Kwd "if");
      parse_expr_no_struct_expr as cond;
      parse_block_expr as trueBranch;
      (_, Kwd "else");
      parse_block_expr as falseBranch;
    ] -> IfExpr (l, cond, trueBranch, falseBranch)
  | [ (l, Kwd "match");
      parse_expr_no_struct_expr as scrutinee;
      (_, Kwd "{");
      parse_match_expr_rest as arms
    ] -> SwitchExpr (l, scrutinee, arms, None)
  | [ (_, Kwd "("); parse_expr as e; (_, Kwd ")") ] -> e
  | [ (l, Kwd "["); [%let pats = rep_comma parse_pat]; (_, Kwd "]") ] -> CallExpr (l, "#list", [], [], pats, Static)
  | [ (l, Kwd "typeid"); (_, Kwd "("); parse_type as t; (_, Kwd ")") ] -> Typeid (l, TypeExpr t)
  and parse_match_arm = function%parser
    [ parse_expr as pat; (l, Kwd "=>"); parse_expr as rhs ] ->
    begin match pat with
      CallExpr (lc, x, [], [], pats, Static) ->
      let pats =
        pats |>
        List.map begin function
          LitPat (Var (_, x)) -> x
        | _ -> raise (ParseException (lc, "Match arm pattern arguments must be variable names"))
        end
      in
      SwitchExprClause (l, x, pats, rhs)
    | _ -> raise (ParseException (expr_loc pat, "Match arm pattern must be constructor application"))
    end
  and parse_match_expr_rest = function%parser
    [ (_, Kwd "}") ] -> []
  | [ parse_match_arm as arm;
      [%let arms = function%parser
        [ (_, Kwd "}") ] -> []
      | [ (_, Kwd ","); parse_match_expr_rest as arms ] -> arms
      | [ parse_match_expr_rest as arms ] when let SwitchExprClause (_, _, _, body) = arm in is_expr_with_block body -> arms
      | [ ] -> raise (Stream.Error "Comma expected")
      ]
    ] -> arm::arms
  and parse_path_rest l x = function%parser
    [ (_, Kwd "::");
      [%let e = function%parser
        [ parse_type_args as targs;
          [%let e = function%parser
            [ (l, Kwd "("); [%let args = rep_comma parse_pat ]; (_, Kwd ")") ] ->
            begin match x, targs with
              "std::mem::size_of", [t] -> SizeofExpr (l, TypeExpr t)
            | _, _ -> CallExpr (l, x, targs, [], args, Static)
            end
          | [ ] ->
            CallExpr (l, x, targs, [], [], Static)
          ]
        ] -> e
      | [ (_, Ident x1); [%let e = parse_path_rest l (x ^ "::" ^ x1) ] ] -> e
      ]
    ] -> e
  | [ ] -> Var (l, x)
  and parse_block_expr = function%parser
    [ (_, Kwd "{"); parse_expr as e; (_, Kwd "}") ] -> e
  and parse_pat0 = function%parser
    [ (_, Kwd "_") ] -> DummyPat
  | [ (_, Kwd "?"); (lx, Ident x) ] -> VarPat (lx, x)
  | [ (_, Kwd "^"); parse_primary_expr as e ] -> LitPat (WidenedParameterArgument e)
  | [ parse_disj_expr as e ] -> pat_of_expr e
  in
  parse_sep_expr, parse_pat0

let parse_expr, parse_pat = parse_expr_funcs true
let parse_expr_no_struct_expr, _ = parse_expr_funcs false

let rec parse_asn stream = parse_expr stream

let parse_coef = function%parser
  [ (_, Kwd "["); parse_pat as pat; (_, Kwd "]") ] -> pat

let parse_pure_spec_clause = function%parser
  [ (_, Kwd "nonghost_callers_only") ] -> NonghostCallersOnlyClause
| [ (l, Kwd "terminates"); (_, Kwd ";") ] -> TerminatesClause l
| [ (_, Kwd "req"); parse_asn as p; (_, Kwd ";") ] -> RequiresClause p
| [ (_, Kwd "ens"); parse_asn as p; (_, Kwd ";") ] -> EnsuresClause p

let parse_spec_clause = function%parser
  [ [%let c = peek_in_ghost_range @@ function%parser
    [ parse_pure_spec_clause as c; (_, Kwd "@*/") ] -> c ] ] -> c
| [ parse_pure_spec_clause as c ] -> c

let parse_spec_clauses = function%parser
  [ [%let cs = rep parse_spec_clause ] ] ->
  let nonghost_callers_only, cs =
    match cs with
      NonghostCallersOnlyClause::cs -> true, cs
    | _ -> false, cs
  in
  let ft, cs =
    match cs with
      FuncTypeClause (ft, fttargs, ftargs)::cs -> Some (ft, fttargs, ftargs), cs
    | _ -> None, cs
  in
  let pre_post, cs =
    match cs with
      RequiresClause pre::EnsuresClause post::cs -> Some (pre, post), cs
    | _ -> None, cs
  in
  let terminates, cs =
    match cs with
      TerminatesClause l::cs -> true, cs
    | _ -> false, cs
  in
  if cs <> [] then raise (Stream.Error "The number, kind, or order of specification clauses is incorrect. Expected: nonghost_callers_only clause (optional), function type clause (optional), contract (optional), terminates clause (optional).");
  (nonghost_callers_only, ft, pre_post, terminates)

let rec parse_stmt = function%parser
  [ (Lexed (sp1, _), Kwd "/*@"); parse_stmt as s; (Lexed (_, sp2), Kwd "@*/") ] ->
  PureStmt (Lexed (sp1, sp2), s)
| [ (l, Kwd "inv"); parse_asn as p; (_, Kwd ";") ] -> InvariantStmt (l, p)
| [ (l, Kwd "open");
    [%let coef = opt parse_coef];
    parse_expr as e;
    (_, Kwd ";")
  ] ->
  begin match e with
    CallExpr (_, g, targs, es1, es2, Static) ->
    Open (l, None, g, targs, es1, es2, coef)
  | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
    Open (l, Some target, g, targs, es1, es2, coef)
  | _ -> raise (ParseException (l, "Body of open statement must be call expression."))
  end
| [ (l, Kwd "close");
    [%let coef = opt parse_coef];
    parse_expr as e;
    (_, Kwd ";")
  ] ->
  begin match e with
    CallExpr (_, g, targs, es1, es2, Static) ->
    Close (l, None, g, targs, es1, es2, coef)
  | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
    Close (l, Some target, g, targs, es1, es2, coef)
  | _ -> raise (ParseException (l, "Body of close statement must be call expression."))
  end
| [ (l, Kwd "let"); (lx, Ident x); (_, Kwd "="); parse_expr as e; (_, Kwd ";") ] ->
  DeclStmt (l, [lx, None, x, Some e, (ref false, ref None)])
| [ (l, Kwd "if"); parse_expr_no_struct_expr as e; parse_block_stmt as s1;
    [%let s = function%parser
      [ (_, Kwd "else");
        parse_block_stmt as s2
      ] -> IfStmt (l, e, [s1], [s2])
    | [] -> IfStmt (l, e, [s1], [])
    ]
  ] -> s
| [ (l, Kwd "match"); parse_expr_no_struct_expr as e; (_, Kwd "{");
    [%let cs = rep parse_match_stmt_arm];
    (_, Kwd "}")
  ] -> SwitchStmt (l, e, cs)
| [ (l, Kwd "assert"); parse_asn as p; (_, Kwd ";") ] -> Assert (l, p)
| [ (l, Kwd "leak"); parse_asn as p; (_, Kwd ";") ] -> Leak (l, p)
| [ (l, Kwd "produce_lem_ptr_chunk");
    parse_produce_lemma_function_pointer_chunk_stmt_function_type_clause as ftclause;
    [%let body = function%parser
      [ (_, Kwd ";") ] -> None
    | [ parse_stmt as s ] -> Some s
    ]
  ] -> ProduceLemmaFunctionPointerChunkStmt (l, None, Some ftclause, body)
| [ (l, Kwd "produce_fn_ptr_chunk"); 
    (li, Ident ftn);
    [%let targs = function%parser
      [ parse_type_args as targs ] -> targs
    | [ ] -> []
    ];
    (_, Kwd "(");
    parse_expr as fpe;
    (_, Kwd ")");
    (_, Kwd "("); [%let args = rep_comma parse_expr]; (_, Kwd ")");
    (_, Kwd "(");
    [%let params = rep_comma (function%parser [ (l, Ident x) ] -> (l, x)) ];
    (_, Kwd ")");
    (openBraceLoc, Kwd "{");
    parse_stmts as ss;
    (closeBraceLoc, Kwd "}")
  ] ->
  ProduceFunctionPointerChunkStmt (l, ftn, fpe, targs, args, params, openBraceLoc, ss, closeBraceLoc)
| [ parse_block_stmt as s ] -> s
| [ parse_expr as e; (_, Kwd ";") ] -> ExprStmt e
and parse_match_stmt_arm = function%parser
  [ parse_expr as pat; (l, Kwd "=>"); parse_block_stmt as s ] -> SwitchStmtClause (l, pat, [s])
and parse_produce_lemma_function_pointer_chunk_stmt_function_type_clause = function%parser
  [ (li, Ident ftn);
    (_, Kwd "("); [%let args = rep_comma parse_expr]; (_, Kwd ")");
    (_, Kwd "("); [%let params = rep_comma (function%parser [ (l, Ident x) ] -> (l, x))]; (_, Kwd ")");
    (openBraceLoc, Kwd "{");
    parse_stmts as ss;
    (closeBraceLoc, Kwd "}")
  ] -> (ftn, [], args, params, openBraceLoc, ss, closeBraceLoc)
and parse_block_stmt = function%parser
  [ (l, Kwd "{");
    parse_stmts as ss;
    (closeBraceLoc, Kwd "}")
  ] -> BlockStmt (l, [], ss, closeBraceLoc, ref [])
and parse_stmts stream = rep parse_stmt stream

let parse_param = function%parser
  [ (_, Ident x); (_, Kwd ":"); parse_type as t ] -> t, x

let parse_pred_paramlist = function%parser
  [ (_, Kwd "(");
    [%let ps = rep_comma parse_param ];
    [%let (ps, inputParamCount) = begin function%parser
        [ (_, Kwd ";");
          [%let ps' = rep_comma parse_param ]
        ] -> ps @ ps', Some (List.length ps)
      | [ ] -> ps, None
    end ];
    (_, Kwd ")")
  ] -> ps, inputParamCount

let parse_pred_body = function%parser
  [ (_, Kwd "="); parse_asn as p ] -> p

let parse_type_params = function%parser
  [ (_, Kwd "<"); [%let tparams = rep_comma (function%parser [ (_, Ident x) ] -> x)]; (_, Kwd ">") ] -> tparams
| [ ] -> []

let parse_func_header k = function%parser
  [ (l, Ident g); [%let l, g = parse_simple_path_rest l g]; parse_type_params as tparams; (_, Kwd "("); [%let ps = rep_comma parse_param]; (_, Kwd ")");
    [%let rt = function%parser
      [ (_, Kwd "->"); parse_type as t ] -> Some t
    | [ ] -> if k = Regular then Some (StructTypeExpr (l, Some "std_tuple_0_", None, [], [])) else None
    ]
  ] -> (l, g, tparams, ps, rt)

let parse_func_rest k = function%parser
  [ [%let (l, g, tparams, ps, rt) = parse_func_header k];
    [%let d = function%parser
      [ (_, Kwd ";");
        [%let (nonghost_callers_only, ft, co, terminates) = parse_spec_clauses]
      ] -> Func (l, k, tparams, rt, g, ps, nonghost_callers_only, ft, co, terminates, None, false, [])
    | [ [%let (nonghost_callers_only, ft, co, terminates) = parse_spec_clauses];
        (_, Kwd "{");
        parse_stmts as ss;
        (closeBraceLoc, Kwd "}")
      ] -> Func (l, k, tparams, rt, g, ps, nonghost_callers_only, ft, co, terminates, Some (ss, closeBraceLoc), false, [])
    ]
  ] -> d

let rec parse_ctors = function%parser
  [ (l, Ident cn);
    [%let ts = function%parser
     | [ (_, Kwd "(");
         [%let ts = rep_comma parse_type_with_opt_name];
         (_, Kwd ")")
       ] -> ts
     | [ ] -> []
    ];
    parse_ctors_suffix as cs
  ] -> Ctor (l, cn, ts)::cs
and parse_ctors_suffix = function%parser
| [ (_, Kwd "|"); parse_ctors as cs ] -> cs
| [ ] -> []

let parse_lemma_keyword = function%parser
  [ (_, Kwd "lem") ] -> Lemma (false, None)
| [ (_, Kwd "lem_auto");
    [%let trigger = function%parser
       [ (_, Kwd "("); parse_expr as e; (_, Kwd ")") ] -> Some e
     | [ ] -> None
    ]
  ] -> Lemma (true, trigger)

let parse_ghost_decl = function%parser
| [ (l, Kwd "inductive"); (li, Ident i); parse_type_params as tparams; (_, Kwd "=");
    [%let cs = function%parser
     | [ parse_ctors as cs ] -> cs
     | [ parse_ctors_suffix as cs ] -> cs
    ];
    (_, Kwd ";")
  ] -> [Inductive (l, i, tparams, cs)]
| [ (l, Kwd "pred"); (li, Ident g); parse_type_params as tparams; [%let l, g = parse_simple_path_rest li g];
    [%let (ps, inputParamCount) = parse_pred_paramlist ];
    [%let body = opt parse_pred_body ];
    (_, Kwd ";")
  ] ->
    [PredFamilyDecl (l, g, tparams, 0, List.map fst ps, inputParamCount, Inductiveness_Inductive)] @
    (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, tparams, [], ps, body)])
| [ (l, Kwd "pred_fam"); (li, Ident g);
    (_, Kwd "("); [%let index_params = rep_comma parse_param]; (_, Kwd ")");
    [%let (ps, inputParamCount) = parse_pred_paramlist ];
    (_, Kwd ";")
  ] -> [PredFamilyDecl (l, g, [], List.length index_params, List.map fst ps, inputParamCount, Inductiveness_Inductive)]
| [ (l, Kwd "pred_fam_inst"); (li, Ident g);
    (_, Kwd "("); [%let indices = rep_comma parse_expr]; (_, Kwd ")");
    [%let (ps, inputParamCount) = parse_pred_paramlist ];
    (_, Kwd "=");
    parse_asn as body;
    (_, Kwd ";")
  ] ->
    let indices = indices |> List.map @@ function
      Typeid (l, TypeExpr (IdentTypeExpr (_, None, x))) -> (l, x)
    | e -> raise (ParseException (expr_loc e, "typeid(T) expected"))
    in
    [PredFamilyInstanceDecl (l, g, [], indices, ps, body)]
| [ (l, Kwd "pred_ctor"); (li, Ident g); parse_type_params as tparams;
    (_, Kwd "("); [%let ps1 = rep_comma parse_param]; (_, Kwd ")");
    [%let (ps2, inputParamCount) = parse_pred_paramlist ];
    parse_pred_body as p;
    (_, Kwd ";")
  ] -> [PredCtorDecl (l, g, tparams, ps1, ps2, inputParamCount, p)]
| [ parse_lemma_keyword as k; [%let d = parse_func_rest k ] ] -> [d]
| [ (_, Kwd "fix"); [%let (l, g, tparams, ps, rt) = parse_func_header Fixpoint]; (_, Kwd "{"); parse_expr as e; (closeBraceLoc, Kwd "}") ] ->
  let ss =
    match e with
      SwitchExpr (l, e, cs, None) ->
      let cs = cs |> List.map begin function
        SwitchExprClause (l, cn, xs, e) ->
        SwitchStmtClause (l, CallExpr (l, cn, [], [], List.map (fun x -> LitPat (Var (l, x))) xs, Static), [ReturnStmt (expr_loc e, Some e)])
      end in
      [SwitchStmt (l, e, cs)]
    | _ -> [ReturnStmt (expr_loc e, Some e)]
  in
  [Func (l, Fixpoint, tparams, rt, g, ps, false, None, None, false, Some (ss, closeBraceLoc), false, [])]
| [ (l, Kwd "fn_type"); (lftn, Ident ftn); (_, Kwd "("); [%let ftps = rep_comma parse_param]; (_, Kwd ")"); (_, Kwd "=");
    [%let unsafe = function%parser
       [ (_, Kwd "unsafe") ] -> true
     | [ ] -> false
    ];
    (_, Kwd "fn"); (_, Kwd "("); [%let ps = rep_comma parse_param]; (_, Kwd ")"); 
    [%let rt = function%parser
      [ (_, Kwd "->"); parse_type as t ] -> Some t
    | [ ] -> Some (StructTypeExpr (l, Some "std_tuple_0_", None, [], []))
    ];
    (_, Kwd ";");
    (_, Kwd "req"); parse_asn as pre; (_, Kwd ";");
    (_, Kwd "ens"); parse_asn as post; (_, Kwd ";");
    [%let terminates = function%parser
       [ (_, Kwd "terminates"); (_, Kwd ";") ] -> true
     | [ ] -> false
    ]
  ] -> [FuncTypeDecl (l, Real, rt, ftn, [], ftps, ps, (pre, post, terminates))]
| [ (l, Kwd "abstract_type"); (_, Ident tn); (_, Kwd ";") ] -> [AbstractTypeDecl (l, tn)]

let parse_ghost_decls stream = List.flatten (rep parse_ghost_decl stream)

let parse_ghost_decl_block = function%parser
  [ (_, Kwd "/*@"); parse_ghost_decls as ds; (_, Kwd "@*/") ] -> ds

let prefix_decl_name l prefix = function
  Func (l, k, tparams, rt, g, ps, nonghost_callers_only, ft, co, terminates, body, isVirtual, overrides) ->
  Func (l, k, tparams, rt, prefix ^ g, ps, nonghost_callers_only, ft, co, terminates, body, isVirtual, overrides)
| AbstractTypeDecl (l, tn) ->
  AbstractTypeDecl (l, prefix ^ tn)
| _ -> static_error l "Items other than functions are not yet supported here" None

let rec parse_decl = function%parser
  [ (l, Kwd ("impl"|"mod")); (lx, Ident x); (_, Kwd "{");
    [%let ds = rep parse_decl];
    (_, Kwd "}")
  ] ->
  let prefix = x ^ "::" in
  ds |> List.flatten |> List.map (prefix_decl_name l prefix)
| [ (l, Kwd "fn"); [%let d = parse_func_rest Regular] ] -> [d]
| [ parse_ghost_decl_block as ds ] -> ds

let parse_decls = function%parser
  [ [%let ds = rep parse_decl] ] -> List.flatten ds
