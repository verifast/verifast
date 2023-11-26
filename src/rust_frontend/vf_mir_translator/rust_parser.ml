open Lexer
open Ast
open Parser
open Big_int

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
| [ (l, Ident x);
    [%let t = function%parser
      [ (_, Kwd "<"); [%let targs = rep_comma parse_type]; (_, Kwd ">") ] -> ConstructedTypeExpr (l, x, targs)
    | [ ] -> IdentTypeExpr (l, None, x)
    ]
  ] -> t
| [ (l, Kwd "*");
    [%let mutability = opt (function%parser [ (_, Kwd "const") ] -> () | [ (_, Kwd "mut") ] -> ()) ];
    parse_type as t
  ] -> ignore mutability; PtrTypeExpr (l, t)

let rec parse_expr stream = parse_sep_expr stream
and parse_sep_expr = function%parser
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
           parse_pat as rhs
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
  [ parse_primary_expr as e; [%let e = parse_suffix e ] ] -> e
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
and parse_primary_expr = function%parser
  [ (l, Ident x); [%let e = parse_path_rest l x] ] -> e
| [ (l, Int (i, dec, usuffix, lsuffix, _)) ] -> IntLit (l, i, dec, usuffix, lsuffix)
| [ (l, String s) ] -> StringLit (l, s)
| [ (l, Kwd "true") ] -> True l
| [ (l, Kwd "false") ] -> False l
| [ (l, Kwd "if");
    parse_expr as cond;
    parse_block_expr as trueBranch;
    (_, Kwd "else");
    parse_block_expr as falseBranch;
  ] -> IfExpr (l, cond, trueBranch, falseBranch)
| [ (_, Kwd "("); parse_expr as e; (_, Kwd ")") ] -> e
| [ (l, Kwd "["); [%let pats = rep_comma parse_pat]; (_, Kwd "]") ] -> CallExpr (l, "#list", [], [], pats, Static)
and parse_path_rest l x = function%parser
  [ (_, Kwd "::");
    [%let e = function%parser
      [ (_, Kwd "<"); [%let targs = rep_comma parse_type]; (_, Kwd ">");
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
and parse_pat = function%parser
  [ (_, Kwd "_") ] -> DummyPat
| [ (_, Kwd "?"); (lx, Ident x) ] -> VarPat (lx, x)
| [ (_, Kwd "^"); parse_expr as e ] -> LitPat (WidenedParameterArgument e)
| [ parse_disj_expr as e ] -> pat_of_expr e

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
| [ (l, Kwd "if"); parse_expr as e; parse_block_stmt as s1;
    [%let s = function%parser
      [ (_, Kwd "else");
        parse_block_stmt as s2
      ] -> IfStmt (l, e, [s1], [s2])
    | [] -> IfStmt (l, e, [s1], [])
    ]
  ] -> s
| [ (l, Kwd "assert"); parse_asn as p; (_, Kwd ";") ] -> Assert (l, p)
| [ (l, Kwd "leak"); parse_asn as p; (_, Kwd ";") ] -> Leak (l, p)
| [ (l, Kwd "produce_lem_ptr_chunk");
    parse_produce_lemma_function_pointer_chunk_stmt_function_type_clause as ftclause;
    [%let body = function%parser
      [ (_, Kwd ";") ] -> None
    | [ parse_stmt as s ] -> Some s
    ]
  ] -> ProduceLemmaFunctionPointerChunkStmt (l, None, Some ftclause, body)
| [ parse_block_stmt as s ] -> s
| [ parse_expr as e; (_, Kwd ";") ] -> ExprStmt e
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

let parse_func_rest k = function%parser
  [ (l, Ident g); (_, Kwd "("); [%let ps = rep_comma parse_param]; (_, Kwd ")");
    [%let rt = function%parser
      [ (_, Kwd "->"); parse_type as t ] -> Some t
    | [ ] -> if k = Regular then Some (StructTypeExpr (l, Some "std_tuple_0_", None, [])) else None
    ];
    [% let d = function%parser
      [ (_, Kwd ";");
        [%let (nonghost_callers_only, ft, co, terminates) = parse_spec_clauses]
      ] -> Func (l, k, [], rt, g, ps, nonghost_callers_only, ft, co, terminates, None, false, [])
    | [ [%let (nonghost_callers_only, ft, co, terminates) = parse_spec_clauses];
        (_, Kwd "{");
        parse_stmts as ss;
        (closeBraceLoc, Kwd "}")
      ] -> Func (l, k, [], rt, g, ps, nonghost_callers_only, ft, co, terminates, Some (ss, closeBraceLoc), false, [])
    ]
  ] -> d

let parse_ghost_decl = function%parser
| [ (l, Kwd "pred"); (li, Ident g);
    [%let (ps, inputParamCount) = parse_pred_paramlist ];
    [%let body = opt parse_pred_body ];
    (_, Kwd ";")
  ] ->
    [PredFamilyDecl (l, g, [], 0, List.map fst ps, inputParamCount, Inductiveness_Inductive)] @
    (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, [], [], ps, body)])
| [ (l, Kwd "pred_ctor"); (li, Ident g);
    (_, Kwd "("); [%let ps1 = rep_comma parse_param]; (_, Kwd ")");
    [%let (ps2, inputParamCount) = parse_pred_paramlist ];
    parse_pred_body as p;
    (_, Kwd ";")
  ] -> [PredCtorDecl (l, g, ps1, ps2, inputParamCount, p)]
| [ (_, Kwd "lem"); [%let d = parse_func_rest (Lemma (false, None)) ] ] -> [d]

let parse_ghost_decls stream = List.flatten (rep parse_ghost_decl stream)

let parse_ghost_decl_block = function%parser
  [ (_, Kwd "/*@"); parse_ghost_decls as ds; (_, Kwd "@*/") ] -> ds

let prefix_decl_name l prefix = function
  Func (l, k, tparams, rt, g, ps, nonghost_callers_only, ft, co, terminates, body, isVirtual, overrides) ->
  Func (l, k, tparams, rt, prefix ^ g, ps, nonghost_callers_only, ft, co, terminates, body, isVirtual, overrides)
| _ -> static_error l "Items other than functions are not yet supported here" None

let rec parse_decl = function%parser
  [ (l, Kwd ("impl"|"mod")); (lx, Ident x); (_, Kwd "{");
    [%let ds = rep parse_decl];
    (_, Kwd "}")
  ] ->
  let prefix = x ^ "::" in
  ds |> List.flatten |> List.map (prefix_decl_name l prefix)
| [ (l, Kwd "fn"); [%let d = parse_func_rest Regular] ] -> [d]

let parse_decls = function%parser
  [ [%let ds = rep parse_decl] ] -> List.flatten ds
