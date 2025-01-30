module LocAux = Src_loc_aux
open Lexer
open Ast
open Parser
open Big_int

let expr_of_lft_param_expr loc e = CallExpr (loc, "lft_of", [], [], [LitPat (Typeid (loc, TypeExpr e))], Static)
let expr_of_lft_param loc x = expr_of_lft_param_expr loc (IdentTypeExpr (loc, None, x))

let is_expr_with_block = function
  IfExpr (_, _, _, _) -> true
| SwitchExpr (_, _, _, _) -> true
| _ -> false

let rec parse_simple_path_rest l x = function%parser
  [ (_, Kwd "::"); (ll, Ident xx);
  [%let l, x = parse_simple_path_rest (Lexed(Result.get_ok @@ LocAux.cover_loc0 (lexed_loc l) (lexed_loc ll))) (x ^ "::" ^ xx)] ] -> (l, x)
| [ ] -> (l, x)

let parse_simple_path = function%parser
  [ (l, Ident x); [%let (l, x) = parse_simple_path_rest l x] ] -> (l, x)

let parse_right_angle_bracket stream = stream |> function%parser
  [ (_, Kwd ">") ] -> ()
| [ (Lexed ((path, line, col), (path', line', col')), Kwd ">>") ] ->
  Lexer.Stream.push (Some (Lexed ((path, line, col + 1), (path', line', col')), Kwd ">")) stream
| [ (Lexed ((path, line, col), (path', line', col')), Ident ">>>") ] ->
  Lexer.Stream.push (Some (Lexed ((path, line, col + 1), (path', line', col')), Kwd ">>")) stream

let parse_fix_req_rel_expr = function%parser
  [ (lx, Ident x); (lrel, Kwd ("<"|"<=" as rel)); (ly, Ident y) ] ->
  Operation (lrel, (match rel with "<" -> Lt | "<=" -> Le), [Var (lx, x); Var (ly, y)])

let rec parse_fix_req_expr_rest e = function%parser
  [ (l, Kwd "&&"); parse_fix_req_expr as e1 ] -> Operation (l, And, [e; e1])
| [ ] -> e
and parse_fix_req_expr = function%parser
  [ parse_fix_req_rel_expr as e; [%let e = parse_fix_req_expr_rest e] ] -> e

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
| [ (l, Ident "char") ] -> ManifestTypeExpr (l, RustChar)
| [ (l, Ident "f32" ) ] -> ManifestTypeExpr (l, Float)
| [ (l, Ident "f64" ) ] -> ManifestTypeExpr (l, Double)
| [ (l, Ident "real" ) ] -> ManifestTypeExpr (l, RealType)
| [ (l, Ident x); [%let l, x = parse_simple_path_rest l x];
    [%let t = function%parser
      [ parse_type_args as targs ] -> ConstructedTypeExpr (l, x, targs)
    | [ ] -> IdentTypeExpr (l, None, x)
    ]
  ] -> t
| [ (l, PrimePrefixedIdent "static") ] -> ManifestTypeExpr (l, StaticLifetime)
| [ (l, PrimePrefixedIdent a) ] -> IdentTypeExpr (l, None, "'" ^ a)
| [ (l, Kwd "fix"); (_, Kwd "(");
    [%let ps = rep_comma (function%parser
       [ parse_type as tp;
         [%let p = function%parser
            [ (_, Kwd ":"); parse_type as tp' ] ->
            begin match tp with
              IdentTypeExpr (l, None, x) -> (tp', Some (l, x))
            | _ -> raise (ParseException (type_expr_loc tp, "Identifier expected"))
            end
          | [ ] -> (tp, None)
         ]
       ] -> p)
    ];
    (_, Kwd ")");
    [%let req_opt = opt (function%parser [ (_, Kwd "req"); parse_fix_req_expr as e ] -> e)]
  ] ->
  PureFuncTypeExpr (l, ps, req_opt)
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
    [%let t = function%parser
       [ (lv, Kwd "_") ] -> ManifestTypeExpr (lv, Void)
     | [ parse_type as t ] -> t
    ]
  ] -> ignore mutability; PtrTypeExpr (l, t)
| [ (l, Kwd "&");
    [%let lft = function%parser
       [ (_, PrimePrefixedIdent "static") ] -> ManifestTypeExpr (l, StaticLifetime)
     | [ (_, PrimePrefixedIdent lft) ] -> IdentTypeExpr (l, None, "'" ^ lft)
     | [ ] -> raise (ParseException (l, "Explicit lifetime required"))
    ];
    [%let mutability = function%parser [ (_, Kwd "mut") ] -> Mutable | [ ] -> Shared];
    [%let tp = function%parser
       [ (ls, Kwd "["); parse_type as elemTp; (_, Kwd "]") ] ->
       if mutability <> Shared then raise (ParseException (l, "Mutable slice references are not yet supported"));
       StructTypeExpr (ls, Some "slice_ref", None, [], [lft; elemTp])
     | [ parse_type as tp ] ->
       RustRefTypeExpr (l, lft, mutability, tp)
    ]
  ] -> tp
| [ (l, Kwd "any") ] -> ManifestTypeExpr (l, AnyType)
| [ (l, Kwd "Self") ] -> IdentTypeExpr (l, None, "Self")
| [ (l, Kwd "(");
    [%let tp = function%parser
       [ (_, Kwd ")") ] -> StructTypeExpr (l, Some "std_tuple_0_", None, [], [])
     | [ parse_type as tp1;
         [%let tp = function%parser
            [ (_, Kwd ")") ] -> tp1
          | [ (_, Kwd ",");
              [%let tps = rep_comma parse_type];
              (_, Kwd ")") ] ->
              let tps = tp1::tps in
              let struct_name = Printf.sprintf "std_tuple_%d_" (List.length tps) in
              StructTypeExpr (l, Some struct_name, None, [], tps)
         ]
       ] -> tp
    ]
    ] -> tp
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
    [ parse_assign_expr as e;
      [%let e = match e with
        CallExpr (l, "#list", [], [], [coefPat], Static) ->
        begin function%parser
          [ parse_pointsto_expr as e ] -> CoefAsn (l, coefPat, e)
        | [ ] -> e
        end
      | _ ->
        begin function%parser
          [ [%let (l, kind) = function%parser [ (l, Kwd "|->") ] -> l, RegularPointsTo | [ (l, Kwd "|-?->") ] -> l, MaybeUninit];
            parse_pat0 as rhs
          ] -> PointsTo (l, e, kind, rhs)
        | [ ] -> e
        end
      ]
    ] -> e
  and parse_assign_expr = function%parser
    [ parse_disj_expr as e; [%let e = parse_assign_expr_rest e] ] -> e
  and parse_assign_expr_rest e = function%parser
    [ (l, Kwd "="); parse_assign_expr as e1 ] -> AssignExpr (l, e, Mutation, e1)
  | [ ] -> e
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
    [ (l, Kwd ".");
      [%let e = function%parser
         [ (_, Ident f); [%let e = parse_suffix (Select (l, e, f)) ] ] -> e
       | [ (_, Int (i, dec, usuffix, lsuffix, _)); [%let e = parse_suffix (Select (l, e, string_of_big_int i)) ] ] -> e
      ]
    ] -> e
  | [ (l, Kwd "("); [%let args = rep_comma parse_pat ]; (_, Kwd ")");
      [%let e = parse_suffix (ExprCallExpr (l, e, args))]
    ] -> e
  | [ (l, Kwd "[");
      [%let p1 = opt parse_pat];
      [%let index = function%parser
         [ (li, Kwd ".."); [%let p2 = opt parse_pat] ] -> SliceExpr (li, p1, p2)
       | [ ] -> match p1 with Some (LitPat e) -> e | _ -> static_error l "Malformed array access" None
      ];
      (_, Kwd "]");
      [%let e = parse_suffix (ReadArray (l, e, index))]
    ] -> e
  | [] -> e
  and parse_struct_expr_field_rest lf f = function%parser
    [ (_, Kwd ":"); parse_expr as e ] -> (Some (lf, f), e)
  | [ ] -> (Some (lf, f), Var (lf, f))
  and parse_struct_expr_field = function%parser
    [ (lf, Ident f); [%let e = parse_struct_expr_field_rest lf f] ] -> e
  | [ (lf, Int (i, dec, usuffix, lsuffix, _)); [%let e = parse_struct_expr_field_rest lf (string_of_big_int i)] ] -> e
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
    | CallExpr (l, x, targs, [], [], Static) ->
      CastExpr (l, StructTypeExpr (l, Some x, None, [], targs), InitializerList (l, es))
    | _ -> raise (ParseException (expr_loc e, "This expression form is not supported in this position"))
    end
  | [ ] -> e
  and parse_if_expr = function%parser
    [ (l, Kwd "if");
      parse_expr_no_struct_expr as cond;
      parse_block_expr as trueBranch;
      (_, Kwd "else");
      [%let falseBranch = function%parser
         [ parse_if_expr as e ] -> e
       | [ parse_block_expr as e ] -> e
      ]
    ] -> IfExpr (l, cond, trueBranch, falseBranch)
  and parse_primary_expr = function%parser
    [ (l, Ident x); [%let e = parse_path_rest l x];
      [%let e = parse_struct_expr_rest e] ] -> e
  | [ (l, Kwd "self") ] -> Var (l, "self")
  | [ (l, Int (i, dec, usuffix, lsuffix, _)) ] -> IntLit (l, i, dec, usuffix, lsuffix)
  | [ (l, String s) ] -> StringLit (l, s)
  | [ (l, Kwd "true") ] -> True l
  | [ (l, Kwd "false") ] -> False l
  | [ parse_if_expr as e ] -> e
  | [ (l, Kwd "match");
      parse_expr_no_struct_expr as scrutinee;
      (_, Kwd "{");
      parse_match_expr_rest as arms
    ] -> SwitchExpr (l, scrutinee, arms, None)
  | [ (_, Kwd "("); parse_expr as e; (_, Kwd ")") ] -> e
  | [ (l, Kwd "["); [%let pats = rep_comma parse_pat]; (_, Kwd "]") ] -> CallExpr (l, "#list", [], [], pats, Static)
  | [ (l, CharToken c) ] -> IntLit (l, big_int_of_int (Char.code c), true, false, NoLSuffix)
  | [ (l, Kwd "typeid"); (_, Kwd "("); parse_type as t; (_, Kwd ")") ] -> Typeid (l, TypeExpr t)
  | [ (_, Kwd "<"); parse_type as t; (_, Kwd ">"); (l, Kwd "."); (_, Ident x) ] -> TypePredExpr (l, t, x)
  | [ (l, PrimePrefixedIdent a) ] -> expr_of_lft_param l ("'" ^ a)
  and parse_match_arm = function%parser
    [ parse_expr as pat; (l, Kwd "=>"); parse_expr as rhs ] ->
    let lpat, lrhs = expr_loc pat, expr_loc rhs in
    let lpat0, lrhs0 = lexed_loc lpat, lexed_loc lrhs in
    let lsc = Ast.Lexed (Result.get_ok @@ LocAux.cover_loc0 lpat0 lrhs0) in
    begin match pat with
      CallExpr (_, x, [], [], pats, Static) ->
      let pats =
        pats |>
        List.map begin function
          LitPat (Var (_, x)) -> x
        | _ -> raise (ParseException (lpat, "Match arm pattern arguments must be variable names"))
        end
      in
      SwitchExprClause (lsc, x, pats, rhs)
    | Var (_, x) -> SwitchExprClause (lsc, x, [], rhs)
    | _ -> raise (ParseException (lpat, "Match arm pattern must be constructor application"))
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
            [ (l, Kwd "("); [%let args = rep_comma parse_pat ]; (_, Kwd ")");
              [%let (indices, args) = function%parser
                [ (_, Kwd "("); [%let args1 = rep_comma parse_pat ]; (_, Kwd ")") ] -> (args, args1)
              | [ ] -> ([], args)
              ] ] ->
            begin match x, targs, indices, args with
              "std::mem::size_of", [t], [], [] -> SizeofExpr (l, TypeExpr t)
            | "std::mem::align_of", [t], [], [] -> AlignofExpr (l, t)
            | _ -> CallExpr (l, x, targs, indices, args, Static)
            end
          | [ ] ->
            CallExpr (l, x, targs, [], [], Static)
          ]
        ] -> e
      | [ (_, Ident x1); [%let e = parse_path_rest l (x ^ "::" ^ x1) ] ] -> e
      ]
    ] -> e
  | [ (_, Kwd "("); [%let args0 = rep_comma parse_pat ]; (_, Kwd ")");
      [%let (indices, args) = function%parser
         [ (_, Kwd "("); [%let args = rep_comma parse_pat]; (_, Kwd ")") ] -> (args0, args)
       | [ ] -> ([], args0)
      ]
    ] ->
      begin match x, indices, args with
        "std::mem::size_of", [], [LitPat e] -> SizeofExpr (l, CastExpr (l, IdentTypeExpr (l, None, "pointer"), e))
      | _, _, _ -> CallExpr (l, x, [], indices, args, Static)
      end
  | [ ] ->
    match x with
      "isize::MIN" -> Operation (l, MinValue (Int (Signed, PtrRank)), [])
    | "isize::MAX" -> Operation (l, MaxValue (Int (Signed, PtrRank)), [])
    | "usize::MAX" -> Operation (l, MaxValue (Int (Unsigned, PtrRank)), [])
    | "i8::MIN" -> Operation (l, MinValue (Int (Signed, FixedWidthRank 0)), [])
    | "i8::MAX" -> Operation (l, MaxValue (Int (Signed, FixedWidthRank 0)), [])
    | "u8::MAX" -> Operation (l, MaxValue (Int (Unsigned, FixedWidthRank 0)), [])
    | "i16::MIN" -> Operation (l, MinValue (Int (Signed, FixedWidthRank 1)), [])
    | "i16::MAX" -> Operation (l, MaxValue (Int (Signed, FixedWidthRank 1)), [])
    | "u16::MAX" -> Operation (l, MaxValue (Int (Unsigned, FixedWidthRank 1)), [])
    | "i32::MIN" -> Operation (l, MinValue (Int (Signed, FixedWidthRank 2)), [])
    | "i32::MAX" -> Operation (l, MaxValue (Int (Signed, FixedWidthRank 2)), [])
    | "u32::MAX" -> Operation (l, MaxValue (Int (Unsigned, FixedWidthRank 2)), [])
    | "i64::MIN" -> Operation (l, MinValue (Int (Signed, FixedWidthRank 3)), [])
    | "i64::MAX" -> Operation (l, MaxValue (Int (Signed, FixedWidthRank 3)), [])
    | "u64::MAX" -> Operation (l, MaxValue (Int (Unsigned, FixedWidthRank 3)), [])
    | _ -> Var (l, x)
  and parse_block_expr = function%parser
    [ (_, Kwd "{"); parse_expr as e; (_, Kwd "}") ] -> e
  and parse_pat0 = function%parser
    [ (_, Kwd "_") ] -> DummyPat
  | [ (_, Kwd "?"); [%let pat = function%parser [ (lx, Ident x) ] -> VarPat (lx, x) | [ (_, Kwd "_") ] -> DummyVarPat] ] -> pat
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
| [ (l, Kwd "assume_correct") ] -> AssumeCorrectClause l
| [ (_, Kwd "req"); parse_asn as p; (_, Kwd ";") ] -> RequiresClause p
| [ (_, Kwd "ens"); parse_asn as p; (_, Kwd ";") ] -> EnsuresClause p
| [ (_, Kwd "on_unwind_ens"); parse_asn as p; (_, Kwd ";") ] -> OnUnwindEnsuresClause p

let parse_spec_clause = function%parser
  [ [%let c = peek_in_ghost_range @@ function%parser
    [ parse_pure_spec_clause as c; (_, Kwd "@*/") ] -> c ] ] -> c
| [ parse_pure_spec_clause as c ] -> c

let mk_outcome_post l post unwind_post =
  "outcome",
  SwitchExpr (l, Var (l, "outcome"), [
    SwitchExprClause (expr_loc post, "returning", ["result"], post);
    SwitchExprClause (expr_loc unwind_post, "unwinding", [], unwind_post)
  ], None) 

let result_post_of_outcome_post ("outcome", SwitchExpr (_, _, [SwitchExprClause (_, "returning", ["result"], post); _], _)) = ("result", post)

let result_spec_of_outcome_spec (pre, post) = (pre, result_post_of_outcome_post post)

let result_decl_of_outcome_decl = function
  Func (l, Regular, tparams, rt, g, ps, nonghost_callers_only, ft, pre_post, terminates, body, is_virtual, overrides) ->
  let rt = Option.map (fun (ConstructedTypeExpr (_, "fn_outcome", [rt])) -> rt) rt in
  Func (l, Regular, tparams, rt, g, ps, nonghost_callers_only, ft, Option.map result_spec_of_outcome_spec pre_post, terminates, body, is_virtual, overrides)
| FuncTypeDecl (l, Real, rt, ftn, tparams, ftps, ps, (pre, post, terminates)) ->
  let rt = Option.map (fun (ConstructedTypeExpr (_, "fn_outcome", [rt])) -> rt) rt in
  FuncTypeDecl (l, Real, rt, ftn, tparams, ftps, ps, (pre, result_post_of_outcome_post post, terminates))
| d -> d

let result_package_of_outcome_package (PackageDecl (l, pn, ilist, ds)) =
  PackageDecl (l, pn, ilist, List.map result_decl_of_outcome_decl ds)

let result_header_of_outcome_header (l, incl, incls, ps) = (l, incl, incls, List.map result_package_of_outcome_package ps)

let parse_spec_clauses l k = function%parser
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
      RequiresClause pre::EnsuresClause post::OnUnwindEnsuresClause unwind_post::cs ->
      if k <> Regular then raise (ParseException (expr_loc unwind_post, "An on_unwind_ens clause is not allowed here."));
      Some (pre, mk_outcome_post l post unwind_post), cs
    | RequiresClause pre::EnsuresClause post::cs ->
      let post =
        if k = Regular then
          mk_outcome_post l post (EmpAsn l)
        else
          "result", post
      in
      Some (pre, post), cs
    | _ -> None, cs
  in
  let terminates, cs =
    match cs with
      TerminatesClause l::cs -> true, cs
    | _ -> false, cs
  in
  let assume_correct, cs =
    match cs with
      AssumeCorrectClause l::cs -> true, cs
    | _ -> false, cs
  in
  if cs <> [] then raise (Stream.Error "The number, kind, or order of specification clauses is incorrect. Expected: nonghost_callers_only clause (optional), function type clause (optional), 'req', 'ens', and 'on_unwind_ens' clauses (optional), terminates clause (optional), assume_correct clause (optional).");
  ((nonghost_callers_only, ft, pre_post, terminates), assume_correct)

let parse_pred_asn = function%parser
  [ parse_expr as e ] ->
  begin match e with
    CallExpr (_, g, targs, es1, es2, Static) ->
    (None, g, targs, es1, es2)
  | CallExpr (_, g, targs, es1, LitPat target::es2, Instance) ->
    (Some target, g, targs, es1, es2)
  | ExprCallExpr (_, TypePredExpr (_, te, g), args) ->
    begin match te with
      IdentTypeExpr (_, None, sn) ->
      (None, sn ^ "_" ^ g, [], [], args)
    | ConstructedTypeExpr (_, sn, targs) ->
      (None, sn ^ "_" ^ g, targs, [], args)
    | _ ->
      raise (ParseException (type_expr_loc te, "Opening or closing a type predicate for this type is not yet supported"))
    end
  | ExprCallExpr (_, ExprCallExpr (_, TypePredExpr (_, te, g), args1), args2) ->
    begin match te with
    IdentTypeExpr (_, None, sn) ->
      (None, sn ^ "_" ^ g, [], args1, args2)
    | ConstructedTypeExpr (_, sn, targs) ->
      (None, sn ^ "_" ^ g, targs, args1, args2)
    | _ ->
      raise (ParseException (type_expr_loc te, "Opening or closing a type predicate for this type is not yet supported"))
    end
  | _ -> raise (ParseException (expr_loc e, "Body of open or close statement must be call expression."))
  end

let rec parse_stmt = function%parser
  [ (Lexed (sp1, _), Kwd "/*@"); parse_stmt as s; (Lexed (_, sp2), Kwd "@*/") ] ->
  PureStmt (Lexed (sp1, sp2), s)
| [ (l, Kwd "inv"); parse_asn as p; (_, Kwd ";") ] -> InvariantStmt (l, p)
| [ (l, Kwd "req"); parse_asn as req; (_, Kwd ";"); (_, Kwd "ens"); parse_asn as ens; (_, Kwd ";") ] -> SpecStmt (l, req, ens)
| [ (l, Kwd "open");
    [%let coef = opt parse_coef];
    [%let (target, g, targs, es1, es2) = parse_pred_asn];
    (_, Kwd ";")
  ] ->
  Open (l, target, g, targs, es1, es2, coef)
| [ (l, Kwd "close");
    [%let coef = opt parse_coef];
    [%let (target, g, targs, es1, es2) = parse_pred_asn];
    (_, Kwd ";")
  ] ->
  Close (l, target, g, targs, es1, es2, coef)
| [ (l, Kwd "let"); (lx, Ident x); (_, Kwd "="); parse_expr as e; (_, Kwd ";") ] ->
  DeclStmt (l, [lx, None, x, Some e, (ref false, ref None)])
| [ parse_if_stmt as s ] -> s
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
    [%let (li, ftn) = parse_simple_path];
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
| [ (Lexed(spos, _), Kwd "return"); [%let e = opt parse_expr]; (Lexed(_, epos), Kwd ";") ] -> ReturnStmt (Lexed(spos, epos), e)
and parse_match_stmt_arm = function%parser
  [ parse_expr as pat; (l, Kwd "=>"); parse_block_stmt as s ] -> SwitchStmtClause (l, pat, [s])
and parse_produce_lemma_function_pointer_chunk_stmt_function_type_clause = function%parser
  [ [%let (li, ftn) = parse_simple_path]; [%let targs = function%parser [ parse_type_args as targs ] -> targs | [ ] -> []];
    (_, Kwd "("); [%let args = rep_comma parse_expr]; (_, Kwd ")");
    (_, Kwd "("); [%let params = rep_comma (function%parser [ (l, Ident x) ] -> (l, x))]; (_, Kwd ")");
    (openBraceLoc, Kwd "{");
    parse_stmts as ss;
    (closeBraceLoc, Kwd "}")
  ] -> (ftn, targs, args, params, openBraceLoc, ss, closeBraceLoc)
and parse_block_stmt = function%parser
  [ (l, Kwd "{");
    parse_ghost_decls as ds;
    parse_stmts as ss;
    (closeBraceLoc, Kwd "}")
  ] -> BlockStmt (l, ds, ss, closeBraceLoc, ref [])
and parse_if_stmt = function%parser
  [ (l, Kwd "if"); parse_expr_no_struct_expr as e; parse_block_stmt as s1;
    [%let s = function%parser
      [ (_, Kwd "else");
        [%let s2 = function%parser
           [ parse_if_stmt as s2 ] -> s2
         | [ parse_block_stmt as s2 ] -> s2
        ]
      ] -> IfStmt (l, e, [s1], [s2])
    | [] -> IfStmt (l, e, [s1], [])
    ]
  ] -> s
and parse_stmts stream = rep parse_stmt stream

and parse_param = function%parser
  [ (_, Ident x); (_, Kwd ":"); parse_type as t ] -> t, x
| [ (_, Kwd "self"); (_, Kwd ":"); parse_type as t ] -> t, "self"

and parse_struct_field = function%parser
  [ (l, Ident x); (_, Kwd ":"); parse_type as t ] ->
  Field (l, Real, t, x, Instance, Public, false, None)

and parse_pred_paramlist = function%parser
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

and parse_pred_body = function%parser
  [ (_, Kwd "="); parse_asn as p ] -> p

and parse_type_params = function%parser
  [ (_, Kwd "<");
    [%let tparams = rep_comma (function%parser
      [ (_, Ident x) ] -> x
    | [ (_, PrimePrefixedIdent a) ] -> "'" ^ a)];
    (_, Kwd ">") ] -> tparams
| [ ] -> []

and parse_func_header k = function%parser
  [ (l, Ident g); [%let l, g = parse_simple_path_rest l g]; parse_type_params as tparams; (_, Kwd "("); [%let ps = rep_comma parse_param]; (_, Kwd ")");
    [%let rt = function%parser
      [ (_, Kwd "->"); parse_type as t ] -> Some t
    | [ ] -> if k = Regular then Some (StructTypeExpr (l, Some "std_tuple_0_", None, [], [])) else None
    ]
  ] ->
  let rt = Option.map (fun rt -> match k with Regular -> ConstructedTypeExpr (type_expr_loc rt, "fn_outcome", [rt]) | _ -> rt) rt in
  (l, g, tparams, ps, rt)

and parse_func_rest k = function%parser
  [ [%let (l, g, tparams, ps, rt) = parse_func_header k];
    [%let d = function%parser
      [ (_, Kwd ";");
        [%let ((nonghost_callers_only, ft, co, terminates), assume_correct) = parse_spec_clauses l k]
      ] ->
      if assume_correct then raise (ParseException (l, "assume_correct clause is not allowed here."));
      Func (l, k, tparams, rt, g, ps, nonghost_callers_only, ft, co, terminates, None, false, [])
    | [ [%let ((nonghost_callers_only, ft, co, terminates), assume_correct) = parse_spec_clauses l k];
        (_, Kwd "{");
        parse_stmts as ss;
        (closeBraceLoc, Kwd "}")
      ] ->
      let ss = if assume_correct then [ExprStmt (CallExpr (l, "assume", [], [], [LitPat (True l)], Static))] else ss in
      Func (l, k, tparams, rt, g, ps, nonghost_callers_only, ft, co, terminates, Some (ss, closeBraceLoc), false, [])
    ]
  ] -> d

and parse_ctors = function%parser
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

and parse_lemma_keyword = function%parser
  [ (_, Kwd "lem") ] -> Lemma (false, None)
| [ (_, Kwd "lem_auto");
    [%let trigger = function%parser
       [ (_, Kwd "("); parse_expr as e; (_, Kwd ")") ] -> Some e
     | [ ] -> None
    ]
  ] -> Lemma (true, trigger)

and parse_ghost_decl = function%parser
| [ (_, Kwd "pub"); parse_ghost_decl as d ] -> d
| [ (l, Kwd "inductive"); (li, Ident i); parse_type_params as tparams; (_, Kwd "=");
    [%let cs = function%parser
     | [ parse_ctors as cs ] -> cs
     | [ parse_ctors_suffix as cs ] -> cs
    ];
    (_, Kwd ";")
  ] -> [Inductive (l, i, tparams, cs)]
| [ (l, Kwd "pred");
    [%let ds = function%parser
       [ parse_type_args as targs;
         [%let (tparams, tp) = function%parser
            [ (_, Kwd "<"); parse_type as tp; parse_right_angle_bracket as dummy ] ->
            let tparams = targs |> List.map @@ function
              IdentTypeExpr (_, None, x) -> x
            | targ -> raise (ParseException (type_expr_loc targ, "Type parameter expected"))
            in
            (tparams, tp)
          | [ ] ->
            match targs with
              [ tp ] -> ([], tp)
            | _ -> raise (ParseException (l, "There should be exactly one type between the angle brackets"))
         ];
         (_, Kwd ".");
         (lp, Ident p);
         (_, Kwd "(");
         [%let ps = rep_comma_ (function%parser [ (_, Ident x) ] -> x )];
         [%let (ps, inputParamCount) = (function%parser
             [ (_, Kwd ";"); [%let ps' = rep_comma_ (function%parser [ (_, Ident x) ] -> x)] ] -> (ps @ ps', Some (List.length ps))
           | [ ] -> (ps, None))
         ];
         (_, Kwd ")");
         (_, Kwd "=");
         parse_asn as a;
         (_, Kwd ";")
       ] -> [TypePredDef (l, tparams, tp, p, Right (ps, inputParamCount, a))]
    | [ [%let (l, g) = parse_simple_path]; parse_type_params as tparams;
        [%let (ps, inputParamCount) = parse_pred_paramlist ];
        [%let body = opt parse_pred_body ];
        (_, Kwd ";")
      ] ->
      [PredFamilyDecl (l, g, tparams, 0, List.map fst ps, inputParamCount, Inductiveness_Inductive)] @
      (match body with None -> [] | Some body -> [PredFamilyInstanceDecl (l, g, tparams, [], ps, body)])
    ]
  ] -> ds
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
| [ (l, Kwd "pred_ctor"); [%let li, g = parse_simple_path]; parse_type_params as tparams;
    (_, Kwd "("); [%let ps1 = rep_comma parse_param]; (_, Kwd ")");
    [%let (ps2, inputParamCount) = parse_pred_paramlist ];
    parse_pred_body as p;
    (_, Kwd ";")
  ] -> [PredCtorDecl (l, g, tparams, ps1, ps2, inputParamCount, p)]
| [ parse_lemma_keyword as k; [%let d = parse_func_rest k ] ] -> [d]
| [ (_, Kwd "fix");
    [%let (l, g, tparams, ps, rt) = parse_func_header Fixpoint];
    [%let body = (function%parser
      [ (_, Kwd ";") ] -> None
    | [ (_, Kwd "{"); parse_expr as e; (closeBraceLoc, Kwd "}") ] ->
        let ss =
          match e with
            SwitchExpr (l, e, cs, None) ->
              let cs = cs |> List.map begin function SwitchExprClause (l, cn, xs, e) ->
                SwitchStmtClause (l, CallExpr (l, cn, [], [], List.map (fun x -> LitPat (Var (l, x))) xs, Static), [ReturnStmt (expr_loc e, Some e)])
              end in
              [SwitchStmt (l, e, cs)]
            | _ -> [ReturnStmt (expr_loc e, Some e)]
        in Some (ss, closeBraceLoc))]
  ] -> [Func (l, Fixpoint, tparams, rt, g, ps, false, None, None, false, body, false, [])]
| [ (l, Kwd "fn_type"); (lftn, Ident ftn);
    parse_type_params as tparams;
    (_, Kwd "("); [%let ftps = rep_comma parse_param]; (_, Kwd ")"); (_, Kwd "=");
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
    [%let unwind_post = function%parser
       [ (_, Kwd "on_unwind_ens"); parse_asn as unwind_post; (_, Kwd ";") ] -> unwind_post
     | [ ] -> EmpAsn l
    ];
    [%let terminates = function%parser
       [ (_, Kwd "terminates"); (_, Kwd ";") ] -> true
     | [ ] -> false
    ]
  ] ->
    let rt = Option.map (fun rt -> ConstructedTypeExpr (l, "fn_outcome", [rt])) rt in
    let post = mk_outcome_post l post unwind_post in
    [FuncTypeDecl (l, Real, rt, ftn, tparams, ftps, ps, (pre, post, terminates))]
| [ (l, Kwd "lem_type"); (lftn, Ident ftn); parse_type_params as tparams; (_, Kwd "("); [%let ftps = rep_comma parse_param]; (_, Kwd ")"); (_, Kwd "=");
  (_, Kwd "lem"); (_, Kwd "("); [%let ps = rep_comma parse_param]; (_, Kwd ")"); 
  [%let rt = function%parser
    [ (_, Kwd "->"); parse_type as t ] -> Some t
  | [ ] -> None
  ];
  (_, Kwd ";");
  (_, Kwd "req"); parse_asn as pre; (_, Kwd ";");
  (_, Kwd "ens"); parse_asn as post; (_, Kwd ";")
] -> [FuncTypeDecl (l, Ghost, rt, ftn, tparams, ftps, ps, (pre, ("result", post), false))]
| [ (l, Kwd "abstract_type"); (_, Ident tn); (_, Kwd ";") ] -> [AbstractTypeDecl (l, tn)]
| [ (l, Kwd "type_pred_decl"); (_, Kwd "<"); (_, Kwd "Self"); (_, Kwd ">"); (_, Kwd "."); (_, Ident predName); (_, Kwd ":"); parse_type as te; (_, Kwd ";") ] ->
  [TypePredDecl (l, te, "Self", predName)]
| [ (l, Kwd "type_pred_def");
    [%let tparams = function%parser
       [ (_, Kwd "for"); parse_type_params as tparams ] -> tparams
     | [ ] -> []
    ];
    (_, Kwd "<"); parse_type as tp; (_, Kwd ">"); (_, Kwd "."); (_, Ident predName); (_, Kwd "=");
    (lrhs, Ident rhs);
    [%let targs = function%parser
       [ (_, Kwd "::"); (_, Kwd "<"); [%let targs = rep_comma parse_type]; (_, Kwd ">") ] -> targs
     | [ ] -> []
    ];
    (_, Kwd ";")
  ] ->
  let targ_names = targs |> List.map @@ function
    IdentTypeExpr (_, None, targ_name) -> targ_name
  | te -> raise (ParseException (type_expr_loc te, "Type parameter name expected"))
  in
  if targ_names <> tparams then raise (ParseException (lrhs, "Right-hand side type arguments must match definition type parameters"));
  [TypePredDef (l, tparams, tp, predName, Left (lrhs, rhs))]
| [ (l, Kwd "let_lft"); (lx, PrimePrefixedIdent x); (_, Kwd "="); parse_expr as e; (_, Kwd ";") ] -> [TypeWithTypeidDecl (l, "'" ^ x, CallExpr (l, "typeid_of_lft", [], [], [LitPat e], Static))]

and parse_ghost_decls stream = List.flatten (rep parse_ghost_decl stream)

let parse_ghost_decl_block = function%parser
  [ (_, Kwd "/*@"); parse_ghost_decls as ds; (_, Kwd "@*/") ] -> ds

let prefix_decl_name l prefix = function
  Func (l, k, tparams, rt, g, ps, nonghost_callers_only, ft, co, terminates, body, isVirtual, overrides) ->
  Func (l, k, tparams, rt, prefix ^ g, ps, nonghost_callers_only, ft, co, terminates, body, isVirtual, overrides)
| AbstractTypeDecl (l, tn) ->
  AbstractTypeDecl (l, prefix ^ tn)
| Struct (l, sn, tparams, body, attrs) ->
  Struct (l, prefix ^ sn, tparams, body, attrs)
| PredFamilyDecl (l, g, tparams, indexCount, pts, inputParamCount, inductiveness) ->
  PredFamilyDecl (l, prefix ^ g, tparams, indexCount, pts, inputParamCount, inductiveness)
| PredFamilyInstanceDecl (l, g, tparams, indices, pts, body) ->
  PredFamilyInstanceDecl (l, prefix ^ g, tparams, indices, pts, body)
| _ -> static_error l "Some of these kinds of items are not yet supported here" None

let decl_add_type_params l tparams = function
  Func (l, k, tparams', rt, g, ps, nonghost_callers_only, ft, co, terminates, body, isVirtual, overrides) ->
  Func (l, k, tparams @ tparams', rt, g, ps, nonghost_callers_only, ft, co, terminates, body, isVirtual, overrides)
| _ -> static_error l "Some of these kinds of items are not yet supported here" None

let parse_enum_ctor enum_name = function%parser
  [ (lc, Ident c);
    [%let params = function%parser
       [ (_, Kwd "("); [%let params = rep_comma parse_type]; (_, Kwd ")") ] ->
       List.mapi (fun i tp -> Printf.sprintf "%d" i, tp) params
     | [ (_, Kwd "{"); [%let params = rep_comma parse_param]; (_, Kwd "}") ] ->
       List.map (fun (tp, x) -> (x, tp)) params
     | [ ] ->
       []
    ]
  ] -> Ast.Ctor (lc, enum_name ^ "::" ^ c, params)

let parse_decls parse_rsspec_file =
let rec parse_decl = function%parser
  [ (l, Kwd "impl"); parse_type_params as tparams; parse_type as tp; (_, Kwd "{");
    [%let ds = rep parse_decl];
    (_, Kwd "}")
  ] ->
  let (lx, x, targs) =
    match tp with
    | IdentTypeExpr (lx, None, x) -> (lx, x, [])
    | ManifestTypeExpr (lx, tp) -> (lx, Printf.sprintf "<impl %s>" (Verifast0.rust_string_of_type tp), [])
    | ConstructedTypeExpr (lx, x, targs) ->
      let targs = targs |> List.map @@ function
          IdentTypeExpr (ltarg, None, x) -> x
        | targ -> static_error (type_expr_loc targ) "This form of type is not yet supported here" None
      in
      (lx, x, targs)
    | _ -> static_error (type_expr_loc tp) "This form of type is not supported here" None
  in
  let prefix = x ^ (if targs = [] then "" else "::<" ^ String.concat ", " targs ^ ">") ^ "::" in
  let ds = ds |> List.flatten |> List.map (prefix_decl_name l prefix) in
  List.map (decl_add_type_params l tparams) ds
| [ (l, Kwd "trait"); (lx, Ident x); parse_type_params as tparams; (_, Kwd "{");
    [%let ds = rep parse_decl];
    (_, Kwd "}")
  ] ->
  let prefix = x ^ "::" in
  let ds = ds |> List.flatten |> List.map (prefix_decl_name l prefix) in
  let ds = List.map (decl_add_type_params l ("Self"::tparams)) ds in
  ds
| [ (l, Kwd "mod"); (lx, Ident x); (_, Kwd "{");
    [%let ds = rep parse_decl];
    (_, Kwd "}")
  ] -> [ModuleDecl (l, x, [], List.flatten ds)]
| [ (l, Ident "include"); (_, Kwd "!"); (_, Kwd "{"); (ls, String path); (_, Kwd "}") ] ->
  parse_rsspec_file ls path
| [ (l, Kwd "type"); (lx, Ident x); parse_type_params as tparams; (_, Kwd "="); parse_type as tp; (_, Kwd ";") ] ->
  [TypedefDecl (l, tp, x, tparams)]
| [ (l, Kwd "fn"); [%let d = parse_func_rest Regular] ] -> [d]
| [ (_, Kwd "unsafe"); (l, Kwd "fn"); [%let d = parse_func_rest Regular] ] -> [d]
| [ (_, Kwd "struct"); (l, Ident sn); parse_type_params as tparams;
    [%let body = function%parser
       [ (_, Kwd ";") ] -> None
     | [ (_, Kwd "{"); [%let fds = rep_comma_ parse_struct_field]; (_, Kwd "}") ] ->
       Some ([], fds, [], false)
     | [ (_, Kwd "("); [%let tys = rep_comma_ parse_type]; (_, Kwd ")") ] ->
       let fds = List.mapi (fun i t -> Field (l, Real, t, string_of_int i, Instance, Public, false, None)) tys in
       Some ([], fds, [], false)
    ]
  ] ->
  let targs = List.map (fun x -> IdentTypeExpr (l, None, x)) tparams in
  let structTypeExpr = StructTypeExpr (l, Some sn, None, [], targs) in
  let own_paramTypes = [IdentTypeExpr (l, None, "thread_id_t"); structTypeExpr] in
  let fbc_paramTypes = [IdentTypeExpr (l, None, "thread_id_t"), "t"; PtrTypeExpr (l, structTypeExpr), "l"] in
  [
    Struct (l, sn, tparams, body, []);
    TypedefDecl (l, structTypeExpr, sn, tparams);
    if tparams = [] then
      PredFamilyDecl (l, sn ^ "_own", [], 0, own_paramTypes, None, Inductiveness_Inductive)
    else
      Func (l, Fixpoint, tparams, Some (PredTypeExpr (l, own_paramTypes, None)), sn ^ "_own", [], false, None, None, false, None, false, []);
    TypePredDef (l, tparams, structTypeExpr, "own", Left (l, sn ^ "_own"));
    Func (l, Fixpoint, tparams, Some (PredTypeExpr (l, [], None)), sn ^ "_full_borrow_content", fbc_paramTypes, false, None, None, false, None, false, []);
    TypePredDef (l, tparams, structTypeExpr, "full_borrow_content", Left (l, sn ^ "_full_borrow_content"))
  ]
| [ (_, Ident "union"); (l, Ident un); (_, Kwd "{"); (_, Kwd "}") ] -> [ Union (l, un, Some []) ]
| [ (_, Kwd "enum"); (l, Ident en); parse_type_params as tparams; (_, Kwd "{");
    [%let ctors = rep (function%parser
       [ [%let ctor = parse_enum_ctor en];
         [%let dummy = function%parser [ (_, Kwd ",") ] -> () | [ ] -> ()]
       ] -> ctor)];
    (_, Kwd "}")
  ] ->
  let tparams_targs = List.map (fun x -> IdentTypeExpr (l, None, x)) tparams in
  let own_pred_def =
    TypePredDef (l, tparams, ConstructedTypeExpr (l, en, tparams_targs), "own", Left (l, en ^ "_own"))
  in
  let own_pred_decls =
    let clauses = ctors |> List.map begin function Ctor (lc, cn, ps) ->
      let arg_own_asns = ps |> List.map begin function (x, tp) ->
        ExprCallExpr (lc, TypePredExpr (lc, tp, "own"), [LitPat (Var (lc, "_t")); LitPat (Var (lc, x))])
      end in
      let body = List.fold_left (fun a1 a2 -> Sep (lc, a1, a2)) (EmpAsn lc) arg_own_asns in
      SwitchExprClause (lc, cn, List.map fst ps, body)
    end in
    let body = SwitchExpr (l, Var (l, "_v"), clauses, None) in
    if tparams = [] then
      [
        PredFamilyDecl (l, en ^ "_own", [], 0, [IdentTypeExpr (l, None, "thread_id_t"); ConstructedTypeExpr (l, en, [])], None, Inductiveness_Inductive);
        PredFamilyInstanceDecl (l, en ^ "_own", [], [], [IdentTypeExpr (l, None, "thread_id_t"), "_t"; ConstructedTypeExpr (l, en, []), "_v"], body)
      ]
    else
      [PredCtorDecl (l, en ^ "_own", tparams, [], [IdentTypeExpr (l, None, "thread_id_t"), "_t"; ConstructedTypeExpr (l, en, tparams_targs), "_v"], None, body)]
  in
  [Inductive (l, en, tparams, ctors)] @ own_pred_decls @ [own_pred_def]
| [ parse_ghost_decl_block as ds ] -> ds
in
function%parser
  [ [%let ds = rep parse_decl] ] -> List.flatten ds

let flatten_module_decls ltop ilist ds =
  let rec iter lp pn ilist ds0 ds cont =
    match ds with
      [] -> PackageDecl (lp, pn, ilist, List.rev ds0)::cont ()
    | ModuleDecl (l, mn, ilist', mds)::ds ->
      PackageDecl (lp, pn, ilist, List.rev ds0)::
      iter l (if pn = "" then mn else pn ^ "::" ^ mn) ilist' [] mds begin fun () ->
        iter lp pn ilist [] ds cont
      end
    | d::ds ->
      iter lp pn ilist (d::ds0) ds cont
  in
  iter ltop "" ilist [] ds (fun () -> [])

let rec parse_use_tree prefix = function%parser
  [ (l, Kwd "*") ] -> [Import (l, Ghost, String.concat "::" (List.rev prefix), None)]
| [ (l, Ident x);
    [%let imports = function%parser
       [ (_, Kwd "::");
         [%let imports = function%parser
            [ (l, Kwd "{");
              [%let imports = rep_comma_ (parse_use_tree (x::prefix))];
              (_, Kwd "}") ] -> List.flatten imports
          | [ [%let imports = parse_use_tree (x::prefix)] ] -> imports
         ] ] -> imports
     | [ ] -> [Import (l, Ghost, String.concat "::" (List.rev prefix), Some x)]]
  ] -> imports

let parse_ghost_generic_arg_list = function%parser
  [ (_, Kwd "/*@"); (_, Kwd "::"); parse_type_args as targs; (_, Kwd "@*/") ] -> targs

let parse_use_decl = function%parser
  [ (l, Kwd "use"); [%let imports = parse_use_tree []]; (_, Kwd ";") ] -> imports

let parse_ghost_use_decl_or_decl_batch = function%parser
  [ (_, Kwd "/*@");
    [%let ds = function%parser
       [ parse_use_decl as imports] -> Either.Left imports
     | [ parse_ghost_decls as ds ] -> Either.Right ds
    ];
    (_, Kwd "@*/")
  ] -> ds

let parse_use_decls = function%parser
  [ [%let imports = rep parse_use_decl] ] -> List.flatten imports