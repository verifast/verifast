open Ocaml_expr
open Ast

let of_list f xs = L (List.map f xs)

let of_option f x =
  match x with
    None -> c "None"
  | Some x -> C ("Some", [f x])

let of_loc l = Loc l

let of_inductiveness = function
  Inductiveness_Inductive -> c "Inductiveness_Inductive"
| Inductiveness_CoInductive -> c "Inductiveness_CoInductive"

let of_signedness = function
  Signed -> c "Signed"
| Unsigned -> c "Unsigned"

let of_int_rank = function
  CharRank -> c "CharRank"
| ShortRank -> c "ShortRank"
| IntRank -> c "IntRank"
| LongRank -> c "LongRank"
| LongLongRank -> c "LongLongRank"
| PtrRank -> c "PtrRank"
| FixedWidthRank k -> C ("FixedWidthRank", [I k])

let rec of_type = function
  Bool -> c "Bool"
| Void -> c "Void"
| Int (s, r) -> C ("Int", [of_signedness s; of_int_rank r])
| RealType -> c "RealType"
| Float -> c "Float"
| Double -> c "Double"
| LongDouble -> c "LongDouble"
| StructType (s, targs) -> C ("StructType", [S s; of_list of_type targs])
| UnionType u -> C ("UnionType", [S u])
| PtrType t -> C ("PtrType", [of_type t])
| FuncType f -> C ("FuncType", [S f])
| InductiveType (i, ts) -> C ("InductiveType", [S i; of_list of_type ts])
| PredType (xs, ts, precise, ind) ->
  C ("PredType", [
    of_list s xs;
    of_list of_type ts;
    of_option i precise;
    of_inductiveness ind
  ])
| PureFuncType (at, rt) -> C ("PureFuncType", [of_type at; of_type rt])
| ObjType (cn, ts) -> C ("ObjType", [S cn; of_list of_type ts])
| ArrayType t -> C ("ArrayType", [of_type t])
| StaticArrayType (t, n) -> C ("StaticArrayType", [of_type t; I n])
| BoxIdType -> c "BoxIdType"
| HandleIdType -> c "HandleIdType"
| AnyType -> c "AnyType"
| RealTypeParam x -> C ("RealTypeParam", [S x])
| InferredRealType x -> C ("InferredRealType", [S x])
| GhostTypeParam x -> C ("GhostTypeParam", [S x])
| InferredType (o, r) -> C ("InferredType", [I (Oo.id o); of_ref of_inferred_type_state r])
| ClassOrInterfaceName x -> C ("ClassOrInterfaceName", [S x])
| PackageName p -> C ("PackageName", [S p])
| RefType t -> C ("RefType", [of_type t])
| AbstractType s -> C ("AbstractType", [S s])
and of_inferred_type_state = function
  Unconstrained -> c "Unconstrained"
| ContainsAnyConstraint b -> C ("ContainsAnyConstraint", [B b])
| EqConstraint t -> C ("EqConstraint", [of_type t])

let of_prover_type = function
  ProverInt -> c "ProverInt"
| ProverBool -> c "ProverBool"
| ProverReal -> c "ProverReal"
| ProverInductive -> c "ProverInductive"

let of_predref p =
  Call ("predref", [S p#name; of_list of_type p#domain; of_option i p#inputParamCount])

let of_ident_scope = function
  LocalVar -> c "LocalVar"
| FuncName -> c "FuncName"
| PredFamName -> c "PredFamName"
| EnumElemName n -> C ("EnumElemName", [BigInt n])
| GlobalName -> c "GlobalName"
| ModuleName -> c "ModuleName"
| PureFuncName typeid_types -> C ("PureFuncName", [of_list of_type typeid_types])
| ClassOrInterfaceNameScope -> c "ClassOrInterfaceNameScope"
| PackageNameScope -> c "PackageNameScope"

let of_int_literal_lsuffix = function
  NoLSuffix -> c "NoLSuffix"
| LSuffix -> c "LSuffix"
| LLSuffix -> c "LLSuffix"

let of_float_literal_suffix = function
  FloatFSuffix -> c "FloatFSuffix"
| FloatLSuffix -> c "FloatLSuffix"

let string_of_operator = function
  Add -> "Add"
| Sub -> "Sub"
| PtrDiff -> "PtrDiff"
| Le -> "Le"
| Ge -> "Ge"
| Lt -> "Lt"
| Gt -> "Gt"
| Eq -> "Eq"
| Neq -> "Neq"
| And -> "And"
| Or -> "Or"
| Xor -> "Xor"
| Not -> "Not"
| Mul -> "Mul"
| Div -> "Div"
| Mod -> "Mod"
| BitNot -> "BitNot"
| BitAnd -> "BitAnd" 
| BitXor -> "BitXor"
| BitOr -> "BitOr"
| ShiftLeft -> "ShiftLeft"
| ShiftRight -> "ShiftRight"

let rec of_type_expr = function
  StructTypeExpr (l, tag, body, attrs, targs) ->
  C ("StructTypeExpr", [
    of_loc l;
    of_option s tag;
    of_option (fun (tparams, fds) -> T [of_list s tparams; of_list of_field fds]) body;
    of_list of_struct_attr attrs;
    of_list of_type_expr targs
  ])
| UnionTypeExpr (l, tag, fds) ->
  C ("UnionTypeExpr", [
    of_loc l;
    of_option s tag;
    of_option (of_list of_field) fds
  ])
| EnumTypeExpr (l, tag, mems) ->
  C ("EnumTypeExpr", [
    of_loc l;
    of_option s tag;
    of_option (of_list (fun (x, e) -> T [S x; of_option of_expr e])) mems
  ])
| PtrTypeExpr (l, t) ->
  C ("PtrTypeExpr", [
    of_loc l; 
    of_type_expr t
  ])
| ArrayTypeExpr (l, elemTp) ->
  C ("ArrayTypeExpr", [
    of_loc l;
    of_type_expr elemTp
  ])
| StaticArrayTypeExpr (l, elemTp, nbElems) ->
  C ("StaticArrayTypeExpr", [
    of_loc l;
    of_type_expr elemTp;
    I nbElems
  ])
| FuncTypeExpr (l, retTp, params) ->
  C ("FuncTypeExpr", [
    of_loc l;
    of_type_expr retTp;
    of_list (fun (t, x) -> T [of_type_expr t; S x]) params
  ])
| ManifestTypeExpr (l, t) ->
  C ("ManifestTypeExpr", [
    of_loc l;
    of_type t
  ])
| IdentTypeExpr (l, pkg, x) ->
  C ("IdentTypeExpr", [
    of_loc l;
    of_option s pkg;
    S x
  ])
| ConstructedTypeExpr (l, x, targs) ->
  C ("ConstructedTypeExpr", [
    of_loc l;
    S x;
    of_list of_type_expr targs
  ])
| PredTypeExpr (l, argTps, inputParamCount) ->
  C ("PredTypeExpr", [
    of_loc l;
    of_list of_type_expr argTps;
    of_option i inputParamCount
  ])
| PureFuncTypeExpr (l, tps) ->
  C ("PureFuncTypeExpr", [
    of_loc l;
    of_list of_type_expr tps
  ])
| LValueRefTypeExpr (l, tp) ->
  C ("LValueRefTypeExpr", [
    of_loc l;
    of_type_expr tp
  ])
and of_operator = function
  MinValue t -> C ("MinValue", [of_type t])
| MaxValue t -> C ("MaxValue", [of_type t])
| op -> c (string_of_operator op)
and of_expr = function
  True l -> C ("True", [of_loc l])
| False l -> C ("False", [of_loc l])
| Null l -> C ("Null", [of_loc l])
| Var (l, x) -> C ("Var", [of_loc l; S x])
| WVar (l, x, scope) -> C ("WVar", [of_loc l; S x; of_ident_scope scope])
| TruncatingExpr (l, e) -> C ("TruncatingExpr", [of_loc l; of_expr e])
| Operation (l, op, es) ->
  C ("Operation", [
    of_loc l;
    of_operator op; 
    of_list of_expr es
  ])
| WOperation (l, op, es, tp) ->
  C ("WOperation", [
    of_loc l;
    of_operator op;
    of_list of_expr es;
    of_type tp
  ])
| IntLit (l, n, dec, uSuffix, lSuffix) ->
  C ("IntLit", [
    of_loc l;
    BigInt n;
    B dec;
    B uSuffix;
    of_int_literal_lsuffix lSuffix
  ])
| WIntLit (l, n) -> C ("WIntLit", [of_loc l; BigInt n])
| RealLit (l, n, suffix) ->
  C ("RealLit", [
    of_loc l;
    Num n;
    of_option of_float_literal_suffix suffix
  ])
| StringLit (l, s) -> C ("StringLit", [of_loc l; S s])
| ClassLit (l, cn) -> C ("ClassLit", [of_loc l; S cn])
| Typeid (l, e) -> C ("TypeId", [of_loc l; of_expr e])
| TypeInfo (l, t) -> C ("TypeInfo", [of_loc l; of_type t])
| Read (l, e, f) -> C ("Read", [of_loc l; of_expr e; S f])
| Select (l, e, f) -> C ("Select", [of_loc l; of_expr e; S f])
| ActivatingRead (l, e, f) -> C ("ActivatingRead", [of_loc l; of_expr e; S f])
| WRead (l, e, sn, tparams, fn, trange, targs, isStatic, value, ghost) ->
  C ("WRead", [
    of_loc l;
    of_expr e;
    S sn;
    of_list s tparams;
    S fn;
    of_type trange;
    of_list of_type targs;
    B isStatic;
    of_option (of_option of_constant_value) !value;
    of_ghostness ghost
  ])
| WReadUnionMember (l, e, un, idx, mn, trange, isActivating) ->
  C ("WReadUnionMember", [
    of_loc l;
    of_expr e;
    S un;
    I idx;
    S mn;
    of_type trange;
    B isActivating
  ])
| WSelect (l, e, sn, tparams, fn, trange, targs) ->
  C ("WSelect", [
    of_loc l;
    of_expr e;
    S sn;
    of_list s tparams;
    S fn;
    of_type trange;
    of_list of_type targs
  ])
| WReadInductiveField (l, e, i, cn, fn, targs, tp0, tp) ->
  C ("WReadInductiveField", [
    of_loc l;
    of_expr e;
    S i;
    S cn;
    S fn;
    of_list of_type targs;
    of_type tp0;
    of_type tp
  ])
| ReadArray (l, ea, ei) ->
  C ("ReadArray", [
    of_loc l;
    of_expr ea;
    of_expr ei
  ])
| WReadArray (l, ea, elemTp, ei) ->
  C ("WReadArray", [
    of_loc l;
    of_expr ea;
    of_type elemTp;
    of_expr ei
  ])
| Deref (l, e) -> C ("Deref", [of_loc l; of_expr e])
| WDeref (l, e, pointeeTp) ->
  C ("WDeref", [
    of_loc l;
    of_expr e;
    of_type pointeeTp
  ])
| CallExpr (l, f, targs, indices, args, binding) ->
  C ("CallExpr", [
    of_loc l;
    S f;
    of_list of_type_expr targs;
    of_list of_pat indices;
    of_list of_pat args;
    of_method_binding binding
  ])
| ExprCallExpr (l, ef, args) ->
  C ("ExprCallExpr", [
    of_loc l;
    of_expr ef;
    of_list of_expr args
  ])
| WFunPtrCall (l, ef, ftn_opt, args) ->
  C ("WFunPtrCall", [
    of_loc l;
    of_expr ef;
    of_option s ftn_opt;
    of_list of_expr args
  ])
| WPureFunCall (l, f, targs, args) ->
  C ("WPureFunCall", [
    of_loc l;
    S f;
    of_list of_type targs;
    of_list of_expr args
  ])
| WPureFunValueCall (l, ef, args) ->
  C ("WPureFunValueCall", [
    of_loc l;
    of_expr ef;
    of_list of_expr args
  ])
| WFunCall (l, f, targs, args, binding) ->
  C ("WFunCall", [
    of_loc l;
    S f;
    of_list of_type targs;
    of_list of_expr args;
    of_method_binding binding
  ])
| WMethodCall (l, cn, mn, paramTps, args, binding, tpenv) ->
  C ("WMethodCall", [
    of_loc l;
    S cn;
    S mn;
    of_list of_type paramTps;
    of_list of_expr args;
    of_method_binding binding;
    of_list (fun (x, t) -> T [S x; of_type t]) tpenv
  ])
| NewArray (l, elemTp, elength) ->
  C ("NewArray", [
    of_loc l;
    of_type_expr elemTp;
    of_expr elength
  ])
| NewObject (l, cn, args, targs) ->
  C ("NewObject", [
    of_loc l;
    S cn;
    of_list of_expr args;
    of_option (of_list of_type_expr) targs
  ])
| CxxConstruct (l, ctor, tp, args) ->
  C ("CxxConstruct", [
    of_loc l;
    S ctor;
    of_type_expr tp;
    of_list of_expr args
  ])
| WCxxConstruct (l, cn, tp, args) ->
  C ("WCxxConstruct", [
    of_loc l;
    S cn;
    of_type tp;
    of_list of_expr args
  ])
| CxxNew (l, tp, ctorExpr) ->
  C ("CxxNew", [
    of_loc l;
    of_type_expr tp;
    of_option of_expr ctorExpr
  ])
| WCxxNew (l, tp, ctorExpr) ->
  C ("WCxxNew", [
    of_loc l;
    of_type tp;
    of_option of_expr ctorExpr
  ])
| CxxDelete (l, e) -> C ("CxxDelete", [of_loc l; of_expr e])
| NewArrayWithInitializer (l, t, es) ->
  C ("NewArrayWithInitializer", [
    of_loc l;
    of_type_expr t;
    of_list of_expr es
  ])
| IfExpr (l, ec, et, ef) ->
  C ("IfExpr", [
    of_loc l;
    of_expr ec;
    of_expr et;
    of_expr ef
  ])
| SwitchExpr (l, e, cs, default) ->
  C ("SwitchExpr", [
    of_loc l;
    of_expr e;
    of_list of_switch_expr_clause cs;
    of_option (fun (l, e) -> T [of_loc l; of_expr e]) default
  ])
| WSwitchExpr (l, e, i, targs, cs, default, tenv, rt) ->
  C ("WSwitchExpr", [
    of_loc l;
    of_expr e;
    S i;
    of_list of_type targs;
    of_list of_switch_expr_clause cs;
    of_option (fun (l, e) -> T [of_loc l; of_expr e]) default;
    of_list (fun (x, t) -> T [S x; of_type t]) tenv;
    of_type rt
  ])
| PredNameExpr (l, p) -> C ("PredNameExpr", [of_loc l; S p])
| CastExpr (l, t, e) ->
  C ("CastExpr", [
    of_loc l;
    of_type_expr t;
    of_expr e
  ])
| CxxLValueToRValue (l, e) -> C ("CxxLValueToRValue", [of_loc l; of_expr e])
| CxxDerivedToBase (l, e, t) ->
  C ("CxxDerivedToBase", [
    of_loc l;
    of_expr e;
    of_type_expr t
  ])
| Upcast (e, tf, tt) -> C ("Upcast", [of_expr e; of_type tf; of_type tt])
| TypedExpr (e, t) -> C ("TypedExpr", [of_expr e; of_type t])
| WidenedParameterArgument e -> C ("WidenedParameterArgument", [of_expr e])
| SizeofExpr (l, e) -> C ("SizeofExpr", [of_loc l; of_expr e])
| TypePredExpr (l, te, x) -> C ("TypePredExpr", [of_loc l; of_type_expr te; S x])
| WTypePredExpr (l, t, x) -> C ("WTypePredExpr", [of_loc l; of_type t; S x])
| TypeExpr t -> C ("TypeExpr", [of_type_expr t])
| GenericExpr (l, e, cs, def) ->
  C ("GenericExpr", [
    of_loc l;
    of_expr e;
    of_list (fun (t, e) -> T [of_type_expr t; of_expr e]) cs;
    of_option of_expr def
  ])
| AddressOf (l, e) -> C ("AddressOf", [of_loc l; of_expr e])
| ProverTypeConversion (ptf, ptt, e) ->
  C ("ProverTypeConversion", [
    of_prover_type ptf;
    of_prover_type ptt;
    of_expr e
  ])
| ArrayTypeExpr' (l, e) -> C ("ArrayTypeExpr'", [of_loc l; of_expr e])
| AssignExpr (l, el, er) ->
  C ("AssignExpr", [
    of_loc l;
    of_expr el;
    of_expr er
  ])
| AssignOpExpr (l, el, op, er, isPostfix) ->
  C ("AssignOpExpr", [
    of_loc l;
    of_expr el;
    of_operator op;
    of_expr er;
    B isPostfix
  ])
| WAssignOpExpr (l, lhs, x, rhs, postOp) ->
  C ("WAssignOpExpr", [
    of_loc l;
    of_expr lhs;
    S x;
    of_expr rhs;
    B postOp
  ])
| InstanceOfExpr (l, e, t) ->
  C ("InstanceOfExpr", [
    of_loc l;
    of_expr e;
    of_type_expr t
  ])
| SuperMethodCall (l, m, es) ->
  C ("SuperMethodCall", [
    of_loc l;
    S m;
    of_list of_expr es
  ])
| WSuperMethodCall (l, super_cn, m, es, methInfo) ->
  C ("WSuperMethodCall", [
    of_loc l;
    S super_cn;
    S m;
    of_list of_expr es
    (* TODO: Add methInfo *)
  ])
| InitializerList (l, es) ->
  C ("InitializerList", [
    of_loc l;
    of_list (fun (f_opt, e) -> T [of_option (fun (l, f) -> T [of_loc l; S f]) f_opt; of_expr e]) es
  ])
| SliceExpr (l, ef, et) ->
  C ("SliceExpr", [
    of_loc l;
    of_option of_pat ef;
    of_option of_pat et
  ])
| PointsTo (l, el, er) ->
  C ("PointsTo", [
    of_loc l;
    of_expr el;
    of_pat er
  ])
| WPointsTo (l, el, t, er) ->
  C ("WPointsTo", [
    of_loc l;
    of_expr el;
    of_type t;
    of_pat er
  ])
| PredAsn (l, p, targs, indices, args) ->
  C ("PredAsn", [
    of_loc l;
    S p;
    of_list of_type_expr targs;
    of_list of_pat indices;
    of_list of_pat args
  ])
| WPredAsn (l, p, isGlobal, targs, indices, args) ->
  C ("WPredAsn", [
    of_loc l;
    of_predref p;
    B isGlobal;
    of_list of_type targs;
    of_list of_pat indices;
    of_list of_pat args
  ])
| PredExprAsn (l, e, args) ->
  C ("PredExprAsn", [
    of_loc l;
    of_expr e;
    of_list of_pat args
  ])
| WPredExprAsn (l, e, pts, inputParamCount, pats) ->
  C ("WPredExprAsn", [
    of_loc l;
    of_expr e;
    of_list of_type pts;
    of_option i inputParamCount;
    of_list of_pat pats
  ])
| InstPredAsn (l, e, p, index, args) ->
  C ("InstPredAsn", [
    of_loc l;
    of_expr e;
    S p;
    of_expr e;
    of_list of_pat args
  ])
| WInstPredAsn (l, e, cn, cnIsFinal, family, p, index, args) ->
  C ("WInstPredAsn", [
    of_loc l;
    of_option of_expr e;
    S cn;
    of_class_finality cnIsFinal;
    S family;
    S p;
    of_expr index;
    of_list of_pat args
  ])
| ExprAsn (l, e) -> C ("ExprAsn", [of_loc l; of_expr e])
| Sep (l, a1, a2) -> C ("Sep", [of_loc l; of_expr a1; of_expr a2])
| IfAsn (l, e, a1, a2) ->
  C ("IfAsn", [
    of_loc l;
    of_expr e;
    of_expr a1;
    of_expr a2
  ])
| SwitchAsn (l, e, cs) ->
  C ("SwitchAsn", [
    of_loc l;
    of_expr e;
    of_list of_switch_asn_clause cs
  ])
| WSwitchAsn (l, e, i, cs) ->
  C ("WSwitchAsn", [
    of_loc l;
    of_expr e;
    S i;
    of_list of_wswitch_asn_clause cs
  ])
| EmpAsn l -> C ("EmpAsn", [of_loc l])
| ForallAsn (l, t, x, e) ->
  C ("ForallAsn", [
    of_loc l;
    of_type_expr t;
    S x;
    of_expr e
  ])
| CoefAsn (l, coef, a) ->
  C ("CoefAsn", [
    of_loc l;
    of_pat coef;
    of_expr a
  ])
| EnsuresAsn (l, a) -> C ("EnsuresAsn", [of_loc l; of_expr a])
| MatchAsn (l, e, pat) ->
  C ("MatchAsn", [
    of_loc l;
    of_expr e;
    of_pat pat
  ])
| WMatchAsn (l, e, pat, t) ->
  C ("WMatchAsn", [
    of_loc l;
    of_expr e;
    of_pat pat;
    of_type t
  ])
| LetTypeAsn (l, x, tp, a) -> C ("LetTypeAsn", [of_loc l; S x; of_type tp; of_expr a])
and of_pat = function
  LitPat e -> C ("LitPat", [of_expr e])
| VarPat (l, x) -> C ("VarPat", [of_loc l; S x])
| DummyPat -> c "DummyPat"
| DummyVarPat -> c "DummyVarPat"
| CtorPat (l, ctor, args) ->
  C ("CtorPat", [
    of_loc l;
    S ctor;
    of_list of_pat args
  ])
| WCtorPat (l, i, targs, ctor, argTps0, argTps, args, e) ->
  C ("WCtorPat", [
    of_loc l;
    S i;
    of_list of_type targs;
    S ctor;
    of_list of_type argTps0;
    of_list of_type argTps;
    of_list of_pat args;
    of_option of_expr e
  ])
and of_switch_asn_clause = function
  SwitchAsnClause (l, cn, xs, a) ->
  C ("SwitchAsnClause", [
    of_loc l;
    S cn;
    of_list s xs;
    of_expr a
  ])
and of_wswitch_asn_clause = function
  WSwitchAsnClause (l, cn, xs, pts, a) ->
  C ("WSwitchAsnClause", [
    of_loc l;
    S cn;
    of_list s xs;
    of_list (of_option of_prover_type) pts;
    of_expr a
  ])
and of_switch_expr_clause = function
  SwitchExprClause (l, cn, xs, e) ->
  C ("SwitchExprClause", [
    of_loc l;
    S cn;
    of_list s xs;
    of_expr e
  ])
and of_language = function
  Java -> c "Java"
| CLang -> c "CLang"
and of_dialect = function
  Cxx -> c "Cxx"
and of_method_binding = function
  Static -> c "Static"
| Instance -> c "Instance"
and of_visibility = function
  Public -> c "Public"
| Protected -> c "Protected"
| Private -> c "Private"
| Package -> c "Package"
and of_package = function
  PackageDecl (l, pn, is, ds) ->
  C ("PackageDecl", [
    of_loc l;
    S pn;
    of_list of_import is;
    of_list of_decl ds
  ])
and of_import = function
  Import (l, gh, pn, dn) ->
  C ("Import", [
    of_loc l;
    of_ghostness gh;
    S pn;
    of_option s dn
  ])
and of_stmt = function
  PureStmt (l, s) -> C ("PureStmt", [of_loc l; of_stmt s])
| NonpureStmt (l, ok, s) ->
  C ("NonpureStmt", [
    of_loc l;
    B ok;
    of_stmt s
  ])
| DeclStmt (l, ds) ->
  C ("DeclStmt", [
    of_loc l;
    of_list begin fun (l, t, x, init, (addressTaken, addressTakenList)) ->
      T [
        of_loc l;
        of_option of_type_expr t;
        S x;
        of_option of_expr init;
        T [
          of_ref b addressTaken;
          of_ref (of_option (of_ref (of_list s))) addressTakenList
        ]
      ]
    end ds
  ])
| ExprStmt e -> C ("ExprStmt", [of_expr e])
| IfStmt (l, e, sst, ssf) ->
  C ("IfStmt", [
    of_loc l;
    of_expr e;
    of_list of_stmt sst;
    of_list of_stmt ssf
  ])
| SwitchStmt (l, e, cs) ->
  C ("SwitchStmt", [
    of_loc l;
    of_expr e;
    of_list of_switch_stmt_clause cs
  ])
| Assert (l, a) -> C ("Assert", [of_loc l; of_expr a])
| Leak (l, a) -> C ("Leak", [of_loc l; of_expr a])
| Open (l, etarget, p, targs, indices, args, coef) ->
  C ("Open", [
    of_loc l;
    of_option of_expr etarget;
    S p;
    of_list of_type_expr targs;
    of_list of_pat indices;
    of_list of_pat args;
    of_option of_pat coef
  ])
| Close (l, etarget, p, targs, indices, args, coef) ->
  C ("Close", [
    of_loc l;
    of_option of_expr etarget;
    S p;
    of_list of_type_expr targs;
    of_list of_pat indices;
    of_list of_pat args;
    of_option of_pat coef
  ])
| ReturnStmt (l, e) -> C ("ReturnStmt", [of_loc l; of_option of_expr e])
| WhileStmt (l, e, spec, decr, body, epilog) ->
  C ("WhileStmt", [
    of_loc l;
    of_expr e;
    of_option of_loop_spec spec;
    of_option of_expr decr;
    of_list of_stmt body;
    of_list of_stmt epilog
  ])
| BlockStmt (l, ds, ss, closeBraceLoc, addressTaken) ->
  C ("BlockStmt", [
    of_loc l;
    of_list of_decl ds;
    of_list of_stmt ss;
    of_loc closeBraceLoc;
    of_ref (of_list s) addressTaken
  ])
| PerformActionStmt (_, _, _, _, _, _, _, _, _, _, _, _) -> failwith "TODO"
| SplitFractionStmt (_, _, _, _, _) -> failwith "TODO"
| MergeFractionsStmt (_, _) -> failwith "TODO"
| CreateBoxStmt (_, _, _, _, _, _, _) -> failwith "TODO"
| CreateHandleStmt (_, _, _, _, _) -> failwith "TODO"
| DisposeBoxStmt (_, _, _, _) -> failwith "TODO"
| LabelStmt (l, lbl) -> C ("LabelStmt", [of_loc l; S lbl])
| GotoStmt (l, lbl) -> C ("GotoStmt", [of_loc l; S lbl])
| NoopStmt l -> C ("NoopStmt", [of_loc l])
| InvariantStmt (l, a) -> C ("InvariantStmt", [of_loc l; of_expr a])
| ProduceLemmaFunctionPointerChunkStmt (l, e, ft_clause, scope) ->
  C ("ProduceLemmaFunctionPointerChunkStmt", [
    of_loc l;
    of_option of_expr e;
    of_option begin fun (ftn, targs, ftargs, ps, openBraceLoc, body, closeBraceLoc) ->
      T [
        S ftn;
        of_list of_type_expr targs;
        of_list of_expr ftargs;
        of_list (fun (l, x) -> T [of_loc l; S x]) ps;
        of_loc openBraceLoc;
        of_list of_stmt body;
        of_loc closeBraceLoc
      ]
    end ft_clause;
    of_option of_stmt scope
  ])
| DuplicateLemmaFunctionPointerChunkStmt (l, e) ->
  C ("DuplicateLemmaFunctionPointerChunkStmt", [
    of_loc l;
    of_expr e
  ])
| ProduceFunctionPointerChunkStmt (l, ftn, e, targs, ftargs, ps, openBraceLoc, ss, closeBraceLoc) ->
  C ("ProduceFunctionPointerChunkStmt", [
    of_loc l;
    S ftn;
    of_expr e;
    of_list of_type_expr targs;
    of_list of_expr ftargs;
    of_list (fun (l, x) -> T [of_loc l; S x]) ps;
    of_loc openBraceLoc;
    of_list of_stmt ss;
    of_loc closeBraceLoc
  ])
| Throw (l, e) -> C ("Throw", [of_loc l; of_expr e])
| TryCatch (l, ss, ccs) ->
  C ("TryCatch", [
    of_loc l;
    of_list of_stmt ss;
    of_list begin fun (l, t, x, ss) ->
      T [
        of_loc l;
        of_type_expr t;
        S x;
        of_list of_stmt ss
      ]
    end ccs
  ])
| TryFinally (l, ss, l_finally, ss_finally) ->
  C ("TryFinally", [
    of_loc l;
    of_list of_stmt ss;
    of_loc l_finally;
    of_list of_stmt ss_finally
  ])
| Break l -> C ("Break", [of_loc l])
| SuperConstructorCall (l, es) ->
  C ("SuperConstructorCall", [of_loc l; of_list of_expr es])
and of_loop_spec = function
  LoopInv a -> C ("LoopInv", [of_expr a])
| LoopSpec (pre, post) -> C ("LoopSpec", [of_expr pre; of_expr post])
and of_switch_stmt_clause = function
  SwitchStmtClause (l, e, ss) ->
  C ("SwitchStmtClause", [of_loc l; of_expr e; of_list of_stmt ss])
| SwitchStmtDefaultClause (l, ss) ->
  C ("SwitchStmtDefaultClause", [of_loc l; of_list of_stmt ss])
and of_func_kind = function
  Regular -> c "Regular"
| Fixpoint -> c "Fixpoint"
| Lemma (auto, trigger) ->
  C ("Lemma", [
    B auto;
    of_option of_expr trigger
  ])
and of_instance_pred_decl = function
  InstancePredDecl (l, p, params, body) ->
  C ("InstancePredDecl", [
    of_loc l;
    S p;
    of_list (fun (t, x) -> T [of_type_expr t; S x]) params;
    of_option of_expr body
  ])
and of_class_finality = function
  FinalClass -> c "FinalClass"
| ExtensibleClass -> c "ExtensibleClass"
and of_decl = function
  Struct (l, sn, tparams, body, attrs) ->
  C ("Struct", [
    of_loc l;
    S sn;
    of_list s tparams;
    of_option begin fun (bases, fds, preds, isPoly) ->
      T [
        of_list of_base_spec bases;
        of_list of_field fds;
        of_list of_instance_pred_decl preds;
        B isPoly
      ]
    end body;
    of_list of_struct_attr attrs
  ])
| Union (l, un, fds) ->
  C ("Union", [
    of_loc l;
    S un;
    of_option (of_list of_field) fds
  ])
| Inductive (l, i, tparams, ctors) ->
  C ("Inductive", [
    of_loc l;
    S i;
    of_list s tparams;
    of_list of_ctor ctors
  ])
| AbstractTypeDecl (l, x) -> C ("AbstractTypeDecl", [of_loc l; S x])
| PredFamilyDecl (l, p, tparams, nbIndices, paramTypes, inputParamCount, inductiveness) ->
  C ("PredFamilyDecl", [
    of_loc l;
    S p;
    of_list s tparams;
    I nbIndices;
    of_list of_type_expr paramTypes;
    of_option i inputParamCount;
    of_inductiveness inductiveness
  ])
| PredFamilyInstanceDecl (l, p, tparams, indices, params, body) ->
  C ("PredFamilyInstanceDecl", [
    of_loc l;
    S p;
    of_list s tparams;
    of_list (fun (l, x) -> T [of_loc l; S x]) indices;
    of_params params;
    of_expr body
  ])
| PredCtorDecl (l, p, tparams, ctorParams, predParams, inputParamCount, body) ->
  C ("PredCtorDecl", [
    of_loc l;
    S p;
    of_list s tparams;
    of_params ctorParams;
    of_params predParams;
    of_option i inputParamCount;
    of_expr body
  ])
| Func (l, k, tparams, rt, g, xs, nonghostCallersOnly, funcTypeClause, spec, terminates, body, isVirtual, overrides) ->
  C ("Func", [
    of_loc l;
    of_func_kind k;
    of_list s tparams;
    of_option of_type_expr rt;
    S g;
    of_params xs;
    B nonghostCallersOnly;
    of_option begin fun (ftn, targs, args) ->
      T [
        S ftn;
        of_list of_type_expr targs;
        of_list (fun (l, x) -> T [of_loc l; S x]) args
      ]
    end funcTypeClause;
    of_option of_spec spec;
    B terminates;
    of_option of_body_ss body;
    B isVirtual;
    of_list s overrides
  ])
| TypedefDecl (l, t, x, tparams) ->
  C ("TypedefDecl", [of_loc l; of_type_expr t; S x; of_list s tparams])
| FuncTypeDecl (l, gh, rt, ftn, tparams, ftparams, params, (pre, post, terminates)) ->
  C ("FuncTypeDecl", [
    of_loc l;
    of_ghostness gh;
    of_option of_type_expr rt;
    S ftn;
    of_list s tparams;
    of_list (fun (t, x) -> T [of_type_expr t; S x]) ftparams;
    of_list (fun (t, x) -> T [of_type_expr t; S x]) params;
    T [
      of_expr pre;
      of_expr post;
      B terminates
    ]
  ])
| CxxCtor (l, mangled_name, params, contract_opt, terminates, body_opt, implicit, tp) ->
  C ("CxxCtor", [
    of_loc l;
    S mangled_name;
    of_params params;
    of_option of_spec contract_opt;
    B terminates;
    body_opt |> of_option (fun (init_list, body_ss) ->
      T [
        init_list |> of_list (fun (x, init_opt) ->
          T [
            S x;
            init_opt |> of_option (fun (e, is_written) ->
              T [
                of_expr e;
                B is_written
              ]  
            )
          ]  
        );
        of_body_ss body_ss
      ]
    );
    B implicit;
    of_type tp
  ])
| CxxDtor (l, mangled_name, contract_opt, terminates, body_opt, implicit, tp, is_virtual, overrides) ->
  C ("CxxDtor", [
    of_loc l;
    S mangled_name;
    of_option of_spec contract_opt;
    B terminates;
    of_option of_body_ss body_opt;
    B implicit;
    of_type tp;
    B is_virtual;
    overrides |> of_list (fun s -> S s)
  ])
| Global (l, tp_expr, name, expr_opt) ->
  C ("Global", [
    of_loc l;
    of_type_expr tp_expr;
    S name;
    of_option of_expr expr_opt
  ])
| ModuleDecl (l, mn, ilist, ds) ->
  C ("ModuleDecl", [
    of_loc l;
    S mn;
    of_list of_import ilist;
    of_list of_decl ds
  ])
| TypePredDecl (l, te, selfTypeName, predName) ->
  C ("TypePredDecl", [
    of_loc l;
    of_type_expr te;
    S selfTypeName;
    S predName
  ])
| TypePredDef (l, tparams, te, predName, lrhs, rhs) ->
  C ("TypePredDef", [
    of_loc l;
    of_list s tparams;
    of_type_expr te;
    S predName;
    of_loc lrhs;
    S rhs
  ])
and of_params params = 
  params |> of_list @@ fun (t, x) -> T [of_type_expr t; S x]
and of_body_ss (ss, close_brace_loc) =
  T [ 
    of_list of_stmt ss; 
    of_loc close_brace_loc
  ]
and of_spec (pre, post) =
  T [
    of_expr pre;
    of_expr post;
  ]
and of_ghostness = function
  Ghost -> c "Ghost"
| Real -> c "Real"
and of_field = function
  Field (l, gh, t, f, binding, vis, isFinal, init) ->
  C ("Field", [
    of_loc l;
    of_ghostness gh;
    of_type_expr t;
    S f;
    of_method_binding binding;
    of_visibility vis;
    B isFinal;
    of_option of_expr init
  ])
and of_base_spec = function
  CxxBaseSpec (l, cn, isVirtual) ->
  C ("CxxBaseSpec", [of_loc l; S cn; B isVirtual])
and of_ctor = function
  Ctor (l, ctor, params) ->
  C ("Ctor", [
    of_loc l;
    S ctor;
    of_list (fun (x, t) -> T [S x; of_type_expr t]) params
  ])
and of_struct_attr = function
  Packed -> c "Packed"
and of_constant_value = function
  IntConst n -> C ("IntConst", [BigInt n])
| BoolConst b -> C ("BoolConst", [B b])
| StringConst s -> C ("StringConst", [S s])
| NullConst -> c "NullConst"
| GhostConst e -> C ("GhostConst", [of_expr e])

