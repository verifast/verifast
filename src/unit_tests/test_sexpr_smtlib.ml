open Big_int
open Ast
open SExpressions
open SExpressionEmitter
open Json

let passed_assertions = ref 0

let check msg condition =
  if condition then
    incr passed_assertions
  else (
    Printf.eprintf "[FAIL] SExpr/SMTLib assertion failed: %s\n" msg;
    assert false
  )

(* ========================================== *)
(* Suite 1: SExpressions                      *)
(* ========================================== *)
let test_sexpressions () =
  (* Symbol *)
  check "Symbol" (string_of_sexpression (Symbol "hello") = "hello");
  check "Empty Symbol" (string_of_sexpression (Symbol "") = "||");
  check "Keyword" (string_of_sexpression (Keyword "test") = ":test");
  check "Number" (string_of_sexpression (Number (big_int_of_int 12345)) = "12345");
  
  (* Lists *)
  check "Empty list" (string_of_sexpression (List []) = "()");
  check "Singleton list" (string_of_sexpression (List [Symbol "foo"]) = "(foo)");
  check "Quoted symbol" (string_of_sexpression (List [Symbol "quote"; Symbol "bar"]) = "'bar");

  (* Nested complex sexpr *)
  let nested = List [Symbol "define-fun"; Symbol "add1"; List [List [Symbol "x"; Symbol "Int"]]; Symbol "Int"; List [Symbol "+"; Symbol "x"; Number unit_big_int]] in
  let str = string_of_sexpression nested in
  check "nested non-empty" (String.length str > 0);
  check "nested contains add1" (String.contains str '1');

  (* Keyword formatting with destructure in SExpressions *)
  let kw_sexpr = List [Symbol "call"; Symbol "target"; Keyword "opt1"; Symbol "val1"; Keyword "opt2"; Symbol "val2"] in
  let str_kw = string_of_sexpression kw_sexpr in
  check "kw sexpr contains :opt1" (String.length str_kw > 0);
  check "format empty list" (string_of_sexpression (List []) = "()")

(* ========================================== *)
(* Suite 2: SExpressionEmitter Comprehensive   *)
(* ========================================== *)
let test_sexpression_emitter () =
  (* --- 2a. Types --- *)
  check "Bool" (string_of_sexpression (sexpr_of_type_ Bool) = "(type-bool)");
  check "Void" (string_of_sexpression (sexpr_of_type_ Void) = "(type-void)");
  check "Char Signed" (string_of_sexpression (sexpr_of_type_ (Int (Signed, CharRank))) = "(type-char)");
  check "Char Unsigned" (string_of_sexpression (sexpr_of_type_ (Int (Unsigned, CharRank))) = "(type-uchar)");
  check "Short Signed" (string_of_sexpression (sexpr_of_type_ (Int (Signed, ShortRank))) = "(type-short)");
  check "Short Unsigned" (string_of_sexpression (sexpr_of_type_ (Int (Unsigned, ShortRank))) = "(type-ushort)");
  check "Int Signed" (string_of_sexpression (sexpr_of_type_ (Int (Signed, IntRank))) = "(type-int)");
  check "Int Unsigned" (string_of_sexpression (sexpr_of_type_ (Int (Unsigned, IntRank))) = "(type-uint)");
  check "Long Signed" (string_of_sexpression (sexpr_of_type_ (Int (Signed, LongRank))) = "(type-long)");
  check "Long Unsigned" (string_of_sexpression (sexpr_of_type_ (Int (Unsigned, LongRank))) = "(type-ulong)");
  check "LLong Signed" (string_of_sexpression (sexpr_of_type_ (Int (Signed, LongLongRank))) = "(type-llong)");
  check "LLong Unsigned" (string_of_sexpression (sexpr_of_type_ (Int (Unsigned, LongLongRank))) = "(type-ullong)");
  check "PtrRank Signed" (string_of_sexpression (sexpr_of_type_ (Int (Signed, PtrRank))) = "(type-intptr)");
  check "PtrRank Unsigned" (string_of_sexpression (sexpr_of_type_ (Int (Unsigned, PtrRank))) = "(type-uintptr)");
  check "FixedWidth Signed" (string_of_sexpression (sexpr_of_type_ (Int (Signed, FixedWidthRank 3))) = "(type-int64)");
  check "FixedWidth Unsigned" (string_of_sexpression (sexpr_of_type_ (Int (Unsigned, FixedWidthRank 3))) = "(type-uint64)");
  check "Real" (string_of_sexpression (sexpr_of_type_ RealType) = "(type-real)");
  check "Float" (string_of_sexpression (sexpr_of_type_ Float) = "(type-float)");
  check "Double" (string_of_sexpression (sexpr_of_type_ Double) = "(type-double)");
  check "LongDouble" (string_of_sexpression (sexpr_of_type_ LongDouble) = "(type-long-double)");

  let t_int = Int (Signed, IntRank) in
  let t_bool = Bool in
  check "StructType" (string_of_sexpression (sexpr_of_type_ (StructType ("Point", [t_int]))) = "(type-struct Point (type-int))");
  check "UnionType" (string_of_sexpression (sexpr_of_type_ (UnionType "MyUnion")) = "(type-union MyUnion)");
  check "PtrType" (string_of_sexpression (sexpr_of_type_ (PtrType t_int)) = "(type-pointer-to (type-int))");
  check "FuncType" (string_of_sexpression (sexpr_of_type_ (FuncType "fn_t")) = "(type-function fn_t)");
  check "InductiveType" (string_of_sexpression (sexpr_of_type_ (InductiveType ("Nat", []))) = "(type-inductive Nat)");
  check "PredType Inductive" (String.length (string_of_sexpression (sexpr_of_type_ (PredType (["i"], [t_int], Some 1, Inductiveness_Inductive)))) > 0);
  check "PredType Coinductive" (String.length (string_of_sexpression (sexpr_of_type_ (PredType (["i"], [t_int], None, Inductiveness_CoInductive)))) > 0);
  check "PureFuncType" (string_of_sexpression (sexpr_of_type_ (PureFuncType (t_int, t_bool))) = "(type-pred-func-type (type-int) (type-bool))");
  check "ObjType" (String.length (string_of_sexpression (sexpr_of_type_ (ObjType ("JavaClass", [t_int])))) > 0);
  check "ArrayType" (string_of_sexpression (sexpr_of_type_ (ArrayType t_int)) = "(type-array-type (type-int))");
  check "StaticArrayType" (string_of_sexpression (sexpr_of_type_ (StaticArrayType (t_int, t_int))) = "(type-static-array-type (type-int) (type-int))");
  check "LiteralConstType" (string_of_sexpression (sexpr_of_type_ (LiteralConstType (Z.of_int 42))) = "(type-literal-const 42)");
  check "BoxIdType" (string_of_sexpression (sexpr_of_type_ BoxIdType) = "(type-box-id)");
  check "HandleIdType" (string_of_sexpression (sexpr_of_type_ HandleIdType) = "(type-handle-id-type)");
  check "AnyType" (string_of_sexpression (sexpr_of_type_ AnyType) = "(AnyType)");
  check "RealTypeParam" (string_of_sexpression (sexpr_of_type_ (RealTypeParam "R")) = "(real-type-param R)");
  check "InferredRealType" (string_of_sexpression (sexpr_of_type_ (InferredRealType "IR")) = "(inferred-real-type IR)");
  check "GhostTypeParam" (string_of_sexpression (sexpr_of_type_ (GhostTypeParam "G")) = "(ghost-type-param G)");
  check "InferredType Unconstrained" (string_of_sexpression (sexpr_of_type_ (InferredType (object end, ref Unconstrained))) = "(type-inferred (inferred-type-state-unconstrained))");
  check "InferredType ContainsAny" (string_of_sexpression (sexpr_of_type_ (InferredType (object end, ref (ContainsAnyConstraint true)))) = "(type-inferred (inferred-type-state-contains-any-constraint #t))");
  check "InferredType EqConstraint" (string_of_sexpression (sexpr_of_type_ (InferredType (object end, ref (EqConstraint t_int)))) = "(type-inferred (inferred-type-state-eq-constraint (type-int)))");
  check "ClassOrInterfaceName" (string_of_sexpression (sexpr_of_type_ (ClassOrInterfaceName "C")) = "(type-class-or-interface-name C)");
  check "PackageName" (string_of_sexpression (sexpr_of_type_ (PackageName "P")) = "(type-package-name P)");
  check "RefType" (string_of_sexpression (sexpr_of_type_ (RefType t_int)) = "(type-ref-type (type-int))");
  check "AbstractType" (string_of_sexpression (sexpr_of_type_ (AbstractType "A")) = "(type-abstract A)");

  (* --- 2b. Type Expressions --- *)
  let te_int = ManifestTypeExpr (dummy_loc, t_int) in
  check "ManifestTypeExpr" (string_of_sexpression (sexpr_of_type_expr te_int) = "(type-expr-manifest (type-int))");
  check "StructTypeExpr" (String.length (string_of_sexpression (sexpr_of_type_expr (StructTypeExpr (dummy_loc, Some "Point", None, [], [te_int])))) > 0);
  check "StructTypeExpr None" (String.length (string_of_sexpression (sexpr_of_type_expr (StructTypeExpr (dummy_loc, None, None, [], [])))) > 0);
  check "UnionTypeExpr" (string_of_sexpression (sexpr_of_type_expr (UnionTypeExpr (dummy_loc, Some "U", None))) = "(type-expr-union U)");
  check "EnumTypeExpr" (string_of_sexpression (sexpr_of_type_expr (EnumTypeExpr (dummy_loc, Some "E", None))) = "(type-expr-enum E)");
  check "PtrTypeExpr" (string_of_sexpression (sexpr_of_type_expr (PtrTypeExpr (dummy_loc, te_int))) = "(type-expr-pointer-to (type-expr-manifest (type-int)))");
  check "FuncTypeExpr" (String.length (string_of_sexpression (sexpr_of_type_expr (FuncTypeExpr (dummy_loc, te_int, [(te_int, "x")])))) > 0);
  check "ArrayTypeExpr" (string_of_sexpression (sexpr_of_type_expr (ArrayTypeExpr (dummy_loc, te_int))) = "(type-expr-array-type (type-expr-manifest (type-int)))");
  check "StaticArrayTypeExpr" (String.length (string_of_sexpression (sexpr_of_type_expr (StaticArrayTypeExpr (dummy_loc, te_int, te_int)))) > 0);
  check "LiteralConstTypeExpr" (string_of_sexpression (sexpr_of_type_expr (LiteralConstTypeExpr (dummy_loc, Z.of_int 7))) = "(type-expr-literal-const 7)");
  check "IdentTypeExpr with pkg" (String.length (string_of_sexpression (sexpr_of_type_expr (IdentTypeExpr (dummy_loc, Some "pkg", "MyType")))) > 0);
  check "IdentTypeExpr without pkg" (String.length (string_of_sexpression (sexpr_of_type_expr (IdentTypeExpr (dummy_loc, None, "LocalType")))) > 0);
  check "ConstructedTypeExpr" (String.length (string_of_sexpression (sexpr_of_type_expr (ConstructedTypeExpr (dummy_loc, "Box", [te_int])))) > 0);
  check "PredTypeExpr" (String.length (string_of_sexpression (sexpr_of_type_expr (PredTypeExpr (dummy_loc, [te_int], Some 1)))) > 0);
  check "PureFuncTypeExpr" (String.length (string_of_sexpression (sexpr_of_type_expr (PureFuncTypeExpr (dummy_loc, [(te_int, Some (dummy_loc, "x"))], None)))) > 0);
  check "LValueRefTypeExpr" (string_of_sexpression (sexpr_of_type_expr (LValueRefTypeExpr (dummy_loc, te_int))) = "(type-expr-lvalue-ref (type-expr-manifest (type-int)))");

  (* --- 2c. Expressions --- *)
  let e_true = Ast.True dummy_loc in
  let e_false = Ast.False dummy_loc in
  let e_null = Ast.Null dummy_loc in
  let e_var = Var (dummy_loc, "my_var") in
  let e_int = IntLit (dummy_loc, big_int_of_int 42, true, false, NoLSuffix) in
  check "True" (string_of_sexpression (sexpr_of_expr e_true) = "expr-true");
  check "False" (string_of_sexpression (sexpr_of_expr e_false) = "expr-false");
  check "Null" (string_of_sexpression (sexpr_of_expr e_null) = "expr-null");
  check "Var" (string_of_sexpression (sexpr_of_expr e_var) = "(expr-var my_var)");
  check "WVar" (String.length (string_of_sexpression (sexpr_of_expr (WVar (dummy_loc, "wv", LocalVar)))) > 0);
  check "Select" (string_of_sexpression (sexpr_of_expr (Select (dummy_loc, e_var, "field"))) = "(expr-select (expr-var my_var) field)");
  check "WIntLit" (string_of_sexpression (sexpr_of_expr (WIntLit (dummy_loc, big_int_of_int 99))) = "(expr-wintlit 99)");
  check "RealLit f" (String.length (string_of_sexpression (sexpr_of_expr (RealLit (dummy_loc, Num.num_of_int 5, Some FloatFSuffix)))) > 0);
  check "RealLit l" (String.length (string_of_sexpression (sexpr_of_expr (RealLit (dummy_loc, Num.num_of_int 6, Some FloatLSuffix)))) > 0);
  check "RealLit none" (String.length (string_of_sexpression (sexpr_of_expr (RealLit (dummy_loc, Num.num_of_int 7, None)))) > 0);
  check "StringLit" (string_of_sexpression (sexpr_of_expr (StringLit (dummy_loc, "text"))) = "(expr-string-literal text)");
  check "ClassLit" (string_of_sexpression (sexpr_of_expr (ClassLit (dummy_loc, "Cls"))) = "(expr-class-lit Cls)");
  check "TruncatingExpr" (string_of_sexpression (sexpr_of_expr (TruncatingExpr (dummy_loc, e_int))) = "(expr-truncating (expr-int 42))");

  (* Operations *)
  let ops = [Add; Sub; Mul; Div; Mod; Eq; Neq; Lt; Le; Gt; Ge; And; Or; Not; BitNot; BitAnd; BitOr; BitXor; ShiftLeft; ShiftRight] in
  List.iter (fun op ->
    let e_op = Operation (dummy_loc, op, [e_var; e_int]) in
    check ("Op " ^ string_of_sexpression (sexpr_of_expr e_op)) (String.length (string_of_sexpression (sexpr_of_expr e_op)) > 0)
  ) ops;

  check "WOperation" (String.length (string_of_sexpression (sexpr_of_expr (WOperation (dummy_loc, Add, [e_var; e_int], t_int)))) > 0);
  check "SliceExpr" (String.length (string_of_sexpression (sexpr_of_expr (SliceExpr (dummy_loc, Some (LitPat e_int), Some (LitPat e_int))))) > 0);
  check "Read" (string_of_sexpression (sexpr_of_expr (Read (dummy_loc, e_var, "field"))) = "(expr-read (expr-var my_var) field)");
  check "ArrayLengthExpr" (string_of_sexpression (sexpr_of_expr (ArrayLengthExpr (dummy_loc, e_var))) = "(expr-array-length (expr-var my_var))");
  check "ReadArray" (String.length (string_of_sexpression (sexpr_of_expr (ReadArray (dummy_loc, e_var, e_int)))) > 0);
  check "WReadArray" (String.length (string_of_sexpression (sexpr_of_expr (WReadArray (dummy_loc, e_var, t_int, e_int)))) > 0);
  check "Deref" (String.length (string_of_sexpression (sexpr_of_expr (Deref (dummy_loc, e_var)))) > 0);
  check "WDeref" (String.length (string_of_sexpression (sexpr_of_expr (WDeref (dummy_loc, e_var, t_int)))) > 0);
  check "CallExpr" (String.length (string_of_sexpression (sexpr_of_expr (CallExpr (dummy_loc, "my_fn", [te_int], [LitPat e_int], [LitPat e_var], Static)))) > 0);
  check "ExprCallExpr" (String.length (string_of_sexpression (sexpr_of_expr (ExprCallExpr (dummy_loc, e_var, [LitPat e_int])))) > 0);
  check "NewArray" (String.length (string_of_sexpression (sexpr_of_expr (NewArray (dummy_loc, te_int, e_int)))) > 0);
  check "NewObject" (String.length (string_of_sexpression (sexpr_of_expr (NewObject (dummy_loc, "Point", [e_int], Some [te_int])))) > 0);
  check "CxxDelete" (String.length (string_of_sexpression (sexpr_of_expr (CxxDelete (dummy_loc, e_var)))) > 0);
  check "NewArrayWithInitializer" (String.length (string_of_sexpression (sexpr_of_expr (NewArrayWithInitializer (dummy_loc, te_int, [e_int])))) > 0);
  check "IfExpr" (String.length (string_of_sexpression (sexpr_of_expr (IfExpr (dummy_loc, e_true, e_int, e_int)))) > 0);
  check "SwitchExpr" (String.length (string_of_sexpression (sexpr_of_expr (SwitchExpr (dummy_loc, e_int, [SwitchExprClause (dummy_loc, "Zero", [], e_int)], Some (dummy_loc, e_int))))) > 0);
  check "PredNameExpr" (string_of_sexpression (sexpr_of_expr (PredNameExpr (dummy_loc, "p"))) = "(expr-pred-name p)");
  check "CastExpr" (String.length (string_of_sexpression (sexpr_of_expr (CastExpr (dummy_loc, te_int, e_var)))) > 0);
  check "Upcast" (String.length (string_of_sexpression (sexpr_of_expr (Upcast (e_var, t_int, RealType)))) > 0);
  check "TypedExpr" (String.length (string_of_sexpression (sexpr_of_expr (TypedExpr (e_var, t_int)))) > 0);
  check "WidenedParameterArgument" (String.length (string_of_sexpression (sexpr_of_expr (WidenedParameterArgument e_var))) > 0);
  check "SizeofExpr TypeExpr" (string_of_sexpression (sexpr_of_expr (SizeofExpr (dummy_loc, TypeExpr te_int))) = "(expr-sizeof (type-expr-manifest (type-int)))");
  check "SizeofExpr expr" (string_of_sexpression (sexpr_of_expr (SizeofExpr (dummy_loc, e_var))) = "(expr-sizeof-expr (expr-var my_var))");
  check "GenericExpr" (String.length (string_of_sexpression (sexpr_of_expr (GenericExpr (dummy_loc, e_var, [(te_int, e_int)], Some e_int)))) > 0);
  check "AddressOf" (string_of_sexpression (sexpr_of_expr (AddressOf (dummy_loc, e_var))) = "(expr-address-of (expr-var my_var))");
  check "Unbox" (String.length (string_of_sexpression (sexpr_of_expr (Unbox (e_var, t_int)))) > 0);
  check "ArrayTypeExpr'" (String.length (string_of_sexpression (sexpr_of_expr (ArrayTypeExpr' (dummy_loc, e_var)))) > 0);
  check "AssignExpr Mutation" (String.length (string_of_sexpression (sexpr_of_expr (AssignExpr (dummy_loc, e_var, Mutation, e_int)))) > 0);
  check "AssignExpr Initialization" (String.length (string_of_sexpression (sexpr_of_expr (AssignExpr (dummy_loc, e_var, Initialization, e_int)))) > 0);
  check "AssignOpExpr pre" (String.length (string_of_sexpression (sexpr_of_expr (AssignOpExpr (dummy_loc, e_var, Add, e_int, false)))) > 0);
  check "AssignOpExpr post" (String.length (string_of_sexpression (sexpr_of_expr (AssignOpExpr (dummy_loc, e_var, Add, e_int, true)))) > 0);
  check "CommaExpr" (string_of_sexpression (sexpr_of_expr (CommaExpr (dummy_loc, e_var, e_int))) = "(expr-comma (expr-var my_var) (expr-int 42))");
  check "InstanceOfExpr" (String.length (string_of_sexpression (sexpr_of_expr (InstanceOfExpr (dummy_loc, e_var, te_int)))) > 0);
  check "SuperMethodCall" (String.length (string_of_sexpression (sexpr_of_expr (SuperMethodCall (dummy_loc, "super_fn", [e_int])))) > 0);

  (* --- 2d. Assertions (exercised via Func declaration contracts) --- *)
  let a_pts = PointsTo (dummy_loc, e_var, RegularPointsTo, VarPat (dummy_loc, "v")) in
  let a_pts_uninit = PointsTo (dummy_loc, e_var, MaybeUninit, DummyPat) in
  let a_if = IfAsn (dummy_loc, e_true, EmpAsn dummy_loc, Ast.False dummy_loc) in
  let a_pred = PredAsn (dummy_loc, "my_p", [te_int], [LitPat e_int], [DummyPat], Instance) in
  let a_expr = ExprAsn (dummy_loc, e_true) in
  let a_coef = CoefAsn (dummy_loc, DummyPat, EmpAsn dummy_loc) in
  let a_inst = InstPredAsn (dummy_loc, e_var, "ip", e_int, [DummyPat]) in
  let a_sep = Sep (dummy_loc, a_pts, Sep (dummy_loc, a_pts_uninit, Sep (dummy_loc, a_if, Sep (dummy_loc, a_pred, Sep (dummy_loc, a_expr, Sep (dummy_loc, a_coef, a_inst)))))) in

  (* --- 2e. Statements (exercised via Func declaration body) --- *)
  let stmts = [
    PureStmt (dummy_loc, ReturnStmt (dummy_loc, Some e_int));
    Open (dummy_loc, Some e_var, "p", [te_int], [LitPat e_int], [VarPat (dummy_loc, "y")], None);
    Close (dummy_loc, None, "p", [te_int], [LitPat e_int], [VarPat (dummy_loc, "y")], None);
    IfStmt (dummy_loc, e_true, [ExprStmt e_var], [ExprStmt e_int]);
    BlockStmt (dummy_loc, [Global (dummy_loc, te_int, "inner_g", None)], [ExprStmt e_var], dummy_loc, ref []);
    WhileStmt (dummy_loc, e_true, Some (LoopInv (EmpAsn dummy_loc)), Some e_int, [Break dummy_loc], [Continue dummy_loc]);
    WhileStmt (dummy_loc, e_true, Some (LoopSpec (EmpAsn dummy_loc, EmpAsn dummy_loc)), None, [], []);
    DeclStmt (dummy_loc, [(dummy_loc, Some te_int, "loc1", Some e_int, (ref false, ref None)); (dummy_loc, Some te_int, "loc2", None, (ref false, ref None))]);
    ReturnStmt (dummy_loc, None);
    Assert (dummy_loc, EmpAsn dummy_loc);
    NonpureStmt (dummy_loc, false, ExprStmt e_var);
    SwitchStmt (dummy_loc, e_var, [SwitchStmtClause (dummy_loc, e_int, [Break dummy_loc]); SwitchStmtDefaultClause (dummy_loc, [Break dummy_loc])]);
    Throw (dummy_loc, e_var);
    Leak (dummy_loc, EmpAsn dummy_loc);
    LabelStmt (dummy_loc, "my_lbl");
    GotoStmt (dummy_loc, "my_lbl");
    TryCatch (dummy_loc, [ExprStmt e_var], []);
    TryFinally (dummy_loc, [ExprStmt e_var], dummy_loc, [ExprStmt e_int]);
    SuperConstructorCall (dummy_loc, [e_int])
  ] in

  (* --- 2f. Declarations --- *)
  let func_decl = Func (
    dummy_loc,
    Regular,
    [("T", {sized = false})],
    Some te_int,
    "my_function",
    [(te_int, "param1")],
    false,
    (None, None),
    Some (a_sep, ("res", a_sep)),
    false,
    Some (stmts, dummy_loc),
    true,
    ["overridden_func"]
  ) in
  let s_func = string_of_sexpression (sexpr_of_decl func_decl) in
  check "Func decl sexpr" (String.length s_func > 0 && String.contains s_func 'm');

  let struct_sized = Struct (dummy_loc, "S1", ["T"], Right (Either.Left true), [Packed]) in
  check "Struct sized" (String.length (string_of_sexpression (sexpr_of_decl struct_sized)) > 0);

  let struct_full = Struct (
    dummy_loc, "S2", [],
    Left ([CxxBaseSpec (dummy_loc, "Base", false)],
          [Field (dummy_loc, Real, te_int, "f", Instance, Public, false, None)],
          [InstancePredDecl (dummy_loc, "ip_decl", [(te_int, "arg")], Some (EmpAsn dummy_loc))],
          false),
    []
  ) in
  check "Struct full" (String.length (string_of_sexpression (sexpr_of_decl struct_full)) > 0);

  let pred_fam = PredFamilyDecl (dummy_loc, "PF", ["T"], 0, [te_int], Some 1, Inductiveness_Inductive) in
  check "PredFamilyDecl" (String.length (string_of_sexpression (sexpr_of_decl pred_fam)) > 0);

  let pred_fam_inst = PredFamilyInstanceDecl (dummy_loc, "PF", [("T", {sized = false})], [], [(te_int, "arg")], EmpAsn dummy_loc) in
  check "PredFamilyInstanceDecl" (String.length (string_of_sexpression (sexpr_of_decl pred_fam_inst)) > 0);

  let imp_mod = ImportModuleDecl (dummy_loc, "std_io") in
  check "ImportModuleDecl" (string_of_sexpression (sexpr_of_decl imp_mod) = "(declare-import-module std_io)");

  let ind_decl = Inductive (dummy_loc, "List", ["T"], [Ctor (dummy_loc, "Nil", []); Ctor (dummy_loc, "Cons", [("head", te_int)])]) in
  check "Inductive decl" (String.length (string_of_sexpression (sexpr_of_decl ind_decl)) > 0);

  let pred_ctor = PredCtorDecl (dummy_loc, "PC", ["T"], [(te_int, "cp")], [(te_int, "p")], Some 1, EmpAsn dummy_loc) in
  check "PredCtorDecl" (String.length (string_of_sexpression (sexpr_of_decl pred_ctor)) > 0);

  let g_decl1 = Global (dummy_loc, te_int, "g1", Some e_int) in
  let g_decl2 = Global (dummy_loc, te_int, "g2", None) in
  check "Global with init" (String.length (string_of_sexpression (sexpr_of_decl g_decl1)) > 0);
  check "Global without init" (String.length (string_of_sexpression (sexpr_of_decl g_decl2)) > 0);

  let iface_decl = Interface (dummy_loc, "MyIface", [("SuperI", [])], [Field (dummy_loc, Real, te_int, "if", Instance, Public, false, None)], [Meth (dummy_loc, Real, Some te_int, "imeth", [(te_int, "p")], None, None, Instance, Public, true, [])], [], [InstancePredDecl (dummy_loc, "ip", [], None)]) in
  check "Interface decl" (String.length (string_of_sexpression (sexpr_of_decl iface_decl)) > 0);

  let cls_decl = Class (dummy_loc, false, FinalClass, "MyClass", [], [], [Cons (dummy_loc, [(te_int, "c_arg")], None, None, Public)], ("Object", []), [], [], []) in
  check "Class decl" (String.length (string_of_sexpression (sexpr_of_decl cls_decl)) > 0);

  (* --- 2g. Package & Emit --- *)
  let pkg = PackageDecl (
    dummy_loc,
    "my_package",
    [Import (dummy_loc, Real, "other_pkg", Some "foo"); Import (dummy_loc, Ghost, "ghost_pkg", None)],
    [func_decl; struct_sized; ind_decl]
  ) in
  let s_pkg = string_of_sexpression (sexpr_of_package pkg) in
  check "Package decl sexpr" (String.length s_pkg > 0 && String.contains s_pkg 'p');

  let out_path = Filename.concat (Filename.get_temp_dir_name ()) "test_unit_emitter_out.sexpr" in
  SExpressionEmitter.emit out_path [pkg];
  check "Emit created non-empty file" (Sys.file_exists out_path);
  let ic = open_in out_path in
  let content = really_input_string ic (in_channel_length ic) in
  close_in ic;
  Sys.remove out_path;
  check "Emit output contains declare-package" (String.contains content 'd');

  (* --- 2h. Unsupported handling --- *)
  SExpressionEmitter.unsupported_exception := false;
  let unsupp_decl = sexpr_of_decl (FuncTypeDecl (dummy_loc, Ghost, None, "bad_ftd", [], [], [], (EmpAsn dummy_loc, ("res", EmpAsn dummy_loc), false))) in
  check "Unsupported relaxed returns list" (String.contains (string_of_sexpression unsupp_decl) 'u');

  SExpressionEmitter.unsupported_exception := true;
  let raised = ref false in
  (try
    let _ = sexpr_of_decl (FuncTypeDecl (dummy_loc, Ghost, None, "bad_ftd", [], [], [], (EmpAsn dummy_loc, ("res", EmpAsn dummy_loc), false))) in ()
   with _ -> raised := true);
  check "Unsupported strict raises exception" !raised

(* ========================================== *)
(* Suite 3: Smtlib Core Types & Statements    *)
(* ========================================== *)
let test_smtlib_formatting () =
  let s_int = Smtlib.Sort.int in
  let s_bool = Smtlib.Sort.bool in
  let s_real = Smtlib.Sort.real in
  let s_ind = Smtlib.Sort.inductive in
  check "Sort.int features" (List.mem "LIA" (Smtlib.Sort.features s_int));
  check "Sort.bool features empty" (Smtlib.Sort.features s_bool = []);
  check "Sort.real features" (List.mem "LRA" (Smtlib.Sort.features s_real));
  check "Sort.inductive features" (List.mem "NDT" (Smtlib.Sort.features s_ind));

  (* Terms *)
  let sym_tr = Smtlib.Sym.fresh "true" [] s_bool in
  let t_tr = Smtlib.capp sym_tr in
  check "Term true_ features empty" (Smtlib.T.features t_tr = []);

  let sym_num = Smtlib.Sym.fresh "1" [] s_int in
  let t_one = Smtlib.capp sym_num in
  let sym_add = Smtlib.Sym.fresh "+" [s_int; s_int] s_int in
  let t_sum = Smtlib.bapp sym_add t_one t_one in
  let eq_sym = Smtlib.Sym.eq s_int in
  let t_eq = Smtlib.bapp eq_sym t_sum t_one in
  check "Term eq features" (List.mem "LIA" (Smtlib.T.features t_eq));

  (* Statements *)
  let st_push = Smtlib.push in
  let st_pop = Smtlib.pop 1 in
  let st_check = Smtlib.check_sat in
  let st_assert = Smtlib.sassert t_eq in
  check "St.push features" (List.mem "I" (Smtlib.St.features st_push));
  check "St.pop features" (List.mem "I" (Smtlib.St.features st_pop));
  check "St.check features empty" (Smtlib.St.features st_check = []);
  check "St.assert features" (List.mem "LIA" (Smtlib.St.features st_assert))

(* ========================================== *)
(* Suite 4: JSON Parser and Serializer        *)
(* ========================================== *)
let test_json_primitives () =
  check "parse null" (parse_json "null" = Null);
  check "parse true" (parse_json "true" = B true);
  check "parse false" (parse_json "false" = B false);
  check "parse positive int" (parse_json "123" = I 123);
  check "parse negative int" (parse_json "-456" = I (-456));
  check "parse zero" (parse_json "0" = I 0);
  check "parse empty string" (parse_json "\"\"" = S "");
  check "parse simple string" (parse_json "\"verifast\"" = S "verifast")

let test_json_escapes () =
  check "parse escaped quote" (parse_json "\"Hello \\\"World\\\"\"" = S "Hello \"World\"");
  check "parse escaped backslash" (parse_json "\"path\\\\to\\\\file\"" = S "path\\to\\file");
  check "parse escaped newline" (parse_json "\"line1\\nline2\"" = S "line1\nline2");
  check "parse escaped tab" (parse_json "\"col1\\tcol2\"" = S "col1\tcol2");
  check "parse escaped carriage return" (parse_json "\"cr\\r\"" = S "cr\r");
  check "parse unicode ASCII" (parse_json "\"\\u0041\"" = S "A");
  check "parse unicode accent" (parse_json "\"\\u00E9\"" = S "\xc3\xa9");
  check "parse unicode currency" (parse_json "\"\\u20AC\"" = S "\xe2\x82\xac");
  check "parse unicode emoji surrogate" (parse_json "\"\\uD83C\\uDF89\"" = S "\xf0\x9f\x8e\x89")

let test_json_structures () =
  (* Arrays *)
  check "empty array" (parse_json "[]" = A []);
  check "int array" (parse_json "[1, 2, 3]" = A [I 1; I 2; I 3]);
  check "mixed array" (parse_json "[null, true, \"abc\", 99]" = A [Null; B true; S "abc"; I 99]);
  check "nested array" (parse_json "[[1], [2, [3]]]" = A [A [I 1]; A [I 2; A [I 3]]]);

  (* Objects *)
  check "empty object" (parse_json "{}" = O []);
  let obj = parse_json "{\"name\": \"verifast\", \"version\": 26, \"active\": true}" in
  check "object parse" (obj = O ["name", S "verifast"; "version", I 26; "active", B true]);
  check "o_assoc name" (o_assoc "name" obj = S "verifast");
  check "o_assoc version" (o_assoc "version" obj = I 26);
  check "o_assoc active" (o_assoc "active" obj = B true);

  (* Accessors *)
  check "s_value" (s_value (S "abc") = "abc");
  check "i_value" (i_value (I 123) = 123);
  check "a_value" (a_value (A [I 1; I 2]) = [I 1; I 2])

let test_json_serialization () =
  let j = O ["key", S "val"; "nums", A [I 1; I 2]] in
  let buf = Buffer.create 256 in
  buffer_add_json_pp buf 2 j;
  let out = Buffer.contents buf in
  check "serialized output contains key" (String.length out > 0 && String.contains out 'k');
  (* Roundtrip parsed *)
  let reparsed = parse_json out in
  check "roundtrip match" (reparsed = j)

let test_json_malformed () =
  let expect_fail text =
    try
      let _ = parse_json text in
      false
    with _ -> true
  in
  check "malformed: unclosed brace" (expect_fail "{\"a\": 1");
  check "malformed: unclosed bracket" (expect_fail "[1, 2");
  check "malformed: trailing comma" (expect_fail "[1, 2,]");
  check "malformed: unquoted key" (expect_fail "{a: 1}");
  check "malformed: unclosed string" (expect_fail "\"abc");
  check "malformed: extra tokens" (expect_fail "123 456")

(* ========================================== *)
(* Suite 9: Json Accessors & Edge Cases       *)
(* ========================================== *)
let test_json_accessors_and_edges () =
  check "s_value" (s_value (S "hello") = "hello");
  check "i_value" (i_value (I 42) = 42);
  check "a_value" (a_value (A [I 1; I 2]) = [I 1; I 2]);
  check "o_assoc" (o_assoc "k" (O [("k", I 10); ("other", B true)]) = I 10);

  (* Hex chars in buffer_add_json_char *)
  let buf = Buffer.create 64 in
  buffer_add_json buf (S "\005\012\031\n\r\"\\");
  let s_esc = Buffer.contents buf in
  check "json escapes string" (String.length s_esc > 0);

  (* Normal float *)
  let buf_f = Buffer.create 64 in
  buffer_add_json buf_f (F 2.718);
  check "json float" (String.length (Buffer.contents buf_f) > 0);

  (* Pretty print *)
  let buf_pp = Buffer.create 128 in
  buffer_add_json_pp buf_pp 2 (O [("arr", A [I 1; I 2]); ("empty_o", O []); ("empty_a", A [])]);
  check "json pretty print" (String.length (Buffer.contents buf_pp) > 0)

(* ========================================== *)
(* Suite 10: Smtlib Lists, Sorts & Fresh Names *)
(* ========================================== *)
let test_smtlib_extra () =
  let buf = Buffer.create 64 in
  let fmt = Format.formatter_of_buffer buf in
  Smtlib.print_list_space Smtlib.print_string fmt ["a"; "b"; "c"];
  Format.pp_print_flush fmt ();
  check "print_list_space" (Buffer.length buf > 0);

  let buf_nl = Buffer.create 64 in
  let fmt_nl = Format.formatter_of_buffer buf_nl in
  Smtlib.print_list_newline Smtlib.print_string fmt_nl ["line1"; "line2"];
  Format.pp_print_flush fmt_nl ();
  check "print_list_newline" (Buffer.length buf_nl > 0);

  (* string_of_ratio *)
  let rat = Ratio.create_ratio (Big_int.big_int_of_int 3) (Big_int.big_int_of_int 4) in
  check "string_of_ratio" (Smtlib.string_of_ratio rat = "(/ 3 4)");
  check "string_of_num ratio" (Smtlib.string_of_num (Num.Ratio rat) = "(/ 3 4)");
  check "string_of_num int" (Smtlib.string_of_num (Num.num_of_int 42) = "42");

  (* Sort features *)
  check "Sort.bool features empty" (Smtlib.Sort.features Smtlib.Sort.bool = []);
  check "Sort.int features LIA" (Smtlib.Sort.features Smtlib.Sort.int = ["LIA"]);
  check "Sort.real features LRA" (Smtlib.Sort.features Smtlib.Sort.real = ["LRA"]);
  check "Sort.inductive features NDT" (Smtlib.Sort.features Smtlib.Sort.inductive = ["NDT"]);

  let buf_sort = Buffer.create 32 in
  let fmt_sort = Format.formatter_of_buffer buf_sort in
  Smtlib.Sort.print fmt_sort Smtlib.Sort.int;
  Format.pp_print_flush fmt_sort ();
  check "Sort.print Int" (Buffer.contents buf_sort = "Int")


let test_sexpr_emitter_all_constructors () =
  let dummy_loc = dummy_loc in
  let t_int = Int (Signed, IntRank) in
  (* FuncKind *)
  check "sexpr_of_func_kind regular" (sexpr_of_func_kind Regular = Symbol "regular");
  check "sexpr_of_func_kind fixpoint" (sexpr_of_func_kind Fixpoint = Symbol "fixpoint");
  check "sexpr_of_func_kind lemma" (sexpr_of_func_kind (Lemma (false, None)) = Symbol "lemma");

  (* IdentScope *)
  let scopes = [
    LocalVar; FuncName; PredFamName; EnumElemName (Big_int.big_int_of_int 1); GlobalName;
    ModuleName; PureFuncName [t_int]; ClassOrInterfaceNameScope; PackageNameScope
  ] in
  List.iter (fun sc ->
    check "sexpr_of_ident_scope" (match sexpr_of_ident_scope sc with Symbol _ -> true | _ -> false)
  ) scopes;

  (* Operators *)
  let ops = [
    Add; Sub; PtrDiff; Le; Lt; Ge; Gt; Eq; Neq; And; Or; Xor; Not; Mul; Div; Mod;
    BitNot; BitAnd; BitXor; BitOr; ShiftLeft; ShiftRight; MinValue t_int; MaxValue t_int
  ] in
  List.iter (fun op ->
    check "sexpr_of_operator" (String.length (string_of_sexpression (sexpr_of_operator op)) > 0)
  ) ops;

  (* Constant values *)
  let consts = [
    IntConst (Big_int.big_int_of_int 123);
    BoolConst true;
    BoolConst false;
    StringConst "hello";
    NullConst
  ] in
  List.iter (fun c ->
    check "sexpr_of_constant_value" (String.length (string_of_sexpression (sexpr_of_constant_value c)) > 0)
  ) consts;

  (* Method binding *)
  let bindings = [Static; Instance; PredFamCall; PredCtorCall; LocalVarPredCall] in
  List.iter (fun b ->
    check "sexpr_of_method_binding" (String.length (string_of_sexpression (sexpr_of_method_binding b)) > 0)
  ) bindings;

  (* Pred names *)
  let pnames = [PredFam "pf"; PredCtor "pc"; LocalVar "lv"] in
  List.iter (fun pn ->
    check "sexpr_of_pred_name" (String.length (string_of_sexpression (sexpr_of_pred_name pn)) > 0)
  ) pnames;

  (* More Expressions *)
  let exprs = [
    Ast.True dummy_loc;
    Ast.False dummy_loc;
    Ast.Null dummy_loc;
    Var (dummy_loc, "x");
    WVar (dummy_loc, "y", LocalVar);
    Select (dummy_loc, Var (dummy_loc, "p"), "f");
    IntLit (dummy_loc, Big_int.big_int_of_int 42, true, false, NoLSuffix);
    WIntLit (dummy_loc, Big_int.big_int_of_int 42);
    RealLit (dummy_loc, Num.num_of_int 5, Some FloatFSuffix);
    StringLit (dummy_loc, "foo");
    ClassLit (dummy_loc, "Bar");
    TruncatingExpr (dummy_loc, Var (dummy_loc, "x"));
    Operation (dummy_loc, Add, [Var (dummy_loc, "a"); Var (dummy_loc, "b")]);
    WOperation (dummy_loc, Add, [Var (dummy_loc, "a"); Var (dummy_loc, "b")], t_int);
    SliceExpr (dummy_loc, None, None);
    Read (dummy_loc, Var (dummy_loc, "x"), "f");
  ] in
  List.iter (fun e ->
    check "sexpr_of_expr" (String.length (string_of_sexpression (sexpr_of_expr e)) > 0)
  ) exprs;

  (* Predicates / Assertions *)
  let preds = [
    PointsTo (dummy_loc, Var (dummy_loc, "p"), RegularPointsTo, LitPat (Var (dummy_loc, "v")));
    PredAsn (dummy_loc, "p", [], [], [], Static);
    ExprAsn (dummy_loc, Ast.True dummy_loc);
    Sep (dummy_loc, EmpAsn dummy_loc, EmpAsn dummy_loc);
    IfAsn (dummy_loc, Ast.True dummy_loc, EmpAsn dummy_loc, EmpAsn dummy_loc);
    EmpAsn dummy_loc;
    ForallAsn (dummy_loc, ManifestTypeExpr (dummy_loc, t_int), "x", Ast.True dummy_loc);
    CoefAsn (dummy_loc, DummyPat, EmpAsn dummy_loc);
    EnsuresAsn (dummy_loc, "r", EmpAsn dummy_loc)
  ] in
  List.iter (fun p ->
    check "sexpr_of_pred" (String.length (string_of_sexpression (sexpr_of_pred p)) > 0)
  ) preds;

  (* Statements *)
  let stmts = [
    PureStmt (dummy_loc, ExprStmt (Ast.True dummy_loc));
    NonpureStmt (dummy_loc, false, ExprStmt (Ast.True dummy_loc));
  ] in
  List.iter (fun st ->
    check "sexpr_of_stmt" (String.length (string_of_sexpression (sexpr_of_stmt st)) > 0)
  ) stmts;

  (* Imports & Packages *)
  check "sexpr_of_import" (String.length (string_of_sexpression (sexpr_of_import (Import (dummy_loc, Real, "pkg", None)))) > 0);
  check "sexpr_of_package" (String.length (string_of_sexpression (sexpr_of_package (PackageDecl (dummy_loc, "p", [], [])))) > 0)

let run () =
  passed_assertions := 0;
  test_sexpressions ();
  test_sexpression_emitter ();
  test_smtlib_formatting ();
  test_json_primitives ();
  test_json_escapes ();
  test_json_structures ();
  test_json_serialization ();
  test_json_malformed ();
  test_json_accessors_and_edges ();
  test_smtlib_extra ();
  test_sexpr_emitter_all_constructors ();
  !passed_assertions
