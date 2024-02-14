[
  PackageDecl (l, "", [], [
    Struct (l, "CellU32", [], Some (([], [Field (l, Real, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))), "v", Instance, Public, true, None)], [], false)), []);
    TypedefDecl (l, StructTypeExpr (l, Some ("CellU32"), None, [], []), "CellU32", []);
    PredCtorDecl (l, "CellU32_full_borrow_content", [], [(IdentTypeExpr (l, None, "thread_id_t"), "tid"); (ManifestTypeExpr (l, PtrType (StructType ("CellU32", []))), "l")], [], None, Sep (l, PointsTo (l, Read (l, Var (l, "l"), "v"), VarPat (l, "v")), Sep (l, CallExpr (l, "struct_CellU32_padding", [], [], [LitPat (Var (l, "l"))], Static), CallExpr (l, "CellU32_own", [], [], [LitPat (Var (l, "tid")); LitPat (Var (l, "v"))], Static))));
    Func (l, Lemma (false, None), [], None, "CellU32_share_mono", [(IdentTypeExpr (l, None, "lifetime_t"), "k"); (IdentTypeExpr (l, None, "lifetime_t"), "k1"); (IdentTypeExpr (l, None, "thread_id_t"), "t"); (ManifestTypeExpr (l, PtrType (Void)), "l")], false, None, Some ((Sep (l, Operation (l, Eq, [
      CallExpr (l, "lifetime_inclusion", [], [], [LitPat (Var (l, "k1")); LitPat (Var (l, "k"))], Static);
      True (l)
    ]), CoefAsn (l, DummyPat, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "k")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static))), CoefAsn (l, DummyPat, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "k1")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static)))), false, None, false, []);
    Func (l, Lemma (false, None), [], None, "CellU32_share_full", [(IdentTypeExpr (l, None, "lifetime_t"), "k"); (IdentTypeExpr (l, None, "thread_id_t"), "t"); (ManifestTypeExpr (l, PtrType (Void)), "l")], false, None, Some ((Sep (l, CallExpr (l, "full_borrow", [], [], [
      LitPat (Var (l, "k"));
      LitPat (CallExpr (l, "CellU32_full_borrow_content", [], [], [LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static))
    ], Static), CoefAsn (l, VarPat (l, "q"), CallExpr (l, "lifetime_token", [], [], [LitPat (Var (l, "k"))], Static))), Sep (l, CoefAsn (l, DummyPat, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "k")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static)), CoefAsn (l, LitPat (Var (l, "q")), CallExpr (l, "lifetime_token", [], [], [LitPat (Var (l, "k"))], Static))))), false, None, false, []);
    PredFamilyDecl (l, "CellU32_own", [], 0, [IdentTypeExpr (l, None, "thread_id_t"); ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))], Some (2), Inductiveness_Inductive);
    PredFamilyInstanceDecl (l, "CellU32_own", [], [], [(IdentTypeExpr (l, None, "thread_id_t"), "t"); (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))), "v")], True (l));
    PredCtorDecl (l, "CellU32_nonatomic_borrow_content", [], [(PtrTypeExpr (l, IdentTypeExpr (l, None, "CellU32")), "l"); (IdentTypeExpr (l, None, "thread_id_t"), "t")], [], Some (0), Sep (l, CallExpr (l, "CellU32_v", [], [], [LitPat (Var (l, "l")); VarPat (l, "v")], Static), Sep (l, CallExpr (l, "struct_CellU32_padding", [], [], [LitPat (Var (l, "l"))], Static), CallExpr (l, "CellU32_own", [], [], [LitPat (Var (l, "t")); LitPat (Var (l, "v"))], Static))));
    PredFamilyDecl (l, "CellU32_share", [], 0, [IdentTypeExpr (l, None, "lifetime_t"); IdentTypeExpr (l, None, "thread_id_t"); PtrTypeExpr (l, IdentTypeExpr (l, None, "CellU32"))], None, Inductiveness_Inductive);
    PredFamilyInstanceDecl (l, "CellU32_share", [], [], [(IdentTypeExpr (l, None, "lifetime_t"), "k"); (IdentTypeExpr (l, None, "thread_id_t"), "t"); (PtrTypeExpr (l, IdentTypeExpr (l, None, "CellU32")), "l")], CoefAsn (l, DummyPat, CallExpr (l, "nonatomic_borrow", [], [], [
      LitPat (Var (l, "k"));
      LitPat (Var (l, "t"));
      LitPat (CallExpr (l, "MaskNshrSingle", [], [], [LitPat (Var (l, "l"))], Static));
      LitPat (CallExpr (l, "CellU32_nonatomic_borrow_content", [], [], [LitPat (Var (l, "l")); LitPat (Var (l, "t"))], Static))
    ], Static)));
    Func (l, Lemma (false, None), [], None, "CellU32_share_mono", [(IdentTypeExpr (l, None, "lifetime_t"), "k"); (IdentTypeExpr (l, None, "lifetime_t"), "k1"); (IdentTypeExpr (l, None, "thread_id_t"), "t"); (PtrTypeExpr (l, IdentTypeExpr (l, None, "CellU32")), "l")], false, None, Some ((Sep (l, Operation (l, Eq, [
      CallExpr (l, "lifetime_inclusion", [], [], [LitPat (Var (l, "k1")); LitPat (Var (l, "k"))], Static);
      True (l)
    ]), CoefAsn (l, DummyPat, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "k")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static))), CoefAsn (l, DummyPat, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "k1")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static)))), false, Some (([
      Open (l, None, "CellU32_share", [], [], [LitPat (Var (l, "k")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], None);
      Assert (l, CoefAsn (l, DummyPat, CallExpr (l, "nonatomic_borrow", [], [], [LitPat (Var (l, "k")); LitPat (Var (l, "t")); VarPat (l, "m"); DummyPat], Static)));
      ExprStmt (CallExpr (l, "nonatomic_borrow_mono", [], [], [
        LitPat (Var (l, "k"));
        LitPat (Var (l, "k1"));
        LitPat (Var (l, "t"));
        LitPat (Var (l, "m"));
        LitPat (CallExpr (l, "CellU32_nonatomic_borrow_content", [], [], [LitPat (Var (l, "l")); LitPat (Var (l, "t"))], Static))
      ], Static));
      Close (l, None, "CellU32_share", [], [], [LitPat (Var (l, "k1")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], None);
      Leak (l, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "k1")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static))
    ], l)), false, []);
    Func (l, Lemma (false, None), [], None, "CellU32_share_full", [(IdentTypeExpr (l, None, "lifetime_t"), "k"); (IdentTypeExpr (l, None, "thread_id_t"), "t"); (PtrTypeExpr (l, IdentTypeExpr (l, None, "CellU32")), "l")], false, None, Some ((Sep (l, CallExpr (l, "full_borrow", [], [], [
      LitPat (Var (l, "k"));
      LitPat (CallExpr (l, "CellU32_full_borrow_content", [], [], [LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static))
    ], Static), CoefAsn (l, VarPat (l, "q"), CallExpr (l, "lifetime_token", [], [], [LitPat (Var (l, "k"))], Static))), Sep (l, CoefAsn (l, DummyPat, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "k")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static)), CoefAsn (l, LitPat (Var (l, "q")), CallExpr (l, "lifetime_token", [], [], [LitPat (Var (l, "k"))], Static))))), false, Some (([
      ProduceLemmaFunctionPointerChunkStmt (l, None, Some (("implies", [], [
        CallExpr (l, "CellU32_full_borrow_content", [], [], [LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static);
        CallExpr (l, "CellU32_nonatomic_borrow_content", [], [], [LitPat (Var (l, "l")); LitPat (Var (l, "t"))], Static)
      ], [], l, [
        Open (l, None, "CellU32_full_borrow_content", [], [LitPat (Var (l, "t")); LitPat (Var (l, "l"))], [], None);
        Close (l, None, "CellU32_nonatomic_borrow_content", [], [LitPat (Var (l, "l")); LitPat (Var (l, "t"))], [], None)
      ], l)), Some (BlockStmt (l, [], [
        ProduceLemmaFunctionPointerChunkStmt (l, None, Some (("implies", [], [
          CallExpr (l, "CellU32_nonatomic_borrow_content", [], [], [LitPat (Var (l, "l")); LitPat (Var (l, "t"))], Static);
          CallExpr (l, "CellU32_full_borrow_content", [], [], [LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static)
        ], [], l, [
          Open (l, None, "CellU32_nonatomic_borrow_content", [], [LitPat (Var (l, "l")); LitPat (Var (l, "t"))], [], None);
          Close (l, None, "CellU32_full_borrow_content", [], [LitPat (Var (l, "t")); LitPat (Var (l, "l"))], [], None)
        ], l)), Some (BlockStmt (l, [], [
          ExprStmt (CallExpr (l, "full_borrow_implies", [], [], [
            LitPat (Var (l, "k"));
            LitPat (CallExpr (l, "CellU32_full_borrow_content", [], [], [LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static));
            LitPat (CallExpr (l, "CellU32_nonatomic_borrow_content", [], [], [LitPat (Var (l, "l")); LitPat (Var (l, "t"))], Static))
          ], Static))
        ], l, ref ([]))))
      ], l, ref ([]))));
      ExprStmt (CallExpr (l, "full_borrow_into_nonatomic_borrow", [], [], [
        LitPat (Var (l, "k"));
        LitPat (Var (l, "t"));
        LitPat (CallExpr (l, "MaskNshrSingle", [], [], [LitPat (Var (l, "l"))], Static));
        LitPat (CallExpr (l, "CellU32_nonatomic_borrow_content", [], [], [LitPat (Var (l, "l")); LitPat (Var (l, "t"))], Static))
      ], Static));
      Close (l, None, "CellU32_share", [], [], [LitPat (Var (l, "k")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], None);
      Leak (l, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "k")); LitPat (Var (l, "t")); LitPat (Var (l, "l"))], Static))
    ], l)), false, []);
    Func (l, Regular, [], Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "CellU32::set", [(PtrTypeExpr (l, StructTypeExpr (l, Some ("CellU32"), None, [], [])), "self"); (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))), "u")], false, None, Some ((Sep (l, CallExpr (l, "thread_token", [], [], [VarPat (l, "_t")], Static), Sep (l, CoefAsn (l, VarPat (l, "_q_a"), CallExpr (l, "lifetime_token", [], [], [VarPat (l, "a")], Static)), CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); LitPat (Var (l, "self"))], Static))), Sep (l, CallExpr (l, "thread_token", [], [], [LitPat (Var (l, "_t"))], Static), Sep (l, CoefAsn (l, LitPat (Var (l, "_q_a")), CallExpr (l, "lifetime_token", [], [], [LitPat (Var (l, "a"))], Static)), True (l))))), false, None, false, []);
    Func (l, Regular, [], Some (StructTypeExpr (l, Some ("CellU32"), None, [], [])), "CellU32::new", [(ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))), "u")], false, None, Some ((CallExpr (l, "thread_token", [], [], [VarPat (l, "_t")], Static), Sep (l, CallExpr (l, "thread_token", [], [], [LitPat (Var (l, "_t"))], Static), CallExpr (l, "CellU32_own", [], [], [LitPat (Var (l, "_t")); LitPat (Var (l, "result"))], Static)))), false, Some (([
      DeclStmt (l, [(l, Some (StructTypeExpr (l, Some ("CellU32"), None, [], [])), "$_0", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (StructTypeExpr (l, Some ("CellU32"), None, [], [])), "c", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "$_3", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "$_4", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_5", None, (ref (false), ref (None)))]);
      LabelStmt (l, "bb0");
      ExprStmt (AssignExpr (l, Var (l, "$_4"), Var (l, "u")));
      ExprStmt (AssignExpr (l, Var (l, "$_3"), Var (l, "$_4")));
      GotoStmt (l, "bb1");
      LabelStmt (l, "bb1");
      BlockStmt (l, [], [ExprStmt (AssignExpr (l, Select (l, Var (l, "c"), "v"), Var (l, "$_3")))], l, ref ([]));
      PureStmt (l, Close (l, None, "CellU32_own", [], [], [LitPat (Var (l, "_t")); LitPat (Var (l, "u"))], None));
      GotoStmt (l, "bb2");
      LabelStmt (l, "bb2");
      ExprStmt (AssignExpr (l, Var (l, "$_0"), Var (l, "c")));
      ReturnStmt (l, Some (Var (l, "$_0")))
    ], l)), false, []);
    Func (l, Regular, [], Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "CellU32::get", [(PtrTypeExpr (l, StructTypeExpr (l, Some ("CellU32"), None, [], [])), "self")], false, None, Some ((Sep (l, CallExpr (l, "thread_token", [], [], [VarPat (l, "_t")], Static), Sep (l, CoefAsn (l, VarPat (l, "_q_a"), CallExpr (l, "lifetime_token", [], [], [VarPat (l, "a")], Static)), CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); LitPat (Var (l, "self"))], Static))), Sep (l, CallExpr (l, "thread_token", [], [], [LitPat (Var (l, "_t"))], Static), Sep (l, CoefAsn (l, LitPat (Var (l, "_q_a")), CallExpr (l, "lifetime_token", [], [], [LitPat (Var (l, "a"))], Static)), True (l))))), false, Some (([
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "$_0", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_2", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_3", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_4", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_5", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_6", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "v", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))))), "$_8", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))))), "$_9", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_10", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_11", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_12", None, (ref (false), ref (None)))]);
      LabelStmt (l, "bb0");
      PureStmt (l, Open (l, None, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); LitPat (Var (l, "self"))], None));
      GotoStmt (l, "bb1");
      LabelStmt (l, "bb1");
      PureStmt (l, Assert (l, CoefAsn (l, DummyPat, CallExpr (l, "nonatomic_borrow", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); VarPat (l, "_m"); DummyPat], Static))));
      GotoStmt (l, "bb2");
      LabelStmt (l, "bb2");
      PureStmt (l, Open (l, None, "thread_token", [], [], [LitPat (Var (l, "_t"))], None));
      GotoStmt (l, "bb3");
      LabelStmt (l, "bb3");
      PureStmt (l, ExprStmt (CallExpr (l, "thread_token_split", [], [], [LitPat (Var (l, "_t")); LitPat (Var (l, "MaskTop")); LitPat (Var (l, "_m"))], Static)));
      GotoStmt (l, "bb4");
      LabelStmt (l, "bb4");
      PureStmt (l, ExprStmt (CallExpr (l, "open_nonatomic_borrow", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); LitPat (Var (l, "_m")); LitPat (Var (l, "_q_a"))], Static)));
      GotoStmt (l, "bb5");
      LabelStmt (l, "bb5");
      ExprStmt (AssignExpr (l, Var (l, "$_9"), AddressOf (l, Select (l, Deref (l, Var (l, "self")), "v"))));
      ExprStmt (AssignExpr (l, Var (l, "$_8"), Var (l, "$_9")));
      GotoStmt (l, "bb6");
      LabelStmt (l, "bb6");
      ExprStmt (AssignExpr (l, Var (l, "v"), Deref (l, Var (l, "$_8"))));
      PureStmt (l, ExprStmt (CallExpr (l, "close_nonatomic_borrow", [], [], [], Static)));
      GotoStmt (l, "bb7");
      LabelStmt (l, "bb7");
      PureStmt (l, ExprStmt (CallExpr (l, "thread_token_merge", [], [], [
        LitPat (Var (l, "_t"));
        LitPat (CallExpr (l, "mask_diff", [], [], [LitPat (Var (l, "MaskTop")); LitPat (Var (l, "_m"))], Static));
        LitPat (Var (l, "_m"))
      ], Static)));
      GotoStmt (l, "bb8");
      LabelStmt (l, "bb8");
      PureStmt (l, Close (l, None, "thread_token", [], [], [LitPat (Var (l, "_t"))], None));
      GotoStmt (l, "bb9");
      LabelStmt (l, "bb9");
      ExprStmt (AssignExpr (l, Var (l, "$_0"), Var (l, "v")));
      ReturnStmt (l, Some (Var (l, "$_0")))
    ], l)), false, []);
    Func (l, Regular, [], Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "CellU32::set", [(PtrTypeExpr (l, StructTypeExpr (l, Some ("CellU32"), None, [], [])), "self"); (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))), "u")], false, None, Some ((Sep (l, CallExpr (l, "thread_token", [], [], [VarPat (l, "t")], Static), Sep (l, CoefAsn (l, VarPat (l, "q"), CallExpr (l, "lifetime_token", [], [], [VarPat (l, "a")], Static)), CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "t")); LitPat (Var (l, "self"))], Static))), Sep (l, CallExpr (l, "thread_token", [], [], [LitPat (Var (l, "t"))], Static), CoefAsn (l, LitPat (Var (l, "q")), CallExpr (l, "lifetime_token", [], [], [LitPat (Var (l, "a"))], Static))))), false, Some (([
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_0", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))))), "p", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))))), "$_4", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_5", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_6", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_7", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_8", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_9", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_10", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "$_11", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_12", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_13", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_14", None, (ref (false), ref (None)))]);
      LabelStmt (l, "bb0");
      ExprStmt (AssignExpr (l, Var (l, "$_4"), AddressOf (l, Select (l, Deref (l, Var (l, "self")), "v"))));
      ExprStmt (AssignExpr (l, Var (l, "p"), Var (l, "$_4")));
      GotoStmt (l, "bb1");
      LabelStmt (l, "bb1");
      PureStmt (l, Open (l, None, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "t")); LitPat (Var (l, "self"))], None));
      GotoStmt (l, "bb2");
      LabelStmt (l, "bb2");
      PureStmt (l, Assert (l, CoefAsn (l, DummyPat, CallExpr (l, "nonatomic_borrow", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "t")); VarPat (l, "m"); DummyPat], Static))));
      GotoStmt (l, "bb3");
      LabelStmt (l, "bb3");
      PureStmt (l, Open (l, None, "thread_token", [], [], [LitPat (Var (l, "t"))], None));
      GotoStmt (l, "bb4");
      LabelStmt (l, "bb4");
      PureStmt (l, ExprStmt (CallExpr (l, "thread_token_split", [], [], [LitPat (Var (l, "t")); LitPat (Var (l, "MaskTop")); LitPat (Var (l, "m"))], Static)));
      GotoStmt (l, "bb5");
      LabelStmt (l, "bb5");
      PureStmt (l, ExprStmt (CallExpr (l, "open_nonatomic_borrow", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "t")); LitPat (Var (l, "m")); LitPat (Var (l, "q"))], Static)));
      GotoStmt (l, "bb6");
      LabelStmt (l, "bb6");
      ExprStmt (AssignExpr (l, Var (l, "$_11"), Var (l, "u")));
      ExprStmt (AssignExpr (l, Deref (l, Var (l, "p")), Var (l, "$_11")));
      BlockStmt (l, [], [
        DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$temp_var_", Some (InitializerList (l, [])), (ref (false), ref (None)))]);
        ExprStmt (AssignExpr (l, Var (l, "$_10"), Var (l, "$temp_var_")))
      ], l, ref ([]));
      PureStmt (l, ExprStmt (CallExpr (l, "close_nonatomic_borrow", [], [], [], Static)));
      GotoStmt (l, "bb7");
      LabelStmt (l, "bb7");
      PureStmt (l, ExprStmt (CallExpr (l, "thread_token_merge", [], [], [
        LitPat (Var (l, "t"));
        LitPat (CallExpr (l, "mask_diff", [], [], [LitPat (Var (l, "MaskTop")); LitPat (Var (l, "m"))], Static));
        LitPat (Var (l, "m"))
      ], Static)));
      GotoStmt (l, "bb8");
      LabelStmt (l, "bb8");
      PureStmt (l, Close (l, None, "thread_token", [], [], [LitPat (Var (l, "t"))], None));
      GotoStmt (l, "bb9");
      LabelStmt (l, "bb9");
      BlockStmt (l, [], [
        DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$temp_var_", Some (InitializerList (l, [])), (ref (false), ref (None)))]);
        ExprStmt (AssignExpr (l, Var (l, "$_0"), Var (l, "$temp_var_")))
      ], l, ref ([]));
      ReturnStmt (l, Some (Var (l, "$_0")))
    ], l)), false, []);
    Func (l, Regular, [], Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "CellU32::swap", [(PtrTypeExpr (l, StructTypeExpr (l, Some ("CellU32"), None, [], [])), "self"); (PtrTypeExpr (l, StructTypeExpr (l, Some ("CellU32"), None, [], [])), "other")], false, None, Some ((Sep (l, CallExpr (l, "thread_token", [], [], [VarPat (l, "_t")], Static), Sep (l, CoefAsn (l, VarPat (l, "_q_a"), CallExpr (l, "lifetime_token", [], [], [VarPat (l, "a")], Static)), Sep (l, CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); LitPat (Var (l, "self"))], Static), CallExpr (l, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); LitPat (Var (l, "other"))], Static)))), Sep (l, CallExpr (l, "thread_token", [], [], [LitPat (Var (l, "_t"))], Static), Sep (l, CoefAsn (l, LitPat (Var (l, "_q_a")), CallExpr (l, "lifetime_token", [], [], [LitPat (Var (l, "a"))], Static)), True (l))))), false, Some (([
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_0", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_3", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_4", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_5", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Bool)), "$_6", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, StructTypeExpr (l, Some ("CellU32"), None, [], []))), "$_7", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, StructTypeExpr (l, Some ("CellU32"), None, [], []))), "$_8", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, UnionType ("std_empty_"))), "$_9", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_10", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_11", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_12", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_13", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_14", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_15", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_16", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))))), "ps", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))))), "$_18", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))))), "po", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (PtrTypeExpr (l, ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2))))), "$_20", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_21", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "tmp", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "$_23", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, Int (Unsigned, FixedWidthRank (2)))), "$_24", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_25", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_26", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_27", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_28", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_29", None, (ref (false), ref (None)))]);
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_30", None, (ref (false), ref (None)))]);
      LabelStmt (l, "bb0");
      PureStmt (l, Open (l, None, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); LitPat (Var (l, "self"))], None));
      GotoStmt (l, "bb1");
      LabelStmt (l, "bb1");
      PureStmt (l, Open (l, None, "CellU32_share", [], [], [LitPat (Var (l, "a")); LitPat (Var (l, "_t")); LitPat (Var (l, "other"))], None));
      GotoStmt (l, "bb2");
      LabelStmt (l, "bb2");
      ExprStmt (AssignExpr (l, Var (l, "$_7"), AddressOf (l, Deref (l, Var (l, "self")))));
      ExprStmt (AssignExpr (l, Var (l, "$_8"), AddressOf (l, Deref (l, Var (l, "other")))));
      ExprStmt (AssignExpr (l, Var (l, "$_6"), Operation (l, Eq, [Var (l, "$_7"); Var (l, "$_8")])));
      IfStmt (l, Var (l, "$_6"), [GotoStmt (l, "bb3")], [GotoStmt (l, "bb4")]);
      LabelStmt (l, "bb3");
      BlockStmt (l, [], [
        DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$temp_var_", Some (InitializerList (l, [])), (ref (false), ref (None)))]);
        ExprStmt (AssignExpr (l, Var (l, "$_0"), Var (l, "$temp_var_")))
      ], l, ref ([]));
      GotoStmt (l, "bb20");
      LabelStmt (l, "bb4");
      BlockStmt (l, [], [
        DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$temp_var_", Some (InitializerList (l, [])), (ref (false), ref (None)))]);
        ExprStmt (AssignExpr (l, Var (l, "$_5"), Var (l, "$temp_var_")))
      ], l, ref ([]));
      PureStmt (l, Assert (l, CoefAsn (l, DummyPat, CallExpr (l, "nonatomic_borrow", [], [], [
        LitPat (Var (l, "a"));
        LitPat (Var (l, "_t"));
        VarPat (l, "ms");
        LitPat (CallExpr (l, "CellU32_nonatomic_borrow_content", [], [], [LitPat (Var (l, "self")); LitPat (Var (l, "_t"))], Static))
      ], Static))));
      GotoStmt (l, "bb5");
      LabelStmt (l, "bb5");
      PureStmt (l, Assert (l, CoefAsn (l, DummyPat, CallExpr (l, "nonatomic_borrow", [], [], [
        LitPat (Var (l, "a"));
        LitPat (Var (l, "_t"));
        VarPat (l, "mo");
        LitPat (CallExpr (l, "CellU32_nonatomic_borrow_content", [], [], [LitPat (Var (l, "other")); LitPat (Var (l, "_t"))], Static))
      ], Static))));
      GotoStmt (l, "bb6");
      LabelStmt (l, "bb6");
      PureStmt (l, Open (l, None, "thread_token", [], [], [LitPat (Var (l, "_t"))], None));
      GotoStmt (l, "bb7");
      LabelStmt (l, "bb7");
      PureStmt (l, ExprStmt (CallExpr (l, "thread_token_split", [], [], [LitPat (Var (l, "_t")); LitPat (Var (l, "MaskTop")); LitPat (Var (l, "ms"))], Static)));
      GotoStmt (l, "bb8");
      LabelStmt (l, "bb8");
      PureStmt (l, ExprStmt (CallExpr (l, "thread_token_split", [], [], [
        LitPat (Var (l, "_t"));
        LitPat (CallExpr (l, "mask_diff", [], [], [LitPat (Var (l, "MaskTop")); LitPat (Var (l, "ms"))], Static));
        LitPat (Var (l, "mo"))
      ], Static)));
      GotoStmt (l, "bb9");
      LabelStmt (l, "bb9");
      PureStmt (l, ExprStmt (CallExpr (l, "open_nonatomic_borrow", [], [], [
        LitPat (Var (l, "a"));
        LitPat (Var (l, "_t"));
        LitPat (Var (l, "ms"));
        LitPat (Operation (l, Div, [Var (l, "_q_a"); IntLit (l, big_int_of_string "2", true, false, NoLSuffix)]))
      ], Static)));
      GotoStmt (l, "bb10");
      LabelStmt (l, "bb10");
      PureStmt (l, ExprStmt (CallExpr (l, "open_nonatomic_borrow", [], [], [
        LitPat (Var (l, "a"));
        LitPat (Var (l, "_t"));
        LitPat (Var (l, "mo"));
        LitPat (Operation (l, Div, [Var (l, "_q_a"); IntLit (l, big_int_of_string "2", true, false, NoLSuffix)]))
      ], Static)));
      GotoStmt (l, "bb11");
      LabelStmt (l, "bb11");
      ExprStmt (AssignExpr (l, Var (l, "$_18"), AddressOf (l, Select (l, Deref (l, Var (l, "self")), "v"))));
      ExprStmt (AssignExpr (l, Var (l, "ps"), Var (l, "$_18")));
      GotoStmt (l, "bb12");
      LabelStmt (l, "bb12");
      ExprStmt (AssignExpr (l, Var (l, "$_20"), AddressOf (l, Select (l, Deref (l, Var (l, "other")), "v"))));
      ExprStmt (AssignExpr (l, Var (l, "po"), Var (l, "$_20")));
      GotoStmt (l, "bb13");
      LabelStmt (l, "bb13");
      ExprStmt (AssignExpr (l, Var (l, "tmp"), Deref (l, Var (l, "po"))));
      ExprStmt (AssignExpr (l, Var (l, "$_23"), Deref (l, Var (l, "ps"))));
      ExprStmt (AssignExpr (l, Deref (l, Var (l, "po")), Var (l, "$_23")));
      ExprStmt (AssignExpr (l, Var (l, "$_24"), Var (l, "tmp")));
      ExprStmt (AssignExpr (l, Deref (l, Var (l, "ps")), Var (l, "$_24")));
      BlockStmt (l, [], [
        DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$temp_var_", Some (InitializerList (l, [])), (ref (false), ref (None)))]);
        ExprStmt (AssignExpr (l, Var (l, "$_21"), Var (l, "$temp_var_")))
      ], l, ref ([]));
      PureStmt (l, Assert (l, CallExpr (l, "partial_thread_token", [], [], [LitPat (Var (l, "_t")); VarPat (l, "rem")], Static)));
      GotoStmt (l, "bb14");
      LabelStmt (l, "bb14");
      PureStmt (l, ExprStmt (CallExpr (l, "close_nonatomic_borrow", [], [], [], Static)));
      GotoStmt (l, "bb15");
      LabelStmt (l, "bb15");
      PureStmt (l, ExprStmt (CallExpr (l, "close_nonatomic_borrow", [], [], [], Static)));
      GotoStmt (l, "bb16");
      LabelStmt (l, "bb16");
      PureStmt (l, ExprStmt (CallExpr (l, "thread_token_merge", [], [], [LitPat (Var (l, "_t")); LitPat (Var (l, "rem")); LitPat (Var (l, "mo"))], Static)));
      GotoStmt (l, "bb17");
      LabelStmt (l, "bb17");
      PureStmt (l, ExprStmt (CallExpr (l, "thread_token_merge", [], [], [
        LitPat (Var (l, "_t"));
        LitPat (CallExpr (l, "mask_diff", [], [], [LitPat (Var (l, "MaskTop")); LitPat (Var (l, "ms"))], Static));
        LitPat (Var (l, "ms"))
      ], Static)));
      GotoStmt (l, "bb18");
      LabelStmt (l, "bb18");
      PureStmt (l, Close (l, None, "thread_token", [], [], [LitPat (Var (l, "_t"))], None));
      GotoStmt (l, "bb19");
      LabelStmt (l, "bb19");
      BlockStmt (l, [], [
        DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$temp_var_", Some (InitializerList (l, [])), (ref (false), ref (None)))]);
        ExprStmt (AssignExpr (l, Var (l, "$_0"), Var (l, "$temp_var_")))
      ], l, ref ([]));
      GotoStmt (l, "bb20");
      LabelStmt (l, "bb20");
      ReturnStmt (l, Some (Var (l, "$_0")))
    ], l)), false, []);
    Func (l, Regular, [], Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "VeriFast_ghost_command", [], false, None, Some ((CallExpr (l, "thread_token", [], [], [VarPat (l, "_t")], Static), Sep (l, CallExpr (l, "thread_token", [], [], [LitPat (Var (l, "_t"))], Static), True (l)))), false, Some (([
      DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$_0", None, (ref (false), ref (None)))]);
      LabelStmt (l, "bb0");
      BlockStmt (l, [], [
        DeclStmt (l, [(l, Some (ManifestTypeExpr (l, StructType ("std_tuple_0_", []))), "$temp_var_", Some (InitializerList (l, [])), (ref (false), ref (None)))]);
        ExprStmt (AssignExpr (l, Var (l, "$_0"), Var (l, "$temp_var_")))
      ], l, ref ([]));
      ReturnStmt (l, Some (Var (l, "$_0")))
    ], l)), false, [])
  ])
]