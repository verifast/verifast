open Stdint
open Ast
open Vf_mir_translator

let passed_assertions = ref 0

let check msg condition =
  if condition then
    incr passed_assertions
  else (
    Printf.eprintf "[FAIL] Rust translator assertion failed: %s\n" msg;
    assert false
  )

(* ========================================== *)
(* Suite 1: SizeAux                           *)
(* ========================================== *)
let test_size_aux () =
  (* sz_bits_of_int: 0 or 2^n with n >= 3 (i.e. 8, 16, 32, 64, 128...) *)
  check "sz_bits_of_int 0" (Result.is_ok (SizeAux.sz_bits_of_int 0));
  check "sz_bits_of_int 8" (Result.is_ok (SizeAux.sz_bits_of_int 8));
  check "sz_bits_of_int 16" (Result.is_ok (SizeAux.sz_bits_of_int 16));
  check "sz_bits_of_int 32" (Result.is_ok (SizeAux.sz_bits_of_int 32));
  check "sz_bits_of_int 64" (Result.is_ok (SizeAux.sz_bits_of_int 64));
  check "sz_bits_of_int 128" (Result.is_ok (SizeAux.sz_bits_of_int 128));

  (* Invalid bit widths *)
  check "sz_bits_of_int 4 is Error" (Result.is_error (SizeAux.sz_bits_of_int 4));
  check "sz_bits_of_int 7 is Error" (Result.is_error (SizeAux.sz_bits_of_int 7));
  check "sz_bits_of_int 10 is Error" (Result.is_error (SizeAux.sz_bits_of_int 10));
  check "sz_bits_of_int 24 is Error" (Result.is_error (SizeAux.sz_bits_of_int 24));
  check "sz_bits_of_int -8 is Error" (Result.is_error (SizeAux.sz_bits_of_int (-8)));

  (* sz_bytes_of_int: non-negative integers *)
  check "sz_bytes_of_int 0" (Result.is_ok (SizeAux.sz_bytes_of_int 0));
  check "sz_bytes_of_int 1" (Result.is_ok (SizeAux.sz_bytes_of_int 1));
  check "sz_bytes_of_int 4" (Result.is_ok (SizeAux.sz_bytes_of_int 4));
  check "sz_bytes_of_int 8" (Result.is_ok (SizeAux.sz_bytes_of_int 8));
  check "sz_bytes_of_int 16" (Result.is_ok (SizeAux.sz_bytes_of_int 16));
  check "sz_bytes_of_int -1 is Error" (Result.is_error (SizeAux.sz_bytes_of_int (-1)));

  (* sz_bytes_of_sz_bits & int_of_sz_bytes *)
  let bits8 = Result.get_ok (SizeAux.sz_bits_of_int 8) in
  let bytes1 = SizeAux.sz_bytes_of_sz_bits bits8 in
  check "8 bits == 1 byte" (SizeAux.int_of_sz_bytes bytes1 = 1);

  let bits32 = Result.get_ok (SizeAux.sz_bits_of_int 32) in
  let bytes4 = SizeAux.sz_bytes_of_sz_bits bits32 in
  check "32 bits == 4 bytes" (SizeAux.int_of_sz_bytes bytes4 = 4);

  let bits64 = Result.get_ok (SizeAux.sz_bits_of_int 64) in
  let bytes8 = SizeAux.sz_bytes_of_sz_bits bits64 in
  check "64 bits == 8 bytes" (SizeAux.int_of_sz_bytes bytes8 = 8);

  let bits128 = Result.get_ok (SizeAux.sz_bits_of_int 128) in
  let bytes16 = SizeAux.sz_bytes_of_sz_bits bits128 in
  check "128 bits == 16 bytes" (SizeAux.int_of_sz_bytes bytes16 = 16)

(* ========================================== *)
(* Suite 2: IntAux Integer Types & Overflow   *)
(* ========================================== *)
let test_int_aux () =
  (* Int8 *)
  check "Int8 addition without overflow" (IntAux.Int8.try_add Int8.zero Int8.one = Ok Int8.one);
  check "Int8 overflow on max_int + 1" (IntAux.Int8.try_add Int8.max_int Int8.one = Error (`IntAuxAdd "Overflow"));
  check "Int8 underflow on min_int - 1" (IntAux.Int8.try_add Int8.min_int (Int8.of_int (-1)) = Error (`IntAuxAdd "Underflow"));
  check "Int8 try_to_int" (IntAux.Int8.try_to_int (Int8.of_int 42) = Ok 42);
  check "Int8 to_big_int" (Big_int.eq_big_int (IntAux.Int8.to_big_int (Int8.of_int 42)) (Big_int.big_int_of_int 42));

  (* Uint8 *)
  check "Uint8 addition" (IntAux.Uint8.try_add Uint8.zero Uint8.one = Ok Uint8.one);
  check "Uint8 overflow on max_int + 1" (IntAux.Uint8.try_add Uint8.max_int Uint8.one = Error (`IntAuxAdd "Overflow"));

  (* Int16 & Uint16 *)
  check "Int16 addition" (IntAux.Int16.try_add Int16.zero Int16.one = Ok Int16.one);
  check "Int16 overflow" (IntAux.Int16.try_add Int16.max_int Int16.one = Error (`IntAuxAdd "Overflow"));
  check "Int16 underflow" (IntAux.Int16.try_add Int16.min_int (Int16.of_int (-1)) = Error (`IntAuxAdd "Underflow"));
  check "Uint16 overflow" (IntAux.Uint16.try_add Uint16.max_int Uint16.one = Error (`IntAuxAdd "Overflow"));

  (* Int32 & Uint32 *)
  check "Int32 addition" (IntAux.Int32.try_add Int32.zero Int32.one = Ok Int32.one);
  check "Int32 overflow" (IntAux.Int32.try_add Int32.max_int Int32.one = Error (`IntAuxAdd "Overflow"));
  check "Int32 underflow" (IntAux.Int32.try_add Int32.min_int (Int32.of_int (-1)) = Error (`IntAuxAdd "Underflow"));
  check "Uint32 overflow" (IntAux.Uint32.try_add Uint32.max_int Uint32.one = Error (`IntAuxAdd "Overflow"));

  (* Int64 & Uint64 *)
  check "Int64 addition" (IntAux.Int64.try_add Int64.zero Int64.one = Ok Int64.one);
  check "Int64 overflow" (IntAux.Int64.try_add Int64.max_int Int64.one = Error (`IntAuxAdd "Overflow"));
  check "Int64 underflow" (IntAux.Int64.try_add Int64.min_int (Int64.of_int (-1)) = Error (`IntAuxAdd "Underflow"));
  check "Uint64 overflow" (IntAux.Uint64.try_add Uint64.max_int Uint64.one = Error (`IntAuxAdd "Overflow"));

  (* Int128 & Uint128 *)
  check "Int128 addition" (IntAux.Int128.try_add Int128.zero Int128.one = Ok Int128.one);
  check "Int128 overflow" (IntAux.Int128.try_add Int128.max_int Int128.one = Error (`IntAuxAdd "Overflow"));
  check "Int128 underflow" (IntAux.Int128.try_add Int128.min_int (Int128.of_int (-1)) = Error (`IntAuxAdd "Underflow"));
  check "Uint128 overflow" (IntAux.Uint128.try_add Uint128.max_int Uint128.one = Error (`IntAuxAdd "Overflow"))

(* ========================================== *)
(* Suite 3: RustBelt Types & Interpretation   *)
(* ========================================== *)
let test_rustbelt () =
  let interp = RustBelt.emp_ty_interp dummy_loc in
  check "emp_ty_interp size is True" (interp.size = True dummy_loc);
  check "emp_ty_interp own is True" (interp.own (Var (dummy_loc, "t")) (Var (dummy_loc, "v")) = Ok (True dummy_loc));
  check "emp_ty_interp shr is not supported" (interp.shr (Var (dummy_loc, "lft")) (Var (dummy_loc, "t")) (Var (dummy_loc, "l")) = Error "Not yet supported");
  check "emp_ty_interp full_bor_content is not supported" (interp.full_bor_content (Var (dummy_loc, "t")) (Var (dummy_loc, "l")) = Error "Not yet supported");
  check "emp_ty_interp pointee_fbc is None" (interp.pointee_fbc = None);

  (* points_to *)
  let tid = Var (dummy_loc, "tid") in
  let l = Var (dummy_loc, "l") in
  check "points_to with None yields DummyVarPat"
    (match interp.points_to tid l None with
     | Ok (PointsTo (_, _, RegularPointsTo, DummyVarPat)) -> true
     | _ -> false);

  check "points_to with Some vid yields VarPat"
    (match interp.points_to tid l (Some "my_val") with
     | Ok (PointsTo (_, _, RegularPointsTo, VarPat (_, "my_val"))) -> true
     | _ -> false);

  (* Aux.vid_op_to_var_pat *)
  check "vid_op None -> DummyVarPat" (RustBelt.Aux.vid_op_to_var_pat None dummy_loc = Ok DummyVarPat);
  check "vid_op Some -> VarPat" (RustBelt.Aux.vid_op_to_var_pat (Some "foo") dummy_loc = Ok (VarPat (dummy_loc, "foo")));

  (* simple_fbc *)
  check "simple_fbc produces CallExpr"
    (match RustBelt.simple_fbc dummy_loc "my_fbc" tid l with
     | Ok (CallExpr (_, "my_fbc", [], [], [LitPat _; LitPat _], Static)) -> true
     | _ -> false)

(* ========================================== *)
(* Suite 4: Source Loc & Decoder Helpers      *)
(* ========================================== *)
let test_loc_and_mir () =
  (* Src_loc_aux via LocAux *)
  let loc0 = (("file.rs", 1, 1), ("file.rs", 1, 10)) in
  let l = Lexed loc0 in
  check "Ast.lexed_loc unwraps loc0" (Ast.lexed_loc l = loc0);

  let loc1 = (("file.rs", 1, 1), ("file.rs", 1, 5)) in
  let loc2 = (("file.rs", 1, 3), ("file.rs", 1, 10)) in
  check "LocAux.cover_loc0 covers span"
    (match LocAux.cover_loc0 loc1 loc2 with
     | Ok (("file.rs", 1, 1), ("file.rs", 1, 10)) -> true
     | _ -> false);

  (* Mir types: Mutability, Terminator, GenericArg *)
  let mut_var = Mir.Mut in
  let not_mut = Mir.Not in
  check "Mir mutability Mut <> Not" (mut_var <> not_mut);

  let term_goto = Mir.GotoTerminator (l, "bb1") in
  check "Mir terminator Goto" (match term_goto with Mir.GotoTerminator (_, id) -> id = "bb1" | _ -> false);

  let gen_lft = Mir.GenArgLifetime "'a" in
  check "Mir generic arg lifetime" (match gen_lft with Mir.GenArgLifetime s -> s = "'a" | _ -> false);

  (* Hir types *)
  let p_lft = Hir.GenParamLifetime in
  let p_ty = Hir.GenParamType in
  let p_const = Hir.GenParamConst in
  check "Hir generic param types distinct" (p_lft <> p_ty && p_ty <> p_const)


(* ========================================== *)
(* Suite 5: Ast_to_src (Rust MIR Translator)  *)
(* ========================================== *)
let test_ast_to_src () =
  let dummy_loc = Ast.dummy_loc in
  let te_i32 = IdentTypeExpr (dummy_loc, None, "i32") in
  let te_u8 = IdentTypeExpr (dummy_loc, None, "u8") in
  let te_bool = ManifestTypeExpr (dummy_loc, Bool) in
  let te_lft = IdentTypeExpr (dummy_loc, None, "'a") in

  (* string_of_type_expr *)
  check "string_of_type_expr Manifest" (Vf_mir_translator__Ast_to_src.string_of_type_expr te_bool = "bool");
  check "string_of_type_expr Ident" (Vf_mir_translator__Ast_to_src.string_of_type_expr te_i32 = "i32");
  
  let te_struct = StructTypeExpr (dummy_loc, Some "Point", None, [], [te_i32]) in
  check "string_of_type_expr Struct" (Vf_mir_translator__Ast_to_src.string_of_type_expr te_struct = "Point<i32>");

  let te_constructed = ConstructedTypeExpr (dummy_loc, "Vec", [te_u8]) in
  check "string_of_type_expr Constructed" (Vf_mir_translator__Ast_to_src.string_of_type_expr te_constructed = "Vec<u8>");

  let te_ref_mut = RustRefTypeExpr (dummy_loc, te_lft, Mutable, te_i32) in
  check "string_of_type_expr Ref mut" (Vf_mir_translator__Ast_to_src.string_of_type_expr te_ref_mut = "&'a mut i32");

  let te_ref_shr = RustRefTypeExpr (dummy_loc, te_lft, Shared, te_i32) in
  check "string_of_type_expr Ref shr" (Vf_mir_translator__Ast_to_src.string_of_type_expr te_ref_shr = "&'a i32");

  let te_ptr = PtrTypeExpr (dummy_loc, te_u8) in
  check "string_of_type_expr Ptr" (Vf_mir_translator__Ast_to_src.string_of_type_expr te_ptr = "*u8");

  let te_slice = SliceTypeExpr (dummy_loc, te_u8) in
  check "string_of_type_expr Slice" (Vf_mir_translator__Ast_to_src.string_of_type_expr te_slice = "[u8]");

  (* string_of_type_targs and string_of_val_targs *)
  check "string_of_type_targs empty" (Vf_mir_translator__Ast_to_src.string_of_type_targs [] = "");
  check "string_of_type_targs non-empty" (Vf_mir_translator__Ast_to_src.string_of_type_targs [te_i32; te_u8] = "<i32, u8>");
  check "string_of_val_targs empty" (Vf_mir_translator__Ast_to_src.string_of_val_targs [] = "");
  check "string_of_val_targs non-empty" (Vf_mir_translator__Ast_to_src.string_of_val_targs [te_i32; te_u8] = "::<i32, u8>");

  (* string_of_tparams *)
  check "string_of_tparams empty" (Vf_mir_translator__Ast_to_src.string_of_tparams [] = "");
  check "string_of_tparams non-empty" (Vf_mir_translator__Ast_to_src.string_of_tparams [("T", {sized = false}); ("U", {sized = false})] = "<T, U>");

  (* string_of_params *)
  check "string_of_params" (Vf_mir_translator__Ast_to_src.string_of_params [(te_i32, "x"); (te_u8, "y")] = "x: i32, y: u8");

  (* string_of_ret *)
  check "string_of_ret None" (Vf_mir_translator__Ast_to_src.string_of_ret None = "");
  check "string_of_ret Some" (Vf_mir_translator__Ast_to_src.string_of_ret (Some te_bool) = " -> bool");

  (* string_of_expr *)
  check "string_of_expr Var" (Vf_mir_translator__Ast_to_src.string_of_expr (Var (dummy_loc, "my_var")) = "my_var");

  let e_lft = CallExpr (dummy_loc, "lft_of", [], [], [LitPat (Typeid (dummy_loc, TypeExpr (IdentTypeExpr (dummy_loc, None, "'static"))))], Static) in
  check "string_of_expr lft_of" (Vf_mir_translator__Ast_to_src.string_of_expr e_lft = "'static");

  let e_call = CallExpr (dummy_loc, "foo", [te_i32], [VarPat (dummy_loc, "p1")], [VarPat (dummy_loc, "p2")], Static) in
  check "string_of_expr CallExpr" (Vf_mir_translator__Ast_to_src.string_of_expr e_call = "foo::<i32>(?p1)(?p2)");

  let e_call_no_ps1 = CallExpr (dummy_loc, "bar", [], [], [DummyPat], Static) in
  check "string_of_expr CallExpr no ps1" (Vf_mir_translator__Ast_to_src.string_of_expr e_call_no_ps1 = "bar(_)");

  let e_type_pred = TypePredExpr (dummy_loc, te_i32, "my_pred") in
  check "string_of_expr TypePredExpr" (Vf_mir_translator__Ast_to_src.string_of_expr e_type_pred = "<i32>.my_pred");

  let e_typeid = Typeid (dummy_loc, Var (dummy_loc, "val")) in
  check "string_of_expr Typeid" (Vf_mir_translator__Ast_to_src.string_of_expr e_typeid = "typeid(val)");

  let e_type_expr = TypeExpr te_i32 in
  check "string_of_expr TypeExpr" (Vf_mir_translator__Ast_to_src.string_of_expr e_type_expr = "i32");

  let e_select = Select (dummy_loc, Var (dummy_loc, "s"), "field") in
  check "string_of_expr Select" (Vf_mir_translator__Ast_to_src.string_of_expr e_select = "s.field");

  let e_eq = Operation (dummy_loc, Eq, [Var (dummy_loc, "a"); Var (dummy_loc, "b")]) in
  check "string_of_expr Operation Eq" (Vf_mir_translator__Ast_to_src.string_of_expr e_eq = "a == b");

  let e_true = True dummy_loc in
  check "string_of_expr True" (Vf_mir_translator__Ast_to_src.string_of_expr e_true = "true");

  let e_cast_struct = CastExpr (dummy_loc, StructTypeExpr (dummy_loc, Some "Point", None, [], [te_i32]), InitializerList (dummy_loc, [(Some (dummy_loc, "x"), Var (dummy_loc, "10"))])) in
  check "string_of_expr CastExpr struct" (Vf_mir_translator__Ast_to_src.string_of_expr e_cast_struct = "Point::<i32> { x: 10 }");

  let e_cast_as = CastExpr (dummy_loc, te_u8, Var (dummy_loc, "n")) in
  check "string_of_expr CastExpr as" (Vf_mir_translator__Ast_to_src.string_of_expr e_cast_as = "n as u8");

  (* Patterns *)
  check "string_of_pats" (Vf_mir_translator__Ast_to_src.string_of_pats [VarPat (dummy_loc, "x"); LitPat (Var (dummy_loc, "y")); DummyPat] = "?x, y, _");

  (* string_of_bool_expr *)
  check "string_of_bool_expr CallExpr" (Vf_mir_translator__Ast_to_src.string_of_bool_expr e_call_no_ps1 = "bar(_) == true");
  check "string_of_bool_expr other" (Vf_mir_translator__Ast_to_src.string_of_bool_expr e_true = "true");

  (* string_of_asn *)
  check "string_of_asn CallExpr" (Vf_mir_translator__Ast_to_src.string_of_asn e_call_no_ps1 = "bar(_)");
  let a_expr_call = ExprCallExpr (dummy_loc, Var (dummy_loc, "pred"), [DummyPat]) in
  check "string_of_asn ExprCallExpr" (Vf_mir_translator__Ast_to_src.string_of_asn a_expr_call = "pred(_)");
  let a_sep = Sep (dummy_loc, EmpAsn dummy_loc, EmpAsn dummy_loc) in
  check "string_of_asn Sep" (Vf_mir_translator__Ast_to_src.string_of_asn a_sep = "emp &*& emp");
  let a_expr = ExprAsn (dummy_loc, e_true) in
  check "string_of_asn ExprAsn" (Vf_mir_translator__Ast_to_src.string_of_asn a_expr = "true");
  let a_coef = CoefAsn (dummy_loc, DummyPat, EmpAsn dummy_loc) in
  check "string_of_asn CoefAsn" (Vf_mir_translator__Ast_to_src.string_of_asn a_coef = "[_]emp");
  check "string_of_asn EmpAsn" (Vf_mir_translator__Ast_to_src.string_of_asn (EmpAsn dummy_loc) = "emp");

  (* string_of_decl *)
  let lemma_decl = Func (
    dummy_loc,
    Lemma (false, None),
    [("T", {sized = false})],
    Some te_bool,
    "my_lemma",
    [(te_i32, "val")],
    false,
    (None, None),
    Some (EmpAsn dummy_loc, ("res", EmpAsn dummy_loc)),
    false,
    None,
    false,
    []
  ) in
  let s_decl = Vf_mir_translator__Ast_to_src.string_of_decl lemma_decl in
  check "string_of_decl contains lem my_lemma" (String.contains s_decl 'l' && String.contains s_decl 'm');
  check "string_of_decl contains assume(false)" (String.contains s_decl 'a');

  (* Failwith fallbacks calling Ocaml_expr_formatter *)
  let unsupp_te = EnumTypeExpr (dummy_loc, Some "E", None) in
  let caught_te = ref false in
  (try let _ = Vf_mir_translator__Ast_to_src.string_of_type_expr unsupp_te in ()
   with Failure msg ->
     check "failwith string_of_type_expr contains EnumTypeExpr" (String.contains msg 'E');
     caught_te := true);
  check "caught unsupported type_expr" !caught_te;

  let unsupp_e = Null dummy_loc in
  let caught_e = ref false in
  (try let _ = Vf_mir_translator__Ast_to_src.string_of_expr unsupp_e in ()
   with Failure msg ->
     check "failwith string_of_expr contains Null" (String.contains msg 'N');
     caught_e := true);
  check "caught unsupported expr" !caught_e


(* ========================================== *)
(* Suite 5: Rust Parser Decls & Constants     *)
(* ========================================== *)
let test_rust_parser_decls_and_constants () =
  let dummy_loc = Ast.DummyLoc in
  let f_decl = Func (dummy_loc, Regular, [], Some (ManifestTypeExpr (dummy_loc, Bool)), "foo", [], false, (None, None), None, false, None, false, []) in
  let at_decl = AbstractTypeDecl (dummy_loc, "T") in
  let st_decl = Struct (dummy_loc, "S", [], Either.Left ([], [], [], false), []) in
  let pf_decl = PredFamilyDecl (dummy_loc, "P", [], 0, [], None, Inductiveness_Inductive) in
  let pfi_decl = PredFamilyInstanceDecl (dummy_loc, "P", [], [], [], ExprAsn (dummy_loc, True dummy_loc)) in
  let fs_decl = FuncSpecializationDecl (dummy_loc, "f_gen", true, "f_spec", [], []) in
  
  check "prefix Func" (match Vf_mir_translator__Rust_parser.prefix_decl_name dummy_loc "mod::" f_decl with Func (_, _, _, _, name, _, _, _, _, _, _, _, _) -> name = "mod::foo" | _ -> false);
  check "prefix AbstractTypeDecl" (match Vf_mir_translator__Rust_parser.prefix_decl_name dummy_loc "mod::" at_decl with AbstractTypeDecl (_, name) -> name = "mod::T" | _ -> false);
  check "prefix Struct" (match Vf_mir_translator__Rust_parser.prefix_decl_name dummy_loc "mod::" st_decl with Struct (_, name, _, _, _) -> name = "mod::S" | _ -> false);
  check "prefix PredFamilyDecl" (match Vf_mir_translator__Rust_parser.prefix_decl_name dummy_loc "mod::" pf_decl with PredFamilyDecl (_, name, _, _, _, _, _) -> name = "mod::P" | _ -> false);
  check "prefix PredFamilyInstanceDecl" (match Vf_mir_translator__Rust_parser.prefix_decl_name dummy_loc "mod::" pfi_decl with PredFamilyInstanceDecl (_, name, _, _, _, _) -> name = "mod::P" | _ -> false);
  check "prefix FuncSpecializationDecl" (match Vf_mir_translator__Rust_parser.prefix_decl_name dummy_loc "mod::" fs_decl with FuncSpecializationDecl (_, g_gen, _, g_spec, _, _) -> g_gen = "mod::f_gen" && g_spec = "mod::f_spec" | _ -> false);

  check "decl_add_type_params Func" (match Vf_mir_translator__Rust_parser.decl_add_type_params dummy_loc [("T", no_bounds)] f_decl with Func (_, _, tps, _, _, _, _, _, _, _, _, _, _) -> List.length tps = 1 | _ -> false);
  check "decl_add_type_params FuncSpecializationDecl" (match Vf_mir_translator__Rust_parser.decl_add_type_params dummy_loc [("T", no_bounds)] fs_decl with FuncSpecializationDecl (_, _, _, _, tps, _) -> List.length tps = 1 | _ -> false)

(* ========================================== *)
(* Suite 6: Mir Translator Make Helpers       *)
(* ========================================== *)
module MockArgs : VF_MIR_TRANSLATOR_ARGS = struct
  let data_model_opt = None
  let report_should_fail _ _ = ()
  let report_range _ _ = ()
  let report_macro_call _ _ = ()
  let verbose_flags = []
  let skip_specless_fns = false
  let allow_ignore_ref_creation = false
  let ignore_ref_creation = false
  let ignore_unwind_paths = false
  let rocq_writer = Rocq_writer.rocq_create_writer false
end

module Tr = Vf_mir_translator.Make(MockArgs)

let test_mir_translator_make_helpers () =
  let dummy_loc = Ast.DummyLoc in
  (* string_of_decoded_type *)
  check "decoded bool" (Tr.string_of_decoded_type `Bool = "bool");
  check "decoded never" (Tr.string_of_decoded_type `Never = "!");
  check "decoded adt empty" (Tr.string_of_decoded_type (`Adt ("MyStruct", `Struct, [])) = "MyStruct");
  check "decoded adt with arg" (Tr.string_of_decoded_type (`Adt ("MyStruct", `Struct, [`Type `Bool])) = "MyStruct<bool>");
  check "decoded i8" (Tr.string_of_decoded_type (`Int D.I8) = "i8");
  check "decoded i16" (Tr.string_of_decoded_type (`Int D.I16) = "i16");
  check "decoded i32" (Tr.string_of_decoded_type (`Int D.I32) = "i32");
  check "decoded i64" (Tr.string_of_decoded_type (`Int D.I64) = "i64");
  check "decoded i128" (Tr.string_of_decoded_type (`Int D.I128) = "i128");
  check "decoded isize" (Tr.string_of_decoded_type (`Int D.ISize) = "isize");
  check "decoded u8" (Tr.string_of_decoded_type (`Uint D.U8) = "u8");
  check "decoded u16" (Tr.string_of_decoded_type (`Uint D.U16) = "u16");
  check "decoded u32" (Tr.string_of_decoded_type (`Uint D.U32) = "u32");
  check "decoded u64" (Tr.string_of_decoded_type (`Uint D.U64) = "u64");
  check "decoded u128" (Tr.string_of_decoded_type (`Uint D.U128) = "u128");
  check "decoded usize" (Tr.string_of_decoded_type (`Uint D.USize) = "usize");
  check "decoded foreign fallback" (Tr.string_of_decoded_type `Foreign = "(type)");

  (* extract_implicit_outlives_clauses *)
  check "outlives bool" (Tr.extract_implicit_outlives_clauses [] `Bool = []);
  check "outlives ref" (List.length (Tr.extract_implicit_outlives_clauses ["'b"] (`Ref ("'a", `Not, `Bool))) = 1);
  check "outlives adt" (List.length (Tr.extract_implicit_outlives_clauses [] (`Adt ("S", `Struct, [`Lifetime "'a"]))) = 0);

  (* decl_mir_adt_kind *)
  let s_decl = Struct (dummy_loc, "S", [], Either.Left ([], [], [], false), []) in
  let e_decl = Inductive (dummy_loc, "E", [], []) in
  check "decl_mir_adt_kind Struct" (Mir.decl_mir_adt_kind s_decl = Ok Mir.Struct);
  check "decl_mir_adt_kind Enum" (Mir.decl_mir_adt_kind e_decl = Ok Mir.Enum);

  (* translate_real_file_name, file_name, source_file, char_pos *)
  check "translate_real_file_name local" (Tr.translate_real_file_name (D.LocalPath "/test.rs") = Ok "/test.rs");
  check "translate_real_file_name remapped nothing" (Tr.translate_real_file_name (D.Remapped {local_path = D.Nothing; virtual_name = "/virt.rs"}) = Ok "/RUSTC_VIRTUAL_PATH/virt.rs");
  check "translate_real_file_name remapped something" (Tr.translate_real_file_name (D.Remapped {local_path = D.Something {text = "/real.rs"}; virtual_name = "/virt.rs"}) = Ok "/real.rs");
  check "translate_file_name" (Tr.translate_file_name (D.Real (D.LocalPath "/test.rs")) = Ok "/test.rs");
  check "translate_source_file" (Tr.translate_source_file {name = D.Real (D.LocalPath "/test.rs")} = Ok "/test.rs");
  check "translate_char_pos" (Tr.translate_char_pos {pos = Stdint.Uint64.of_int 9} = Ok (Stdint.Uint64.of_int 10));

  (* never_ty_info *)
  let dummy_expr = Var (dummy_loc, "x") in
  let n_info = Tr.never_ty_info dummy_loc in
  check "never vf_ty" (match n_info.Mir.vf_ty with ManifestTypeExpr (_, UnionType "std_empty_") -> true | _ -> false);
  check "never own" (n_info.Mir.interp.own dummy_expr (True dummy_loc) = Ok (False dummy_loc));
  check "never points_to" (n_info.Mir.interp.points_to dummy_expr dummy_expr None = Ok (False dummy_loc));
  check "never shr error" (Result.is_error (n_info.Mir.interp.shr dummy_expr dummy_expr dummy_expr));
  check "never full_bor error" (Result.is_error (n_info.Mir.interp.full_bor_content dummy_expr dummy_expr));

  (* char_ty_info *)
  let c_info = Tr.char_ty_info dummy_loc in
  check "char vf_ty" (match c_info.Mir.vf_ty with ManifestTypeExpr (_, RustChar) -> true | _ -> false);
  check "char points_to some" (Result.is_ok (c_info.Mir.interp.points_to dummy_expr dummy_expr (Some "c_val")));
  check "char points_to none error" (Result.is_error (c_info.Mir.interp.points_to dummy_expr dummy_expr None));

  (* translate_param_ty *)
  match Tr.translate_param_ty "T" dummy_loc with
  | Ok p_info ->
    check "param_ty vf_ty" (p_info.Mir.vf_ty = IdentTypeExpr (dummy_loc, None, "T"));
    check "param_ty own" (Result.is_ok (p_info.Mir.interp.own dummy_expr (True dummy_loc)));
    check "param_ty shr" (Result.is_ok (p_info.Mir.interp.shr dummy_expr dummy_expr dummy_expr))
  | Error _ -> check "translate_param_ty returned Error" false


(* ========================================== *)
(* Suite 7: Rust Parser Integer Constants     *)
(* ========================================== *)
let test_rust_parser_integer_constants_and_exprs () =
  let dummy_loc = Ast.DummyLoc in
  let parse_from_tokens toks =
    let stream = Lexer.Stream.of_list toks in
    Vf_mir_translator__Rust_parser.parse_expr stream
  in
  let check_const str is_min signed rank =
    let e = parse_from_tokens [(dummy_loc, Lexer.Ident str)] in
    match e with
    | Operation (_, (MinValue (Int (s, r)) | MaxValue (Int (s, r))), []) ->
      check (str ^ " matched") (s = signed && r = rank)
    | _ -> check (str ^ " failed to parse as min/max") false
  in
  check_const "isize::MIN" true Signed PtrRank;
  check_const "isize::MAX" false Signed PtrRank;
  check_const "usize::MAX" false Unsigned PtrRank;
  check_const "i8::MIN" true Signed (FixedWidthRank 0);
  check_const "i8::MAX" false Signed (FixedWidthRank 0);
  check_const "u8::MAX" false Unsigned (FixedWidthRank 0);
  check_const "i16::MIN" true Signed (FixedWidthRank 1);
  check_const "i16::MAX" false Signed (FixedWidthRank 1);
  check_const "u16::MAX" false Unsigned (FixedWidthRank 1);
  check_const "i32::MIN" true Signed (FixedWidthRank 2);
  check_const "i32::MAX" false Signed (FixedWidthRank 2);
  check_const "u32::MAX" false Unsigned (FixedWidthRank 2);
  check_const "i64::MIN" true Signed (FixedWidthRank 3);
  check_const "i64::MAX" false Signed (FixedWidthRank 3);
  check_const "u64::MAX" false Unsigned (FixedWidthRank 3);

  (* result_pre_of_outcome_pre and result_decl_of_outcome_decl *)
  let switch_e = SwitchExpr (
    dummy_loc,
    Var (dummy_loc, "res"),
    [SwitchExprClause (dummy_loc, "Success", [], True dummy_loc)],
    Some (dummy_loc, False dummy_loc)
  ) in
  let sw_out = Vf_mir_translator__Rust_parser.result_pre_of_outcome_pre switch_e in
  check "result_pre_of_outcome_pre on SwitchExpr" (match sw_out with SwitchExpr _ -> true | _ -> false);

  let outcome_post = (
    "outcome",
    SwitchExpr (
      dummy_loc,
      Var (dummy_loc, "outcome"),
      [
        SwitchExprClause (dummy_loc, "returning", ["result"], EmpAsn dummy_loc);
        SwitchExprClause (dummy_loc, "panicking", [], EmpAsn dummy_loc)
      ],
      None
    )
  ) in
  let f_decl = Func (
    dummy_loc,
    Regular,
    [],
    Some (ConstructedTypeExpr (dummy_loc, "fn_outcome", [ManifestTypeExpr (dummy_loc, Bool)])),
    "foo",
    [],
    false,
    (None, None),
    Some (EmpAsn dummy_loc, outcome_post),
    false,
    None,
    false,
    []
  ) in
  let f_res = Vf_mir_translator__Rust_parser.result_decl_of_outcome_decl f_decl in
  check "result_decl_of_outcome_decl on Func" (match f_res with Func (_, _, _, Some (ManifestTypeExpr (_, Bool)), _, _, _, _, _, _, _, _, _) -> true | _ -> false)


(* ========================================== *)
(* Suite 8: Mir Translator Ints, Sync & Send  *)
(* ========================================== *)
let test_mir_translator_int_types_and_helpers () =
  let dummy_loc = Ast.DummyLoc in
  let open Vf_mir_translator.Mir in
  let open Vf_mir_translator.TrName in
  (* int_ty_to_string *)
  check "int_ty_to_string isize" (int_ty_to_string ISize = "isize");
  check "int_ty_to_string i8" (int_ty_to_string I8 = "i8");
  check "int_ty_to_string i16" (int_ty_to_string I16 = "i16");
  check "int_ty_to_string i32" (int_ty_to_string I32 = "i32");
  check "int_ty_to_string i64" (int_ty_to_string I64 = "i64");
  check "int_ty_to_string i128" (int_ty_to_string I128 = "i128");

  (* int_ty_bits_len *)
  check "int_ty_bits_len isize" (match int_ty_bits_len ISize with Error (`UIntTyBitsLen _) -> true | _ -> false);
  check "int_ty_bits_len i8" (int_ty_bits_len I8 = Ok 8);
  check "int_ty_bits_len i16" (int_ty_bits_len I16 = Ok 16);
  check "int_ty_bits_len i32" (int_ty_bits_len I32 = Ok 32);
  check "int_ty_bits_len i64" (int_ty_bits_len I64 = Ok 64);
  check "int_ty_bits_len i128" (int_ty_bits_len I128 = Ok 128);

  (* u_int_ty_to_string *)
  check "u_int_ty_to_string usize" (u_int_ty_to_string USize = "usize");
  check "u_int_ty_to_string u8" (u_int_ty_to_string U8 = "u8");
  check "u_int_ty_to_string u16" (u_int_ty_to_string U16 = "u16");
  check "u_int_ty_to_string u32" (u_int_ty_to_string U32 = "u32");
  check "u_int_ty_to_string u64" (u_int_ty_to_string U64 = "u64");
  check "u_int_ty_to_string u128" (u_int_ty_to_string U128 = "u128");

  (* u_int_ty_bits_len *)
  check "u_int_ty_bits_len usize" (match u_int_ty_bits_len USize with Error (`UIntTyBitsLen _) -> true | _ -> false);
  check "u_int_ty_bits_len u8" (u_int_ty_bits_len U8 = Ok 8);
  check "u_int_ty_bits_len u16" (u_int_ty_bits_len U16 = Ok 16);
  check "u_int_ty_bits_len u32" (u_int_ty_bits_len U32 = Ok 32);
  check "u_int_ty_bits_len u64" (u_int_ty_bits_len U64 = Ok 64);
  check "u_int_ty_bits_len u128" (u_int_ty_bits_len U128 = Ok 128);

  (* Name and string helpers *)
  check "make_tmp_var_name" (make_tmp_var_name "foo" = "$temp_var_foo");
  check "lft_name_without_apostrophe apostrophe" (lft_name_without_apostrophe "'a" = "a");
  let caught_apostrophe = ref false in
  (try let _ = lft_name_without_apostrophe "b" in () with Failure _ -> caught_apostrophe := true);
  check "lft_name_without_apostrophe no apostrophe caught" !caught_apostrophe;
  check "is_from_std_lib std" (is_from_std_lib "std::vec::Vec");
  check "is_from_std_lib non-std" (not (is_from_std_lib "alloc::vec::Vec"));
  check "split_def_path matching prefix" (split_def_path "foo::bar" "foo::bar::baz" = ("foo::bar", "baz"));
  check "split_def_path mismatch" (split_def_path "foo::bar" "other::baz" = ("foo::bar", "other::baz"));
  check "split_item_name with colon" (Vf_mir_translator.split_item_name "foo::bar" = ("foo", "bar"));
  check "split_item_name without colon" (Vf_mir_translator.split_item_name "bar" = ("", "bar"));
  check "substring_eq match" (Tr.substring_eq "hello world" 6 "world");
  check "substring_eq mismatch" (not (Tr.substring_eq "hello world" 6 "earth"));
  check "substring_eq out of bounds" (not (Tr.substring_eq "short" 10 "long"));

  (* Send and Sync expression and assertion helpers *)
  let te_bool = Ast.ManifestTypeExpr (dummy_loc, Bool) in
  check "mk_send_expr" (match Tr.mk_send_expr dummy_loc te_bool with CallExpr (_, "is_Send", _, _, _, _) -> true | _ -> false);
  check "mk_send_tparam_expr" (match Tr.mk_send_tparam_expr dummy_loc "T" with CallExpr (_, "is_Send", _, _, _, _) -> true | _ -> false);
  check "mk_send_asn" (match Tr.mk_send_asn dummy_loc te_bool with ExprAsn (_, CallExpr (_, "is_Send", _, _, _, _)) -> true | _ -> false);
  check "mk_send_tparam_asn" (match Tr.mk_send_tparam_asn dummy_loc "T" with ExprAsn (_, CallExpr (_, "is_Send", _, _, _, _)) -> true | _ -> false);

  check "mk_sync_expr" (match Tr.mk_sync_expr dummy_loc te_bool with CallExpr (_, "is_Sync", _, _, _, _) -> true | _ -> false);
  check "mk_sync_tparam_expr" (match Tr.mk_sync_tparam_expr dummy_loc "T" with CallExpr (_, "is_Sync", _, _, _, _) -> true | _ -> false);
  check "mk_sync_asn" (match Tr.mk_sync_asn dummy_loc te_bool with ExprAsn (_, CallExpr (_, "is_Sync", _, _, _, _)) -> true | _ -> false);
  check "mk_sync_tparam_asn" (match Tr.mk_sync_tparam_asn dummy_loc "T" with ExprAsn (_, CallExpr (_, "is_Sync", _, _, _, _)) -> true | _ -> false);

  (* mk_list_pat *)
  check "mk_list_pat empty" (match Tr.mk_list_pat dummy_loc [] with LitPat (Var (_, "nil")) -> true | _ -> false);
  check "mk_list_pat cons" (match Tr.mk_list_pat dummy_loc [DummyPat; DummyPat] with CtorPat (_, "cons", [DummyPat; CtorPat (_, "cons", [DummyPat; LitPat (Var (_, "nil"))])]) -> true | _ -> false)

let run () =
  passed_assertions := 0;
  test_rust_parser_decls_and_constants ();
  test_size_aux ();
  test_int_aux ();
  test_rustbelt ();
  test_loc_and_mir ();
  test_ast_to_src ();
  test_mir_translator_make_helpers ();
  test_rust_parser_integer_constants_and_exprs ();
  test_mir_translator_int_types_and_helpers ();
  !passed_assertions
