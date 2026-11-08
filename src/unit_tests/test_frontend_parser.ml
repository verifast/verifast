open Ocaml_expr
open Ocaml_expr_formatter
open Ocaml_expr_of_ast
open Big_int
open Num
open Util
open Ast
open Lexer
open Parser

let passed_assertions = ref 0

let check msg condition =
  if condition then
    incr passed_assertions
  else (
    Printf.eprintf "[FAIL] Frontend/Parser assertion failed: %s\n" msg;
    assert false
  )

(* ========================================== *)
(* Suite 1: Util Functions                    *)
(* ========================================== *)
let test_util () =
  (* Rational conversion *)
  let half = num_of_ints 1 2 in
  check "num_of_ints 1 2 == 1/2" (string_of_num half = "1/2");
  
  let pi_approx = num_of_decimal_fraction "3.1415" in
  check "num_of_decimal_fraction" (string_of_num pi_approx = "6283/2000");

  let hex_frac = num_of_hex_fraction "0x1.8" in
  check "num_of_hex_fraction 0x1.8 == 3/2" (string_of_num hex_frac = "3/2");

  (* List utilities *)
  check "zip" (zip [1; 2] ["a"; "b"] = Some [(1, "a"); (2, "b")]);
  check "zip2" (zip2 [1; 2] ["a"; "b"] = [(1, "a"); (2, "b")]);
  check "zip_with_remainder" (zip_with_remainder [1; 2; 3] ["a"; "b"] = ([(1, "a"); (2, "b")], [3], []));
  
  check "flatmap" (flatmap (fun x -> [x; x * 10]) [1; 2] = [1; 10; 2; 20]);
  check "head_flatmap" (head_flatmap (fun x -> if x > 2 then [x] else []) [1; 2; 3; 4] = Some 3);
  check "head_flatmap_option" (head_flatmap_option (fun x -> if x = 3 then Some x else None) [1; 2; 3; 4] = Some 3);
  check "extract" (extract (fun x -> if x = 2 then Some "two" else None) [1; 2; 3] = Some ("two", [1; 3]));
  
  check "take" (take 2 [1; 2; 3; 4] = [1; 2]);
  check "drop" (drop 2 [1; 2; 3; 4] = [3; 4]);
  check "take_drop" (take_drop 2 [1; 2; 3; 4] = ([1; 2], [3; 4]));
  check "drop_while" (drop_while (fun x -> x < 3) [1; 2; 3; 4] = [3; 4]);
  check "list_make" (list_make 3 "a" = ["a"; "a"; "a"]);
  check "distinct with dups is false" (not (distinct [1; 2; 2; 3])); check "distinct without dups is true" (distinct [1; 2; 3]);
  check "index_of" (index_of "b" ["a"; "b"; "c"] 0 = Some 1);
  check "try_assoc" (try_assoc "k" [("k", 42)] = Some 42);
  check "try_assoc not found" (try_assoc "missing" [("k", 42)] = None);
  check "try_assoc_case_insensitive" (try_assoc_case_insensitive "KEY" [("key", 100)] = Some 100);

  (* Exponent parsing *)
  let n1 = num_of_decimal_fraction "1e+5" in
  check "num_of_decimal_fraction 1e+5" (string_of_num n1 = "100000");
  let n2 = num_of_decimal_fraction "1.5e+2" in
  check "num_of_decimal_fraction 1.5e+2" (string_of_num n2 = "150");
  let n3 = num_of_decimal_fraction "2.5E-1" in
  check "num_of_decimal_fraction 2.5E-1" (string_of_num n3 = "1/4");

  (* Path utilities *)
  check "reduce_rooted_path" (reduce_rooted_path "/a/b/../c/./d//e" = "/a/c/d/e");
  check "remove_prefix match" (remove_prefix "/foo/" "/foo/bar" = Some "bar");
  check "remove_prefix no match" (remove_prefix "/foo/" "/baz/bar" = None);

  (* Unique list *)
  check "add_unique new" (add_unique [1; 2] 3 = [3; 1; 2]);
  check "add_unique dup" (add_unique [1; 2] 2 = [1; 2]);
  check "add_uniques" (add_uniques [1] [2; 1; 3] = [3; 2; 1]);

  (* InfiniteArray *)
  let ia = InfiniteArray.make 0 in
  check "ia get default" (ia.elems.(0) = 0);
  InfiniteArray.set ia 25 99;
  check "ia get set" (ia.elems.(25) = 99)

(* ========================================== *)
(* Suite 2: Ast Data Models & Types           *)
(* ========================================== *)
let test_ast_data_models () =
  check "LP64 widths: int=2, long=3, ptr=3"
    (data_model_lp64.int_width = 2 && data_model_lp64.long_width = 3 && data_model_lp64.ptr_width = 3);
  
  check "32bit widths: int=2, long=2, ptr=2"
    (data_model_32bit.int_width = 2 && data_model_32bit.long_width = 2 && data_model_32bit.ptr_width = 2);

  check "LLP64 widths: int=2, long=2, ptr=3"
    (data_model_llp64.int_width = 2 && data_model_llp64.long_width = 2 && data_model_llp64.ptr_width = 3);

  check "IP16 widths: int=1, long=2, ptr=1"
    (data_model_ip16.int_width = 1 && data_model_ip16.long_width = 2 && data_model_ip16.ptr_width = 1);

  check "I16 widths: int=1, long=2, ptr=2"
    (data_model_i16.int_width = 1 && data_model_i16.long_width = 2 && data_model_i16.ptr_width = 2);

  (* data_model_of_string *)
  check "model LP64" (data_model_of_string "LP64" = data_model_lp64);
  check "model Linux64" (data_model_of_string "LINUX64" = data_model_lp64);
  check "model macOS" (data_model_of_string "MACOS" = data_model_lp64);
  check "model ILP32" (data_model_of_string "ILP32" = data_model_32bit);
  check "model 32bit" (data_model_of_string "32BIT" = data_model_32bit);
  check "model Win64" (data_model_of_string "WIN64" = data_model_llp64);
  check "model LLP64" (data_model_of_string "LLP64" = data_model_llp64);
  check "model IP16" (data_model_of_string "IP16" = data_model_ip16);
  check "model I16" (data_model_of_string "I16" = data_model_i16);

  (* string_of_func_kind *)
  check "func_kind Regular" (string_of_func_kind Regular = "regular");
  check "func_kind Fixpoint" (string_of_func_kind Fixpoint = "fixpoint");
  check "func_kind Lemma" (string_of_func_kind (Lemma (false, None)) = "lemma")

(* ========================================== *)
(* Suite 3: Lexer Tokenizer                   *)
(* ========================================== *)
let test_lexer () =
  (* latin1_to_utf8 *)
  check "latin1 ASCII passthrough" (latin1_to_utf8 "hello" = "hello");
  check "latin1 e-acute" (latin1_to_utf8 "\xe9" = "\xc3\xa9");
  check "latin1 copyright" (latin1_to_utf8 "\xa9" = "\xc2\xa9");

  (* Tokenization via make_lexer *)
  let tokenize text =
    let report _ _ = () in
    let (_, _, stream) = make_lexer (common_keywords @ c_keywords) ghost_keywords "test.c" text report report in
    let tokens = ref [] in
    let rec iter () =
      match Stream.peek stream with
      | None -> List.rev !tokens
      | Some (_, Eof) -> Stream.junk stream; List.rev !tokens
      | Some (_, t) -> Stream.junk stream; tokens := t :: !tokens; iter ()
    in
    iter ()
  in

  (* Integer tokens *)
  let t_int = tokenize "123 0x1f 077 42u 100L 1000LL" in
  check "tokenize decimal int" (match List.nth t_int 0 with Int (bi, true, false, NoLSuffix, "123") -> eq_big_int bi (big_int_of_int 123) | _ -> false);
  check "tokenize hex int" (match List.nth t_int 1 with Int (bi, false, false, NoLSuffix, "0x1f") -> eq_big_int bi (big_int_of_int 31) | _ -> false);
  check "tokenize octal int" (match List.nth t_int 2 with Int (bi, false, false, NoLSuffix, "077") -> eq_big_int bi (big_int_of_int 63) | _ -> false);
  check "tokenize u suffix" (match List.nth t_int 3 with Int (bi, true, true, NoLSuffix, "42u") -> eq_big_int bi (big_int_of_int 42) | _ -> false);
  check "tokenize L suffix" (match List.nth t_int 4 with Int (bi, true, false, LSuffix, "100L") -> eq_big_int bi (big_int_of_int 100) | _ -> false);
  check "tokenize LL suffix" (match List.nth t_int 5 with Int (bi, true, false, LLSuffix, "1000LL") -> eq_big_int bi (big_int_of_int 1000) | _ -> false);

  (* Real and Rational tokens *)
  let t_real = tokenize "123r 3.14 2.5f" in
  check "tokenize RealToken" (match List.nth t_real 0 with RealToken bi -> eq_big_int bi (big_int_of_int 123) | _ -> false);
  check "tokenize RationalToken" (match List.nth t_real 1 with RationalToken (n, None) -> string_of_num n = "157/50" | _ -> false);
  check "tokenize RationalToken float" (match List.nth t_real 2 with RationalToken (n, Some FloatFSuffix) -> string_of_num n = "5/2" | _ -> false);

  (* String and Char tokens *)
  let t_str = tokenize "\"hello world\" 'x' '\\n'" in
  check "tokenize string" (match List.nth t_str 0 with String "hello world" -> true | _ -> false);
  check "tokenize char 'x'" (match List.nth t_str 1 with CharToken 'x' -> true | _ -> false);
  check "tokenize newline char" (match List.nth t_str 2 with CharToken '\n' -> true | _ -> false);

  (* Rust lifetime / prime prefixed ident *)
  let tokenize_rust text =
    let report _ _ = () in
    let (_, _, stream) = make_lexer rust_keywords rust_ghost_keywords "test.rs" text report report in
    let tokens = ref [] in
    let rec iter () =
      match Stream.peek stream with
      | None -> List.rev !tokens
      | Some (_, Eof) -> Stream.junk stream; List.rev !tokens
      | Some (_, t) -> Stream.junk stream; tokens := t :: !tokens; iter ()
    in
    iter ()
  in
  let t_prime = tokenize_rust "'static 'a" in
  check "tokenize static lifetime" (match List.nth t_prime 0 with PrimePrefixedIdent "static" -> true | _ -> false);
  check "tokenize a lifetime" (match List.nth t_prime 1 with PrimePrefixedIdent "a" -> true | _ -> false);

  (* Ghost comments *)
  let t_ghost = tokenize "int x; /*@ requires true; @*/ y;" in
  check "tokens across ghost comment" (List.length t_ghost >= 5);
  check "ghost keyword requires found" (List.mem (Kwd "requires") t_ghost);

  (* Strings containing comment markers do not trigger ghost parsing *)
  let t_str_comment = tokenize "char* s = \"/*@ requires true; @*/\";" in
  check "comment in string is String token"
    (List.exists (function String "/*@ requires true; @*/" -> true | _ -> false) t_str_comment);
  check "no ghost requires keyword from inside string"
    (not (List.mem (Kwd "requires") t_str_comment))

(* ========================================== *)
(* Suite 4: Parser C & Ghost Declarations     *)
(* ========================================== *)
let test_parser_c_and_ghost () =
  let path = Filename.concat (Filename.get_temp_dir_name ()) "test_unit_c_parser.c" in
  let oc = open_out path in
  output_string oc "
struct Point {
  int x;
  int y;
};

/*@
inductive my_tree = leaf | node(int, my_tree, my_tree);

fixpoint int tree_size(my_tree t) {
  switch (t) {
    case leaf: return 0;
    case node(v, l, r): return 1 + tree_size(l) + tree_size(r);
  }
}

lemma void size_nonneg(my_tree t)
  requires true;
  ensures tree_size(t) >= 0;
{
  switch (t) {
    case leaf:
    case node(v, l, r):
      size_nonneg(l);
      size_nonneg(r);
  }
}
@*/

int add(int a, int b)
//@ requires true;
//@ ensures result == a + b;
{
  return a + b;
}
";
  close_out oc;

  let reportMacroCall _ _ = () in
  let reportRange _ _ = () in
  let reportShouldFail _ _ = () in
  let make_lexer path include_paths ~inGhostRange =
    let text = Lexer.readFile path in
    make_lexer (common_keywords @ c_keywords) ghost_keywords path text reportRange ~inGhostRange reportShouldFail
  in
  let (_, token_stream) = make_preprocessor reportMacroCall make_lexer path 0 [] (Some data_model_lp64) [] in
  let (_, packages) =
    let parse_c =
      function%parser
      | [ [%l (headers, _d) = parse_include_directives 0 false (Some data_model_lp64)]; 
          [%l ds = parse_decls CLang (Some data_model_lp64) false ~inGhostHeader:false]; 
          (_, Eof) 
        ] -> (headers, [PackageDecl(dummy_loc,"",[],ds)])
    in
    parse_c token_stream
  in
  Sys.remove path;

  check "packages parsed" (List.length packages = 1);
  let [PackageDecl(_, _, _, ds)] = packages in
  check "decls count >= 5" (List.length ds >= 5);

  (* Find struct Point *)
  check "struct Point declared"
    (List.exists (function Struct (_, "Point", _, _, _) -> true | _ -> false) ds);

  (* Find inductive my_tree *)
  check "inductive my_tree declared with 2 ctors"
    (List.exists (function Inductive (_, "my_tree", [], ctors) -> List.length ctors = 2 | _ -> false) ds);

  (* Find fixpoint tree_size *)
  check "fixpoint tree_size declared"
    (List.exists (function Func (_, Fixpoint, _, _, "tree_size", _, _, _, _, _, _, _, _) -> true | _ -> false) ds);

  (* Find lemma size_nonneg *)
  check "lemma size_nonneg declared"
    (List.exists (function Func (_, Lemma _, _, _, "size_nonneg", _, _, _, _, _, _, _, _) -> true | _ -> false) ds);

  (* Find regular func add *)
  check "func add declared"
    (List.exists (function Func (_, Regular, _, _, "add", _, _, _, _, _, _, _, _) -> true | _ -> false) ds)


(* ========================================== *)
(* Suite 5: Frontend.Z Integers               *)
(* ========================================== *)
let test_z () =
  check "Z.zero" (Z.to_string Z.zero = "0");
  check "Z.one" (Z.to_string Z.one = "1");
  check "Z.minus_one" (Z.to_string Z.minus_one = "-1");
  check "Z.of_int" (Z.to_string (Z.of_int 42) = "42");
  check "Z.to_int" (Z.to_int (Z.of_int 42) = 42);

  let huge = Z.of_big_int (Big_int.big_int_of_string "9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999") in
  let of_flow = ref false in
  (try let _ = Z.to_int huge in () with Z.Overflow | Invalid_argument _ -> of_flow := true);
  check "Z.to_int overflow" !of_flow;

  let i32 = Int32.of_int 1234 in
  check "Z.of_int32" (Z.to_string (Z.of_int32 i32) = "1234");
  check "Z.to_int32" (Z.to_int32 (Z.of_int32 i32) = i32);
  of_flow := false;
  (try let _ = Z.to_int32 huge in () with Z.Overflow | Invalid_argument _ -> of_flow := true);
  check "Z.to_int32 overflow" !of_flow;

  let i64 = Int64.of_int 5678 in
  check "Z.of_int64" (Z.to_string (Z.of_int64 i64) = "5678");
  check "Z.to_int64" (Z.to_int64 (Z.of_int64 i64) = i64);
  of_flow := false;
  (try let _ = Z.to_int64 huge in () with Z.Overflow | Invalid_argument _ -> of_flow := true);
  check "Z.to_int64 overflow" !of_flow;

  let nint = Nativeint.of_int 99 in
  check "Z.of_nativeint" (Z.to_string (Z.of_nativeint nint) = "99");
  check "Z.to_nativeint" (Z.to_nativeint (Z.of_nativeint nint) = nint);
  of_flow := false;
  (try let _ = Z.to_nativeint huge in () with Z.Overflow | Invalid_argument _ -> of_flow := true);
  check "Z.to_nativeint overflow" !of_flow;

  let u32 = Stdint.Uint32.of_int 77 in
  check "Z.of_uint32" (Z.to_string (Z.of_uint32 u32) = "77");
  check "Z.to_uint32" (Z.to_uint32 (Z.of_uint32 u32) = u32);
  of_flow := false;
  (try let _ = Z.to_uint32 huge in () with Z.Overflow | Invalid_argument _ -> of_flow := true);
  check "Z.to_uint32 overflow" !of_flow;

  let u64 = Stdint.Uint64.of_int 88 in
  check "Z.of_uint64" (Z.to_string (Z.of_uint64 u64) = "88");
  check "Z.to_uint64" (Z.to_uint64 (Z.of_uint64 u64) = u64);
  of_flow := false;
  (try let _ = Z.to_uint64 huge in () with Z.Overflow | Invalid_argument _ -> of_flow := true);
  check "Z.to_uint64 overflow" !of_flow;

  let i128 = Stdint.Int128.of_int 128 in
  check "Z.of_int128" (Z.to_string (Z.of_int128 i128) = "128");
  check "Z.to_int128" (Z.to_int128 (Z.of_int128 i128) = i128);
  of_flow := false;
  (try let _ = Z.to_int128 huge in () with Z.Overflow | Invalid_argument _ -> of_flow := true);
  check "Z.to_int128 overflow" !of_flow;

  let u128 = Stdint.Uint128.of_int 256 in
  check "Z.of_uint128" (Z.to_string (Z.of_uint128 u128) = "256");
  check "Z.to_uint128" (Z.to_uint128 (Z.of_uint128 u128) = u128);
  of_flow := false;
  (try let _ = Z.to_uint128 huge in () with Z.Overflow | Invalid_argument _ -> of_flow := true);
  check "Z.to_uint128 overflow" !of_flow;

  let bi = Big_int.big_int_of_int 1000 in
  check "Z.of_big_int" (Z.to_string (Z.of_big_int bi) = "1000");
  check "Z.to_big_int" (Big_int.eq_big_int (Z.to_big_int (Z.of_big_int bi)) bi);
  check "Z.to_string" (Z.to_string (Z.of_int 1000) = "1000")

(* ========================================== *)
(* Suite 6: Ocaml_expr, Formatter & of_ast    *)
(* ========================================== *)
let test_ocaml_expr_and_ast () =
  (* 6a. Ocaml_expr construction *)
  let oe_c = c "Nil" in
  let oe_s = s "test_str" in
  let oe_i = i 123 in
  let oe_b = b true in
  let oe_ref = of_ref (fun r -> i r) (ref 42) in
  let oe_big = BigInt (Big_int.big_int_of_int 9999) in
  let oe_num = Num (Num.num_of_int 3) in
  let oe_l = L [oe_c; oe_s; oe_i; oe_b] in
  let oe_l_empty = L [] in
  let oe_t = T [oe_c; oe_s] in
  let oe_t_empty = T [] in
  let oe_t_single = T [oe_i] in
  let oe_call = Call ("my_fun", [oe_i; oe_s]) in
  let oe_loc = Loc dummy_loc in

  (* 6b. Ocaml_expr_formatter *)
  check "fmt C" (string_of_ocaml_expr true oe_c = "Nil");
  check "fmt S" (string_of_ocaml_expr true oe_s = "\"test_str\"");
  check "fmt I" (string_of_ocaml_expr true oe_i = "123");
  check "fmt B" (string_of_ocaml_expr true oe_b = "true");
  check "fmt BigInt" (String.contains (string_of_ocaml_expr true oe_big) '9');
  check "fmt Num" (String.contains (string_of_ocaml_expr true oe_num) '3');
  check "fmt L" (String.contains (string_of_ocaml_expr true oe_l) ';');
  check "fmt L empty" (string_of_ocaml_expr true oe_l_empty = "[]");
  check "fmt T" (String.contains (string_of_ocaml_expr true oe_t) ',');
  check "fmt T empty" (string_of_ocaml_expr true oe_t_empty = "()");
  check "fmt T single" (string_of_ocaml_expr true oe_t_single = "(123)");
  check "fmt Ref" (String.contains (string_of_ocaml_expr true oe_ref) '4');
  check "fmt Call" (String.contains (string_of_ocaml_expr true oe_call) 'm');
  check "fmt Loc noLocs true" (string_of_ocaml_expr true oe_loc = "l");
  check "fmt Loc noLocs false" (String.contains (string_of_ocaml_expr false oe_loc) 'l');

  (* File formatting *)
  let out_path = Filename.concat (Filename.get_temp_dir_name ()) "test_ocaml_expr_out.ml" in
  print_ocaml_expr_to_file false out_path oe_l;
  check "print_ocaml_expr_to_file exists" (Sys.file_exists out_path);
  Sys.remove out_path;

  (* 6c. Ocaml_expr_of_ast: of_type *)
  let types = [
    Bool; Void; Int (Signed, IntRank); Int (Unsigned, CharRank);
    Int (Signed, ShortRank); Int (Unsigned, ShortRank);
    Int (Signed, LongRank); Int (Unsigned, LongRank);
    Int (Signed, LongLongRank); Int (Unsigned, LongLongRank);
    Int (Signed, PtrRank); Int (Unsigned, PtrRank);
    Int (Signed, FixedWidthRank 2); Int (Unsigned, FixedWidthRank 2);
    RustChar; RealType; Float; Double; LongDouble;
    StructType ("MyS", [Bool]); UnionType "MyU"; PtrType Bool; FuncType "my_ft";
    InductiveType ("MyInd", [Bool]);
    PredType (["p"], [Bool], Some 1, Inductiveness_Inductive);
    PredType (["p"], [Bool], None, Inductiveness_CoInductive);
    PureFuncType (Bool, Bool); ObjType ("MyObj", [Bool]); ArrayType Bool;
    StaticArrayType (Bool, Bool); LiteralConstType (Z.of_int 10);
    BoxIdType; HandleIdType; AnyType; RealTypeParam "R"; GhostTypeParam "G";
    InferredRealType "IR"; ClassOrInterfaceName "C"; PackageName "P";
    RefType Bool; AbstractType "A";
    InferredType (object end, ref Unconstrained);
    InferredType (object end, ref (ContainsAnyConstraint true));
    InferredType (object end, ref (EqConstraint Bool))
  ] in
  List.iter (fun tp ->
    let oe = of_type tp in
    check "of_type produces valid ocaml_expr" (String.length (string_of_ocaml_expr true oe) > 0)
  ) types;

  (* 6d. of_type_expr *)
  let te_m = ManifestTypeExpr (dummy_loc, Int (Signed, IntRank)) in
  let type_exprs = [
    te_m;
    StructTypeExpr (dummy_loc, Some "Point", None, [Packed; ReprC], [te_m]);
    StructTypeExpr (dummy_loc, None, Some (["T"], [Field (dummy_loc, Real, te_m, "f", Instance, Public, false, None)]), [], []);
    UnionTypeExpr (dummy_loc, Some "U", Some [Field (dummy_loc, Real, te_m, "u_f", Instance, Public, false, None)]);
    EnumTypeExpr (dummy_loc, Some "E", Some [("A", Some (IntLit (dummy_loc, big_int_of_int 1, true, false, NoLSuffix)))]);
    PtrTypeExpr (dummy_loc, te_m);
    RustRefTypeExpr (dummy_loc, te_m, Mutable, te_m);
    RustRefTypeExpr (dummy_loc, te_m, Shared, te_m);
    ArrayTypeExpr (dummy_loc, te_m);
    StaticArrayTypeExpr (dummy_loc, te_m, te_m);
    LiteralConstTypeExpr (dummy_loc, Z.of_int 99);
    FuncTypeExpr (dummy_loc, te_m, [(te_m, "param")]);
    IdentTypeExpr (dummy_loc, Some "pkg", "MyType");
    IdentTypeExpr (dummy_loc, None, "LocalType");
    ConstructedTypeExpr (dummy_loc, "Box", [te_m]);
    PredTypeExpr (dummy_loc, [te_m], Some 1);
    PureFuncTypeExpr (dummy_loc, [(te_m, Some (dummy_loc, "arg"))], Some (True dummy_loc));
    LValueRefTypeExpr (dummy_loc, te_m);
    ConstTypeExpr (dummy_loc, te_m);
    ProjectionTypeExpr (dummy_loc, te_m, "Trait", [te_m], "Assoc");
    SliceTypeExpr (dummy_loc, te_m)
  ] in
  List.iter (fun te ->
    let oe = of_type_expr te in
    check "of_type_expr produces valid ocaml_expr" (String.length (string_of_ocaml_expr true oe) > 0)
  ) type_exprs;

  (* 6e. of_expr *)
  let e_var = Var (dummy_loc, "x") in
  let e_int = IntLit (dummy_loc, big_int_of_int 10, true, false, NoLSuffix) in
  let exprs = [
    True dummy_loc; False dummy_loc; Null dummy_loc;
    e_var; WVar (dummy_loc, "wx", LocalVar);
    Select (dummy_loc, e_var, "f");
    e_int; WIntLit (dummy_loc, big_int_of_int 20);
    RealLit (dummy_loc, Num.num_of_int 5, Some FloatFSuffix);
    RealLit (dummy_loc, Num.num_of_int 6, Some FloatLSuffix);
    RealLit (dummy_loc, Num.num_of_int 7, None);
    StringLit (dummy_loc, "str"); ClassLit (dummy_loc, "Cls");
    TruncatingExpr (dummy_loc, e_int);
    Operation (dummy_loc, Add, [e_var; e_int]);
    WOperation (dummy_loc, Sub, [e_var; e_int], Int (Signed, IntRank));
    SliceExpr (dummy_loc, Some (LitPat e_int), Some (LitPat e_int));
    SliceExpr (dummy_loc, None, None);
    Read (dummy_loc, e_var, "f");
    ReadArray (dummy_loc, e_var, e_int);
    WReadArray (dummy_loc, e_var, Int (Signed, IntRank), e_int);
    Deref (dummy_loc, e_var); WDeref (dummy_loc, e_var, Int (Signed, IntRank));
    CallExpr (dummy_loc, "my_fn", [te_m], [LitPat e_int], [LitPat e_var], Static);
    ExprCallExpr (dummy_loc, e_var, [LitPat e_int]);
    NewArray (dummy_loc, te_m, e_int);
    NewObject (dummy_loc, "Point", [e_int], Some [te_m]);
    CxxDelete (dummy_loc, e_var);
    NewArrayWithInitializer (dummy_loc, te_m, [e_int]);
    IfExpr (dummy_loc, True dummy_loc, e_int, e_int);
    SwitchExpr (dummy_loc, e_int, [SwitchExprClause (dummy_loc, "Zero", [], e_int)], Some (dummy_loc, e_int));
    PredNameExpr (dummy_loc, "p"); CastExpr (dummy_loc, te_m, e_var);
    Upcast (e_var, Int (Signed, IntRank), RealType);
    TypedExpr (e_var, Int (Signed, IntRank));
    WidenedParameterArgument e_var;
    SizeofExpr (dummy_loc, TypeExpr te_m); SizeofExpr (dummy_loc, e_var);
    GenericExpr (dummy_loc, e_var, [(te_m, e_int)], Some e_int);
    AddressOf (dummy_loc, e_var);
    AssignExpr (dummy_loc, e_var, Mutation, e_int);
    AssignExpr (dummy_loc, e_var, Initialization, e_int);
    AssignOpExpr (dummy_loc, e_var, Add, e_int, false);
    AssignOpExpr (dummy_loc, e_var, Add, e_int, true);
    CommaExpr (dummy_loc, e_var, e_int);
    InstanceOfExpr (dummy_loc, e_var, te_m);
    SuperMethodCall (dummy_loc, "super_fn", [e_int])
  ] in
  List.iteri (fun idx e ->
    let oe = try of_expr e with ex -> Printf.eprintf "of_expr failed on idx %d\n" idx; raise ex in
    check "of_expr produces valid ocaml_expr" (String.length (string_of_ocaml_expr true oe) > 0)
  ) exprs;

  (* 6f. Patterns, Statements & Declarations *)
  let pats = [VarPat (dummy_loc, "p"); LitPat e_int; DummyPat] in
  List.iter (fun p -> check "of_pat" (String.length (string_of_ocaml_expr true (of_pat p)) > 0)) pats;

  let stmts = [
    PureStmt (dummy_loc, ReturnStmt (dummy_loc, Some e_int));
    Open (dummy_loc, Some e_var, "p", [te_m], [LitPat e_int], [VarPat (dummy_loc, "y")], None);
    Close (dummy_loc, None, "p", [te_m], [LitPat e_int], [VarPat (dummy_loc, "y")], None);
    IfStmt (dummy_loc, True dummy_loc, [ExprStmt e_var], [ExprStmt e_int]);
    BlockStmt (dummy_loc, [Global (dummy_loc, te_m, "inner_g", None)], [ExprStmt e_var], dummy_loc, ref []);
    WhileStmt (dummy_loc, True dummy_loc, Some (LoopInv (EmpAsn dummy_loc)), Some e_int, [Break dummy_loc], [Continue dummy_loc]);
    DeclStmt (dummy_loc, [(dummy_loc, Some te_m, "loc1", Some e_int, (ref false, ref None))]);
    ReturnStmt (dummy_loc, None); Assert (dummy_loc, EmpAsn dummy_loc);
    NonpureStmt (dummy_loc, false, ExprStmt e_var);
    SwitchStmt (dummy_loc, e_var, [SwitchStmtClause (dummy_loc, e_int, [Break dummy_loc]); SwitchStmtDefaultClause (dummy_loc, [Break dummy_loc])]);
    Throw (dummy_loc, e_var); Leak (dummy_loc, EmpAsn dummy_loc);
    LabelStmt (dummy_loc, "my_lbl"); GotoStmt (dummy_loc, "my_lbl");
    TryCatch (dummy_loc, [ExprStmt e_var], []);
    TryFinally (dummy_loc, [ExprStmt e_var], dummy_loc, [ExprStmt e_int]);
    SuperConstructorCall (dummy_loc, [e_int])
  ] in
  List.iter (fun st -> check "of_stmt" (String.length (string_of_ocaml_expr true (of_stmt st)) > 0)) stmts;

  let decls = [
    Struct (dummy_loc, "S1", ["T"], Either.Right (Either.Left true), [Packed; ReprC]);
    Struct (dummy_loc, "S2", [], Left ([CxxBaseSpec (dummy_loc, "Base", false)], [Field (dummy_loc, Real, te_m, "f", Instance, Public, false, None)], [InstancePredDecl (dummy_loc, "ip_decl", [(te_m, "arg")], Some (EmpAsn dummy_loc))], false), []);
    Union (dummy_loc, "U", Some []);
    AbstractTypeDecl (dummy_loc, "A");
    PredFamilyDecl (dummy_loc, "PF", ["T"], 0, [te_m], Some 1, Inductiveness_Inductive);
    PredFamilyInstanceDecl (dummy_loc, "PF", [("T", {sized = false})], [], [(te_m, "arg")], EmpAsn dummy_loc);
    Inductive (dummy_loc, "List", ["T"], [Ctor (dummy_loc, "Nil", []); Ctor (dummy_loc, "Cons", [("head", te_m)])]);
    PredCtorDecl (dummy_loc, "PC", ["T"], [(te_m, "cp")], [(te_m, "p")], Some 1, EmpAsn dummy_loc);
    Global (dummy_loc, te_m, "g1", Some e_int);
    Global (dummy_loc, te_m, "g2", None);
    TypedefDecl (dummy_loc, te_m, "my_td", []);
    TypePredDecl (dummy_loc, te_m, "Self", "my_pred");
    EnumDecl (dummy_loc, "MyEnum", [("EV", None)]);
    Func (dummy_loc, Regular, [("T", {sized = false})], Some te_m, "my_fn", [(te_m, "x")], false, (None, None), Some (EmpAsn dummy_loc, ("res", EmpAsn dummy_loc)), false, Some (stmts, dummy_loc), false, [])
  ] in
  List.iter (fun d -> check "of_decl" (String.length (string_of_ocaml_expr true (of_decl d)) > 0)) decls;

  (* 6g. Package & Helpers *)
  let pkg = PackageDecl (dummy_loc, "p", [Import (dummy_loc, Real, "other", Some "x")], decls) in
  check "of_package" (String.length (string_of_ocaml_expr true (of_package pkg)) > 0);
  check "of_import" (String.length (string_of_ocaml_expr true (of_import (Import (dummy_loc, Real, "other", None)))) > 0);
  check "of_prover_type" (String.length (string_of_ocaml_expr true (of_prover_type ProverInt)) > 0);
  check "of_pred_name" (String.length (string_of_ocaml_expr true (of_pred_name (PredFam "my_pred"))) > 0);
  check "of_ident_scope" (String.length (string_of_ocaml_expr true (of_ident_scope LocalVar)) > 0);
  check "of_signedness" (String.length (string_of_ocaml_expr true (of_signedness Signed)) > 0);
  check "of_int_rank" (String.length (string_of_ocaml_expr true (of_int_rank IntRank)) > 0);
  check "of_rust_ref_kind" (String.length (string_of_ocaml_expr true (of_rust_ref_kind Mutable)) > 0);
  check "of_inductiveness" (String.length (string_of_ocaml_expr true (of_inductiveness Inductiveness_Inductive)) > 0);

  (* Check Ast loc inspectors on all variants *)
  List.iter (fun te -> check "type_expr_loc" (type_expr_loc te = dummy_loc)) type_exprs;
  List.iter (fun e -> check "expr_loc" (expr_loc e = dummy_loc)) exprs;
  List.iter (fun st -> check "stmt_loc" (stmt_loc st = dummy_loc)) stmts;
  List.iter (fun d -> match d with Struct _ | Func _ -> check "decl_loc" (Ast_aux.decl_loc d = dummy_loc) | _ -> ()) decls;
  let asns = [
    PointsTo (dummy_loc, e_var, RegularPointsTo, LitPat e_int);
    PredAsn (dummy_loc, "p", [], [], [LitPat e_int], Static);
    ExprAsn (dummy_loc, True dummy_loc);
    Sep (dummy_loc, EmpAsn dummy_loc, EmpAsn dummy_loc);
    IfAsn (dummy_loc, True dummy_loc, EmpAsn dummy_loc, EmpAsn dummy_loc);
    EmpAsn dummy_loc;
    ForallAsn (dummy_loc, te_m, "x", True dummy_loc);
    CoefAsn (dummy_loc, DummyPat, EmpAsn dummy_loc);
    EnsuresAsn (dummy_loc, "res", EmpAsn dummy_loc)
  ] in
  List.iter (fun a -> check "asn_loc" (asn_loc a = dummy_loc)) asns;
  check "string_of_func_kind regular" (string_of_func_kind Regular = "regular");
  check "string_of_func_kind lemma" (string_of_func_kind (Lemma (false, None)) = "lemma");
  check "string_of_func_kind fixpoint" (string_of_func_kind Fixpoint = "fixpoint");
  check "tostring instance" (tostring Instance = "instance");
  check "tostring static" (tostring Static = "static")

(* ========================================== *)
(* Suite 7: Ocaml_aux                         *)
(* ========================================== *)
let test_ocaml_aux () =
  let open Ocaml_aux in
  check "OptionAux.value_or_else Some" (OptionAux.value_or_else ~opt:(Some 42) ~none:(fun () -> 0) = 42);
  check "OptionAux.value_or_else None" (OptionAux.value_or_else ~opt:None ~none:(fun () -> 99) = 99);

  check "ListAux.is_empty empty" (ListAux.is_empty []);
  check "ListAux.is_empty non-empty" (not (ListAux.is_empty [1]));
  check "ListAux.first empty" (ListAux.first [] = None);
  check "ListAux.first non-empty" (ListAux.first [10; 20] = Some 10);
  check "ListAux.last empty" (ListAux.last [] = None);
  check "ListAux.last 1 elem" (ListAux.last [10] = Some 10);
  check "ListAux.last multi elem" (ListAux.last [10; 20; 30] = Some 30);

  let (sat, unsat) = ListAux.partitioni (fun idx x -> idx mod 2 = 0) [10; 20; 30; 40] in
  check "ListAux.partitioni sat" (sat = [10; 30]);
  check "ListAux.partitioni unsat" (unsat = [20; 40]);
  check "ListAux.partitioni empty" (ListAux.partitioni (fun _ _ -> true) [] = ([], []));

  check "ListAux.split3" (ListAux.split3 [(1, "a", true); (2, "b", false)] = ([1; 2], ["a"; "b"], [true; false]));
  check "ListAux.split3 empty" (ListAux.split3 [] = ([], [], []));

  check "ListAux.try_map ok" (ListAux.try_map (fun x -> Ok (x + 1)) [1; 2; 3] = Ok [2; 3; 4]);
  check "ListAux.try_map err" (ListAux.try_map (fun x -> if x = 2 then Error "err" else Ok x) [1; 2; 3] = Error "err");
  check "ListAux.try_map empty" (ListAux.try_map (fun x -> Ok x) [] = Ok []);

  check "ListAux.try_filter_map ok" (ListAux.try_filter_map (fun x -> if x mod 2 = 0 then Ok (Some (x * 10)) else Ok None) [1; 2; 3; 4] = Ok [20; 40]);
  check "ListAux.try_filter_map err" (ListAux.try_filter_map (fun x -> if x = 3 then Error "err3" else Ok (Some x)) [1; 2; 3] = Error "err3");
  check "ListAux.try_filter_map empty" (ListAux.try_filter_map (fun x -> Ok (Some x)) [] = Ok []);

  check "ListAux.try_fold_left ok" (ListAux.try_fold_left (fun acc x -> Ok (acc + x)) 0 [1; 2; 3] = Ok 6);
  check "ListAux.try_fold_left err" (ListAux.try_fold_left (fun _ x -> if x = 2 then Error "err" else Ok x) 0 [1; 2; 3] = Error "err");
  check "ListAux.try_fold_left empty" (ListAux.try_fold_left (fun acc _ -> Ok acc) 42 [] = Ok 42);

  check "ListAux.try_partition ok" (ListAux.try_partition (fun x -> Ok (x > 2)) [1; 2; 3; 4] = Ok ([3; 4], [1; 2]));
  check "ListAux.try_partition err" (ListAux.try_partition (fun x -> if x = 2 then Error "err" else Ok true) [1; 2] = Error "err");
  check "ListAux.try_partition empty" (ListAux.try_partition (fun _ -> Ok true) [] = Ok ([], []));

  check "ListAux.try_merge_sorted_lists ok" (ListAux.try_merge_sorted_lists (fun a b -> Ok (compare a b)) [1; 3; 5] [2; 4; 6] = Ok [1; 2; 3; 4; 5; 6]);
  check "ListAux.try_merge_sorted_lists empty left" (ListAux.try_merge_sorted_lists (fun a b -> Ok (compare a b)) [] [1; 2] = Ok [1; 2]);
  check "ListAux.try_merge_sorted_lists empty right" (ListAux.try_merge_sorted_lists (fun a b -> Ok (compare a b)) [1; 2] [] = Ok [1; 2]);
  check "ListAux.try_merge_sorted_lists err" (ListAux.try_merge_sorted_lists (fun _ _ -> Error "err") [1] [2] = Error "err");

  check "ListAux.fold_left2_opt ok" (ListAux.fold_left2_opt (fun acc x y -> Some (acc + x + y)) 0 [1; 2] [10; 20] = Some 33);
  check "ListAux.fold_left2_opt none" (ListAux.fold_left2_opt (fun _ _ _ -> None) 0 [1] [2] = None);
  check "ListAux.fold_left2_opt length mismatch 1" (ListAux.fold_left2_opt (fun acc _ _ -> Some acc) 0 [1] [2; 3] = None);
  check "ListAux.fold_left2_opt length mismatch 2" (ListAux.fold_left2_opt (fun acc _ _ -> Some acc) 0 [1; 2] [3] = None);
  check "ListAux.fold_left2_opt empty" (ListAux.fold_left2_opt (fun acc _ _ -> Some acc) 0 [] [] = Some 0);

  check "ListAux.try_sort ok" (ListAux.try_sort (fun s -> s) (fun a b -> Ok (compare a b)) [3; 1; 2] = Ok [1; 2; 3]);
  check "ListAux.try_sort err" (ListAux.try_sort (fun s -> s) (fun a b -> if a = 2 || b = 2 then Error "bad2" else Ok (compare a b)) [3; 2; 1] = Error (`Sort "bad2"));
  check "ListAux.try_sort empty" (ListAux.try_sort (fun s -> s) (fun _ _ -> Ok 0) [] = Ok [])

(* ========================================== *)
(* Suite 8: Src_loc_aux                       *)
(* ========================================== *)
let test_src_loc_aux () =
  let open Src_loc_aux in
  check "is_well_formed_src_pos valid" (is_well_formed_src_pos ("f.c", 1, 1) = Ok ());
  check "is_well_formed_src_pos invalid ln" (Result.is_error (is_well_formed_src_pos ("f.c", 0, 1)));
  check "is_well_formed_src_pos invalid col" (Result.is_error (is_well_formed_src_pos ("f.c", 1, 0)));

  check "is_well_formed_loc0 valid" (is_well_formed_loc0 ((("f.c", 1, 1), ("f.c", 1, 5))) = Ok ());
  check "is_well_formed_loc0 diff file" (Result.is_error (is_well_formed_loc0 ((("a.c", 1, 1), ("b.c", 1, 5)))));
  check "is_well_formed_loc0 out of order ln" (Result.is_error (is_well_formed_loc0 ((("f.c", 2, 1), ("f.c", 1, 5)))));
  check "is_well_formed_loc0 out of order col" (Result.is_error (is_well_formed_loc0 ((("f.c", 1, 5), ("f.c", 1, 2)))));

  let loc = Lexed ((("f.c", 1, 2), ("f.c", 1, 10))) in
  check "get_start_loc" (get_start_loc loc = Ok (Lexed ((("f.c", 1, 2), ("f.c", 1, 2)))));

  check "get_last_col_loc ok" (get_last_col_loc loc = Ok (Lexed ((("f.c", 1, 9), ("f.c", 1, 10)))));
  let loc_col1 = Lexed ((("f.c", 1, 1), ("f.c", 2, 1))) in
  check "get_last_col_loc col1 is error" (Result.is_error (get_last_col_loc loc_col1));

  check "try_compare_src_pos equal" (try_compare_src_pos ("f.c", 1, 1) ("f.c", 1, 1) = Ok 0);
  check "try_compare_src_pos ln greater" (try_compare_src_pos ("f.c", 2, 1) ("f.c", 1, 1) = Ok 1);
  check "try_compare_src_pos ln less" (try_compare_src_pos ("f.c", 1, 1) ("f.c", 2, 1) = Ok (-1));
  check "try_compare_src_pos col greater" (try_compare_src_pos ("f.c", 1, 5) ("f.c", 1, 2) = Ok 1);
  check "try_compare_src_pos col less" (try_compare_src_pos ("f.c", 1, 2) ("f.c", 1, 5) = Ok (-1));
  check "try_compare_src_pos diff file" (Result.is_error (try_compare_src_pos ("a.c", 1, 1) ("b.c", 1, 1)));

  let l1 = (("f.c", 1, 1), ("f.c", 3, 10)) in
  let l2 = (("f.c", 1, 5), ("f.c", 2, 5)) in
  check "cover_loc0 true" (Result.is_ok (cover_loc0 l1 l2));
  check "cover_loc0 reverse" (Result.is_ok (cover_loc0 l2 l1));

  check "loc0_contains_srcpos true" (loc0_contains_srcpos l1 ("f.c", 2, 1));
  check "loc0_contains_srcpos false" (not (loc0_contains_srcpos l1 ("f.c", 4, 1)));
  check "loc_contains_srcpos" (loc_contains_srcpos (Lexed l1) ("f.c", 2, 1));
  check "r_path" (Result.is_ok (rel l1 l2));
  check "try_compare_loc" (Result.is_ok (try_compare_loc (("f.c", 1, 1), ("f.c", 1, 2)) (("f.c", 2, 1), ("f.c", 2, 2))))

(* ========================================== *)
(* Suite 9: Stats                             *)
(* ========================================== *)
let test_stats () =
  let s = new Stats.stats in
  s#stmtParsed;
  s#openParsed;
  s#closeParsed;
  s#execStep;
  s#branch;
  s#proverAssume;
  s#definitelyEqualSameTerm;
  s#definitelyEqualQuery;
  s#proverOtherQuery;
  let l = Lexed ((("f.c", 1, 1), ("f.c", 1, 10))) in
  s#stmtExec l;
  check "stats stmtExec count" (s#getStmtExec = 1);
  check "stats stmtExecLocs" (List.length s#getStmtExecLocs = 1);
  check "stats stmtExecOnAllPaths" (s#getStmtExecOnAllPaths = 1);
  s#appendProverStats ("Z3 query stats:
", [("check", 1000L); ("sat", 500L)]);
  s#overhead ~path:"main.c" ~nonGhostLineCount:100 ~ghostLineCount:20 ~mixedLineCount:5;
  s#recordFunctionTiming "my_function" 0.5;
  check "stats function timings" (String.length s#getFunctionTimings > 0);
  check "stats stmt exec msg" (String.length s#get_success_message > 0)

(* ========================================== *)
(* Suite 10: Ast_aux                          *)
(* ========================================== *)
let test_ast_aux () =
  let open Ast_aux in
  let te_int = IdentTypeExpr (dummy_loc, None, "int") in
  let f1 = Field (dummy_loc, Real, te_int, "field1", Instance, Public, false, None) in
  check "field_name" (field_name f1 = "field1");
  check "field_ty" (field_ty f1 = te_int);
  check "field_loc" (field_loc f1 = dummy_loc);
  let s_def = Either.Left ([], [f1], [], false) in
  let s_decl = Struct (dummy_loc, "MyStruct", [], s_def, []) in
  check "decl_name struct" (decl_name s_decl = Some "MyStruct");
  check "decl_loc struct" (decl_loc s_decl = dummy_loc);
  check "decl_fields struct Left" (match decl_fields s_decl with Ok (Some [f]) -> field_name f = "field1" | _ -> false);
  let s_sized = Struct (dummy_loc, "SizedStruct", [], Either.Right (Either.Left true), []) in
  check "decl_fields struct Right" (match decl_fields s_sized with Ok None -> true | _ -> false);
  let fn_decl = Func (dummy_loc, Regular, [], Some te_int, "my_func", [], false, (None, None), None, false, None, false, []) in
  check "decl_name func" (decl_name fn_decl = Some "my_func");
  check "decl_loc func" (decl_loc fn_decl = dummy_loc);
  check "is_adt_ty StructTypeExpr" (is_adt_ty (StructTypeExpr (dummy_loc, Some "S", None, [], [])));
  check "is_adt_ty other" (not (is_adt_ty te_int));
  check "adt_ty_name" (adt_ty_name (StructTypeExpr (dummy_loc, Some "S", None, [], [])) = Ok "S");
  check "adt_type_name StructType" (adt_type_name (StructType ("S", [])) = Some "S");
  check "adt_type_name InductiveType" (adt_type_name (InductiveType ("List", [])) = Some "List");
  check "adt_type_name Int" (adt_type_name (Int (Signed, IntRank)) = None);
  check "is_adt_type_ true" (is_adt_type_ (StructType ("S", [])));
  check "is_adt_type_ false" (not (is_adt_type_ (Int (Signed, IntRank))));
  let check_setter d expected_name new_name =
    match decl_loc_name_and_name_setter d with
    | None -> false
    | Some (_, name, setter) ->
      let d' = setter new_name in
      name = expected_name && (match decl_loc_name_and_name_setter d' with Some (_, n, _) -> n = new_name | None -> false)
  in
  check "setter Struct" (check_setter s_decl "MyStruct" "NewStruct");
  check "setter Func" (check_setter fn_decl "my_func" "new_func");
  check "setter AbstractTypeDecl" (check_setter (AbstractTypeDecl (dummy_loc, "A")) "A" "A2");
  check "setter TypedefDecl" (check_setter (TypedefDecl (dummy_loc, te_int, "T", [])) "T" "T2");
  check "setter PredFamilyDecl" (check_setter (PredFamilyDecl (dummy_loc, "PF", [], 0, [], None, Inductiveness_Inductive)) "PF" "PF2");
  check "setter PredFamilyInstanceDecl" (check_setter (PredFamilyInstanceDecl (dummy_loc, "PFI", [], [], [], EmpAsn dummy_loc)) "PFI" "PFI2");
  check "setter PredCtorDecl" (check_setter (PredCtorDecl (dummy_loc, "PC", [], [], [], None, EmpAsn dummy_loc)) "PC" "PC2");
  check "setter FuncTypeDecl" (check_setter (FuncTypeDecl (dummy_loc, Real, Some te_int, "FT", [], [], [], (EmpAsn dummy_loc, ("res", EmpAsn dummy_loc), false))) "FT" "FT2");
  let dmap = decl_map_of [ModuleDecl (dummy_loc, "M", [], [s_decl; fn_decl]); AbstractTypeDecl (dummy_loc, "A")] in
  check "decl_map_of length" (List.length dmap = 3);
  check "decl_map_of M::MyStruct" (List.mem_assoc "M::MyStruct" dmap);
  check "decl_map_of M::my_func" (List.mem_assoc "M::my_func" dmap);
  check "decl_map_of A" (List.mem_assoc "A" dmap);
  let pf_inst = PredFamilyInstanceDecl (dummy_loc, "PF_inst", [], [], [], EmpAsn dummy_loc) in
  let dmap_pf = [("PF_inst", pf_inst)] in
  check "decl_map_contains_pred_fam_inst" (decl_map_contains_pred_fam_inst_or_pred_ctor_inst dmap_pf "PF_inst");
  check "decl_map_contains_pred_fam_inst not found" (not (decl_map_contains_pred_fam_inst_or_pred_ctor_inst dmap_pf "Other"));
  let sorted = sort_decls_lexically [("b", Struct (Lexed ((("f.c", 2, 1), ("f.c", 2, 10))), "B", [], s_def, []));
                                     ("a", Struct (Lexed ((("f.c", 1, 1), ("f.c", 1, 10))), "A", [], s_def, []))] in
  check "sort_decls_lexically" (fst (List.hd sorted) = "a")

(* ========================================== *)
(* Suite 11: Verifast0                        *)
(* ========================================== *)
let test_verifast0 () =
  let open Verifast0 in
  check "lookup found" (lookup [("x", 10); ("y", 20)] "y" = 20);
  let env = update [("x", 10)] "z" 30 in
  check "update" (lookup env "z" = 30);
  check "string_of_env" (string_of_env [("a", "1"); ("b", "2")] = "a = 1; b = 2");
  check "is_lemma Lemma" (is_lemma (Lemma (true, None)));
  check "is_lemma Regular" (not (is_lemma Regular));
  check "tparam_is_uppercase T" (tparam_is_uppercase "T");
  check "tparam_is_uppercase t" (not (tparam_is_uppercase "t"));
  check "tparam_is_uppercase empty" (not (tparam_is_uppercase ""));
  check "tparam_is_uppercase_or_lifetime T" (tparam_is_uppercase_or_lifetime "T");
  check "tparam_is_uppercase_or_lifetime 'a" (tparam_is_uppercase_or_lifetime "'a");
  check "tparam_is_uppercase_or_lifetime x" (not (tparam_is_uppercase_or_lifetime "x"));
  check "tparam_is_uppercase_or_lifetime empty" (not (tparam_is_uppercase_or_lifetime ""));
  
  check "tparams_with_default_bounds_exprs" (List.length (tparams_with_default_bounds_exprs ["T"; "'a"]) = 2);
  let ctxts = [
    Executing ([], [], dummy_loc, "step 1");
    PushSubcontext;
    Executing ([], [], dummy_loc, "step 2");
    PopSubcontext;
    Branching LeftBranch;
    Assuming ()
  ] in
  check "get_callers" (List.length (get_callers ctxts) >= 0);
  check "get_root_caller" (get_root_caller ctxts = Some dummy_loc);

    let rust_only_types = [
    RustChar;
    PtrType Void;
    RustRefType (StaticLifetime, Mutable, Int (Signed, IntRank));
    RustRefType (StaticLifetime, Shared, Int (Signed, IntRank));
    BoundedGhostTypeParam ("T", {sized = true; eqs = []});
    StaticLifetime;
    ProjectionType (Int (Signed, IntRank), "Trait", [Bool], "Assoc");
    Str;
    Slice (Int (Signed, IntRank))
  ] in
  let c_java_types = [
    Bool; Void;
    Int (Signed, CharRank); Int (Unsigned, CharRank);
    Int (Signed, ShortRank); Int (Unsigned, ShortRank);
    Int (Signed, IntRank); Int (Unsigned, IntRank);
    Int (Signed, LongRank); Int (Unsigned, LongRank);
    Int (Signed, LongLongRank); Int (Unsigned, LongLongRank);
    Int (Signed, PtrRank); Int (Unsigned, PtrRank);
    Int (Signed, FixedWidthRank 1); Int (Unsigned, FixedWidthRank 1);
    Int (Signed, FixedWidthRank 2); Int (Unsigned, FixedWidthRank 2);
    Float; Double; LongDouble; RealType;
    InductiveType ("List", []);
    InductiveType ("List", [Int (Signed, IntRank)]);
    ObjType ("C", []);
    ObjType ("C", [Bool]);
    StructType ("Point", []);
    StructType ("Point", [Int (Signed, IntRank)]);
    UnionType "U";
    PtrType (Int (Signed, IntRank));
    FuncType "my_func";
    InlineFuncType (Int (Signed, IntRank));
    PredType ([], [Int (Signed, IntRank)], None, Inductiveness_Inductive);
    PredType (["T"], [Int (Signed, IntRank); Bool], Some 1, Inductiveness_CoInductive);
    PureFuncType (Int (Signed, IntRank), PureFuncType (Bool, Void));
    BoxIdType; HandleIdType; AnyType;
    RealTypeParam "T"; RealTypeParam "t";
    GhostTypeParam "T"; GhostTypeParam "t";
    InferredRealType "r";
    InferredType (object end, ref (EqConstraint (Int (Signed, IntRank))));
    InferredType (object end, ref Unconstrained);
    ArrayType (Int (Signed, IntRank));
    StaticArrayType (Int (Signed, IntRank), LiteralConstType (Z.of_int 5));
    LiteralConstType (Z.of_int 42);
    ClassOrInterfaceName "Cls";
    PackageName "pkg";
    RefType (Int (Signed, IntRank));
    AbstractType "Abs"
  ] in
  List.iter (fun t ->
    (try ignore (c_string_of_type t) with Match_failure _ -> Printf.eprintf "FAILED ON C TYPE
"; raise (Match_failure ("test", 0, 0)));
    check "c_string_of_type" (String.length (c_string_of_type t) > 0);
    check "java_string_of_type" (String.length (java_string_of_type t) > 0);
    check "string_of_type CLang" (String.length (string_of_type CLang None t) > 0);
    check "string_of_type Java" (String.length (string_of_type Java None t) > 0)
  ) c_java_types;
  List.iter (fun t ->
    check "rust_string_of_type" (String.length (rust_string_of_type t) > 0);
    check "string_of_type Rust" (String.length (string_of_type CLang (Some Rust) t) > 0)
  ) (c_java_types @ rust_only_types);
  check "cxx_dtor_name" (cxx_dtor_name "MyClass" = "~MyClass()");
  check "bases_constructed_pred_name" (bases_constructed_pred_name "Base" = "Base_bases_constructed");
  check "vtype_pred_name" (vtype_pred_name "Foo" = "Foo_vtype");

  let module S = StringOf(struct let string_of_type = c_string_of_type end) in
  check "string_of_targs empty" (S.string_of_targs [] = "");
  check "string_of_targs non-empty" (String.length (S.string_of_targs [Int (Signed, IntRank)]) > 0);
  let chunk = Chunk (("p", true), [Int (Signed, IntRank)], "1", ["x"], None) in
  check "string_of_chunk coef 1" (String.length (S.string_of_chunk chunk) > 0);
  let chunk2 = Chunk (("p", true), [Int (Signed, IntRank)], "1/2", ["x"], None) in
  check "string_of_chunk coef 1/2" (String.length (S.string_of_chunk chunk2) > 0);
  check "string_of_heap" (String.length (S.string_of_heap [chunk; chunk2]) > 0);
  check "string_of_context Assuming" (String.length (S.string_of_context (Assuming "t")) > 0);
  check "string_of_context Executing" (String.length (S.string_of_context (Executing ([chunk], [("x", "1")], dummy_loc, "msg"))) > 0);
  check "string_of_context Push" (String.length (S.string_of_context PushSubcontext) > 0);
  check "string_of_context Pop" (String.length (S.string_of_context PopSubcontext) > 0);
  check "string_of_context LeftBranch" (String.length (S.string_of_context (Branching LeftBranch)) > 0);
  check "string_of_context RightBranch" (String.length (S.string_of_context (Branching RightBranch)) > 0)


(* ========================================== *)
(* Suite 12: Ast Unify & Helpers              *)
(* ========================================== *)
let test_ast_unify_and_helpers () =
  let t_int = Ast.Int (Signed, IntRank) in
  let all_types = [
    Ast.Bool; Ast.Void; t_int;
    Ast.Int (Unsigned, IntRank); Ast.Float; Ast.Double;
    Ast.RealType; Ast.InductiveType ("List", [t_int]);
    Ast.ObjType ("C", []); Ast.StructType ("Point", []);
    Ast.UnionType "U"; Ast.PtrType t_int;
    Ast.FuncType "f"; Ast.InlineFuncType t_int;
    Ast.ArrayType t_int; Ast.LiteralConstType (Z.of_int 10);
    Ast.AbstractType "A"; Ast.Str; Ast.Slice t_int
  ] in
  List.iter (fun t ->
    check "unfold_inferred_type" (unfold_inferred_type t = t)
  ) all_types;

  (* string_of_loc, string_of_srcpos, string_of_loc0 *)
  check "string_of_srcpos" (String.length (string_of_srcpos ("f.c", 10, 5)) > 0);
  check "string_of_loc0 same" (String.length (string_of_loc0 (("f.c", 1, 1), ("f.c", 1, 10))) > 0);
  check "string_of_loc0 diff_line" (String.length (string_of_loc0 (("f.c", 1, 1), ("f.c", 2, 5))) > 0);
  check "string_of_loc0 diff_file" (String.length (string_of_loc0 (("f.c", 1, 1), ("g.c", 1, 5))) > 0);
  check "string_of_loc Lexed" (String.length (string_of_loc (Lexed (("f.c", 1, 1), ("f.c", 1, 5)))) > 0);
  check "string_of_loc DummyLoc" (string_of_loc DummyLoc = "<dummy location>");
  check "root_caller_token" (root_caller_token DummyLoc = dummy_loc0);
  check "lexed_loc" (lexed_loc DummyLoc = dummy_loc0);
  check "parse_error_attributes None" (parse_error_attributes None = {help_topic = None; quick_fixes = []});
  check "parse_error_attributes Some" (
    let attrs = parse_error_attributes (Some [HelpTopic "url"; QuickFix ("desc", InsertTextAt (("f.c", 1, 1), "text"))]) in
    attrs.help_topic = Some "url" && List.length attrs.quick_fixes = 1
  );

  (* Src_loc_aux *)
  check "loc0_contains_srcpos inside" (Src_loc_aux.loc0_contains_srcpos (("a.c", 1, 1), ("a.c", 5, 10)) ("a.c", 2, 4));
  check "loc0_contains_srcpos outside" (not (Src_loc_aux.loc0_contains_srcpos (("a.c", 1, 1), ("a.c", 5, 10)) ("b.c", 2, 4)));
  check "loc_contains_srcpos inside" (Src_loc_aux.loc_contains_srcpos (Lexed (("a.c", 1, 1), ("a.c", 5, 10))) ("a.c", 2, 4));
  check "try_compare_loc same" (Src_loc_aux.try_compare_loc (("a.c", 1, 1), ("a.c", 1, 2)) (("a.c", 2, 1), ("a.c", 2, 2)) = Ok (-1));
  check "cover_loc0 ok" (Result.is_ok (Src_loc_aux.cover_loc0 (("a.c", 1, 1), ("a.c", 2, 2)) (("a.c", 1, 1), ("a.c", 2, 2))))

(* ========================================== *)
(* Suite 13: Lexer Deep Utilities & Operators *)
(* ========================================== *)
let test_lexer_deep () =
  (* latin1_to_utf8 *)
  check "latin1_to_utf8 ascii" (latin1_to_utf8 "hello" = "hello");
  let non_ascii = "\xe9\xe8\xe0" in
  let utf8_res = latin1_to_utf8 non_ascii in
  check "latin1_to_utf8 non-ascii" (String.length utf8_res > String.length non_ascii);

  (* file_to_utf8 and utf8_to_file *)
  let with_bom = utf8_byte_order_mark ^ "int x = 1;" in
  check "file_to_utf8 with BOM" (file_to_utf8 with_bom = "int x = 1;");
  check "file_to_utf8 without BOM" (file_to_utf8 "int x = 1;" = "int x = 1;");
  check "utf8_to_file" (utf8_to_file "ascii text" = "ascii text");

  (* get_first_line_tokens & split_into_words *)
  let opt_line = "// verifast_options{target:x86_64 prover:z3v4.5 skip_specless_fns}" in
  let first_tokens = get_first_line_tokens opt_line in
  check "get_first_line_tokens" (List.length first_tokens > 0);
  let words = split_into_words "word1 \"quoted word2\" word3" in
  check "split_into_words" (List.length words = 3);
  check "split_into_words quoted" (List.nth words 1 = "quoted word2");

  (* get_file_options & readFileOptions *)
  let parsed_opts = get_file_options opt_line in
  check "get_file_options prover" (parsed_opts.prover = Some "z3v4.5");
  check "get_file_options bindings" (List.length parsed_opts.bindings >= 2);
  let opts_annot = get_file_options "// verifast_annotation_char:# tab_size:8" in
  check "get_file_options annot_char" (opts_annot.annot_char = '#');
  check "get_file_options tab_size" (opts_annot.tab_size = 8);

  let tmp_opt_file = Filename.concat (Filename.get_temp_dir_name ()) "test_file_opts.c" in
  let oc = open_out tmp_opt_file in
  output_string oc "// verifast_options{prover:redux}\nint main() { return 0; }\n";
  close_out oc;
  let file_opts = readFileOptions tmp_opt_file in
  check "readFileOptions" (file_opts.prover = Some "redux");
  Sys.remove tmp_opt_file;

  (* string_of_include_kind *)
  check "string_of_include_kind Double" (string_of_include_kind DoubleQuoteInclude = "DoubleQuoteInclude");
  check "string_of_include_kind Angle" (string_of_include_kind AngleBracketInclude = "AngleBracketInclude");

  (* string_of_token across all variants *)
  let bi = big_int_of_int 42 in
  let num_val = num_of_int 42 in
  let all_tokens = [
    Kwd "while"; Ident "my_var";
    Int (bi, true, false, NoLSuffix, "42");
    Int (bi, true, true, LSuffix, "42UL");
    Int (bi, false, false, LLSuffix, "0x2A");
    RealToken bi;
    RationalToken (num_val, None);
    RationalToken (num_val, Some FloatFSuffix);
    RationalToken (num_val, Some FloatLSuffix);
    String "hello";
    AngleBracketString "stdio.h";
    CharToken 'z';
    BeginInclude (DoubleQuoteInclude, "header.h", "");
    SecondaryInclude ("header2.h", "");
    EndInclude;
    Eol;
    Eof;
    ErrorToken
  ] in
  List.iter (fun tok ->
    check "string_of_token non-empty" (String.length (string_of_token tok) > 0)
  ) all_tokens;

  (* compare_tokens *)
  check "compare_tokens None None" (compare_tokens None None);
  check "compare_tokens same Int" (compare_tokens (Some (dummy_loc, Int (bi, true, false, NoLSuffix, "42"))) (Some (dummy_loc, Int (bi, true, false, NoLSuffix, "42"))));
  check "compare_tokens diff Int" (not (compare_tokens (Some (dummy_loc, Int (bi, true, false, NoLSuffix, "42"))) (Some (dummy_loc, Int (bi, true, false, NoLSuffix, "43")))));
  check "compare_tokens RealToken" (compare_tokens (Some (dummy_loc, RealToken bi)) (Some (dummy_loc, RealToken bi)));
  check "compare_tokens RationalToken" (compare_tokens (Some (dummy_loc, RationalToken (num_val, None))) (Some (dummy_loc, RationalToken (num_val, None))));
  check "compare_tokens generic Kwd" (compare_tokens (Some (dummy_loc, Kwd "x")) (Some (dummy_loc, Kwd "x")));

  (* big_int_of_hex_string & big_int_of_octal_string *)
  check "big_int_of_hex_string 0x0" (eq_big_int (big_int_of_hex_string "0x0") zero_big_int);
  check "big_int_of_hex_string 0x2A" (eq_big_int (big_int_of_hex_string "0x2A") (big_int_of_int 42));
  check "big_int_of_hex_string 0xFF" (eq_big_int (big_int_of_hex_string "0xFF") (big_int_of_int 255));
  check "big_int_of_hex_string upper" (eq_big_int (big_int_of_hex_string "0xDEAD") (big_int_of_int 0xDEAD));
  check "big_int_of_octal_string 0" (eq_big_int (big_int_of_octal_string "0") zero_big_int);
  check "big_int_of_octal_string 77" (eq_big_int (big_int_of_octal_string "77") (big_int_of_int 63));
  check "big_int_of_octal_string 123" (eq_big_int (big_int_of_octal_string "123") (big_int_of_int 83));

  (* string_of_range_kind *)
  let range_kinds = [
    KeywordRange; GhostKeywordRange; GhostRange; GhostRangeDelimiter; CommentRange; ErrorRange
  ] in
  List.iter (fun rk ->
    check "string_of_range_kind" (String.length (string_of_range_kind rk) > 0)
  ) range_kinds;

  (* is_ghost_header *)
  check "is_ghost_header .gh" (is_ghost_header "list.gh");
  check "is_ghost_header .h" (not (is_ghost_header "list.h"));
  check "is_ghost_header .c" (not (is_ghost_header "list.c"));

  (* Macro_param *)
  check "name_of_macro_param Ident" (Macro_param.name_of_macro_param (Macro_param.Ident "x") = "x");
  check "name_of_macro_param VarArgs Some" (Macro_param.name_of_macro_param (Macro_param.VarArgs (Some "args")) = "args");
  check "name_of_macro_param VarArgs None" (Macro_param.name_of_macro_param (Macro_param.VarArgs None) = "__VA_ARGS__");

  (* eval_operators on preprocessor AST expressions *)
  let lit n = IntLit (dummy_loc, big_int_of_int n, true, false, NoLSuffix) in
  let op2 op e1 e2 = Operation (dummy_loc, op, [e1; e2]) in
  let op1 op e = Operation (dummy_loc, op, [e]) in

  check "eval Add" (eq_big_int (snd (eval_operators (op2 Add (lit 10) (lit 20)))) (big_int_of_int 30));
  check "eval Sub" (eq_big_int (snd (eval_operators (op2 Sub (lit 20) (lit 5)))) (big_int_of_int 15));
  check "eval Mul" (eq_big_int (snd (eval_operators (op2 Mul (lit 6) (lit 7)))) (big_int_of_int 42));
  check "eval Div" (eq_big_int (snd (eval_operators (op2 Div (lit 42) (lit 7)))) (big_int_of_int 6));
  check "eval Mod" (eq_big_int (snd (eval_operators (op2 Mod (lit 45) (lit 7)))) (big_int_of_int 3));
  check "eval ShiftLeft" (eq_big_int (snd (eval_operators (op2 ShiftLeft (lit 1) (lit 4)))) (big_int_of_int 16));
  check "eval ShiftRight" (eq_big_int (snd (eval_operators (op2 ShiftRight (lit 16) (lit 2)))) (big_int_of_int 4));
  check "eval Eq true" (eq_big_int (snd (eval_operators (op2 Eq (lit 5) (lit 5)))) unit_big_int);
  check "eval Eq false" (eq_big_int (snd (eval_operators (op2 Eq (lit 5) (lit 6)))) zero_big_int);
  check "eval Neq" (eq_big_int (snd (eval_operators (op2 Neq (lit 5) (lit 6)))) unit_big_int);
  check "eval Lt" (eq_big_int (snd (eval_operators (op2 Lt (lit 3) (lit 5)))) unit_big_int);
  check "eval Le" (eq_big_int (snd (eval_operators (op2 Le (lit 5) (lit 5)))) unit_big_int);
  check "eval Gt" (eq_big_int (snd (eval_operators (op2 Gt (lit 5) (lit 3)))) unit_big_int);
  check "eval Ge" (eq_big_int (snd (eval_operators (op2 Ge (lit 5) (lit 5)))) unit_big_int);
  check "eval BitAnd" (eq_big_int (snd (eval_operators (op2 BitAnd (lit 0xF) (lit 0x3)))) (big_int_of_int 3));
  check "eval BitOr" (eq_big_int (snd (eval_operators (op2 BitOr (lit 0x1) (lit 0x2)))) (big_int_of_int 3));
  check "eval BitXor" (eq_big_int (snd (eval_operators (op2 BitXor (lit 0x3) (lit 0x1)))) (big_int_of_int 2));
  check "eval And" (eq_big_int (snd (eval_operators (op2 And (lit 1) (lit 1)))) unit_big_int);
  check "eval Or" (eq_big_int (snd (eval_operators (op2 Or (lit 1) (lit 0)))) unit_big_int);
  check "eval Not" (eq_big_int (snd (eval_operators (op1 Not (lit 0)))) unit_big_int);
  check "eval Not false" (eq_big_int (snd (eval_operators (op1 Not (lit 1)))) zero_big_int)

(* ========================================== *)
(* Suite 14: Ocaml_expr_of_ast All Variants   *)
(* ========================================== *)
let test_ocaml_expr_of_ast_deep () =
  let t_int = Ast.Int (Signed, IntRank) in
  let e_var = Var (dummy_loc, "x") in
  let e_int = IntLit (dummy_loc, big_int_of_int 42, true, false, NoLSuffix) in
  let te_int = InferredTypeExpr dummy_loc in

  (* of_inductiveness, of_signedness, of_int_rank, of_rust_ref_kind *)
  check "of_inductiveness Inductive" (String.length (string_of_ocaml_expr true (of_inductiveness Inductiveness_Inductive)) > 0);
  check "of_inductiveness CoInductive" (String.length (string_of_ocaml_expr true (of_inductiveness Inductiveness_CoInductive)) > 0);
  check "of_signedness Signed" (String.length (string_of_ocaml_expr true (of_signedness Signed)) > 0);
  check "of_signedness Unsigned" (String.length (string_of_ocaml_expr true (of_signedness Unsigned)) > 0);
  let ranks = [CharRank; ShortRank; IntRank; LongRank; LongLongRank; PtrRank; FixedWidthRank 8] in
  List.iter (fun r ->
    check "of_int_rank" (String.length (string_of_ocaml_expr true (of_int_rank r)) > 0)
  ) ranks;
  let ref_kinds = [Shared; Mutable] in
  List.iter (fun k ->
    check "of_rust_ref_kind" (String.length (string_of_ocaml_expr true (of_rust_ref_kind k)) > 0)
  ) ref_kinds;

  (* of_prover_type *)
  let prover_types = [ProverBool; ProverInt; ProverReal; ProverInductive] in
  List.iter (fun pt ->
    check "of_prover_type" (String.length (string_of_ocaml_expr true (of_prover_type pt)) > 0)
  ) prover_types;

  (* of_pred_name, of_predref, of_ident_scope *)
  check "of_pred_name PredFam" (String.length (string_of_ocaml_expr true (of_pred_name (PredFam "p"))) > 0);
  check "of_pred_name PredCtor" (String.length (string_of_ocaml_expr true (of_pred_name (PredCtor "c"))) > 0);
  check "of_pred_name LocalVar" (String.length (string_of_ocaml_expr true (of_pred_name (LocalVar "v"))) > 0);
  check "of_predref" (String.length (string_of_ocaml_expr true (of_predref (new predref (PredFam "p") [] None))) > 0);
  check "of_ident_scope LocalVar" (String.length (string_of_ocaml_expr true (of_ident_scope LocalVar)) > 0);
  check "of_ident_scope FuncName" (String.length (string_of_ocaml_expr true (of_ident_scope FuncName)) > 0);
  check "of_ident_scope PredFamName" (String.length (string_of_ocaml_expr true (of_ident_scope PredFamName)) > 0);
  check "of_ident_scope GlobalName" (String.length (string_of_ocaml_expr true (of_ident_scope GlobalName)) > 0);
  check "of_ident_scope EnumElemName" (String.length (string_of_ocaml_expr true (of_ident_scope (EnumElemName (big_int_of_int 1)))) > 0);

  (* of_int_literal_lsuffix, of_float_literal_suffix *)
  let lsuffs = [NoLSuffix; LSuffix; LLSuffix] in
  List.iter (fun s ->
    check "of_int_literal_lsuffix" (String.length (string_of_ocaml_expr true (of_int_literal_lsuffix s)) > 0)
  ) lsuffs;
  let fsuffs = [FloatFSuffix; FloatLSuffix] in
  List.iter (fun s ->
    check "of_float_literal_suffix" (String.length (string_of_ocaml_expr true (of_float_literal_suffix s)) > 0)
  ) fsuffs;

  (* string_of_operator all 22 operators *)
  let operators = [
    Add; Sub; PtrDiff; Le; Ge; Lt; Gt; Eq; Neq; And; Or; Xor; Not;
    Mul; Div; Mod; BitNot; BitAnd; BitXor; BitOr; ShiftLeft; ShiftRight
  ] in
  List.iter (fun op ->
    check "string_of_operator" (String.length (string_of_operator op) > 0);
    check "of_operator" (String.length (string_of_ocaml_expr true (of_operator op)) > 0)
  ) operators;
  check "of_operator MinValue" (String.length (string_of_ocaml_expr true (of_operator (MinValue t_int))) > 0);
  check "of_operator MaxValue" (String.length (string_of_ocaml_expr true (of_operator (MaxValue t_int))) > 0);

  (* of_type_expr all variants *)
  let type_exprs = [
    StructTypeExpr (dummy_loc, Some "Point", None, [Packed], []);
    UnionTypeExpr (dummy_loc, Some "U", None);
    EnumTypeExpr (dummy_loc, Some "E", Some [("A", None); ("B", Some e_int)]);
    PtrTypeExpr (dummy_loc, te_int);
    RustRefTypeExpr (dummy_loc, te_int, Mutable, te_int);
    ArrayTypeExpr (dummy_loc, te_int);
    StaticArrayTypeExpr (dummy_loc, te_int, te_int);
    LiteralConstTypeExpr (dummy_loc, Z.of_int 10);
    FuncTypeExpr (dummy_loc, te_int, [(te_int, "arg")]);
    ManifestTypeExpr (dummy_loc, t_int);
    IdentTypeExpr (dummy_loc, None, "MyType");
    PredTypeExpr (dummy_loc, [te_int], Some 1);
    PureFuncTypeExpr (dummy_loc, [(te_int, Some (dummy_loc, "x"))], Some (True dummy_loc));
    LValueRefTypeExpr (dummy_loc, te_int);
    ConstTypeExpr (dummy_loc, te_int);
    ProjectionTypeExpr (dummy_loc, te_int, "Trait", [], "Assoc");
    SliceTypeExpr (dummy_loc, te_int)
  ] in
  List.iter (fun te ->
    check "of_type_expr" (String.length (string_of_ocaml_expr true (of_type_expr te)) > 0)
  ) type_exprs;

  (* of_expr across rich expressions *)
  let exprs = [
    True dummy_loc; False dummy_loc; Null dummy_loc;
    Var (dummy_loc, "x");
    WVar (dummy_loc, "x", LocalVar);
    TruncatingExpr (dummy_loc, e_var);
    Operation (dummy_loc, Add, [e_var; e_int]);
    WOperation (dummy_loc, Mul, [e_var; e_int], t_int);
    IntLit (dummy_loc, big_int_of_int 42, true, false, NoLSuffix);
    WIntLit (dummy_loc, big_int_of_int 42);
    RealLit (dummy_loc, num_of_int 5, Some FloatFSuffix);
    StringLit (dummy_loc, "test");
    ClassLit (dummy_loc, "MyClass");
    Typeid (dummy_loc, e_var);
    TypeInfo (dummy_loc, t_int);
    Read (dummy_loc, e_var, "f");
    Select (dummy_loc, e_var, "f");
    ActivatingRead (dummy_loc, e_var, "f");
    ReadArray (dummy_loc, e_var, e_int);
    WReadArray (dummy_loc, e_var, t_int, e_int);
    Deref (dummy_loc, e_var);
    WDeref (dummy_loc, e_var, t_int)
  ] in
  List.iter (fun e ->
    check "of_expr" (String.length (string_of_ocaml_expr true (of_expr e)) > 0)
  ) exprs;

  (* of_field, of_ctor, of_struct_attr, of_constant_value, of_decl *)
  let fld = Field (dummy_loc, Real, te_int, "val", Static, Public, false, Some e_int) in
  check "of_field" (String.length (string_of_ocaml_expr true (of_field fld)) > 0);

  let ctor = Ctor (dummy_loc, "MyCtor", [("a", te_int)]) in
  check "of_ctor" (String.length (string_of_ocaml_expr true (of_ctor ctor)) > 0);

  let cvals = [IntConst (big_int_of_int 7); BoolConst true; StringConst "str"; NullConst; GhostConst (True dummy_loc)] in
  List.iter (fun cv ->
    check "of_constant_value" (String.length (string_of_ocaml_expr true (of_constant_value cv)) > 0)
  ) cvals;

  let decls = [
    EnumDecl (dummy_loc, "Color", [("Red", None); ("Green", Some e_int)]);
    TypeWithTypeidDecl (dummy_loc, "MyId", e_var)
  ] in
  List.iter (fun d ->
    check "of_decl" (String.length (string_of_ocaml_expr true (of_decl d)) > 0)
  ) decls

(* ========================================== *)
(* Suite 15: Json Module Comprehensive        *)
(* ========================================== *)
let test_json_module () =
  let open Json in
  (* Value accessors *)
  check "s_value" (s_value (S "str") = "str");
  check "i_value" (i_value (I 42) = 42);
  check "a_value" (a_value (A [I 1; I 2]) = [I 1; I 2]);
  check "o_assoc" (o_assoc "k" (O [("k", S "v"); ("k2", I 2)]) = S "v");

  (* string_of_token_type *)
  let tokens = [LBracket; RBracket; LBrace; RBrace; Comma; Colon; NullToken; True; False; Integer; String; Eof] in
  List.iter (fun tok ->
    check "string_of_token_type" (String.length (string_of_token_type tok) > 0)
  ) tokens;

  (* Serialization: string_of_json *)
  check "json Null" (string_of_json Null = "null");
  check "json True" (string_of_json (B true) = "true");
  check "json False" (string_of_json (B false) = "false");
  check "json I" (string_of_json (I 123) = "123");
  check "json I neg" (string_of_json (I (-456)) = "-456");
  check "json F" (String.length (string_of_json (F 3.14159)) > 0);
  check "json S" (String.length (string_of_json (S "hello\n\t\"world\"")) > 0);
  check "json S ctrl" (String.contains (string_of_json (S "\x01\x1f")) '\\');
  check "json A empty" (string_of_json (A []) = "[]");
  check "json A non-empty" (string_of_json (A [I 1; B true; Null]) = "[1,true,null]");
  check "json O empty" (string_of_json (O []) = "{}");
  check "json O non-empty" (string_of_json (O [("a", I 1); ("b", B false)]) = "{\"a\":1,\"b\":false}");

  (* Pretty-printing: buffer_add_json_pp *)
  let buf = Buffer.create 128 in
  buffer_add_json_pp buf 2 (O [("nested", A [I 1; I 2]); ("empty_arr", A []); ("empty_obj", O [])]);
  check "buffer_add_json_pp non-empty" (Buffer.length buf > 0);

  (* Parsing: parse_json *)
  check "parse null" (parse_json "null" = Null);
  check "parse true" (parse_json "true" = B true);
  check "parse false" (parse_json "false" = B false);
  check "parse int" (parse_json "42" = I 42);
  check "parse neg int" (parse_json "-100" = I (-100));
  check "parse str simple" (parse_json "\"hello\"" = S "hello");
  check "parse str escapes" (parse_json "\"\\\"\\\\\\n\\r\\t\\u0041\"" = S "\"\\\n\r\tA");
  check "parse str surrogate" (parse_json "\"\\uD83D\\uDE00\"" = S "\xF0\x9F\x98\x80");
  check "parse empty array" (parse_json "[]" = A []);
  check "parse array" (parse_json "[1, true, null, \"foo\"]" = A [I 1; B true; Null; S "foo"]);
  check "parse empty obj" (parse_json "{}" = O []);
  check "parse obj" (parse_json "{\"x\": 10, \"y\": [20, 30]}" = O [("x", I 10); ("y", A [I 20; I 30])]);

  (* Error handling *)
  let should_fail_parse s =
    try let _ = parse_json s in false with Json.JsonException _ -> true
  in
  check "error invalid token" (should_fail_parse "invalid");
  check "error unclosed brace" (should_fail_parse "{\"a\": 1");
  check "error unclosed bracket" (should_fail_parse "[1, 2");
  check "error missing colon" (should_fail_parse "{\"a\" 1}");
  check "error unclosed str" (should_fail_parse "\"unclosed");
  check "error bad escape" (should_fail_parse "\"\\x\"");
  check "error bad unicode" (should_fail_parse "\"\\u123\"");
  check "error unpaired high surrogate" (should_fail_parse "\"\\uD800\\u0000\"")

(* =================================================== *)
(* Suite 16: Ast Exhaustive Locators, Types & Inspector *)
(* =================================================== *)
let test_ast_exhaustive_locs_and_types () =
  let t_int = Ast.Int (Signed, IntRank) in
  let e_var = Var (dummy_loc, "x") in
  let e_int = IntLit (dummy_loc, big_int_of_int 42, true, false, NoLSuffix) in
  let te_int = InferredTypeExpr dummy_loc in

  (* string_of_inductiveness *)
  check "string_of_inductiveness Inductive" (string_of_inductiveness Inductiveness_Inductive = "inductive");
  check "string_of_inductiveness CoInductive" (string_of_inductiveness Inductiveness_CoInductive = "coinductive");

  (* string_of_func_kind & tostring *)
  check "string_of_func_kind Lemma" (string_of_func_kind (Lemma (false, None)) = "lemma");
  check "string_of_func_kind Regular" (string_of_func_kind Regular = "regular");
  check "string_of_func_kind Fixpoint" (string_of_func_kind Fixpoint = "fixpoint");
  check "tostring Instance" (tostring Instance = "instance");
  check "tostring Static" (tostring Static = "static");
  check "func_kind_of_ghostness Real" (func_kind_of_ghostness Real = Regular);
  check "func_kind_of_ghostness Ghost" (match func_kind_of_ghostness Ghost with Lemma _ -> true | _ -> false);

  (* is_ptr_type *)
  check "is_ptr_type true" (is_ptr_type (PtrType Bool));
  check "is_ptr_type false" (not (is_ptr_type Bool));

  (* inferred_type_constraint_le & meet *)
  check "constraint_le 1" (inferred_type_constraint_le Unconstrained Unconstrained);
  check "constraint_le 2" (inferred_type_constraint_le (ContainsAnyConstraint true) Unconstrained);
  check "constraint_le 3" (not (inferred_type_constraint_le Unconstrained (ContainsAnyConstraint true)));
  check "constraint_le 4" (inferred_type_constraint_le (ContainsAnyConstraint false) (ContainsAnyConstraint false));
  check "constraint_meet" (inferred_type_constraint_meet Unconstrained (ContainsAnyConstraint true) = ContainsAnyConstraint true);

  (* type_fold_open *)
  let collect_types tp =
    type_fold_open [] (fun acc t -> t :: acc) tp
  in
  let all_compound_types = [
    StructType ("S", [Bool; t_int]);
    PtrType t_int;
    RustRefType (StaticLifetime, Mutable, t_int);
    InlineFuncType t_int;
    InductiveType ("I", [Bool]);
    PredType ([], [Bool], None, Inductiveness_Inductive);
    PureFuncType (Bool, t_int);
    ObjType ("O", [Bool]);
    ArrayType t_int;
    StaticArrayType (t_int, t_int);
    RefType t_int;
    ProjectionType (Bool, "Trait", [t_int], "Assoc");
    Slice t_int
  ] in
  List.iter (fun tp ->
    check "type_fold_open" (List.length (collect_types tp) >= 1)
  ) all_compound_types;

  (* type_expr_loc on all variants *)
  let all_type_exprs = [
    ManifestTypeExpr (dummy_loc, t_int);
    StructTypeExpr (dummy_loc, Some "S", None, [], []);
    UnionTypeExpr (dummy_loc, Some "U", None);
    EnumTypeExpr (dummy_loc, Some "E", None);
    IdentTypeExpr (dummy_loc, None, "T");
    ConstructedTypeExpr (dummy_loc, "C", []);
    PtrTypeExpr (dummy_loc, te_int);
    RustRefTypeExpr (dummy_loc, te_int, Shared, te_int);
    ArrayTypeExpr (dummy_loc, te_int);
    StaticArrayTypeExpr (dummy_loc, te_int, te_int);
    LiteralConstTypeExpr (dummy_loc, Z.of_int 5);
    PredTypeExpr (dummy_loc, [], None);
    PureFuncTypeExpr (dummy_loc, [], None);
    LValueRefTypeExpr (dummy_loc, te_int);
    FuncTypeExpr (dummy_loc, te_int, []);
    ConstTypeExpr (dummy_loc, te_int);
    ProjectionTypeExpr (dummy_loc, te_int, "Tr", [], "As");
    SliceTypeExpr (dummy_loc, te_int)
  ] in
  List.iter (fun te ->
    check "type_expr_loc" (type_expr_loc te = dummy_loc)
  ) all_type_exprs;

  (* expr_loc on wide variety of exprs *)
  let all_exprs = [
    True dummy_loc; False dummy_loc; Null dummy_loc;
    Var (dummy_loc, "x"); WVar (dummy_loc, "x", LocalVar);
    IntLit (dummy_loc, big_int_of_int 1, true, false, NoLSuffix);
    WIntLit (dummy_loc, big_int_of_int 1);
    RealLit (dummy_loc, num_of_int 1, None);
    StringLit (dummy_loc, "s"); ClassLit (dummy_loc, "C");
    TruncatingExpr (dummy_loc, e_var);
    Operation (dummy_loc, Add, [e_var; e_int]);
    WOperation (dummy_loc, Add, [e_var; e_int], t_int);
    SliceExpr (dummy_loc, Some (LitPat e_var), Some (LitPat e_int));
    Read (dummy_loc, e_var, "f");
    Select (dummy_loc, e_var, "f");
    ArrayLengthExpr (dummy_loc, e_var);
    Deref (dummy_loc, e_var);
    WDeref (dummy_loc, e_var, t_int);
    CallExpr (dummy_loc, "f", [], [], [], Static);
    ExprCallExpr (dummy_loc, e_var, []);
    IfExpr (dummy_loc, True dummy_loc, e_var, e_int);
    SizeofExpr (dummy_loc, TypeExpr (ManifestTypeExpr (dummy_loc, t_int)));
    AlignofExpr (dummy_loc, ManifestTypeExpr (dummy_loc, t_int));
    TypeExpr (ManifestTypeExpr (dummy_loc, t_int));
    CastExpr (dummy_loc, ManifestTypeExpr (dummy_loc, t_int), e_var);
    TypedExpr (e_var, t_int);
    AddressOf (dummy_loc, e_var);
    AssignExpr (dummy_loc, e_var, Mutation, e_int);
    CommaExpr (dummy_loc, e_var, e_int);
    PointsTo (dummy_loc, e_var, RegularPointsTo, LitPat e_int);
    PredAsn (dummy_loc, "p", [], [], [], Static);
    ExprAsn (dummy_loc, True dummy_loc);
    EmpAsn dummy_loc;
    Sep (dummy_loc, ExprAsn (dummy_loc, True dummy_loc), ExprAsn (dummy_loc, True dummy_loc));
    IfAsn (dummy_loc, True dummy_loc, ExprAsn (dummy_loc, True dummy_loc), ExprAsn (dummy_loc, True dummy_loc))
  ] in
  List.iter (fun e ->
    check "expr_loc" (expr_loc e = dummy_loc);
    check "asn_loc" (asn_loc e = dummy_loc)
  ) all_exprs;

  (* stmt_loc *)
  let all_stmts = [
    PureStmt (dummy_loc, ExprStmt e_var);
    NonpureStmt (dummy_loc, false, ExprStmt e_var);
    ExprStmt e_var;
    DeclStmt (dummy_loc, []);
    IfStmt (dummy_loc, True dummy_loc, [], []);
    Assert (dummy_loc, ExprAsn (dummy_loc, True dummy_loc));
    Leak (dummy_loc, ExprAsn (dummy_loc, True dummy_loc));
    ReturnStmt (dummy_loc, Some e_var);
    WhileStmt (dummy_loc, True dummy_loc, None, None, [], [])
  ] in
  List.iter (fun s ->
    check "stmt_loc" (stmt_loc s = dummy_loc)
  ) all_stmts

(* ========================================== *)
(* Suite 17: Src_loc_aux Exhaustive           *)
(* ========================================== *)
let test_src_loc_aux_exhaustive () =
  let open Src_loc_aux in
  (* is_well_formed_src_pos *)
  check "wf pos valid" (is_well_formed_src_pos ("a.c", 1, 1) = Ok ());
  check "wf pos bad line" (Result.is_error (is_well_formed_src_pos ("a.c", 0, 1)));
  check "wf pos bad col" (Result.is_error (is_well_formed_src_pos ("a.c", 1, 0)));

  (* is_well_formed_loc0 *)
  let l_ok = (("a.c", 1, 1), ("a.c", 1, 10)) in
  let l_diff_file = (("a.c", 1, 1), ("b.c", 1, 10)) in
  let l_bad_order = (("a.c", 2, 1), ("a.c", 1, 10)) in
  check "wf loc0 ok" (is_well_formed_loc0 l_ok = Ok ());
  check "wf loc0 diff file" (Result.is_error (is_well_formed_loc0 l_diff_file));
  check "wf loc0 bad order" (Result.is_error (is_well_formed_loc0 l_bad_order));

  (* get_start_loc & get_last_col_loc *)
  check "get_start_loc" (Result.is_ok (get_start_loc (Lexed l_ok)));
  check "get_last_col_loc ok" (Result.is_ok (get_last_col_loc (Lexed l_ok)));
  let l_col1 = (("a.c", 1, 1), ("a.c", 1, 1)) in
  check "get_last_col_loc col 1 error" (Result.is_error (get_last_col_loc (Lexed l_col1)));

  (* try_compare_src_pos *)
  check "try_compare pos lt" (try_compare_src_pos ("a.c", 1, 1) ("a.c", 1, 2) = Ok (-1));
  check "try_compare pos gt" (try_compare_src_pos ("a.c", 2, 1) ("a.c", 1, 2) = Ok 1);
  check "try_compare pos eq" (try_compare_src_pos ("a.c", 1, 1) ("a.c", 1, 1) = Ok 0);
  check "try_compare pos diff file" (Result.is_error (try_compare_src_pos ("a.c", 1, 1) ("b.c", 1, 1)));

  (* rel & overlapping kinds *)
  let l1 = (("a.c", 1, 1), ("a.c", 1, 10)) in
  let l2_inside = (("a.c", 1, 2), ("a.c", 1, 5)) in
  let l3_disjoint = (("a.c", 2, 1), ("a.c", 2, 5)) in
  let l4_partial = (("a.c", 1, 5), ("a.c", 1, 15)) in
  check "rel Eq" (match rel l1 l1 with Ok (Overlapping { kind = Eq }) -> true | _ -> false);
  check "rel RightInLeft" (match rel l1 l2_inside with Ok (Overlapping { kind = Inclusion { kind = RightInLeft } }) -> true | _ -> false);
  check "rel LeftInRight" (match rel l2_inside l1 with Ok (Overlapping { kind = Inclusion { kind = LeftInRight } }) -> true | _ -> false);
  check "rel Partial" (match rel l1 l4_partial with Ok (Overlapping { kind = Partial _ }) -> true | _ -> false);
  check "rel Disjoint" (match rel l1 l3_disjoint with Ok (Disjoint _) -> true | _ -> false);
  let l_file_b = (("b.c", 1, 1), ("b.c", 1, 10)) in
  check "rel diff file" (match rel l1 l_file_b with Ok None -> true | _ -> false);

  (* compare_err_desc *)
  check "err_desc Loc0" (String.length (compare_err_desc (`IsWellFormedLoc0 "msg")) > 0);
  check "err_desc Pos" (String.length (compare_err_desc (`IsWellFormedSrcPos "msg")) > 0);
  check "err_desc CompareLoc" (String.length (compare_err_desc (`TryCompareLoc "msg")) > 0);
  check "err_desc ComparePos" (String.length (compare_err_desc (`TryCompareSrcPos "msg")) > 0);

  (* disjoint_batches *)
  let elms = [
    Lexed (("a.c", 1, 1), ("a.c", 1, 5));
    Lexed (("a.c", 2, 1), ("a.c", 2, 5));
    Lexed (("a.c", 2, 2), ("a.c", 2, 4))
  ] in
  let res_batches = disjoint_batches (fun x -> x) elms in
  check "disjoint_batches" (Result.is_ok res_batches)


(* ========================================== *)
(* Suite 18: Verifast0 Exhaustive             *)
(* ========================================== *)
let test_verifast0_exhaustive () =
  let open Verifast0 in
  let rust_only_types = [
    RustChar;
    PtrType Void;
    RustRefType (StaticLifetime, Mutable, Int (Signed, IntRank));
    RustRefType (StaticLifetime, Shared, Int (Signed, IntRank));
    BoundedGhostTypeParam ("T", {sized = true; eqs = []});
    StaticLifetime;
    ProjectionType (Int (Signed, IntRank), "Trait", [Bool], "Assoc");
    Str;
    Slice (Int (Signed, IntRank))
  ] in
  let c_java_types = [
    Bool; Void;
    Int (Signed, CharRank); Int (Unsigned, CharRank);
    Int (Signed, ShortRank); Int (Unsigned, ShortRank);
    Int (Signed, IntRank); Int (Unsigned, IntRank);
    Int (Signed, LongRank); Int (Unsigned, LongRank);
    Int (Signed, LongLongRank); Int (Unsigned, LongLongRank);
    Int (Signed, PtrRank); Int (Unsigned, PtrRank);
    Int (Signed, FixedWidthRank 1); Int (Unsigned, FixedWidthRank 1);
    Int (Signed, FixedWidthRank 2); Int (Unsigned, FixedWidthRank 2);
    Float; Double; LongDouble; RealType;
    InductiveType ("List", []);
    InductiveType ("List", [Int (Signed, IntRank)]);
    ObjType ("C", []);
    ObjType ("C", [Bool]);
    StructType ("Point", []);
    StructType ("Point", [Int (Signed, IntRank)]);
    UnionType "U";
    PtrType (Int (Signed, IntRank));
    FuncType "my_func";
    InlineFuncType (Int (Signed, IntRank));
    PredType ([], [Int (Signed, IntRank)], None, Inductiveness_Inductive);
    PredType (["T"], [Int (Signed, IntRank); Bool], Some 1, Inductiveness_CoInductive);
    PureFuncType (Int (Signed, IntRank), PureFuncType (Bool, Void));
    BoxIdType; HandleIdType; AnyType;
    RealTypeParam "T"; RealTypeParam "t";
    GhostTypeParam "T"; GhostTypeParam "t";
    InferredRealType "r";
    InferredType (object end, ref (EqConstraint (Int (Signed, IntRank))));
    InferredType (object end, ref Unconstrained);
    ArrayType (Int (Signed, IntRank));
    StaticArrayType (Int (Signed, IntRank), LiteralConstType (Z.of_int 5));
    LiteralConstType (Z.of_int 42);
    ClassOrInterfaceName "Cls";
    PackageName "pkg";
    RefType (Int (Signed, IntRank));
    AbstractType "Abs"
  ] in
  List.iter (fun t ->
    check "c_string_of_type" (String.length (c_string_of_type t) > 0);
    check "java_string_of_type" (String.length (java_string_of_type t) > 0);
    check "string_of_type CLang" (String.length (string_of_type CLang None t) > 0);
    check "string_of_type Java" (String.length (string_of_type Java None t) > 0)
  ) c_java_types;
  List.iter (fun t ->
    check "rust_string_of_type" (String.length (rust_string_of_type t) > 0);
    check "string_of_type Rust" (String.length (string_of_type CLang (Some Rust) t) > 0)
  ) (c_java_types @ rust_only_types);

  (* StringOf module *)
  let module SO = StringOf(struct let string_of_type = c_string_of_type end) in
  let chunk1 = Chunk (("pred1", true), [Int (Signed, IntRank)], "1", ["arg1"], None) in
  let chunk2 = Chunk (("pred2", false), [], "1/2", ["arg2"], Some (PredicateChunkSize 2)) in
  let heap = [chunk1; chunk2] in
  check "string_of_chunk" (String.length (SO.string_of_chunk chunk1) > 0);
  check "string_of_chunk coef" (String.length (SO.string_of_chunk chunk2) > 0);
  check "string_of_heap" (String.length (SO.string_of_heap heap) > 0);
  check "string_of_context Assuming" (String.length (SO.string_of_context (Assuming "x > 0")) > 0);
  check "string_of_context Executing" (String.length (SO.string_of_context (Executing (heap, [("v", "1")], dummy_loc, "stmt"))) > 0);
  check "string_of_context Push" (SO.string_of_context PushSubcontext = "Entering subcontext");
  check "string_of_context Pop" (SO.string_of_context PopSubcontext = "Leaving subcontext");
  check "string_of_context LeftBranch" (SO.string_of_context (Branching LeftBranch) = "Executing first branch");
  check "string_of_context RightBranch" (SO.string_of_context (Branching RightBranch) = "Executing second branch");

  (* Environment and caller helpers *)
  let env = update [] "a" "10" in
  let env = update env "b" "20" in
  check "lookup" (lookup env "a" = "10");
  check "string_of_env" (string_of_env env = "b = 20; a = 10");
  check "is_lemma" (is_lemma (Lemma (false, None)) && not (is_lemma Regular));
  check "tparam uppercase" (tparam_is_uppercase "T" && not (tparam_is_uppercase "t") && not (tparam_is_uppercase ""));
  check "tparam lifetime" (tparam_is_uppercase_or_lifetime "'a" && tparam_is_uppercase_or_lifetime "T");
  let bounds = tparams_with_default_bounds_exprs ["T"; "t"] in
  check "default bounds" (List.length bounds = 2);
  let ctxts = [
    PushSubcontext;
    Executing ([], [], dummy_loc, "s1");
    Executing ([], [], dummy_loc, "s2");
    PopSubcontext
  ] in
  check "get_callers" (List.length (get_callers ctxts) >= 0);
  check "get_root_caller none" (get_root_caller [] = None);
  check "get_root_caller some" (get_root_caller [PushSubcontext; Executing ([], [], dummy_loc, "s")] = Some dummy_loc)


(* ========================================== *)
(* Suite 20: Ast Fold Traversals Exhaustive   *)
(* ========================================== *)
let test_ast_fold_traversals () =
  (* is_instance *)
  check "inst GhostTypeParam" (is_instance dummy_loc (GhostTypeParam "T") (Int (Signed, IntRank)) = Some [("T", Int (Signed, IntRank))]);
  check "inst InferredType" (is_instance dummy_loc (InferredType (object end, ref (EqConstraint Bool))) Bool = Some []);
  check "inst RefType" (is_instance dummy_loc (RefType (Int (Signed, IntRank))) (RefType (Int (Signed, IntRank))) = Some []);
  check "inst AbstractType eq" (is_instance dummy_loc (AbstractType "A") (AbstractType "A") = Some []);
  check "inst AbstractType neq" (is_instance dummy_loc (AbstractType "A") (AbstractType "B") = None);
  check "inst StaticLifetime" (is_instance dummy_loc StaticLifetime StaticLifetime = Some []);
  check "inst ProjectionType eq" (is_instance dummy_loc (ProjectionType (Bool, "Tr", [], "A")) (ProjectionType (Bool, "Tr", [], "A")) = Some []);
  check "inst ProjectionType diff trait" (is_instance dummy_loc (ProjectionType (Bool, "Tr1", [], "A")) (ProjectionType (Bool, "Tr2", [], "A")) = None);
  check "inst ArrayType mismatch" (is_instance dummy_loc (ArrayType (Int (Signed, IntRank))) (ArrayType Bool) = None);
  check "inst StructType mismatch" (is_instance dummy_loc (StructType ("P", [Bool])) (StructType ("P", [Int (Signed, IntRank)])) = None);
  check "inst UnionType mismatch" (is_instance dummy_loc (UnionType "U") (UnionType "V") = None);
  check "inst FuncType mismatch" (is_instance dummy_loc (FuncType "f") (FuncType "g") = None);
  check "inst PredType mismatch" (is_instance dummy_loc (PredType ([], [Bool], None, Inductiveness_Inductive)) (PredType ([], [Bool], Some 1, Inductiveness_Inductive)) = None);
  check "inst Int mismatch" (is_instance dummy_loc (Int (Signed, IntRank)) Bool = None);

  (* type_fold_open *)
  let test_types = [
    Bool; Void; Int (Signed, IntRank); RustChar; RealType; Float; Double; LongDouble; Str;
    StructType ("S", [Bool]); UnionType "U"; PtrType Bool; RustRefType (StaticLifetime, Mutable, Bool);
    FuncType "f"; InlineFuncType Bool; InductiveType ("I", [Bool]); PredType ([], [Bool], None, Inductiveness_Inductive);
    PureFuncType (Bool, Bool); ObjType ("O", [Bool]); ArrayType Bool; StaticArrayType (Bool, LiteralConstType (Z.of_int 1));
    LiteralConstType (Z.of_int 1); BoxIdType; HandleIdType; AnyType; RealTypeParam "T"; GhostTypeParam "T";
    InferredRealType "r"; InferredType (object end, ref Unconstrained); ClassOrInterfaceName "C"; PackageName "P";
    RefType Bool; AbstractType "A"; StaticLifetime; BoundedGhostTypeParam ("T", {sized = true; eqs = []});
    ProjectionType (Bool, "Tr", [Bool], "A"); Slice Bool
  ] in
  List.iter (fun t ->
    let res = type_fold_open [] (fun st sub -> sub :: st) t in
    check "type_fold_open" (List.length res >= 0)
  ) test_types;

  (* type_expr_fold_open *)
  let test_type_exprs = [
    StructTypeExpr (dummy_loc, Some "S", None, [], [ManifestTypeExpr (dummy_loc, Bool)]);
    UnionTypeExpr (dummy_loc, Some "U", None);
    EnumTypeExpr (dummy_loc, Some "E", None);
    PtrTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool));
    RustRefTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), Mutable, ManifestTypeExpr (dummy_loc, Bool));
    ArrayTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool));
    StaticArrayTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), ManifestTypeExpr (dummy_loc, Bool));
    LiteralConstTypeExpr (dummy_loc, Z.of_int 5);
    FuncTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), [(ManifestTypeExpr (dummy_loc, Bool), "x")]);
    ManifestTypeExpr (dummy_loc, Bool);
    IdentTypeExpr (dummy_loc, None, "id");
    ConstructedTypeExpr (dummy_loc, "C", [ManifestTypeExpr (dummy_loc, Bool)]);
    PredTypeExpr (dummy_loc, [ManifestTypeExpr (dummy_loc, Bool)], None);
    PureFuncTypeExpr (dummy_loc, [(ManifestTypeExpr (dummy_loc, Bool), None)], None);
    LValueRefTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool));
    ConstTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool));
    ProjectionTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), "Tr", [ManifestTypeExpr (dummy_loc, Bool)], "A");
    SliceTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool))
  ] in
  List.iter (fun te ->
    let res = type_expr_fold_open (fun st sub -> sub :: st) [] te in
    check "type_expr_fold_open" (List.length res >= 0)
  ) test_type_exprs;

  (* stmt_fold_open *)
  let test_stmts = [
    PureStmt (dummy_loc, ExprStmt (True dummy_loc));
    NonpureStmt (dummy_loc, false, ExprStmt (True dummy_loc));
    ExprStmt (True dummy_loc);
    DeclStmt (dummy_loc, []);
    IfStmt (dummy_loc, True dummy_loc, [ExprStmt (True dummy_loc)], [ExprStmt (False dummy_loc)]);
    SwitchStmt (dummy_loc, True dummy_loc, [SwitchStmtClause (dummy_loc, True dummy_loc, [ExprStmt (True dummy_loc)]); SwitchStmtDefaultClause (dummy_loc, [ExprStmt (False dummy_loc)])]);
    Assert (dummy_loc, ExprAsn (dummy_loc, True dummy_loc));
    Leak (dummy_loc, ExprAsn (dummy_loc, True dummy_loc));
    ReturnStmt (dummy_loc, Some (True dummy_loc));
    WhileStmt (dummy_loc, True dummy_loc, None, None, [ExprStmt (True dummy_loc)], [ExprStmt (False dummy_loc)]);
    TryCatch (dummy_loc, [ExprStmt (True dummy_loc)], [(dummy_loc, ManifestTypeExpr (dummy_loc, Bool), "e", [ExprStmt (False dummy_loc)])]);
    TryFinally (dummy_loc, [ExprStmt (True dummy_loc)], dummy_loc, [ExprStmt (False dummy_loc)])
  ] in
  List.iter (fun s ->
    let res = stmt_fold_open (fun st sub -> sub :: st) [] s in
    check "stmt_fold_open" (List.length res >= 0)
  ) test_stmts;

  (* expr_fold_open *)
  let extra_exprs = [
    TruncatingExpr (dummy_loc, True dummy_loc);
    Operation (dummy_loc, Add, [True dummy_loc]);
    WOperation (dummy_loc, Add, [True dummy_loc], Bool);
    SliceExpr (dummy_loc, Some (LitPat (True dummy_loc)), Some (LitPat (False dummy_loc)));
    Read (dummy_loc, True dummy_loc, "f");
    ActivatingRead (dummy_loc, True dummy_loc, "f");
    Select (dummy_loc, True dummy_loc, "f");
    ArrayLengthExpr (dummy_loc, True dummy_loc);
    ReadArray (dummy_loc, True dummy_loc, True dummy_loc);
    WReadArray (dummy_loc, True dummy_loc, Bool, True dummy_loc);
    Deref (dummy_loc, True dummy_loc);
    WDeref (dummy_loc, True dummy_loc, Bool);
    CallExpr (dummy_loc, "f", [], [LitPat (True dummy_loc)], [LitPat (True dummy_loc)], Static);
    ExprCallExpr (dummy_loc, True dummy_loc, [LitPat (True dummy_loc)]);
    WPureFunCall (dummy_loc, "f", [], [True dummy_loc]);
    WPureFunValueCall (dummy_loc, True dummy_loc, [True dummy_loc]);
    WFunCall (dummy_loc, "f", [], [True dummy_loc], Static);
    WFunPtrCall (dummy_loc, True dummy_loc, Some "f", [True dummy_loc]);
    WMethodCall (dummy_loc, "C", "m", [], [True dummy_loc], Static, []);
    NewObject (dummy_loc, "C", [True dummy_loc], None);
    NewArray (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), True dummy_loc);
    NewArrayWithInitializer (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), [True dummy_loc]);
    IfExpr (dummy_loc, True dummy_loc, True dummy_loc, False dummy_loc);
    SwitchExpr (dummy_loc, True dummy_loc, [SwitchExprClause (dummy_loc, "C", [], True dummy_loc)], Some (dummy_loc, False dummy_loc));
    CastExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), True dummy_loc);
    Upcast (True dummy_loc, Bool, Bool);
    TypedExpr (True dummy_loc, Bool);
    WidenedParameterArgument (True dummy_loc);
    SizeofExpr (dummy_loc, TypeExpr (ManifestTypeExpr (dummy_loc, Bool)));
    SizeofExpr (dummy_loc, True dummy_loc);
    AlignofExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool));
    GenericExpr (dummy_loc, True dummy_loc, [(ManifestTypeExpr (dummy_loc, Bool), True dummy_loc)], Some (False dummy_loc));
    AddressOf (dummy_loc, True dummy_loc);
    ProverTypeConversion (ProverInt, ProverBool, True dummy_loc);
    Unbox (True dummy_loc, Bool);
    ArrayTypeExpr' (dummy_loc, True dummy_loc);
    AssignExpr (dummy_loc, True dummy_loc, Mutation, False dummy_loc);
    AssignOpExpr (dummy_loc, True dummy_loc, Add, False dummy_loc, false);
    WAssignOpExpr (dummy_loc, True dummy_loc, "op", False dummy_loc, false);
    CommaExpr (dummy_loc, True dummy_loc, False dummy_loc);
    InstanceOfExpr (dummy_loc, True dummy_loc, ManifestTypeExpr (dummy_loc, Bool));
    SuperMethodCall (dummy_loc, "m", [True dummy_loc]);
    InitializerList (dummy_loc, [(Some (dummy_loc, "f"), True dummy_loc)]);
    CxxNew (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), Some (True dummy_loc));
    CxxNew (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), None);
    CxxDelete (dummy_loc, True dummy_loc);
    Typeid (dummy_loc, True dummy_loc);
    PointsTo (dummy_loc, True dummy_loc, RegularPointsTo, LitPat (False dummy_loc));
    WPointsTo (dummy_loc, True dummy_loc, Bool, RegularPointsTo, LitPat (False dummy_loc));
    PredAsn (dummy_loc, "p", [], [LitPat (True dummy_loc)], [LitPat (True dummy_loc)], Static);
    PredExprAsn (dummy_loc, True dummy_loc, [LitPat (True dummy_loc)]);
    WPredExprAsn (dummy_loc, True dummy_loc, [], None, [LitPat (True dummy_loc)]);
    InstPredAsn (dummy_loc, True dummy_loc, "p", True dummy_loc, [LitPat (True dummy_loc)]);
    ExprAsn (dummy_loc, True dummy_loc);
    MatchAsn (dummy_loc, True dummy_loc, LitPat (True dummy_loc));
    WMatchAsn (dummy_loc, True dummy_loc, LitPat (True dummy_loc), Bool);
    Sep (dummy_loc, ExprAsn (dummy_loc, True dummy_loc), ExprAsn (dummy_loc, False dummy_loc));
    IfAsn (dummy_loc, True dummy_loc, ExprAsn (dummy_loc, True dummy_loc), ExprAsn (dummy_loc, False dummy_loc));
    WSwitchAsn (dummy_loc, True dummy_loc, "I", [WSwitchAsnClause (dummy_loc, "C", "I::C", [], [], ExprAsn (dummy_loc, True dummy_loc))]);
    ForallAsn (dummy_loc, ManifestTypeExpr (dummy_loc, Bool), "x", True dummy_loc);
    CoefAsn (dummy_loc, LitPat (True dummy_loc), ExprAsn (dummy_loc, True dummy_loc));
    EnsuresAsn (dummy_loc, "result", ExprAsn (dummy_loc, True dummy_loc))
  ] in
  List.iter (fun e ->
    let res = expr_fold_open (fun st sub -> sub :: st) [] e in
    check "expr_fold_open" (List.length res >= 0);
    expr_iter (fun _ -> ()) e
  ) extra_exprs;
  check "make_addr_of" (match make_addr_of dummy_loc (CxxDerivedToBase (dummy_loc, True dummy_loc, ManifestTypeExpr (dummy_loc, Bool))) with CxxDerivedToBase _ -> true | _ -> false)

(* ========================================== *)
(* ========================================== *)
(* Suite 21: Ast Is_Instance & Types Exhaustive *)
(* ========================================== *)
let test_ast_is_instance_and_types_exhaustive () =
  let dummy_loc = Ast.DummyLoc in
  let check_inst t1 t2 expected =
    check "is_instance" ((Ast.is_instance dummy_loc t1 t2 <> None) = expected)
  in
  check_inst Bool Bool true;
  check_inst Void Void true;
  check_inst (Int (Signed, IntRank)) (Int (Signed, IntRank)) true;
  check_inst (Int (Signed, IntRank)) (Int (Unsigned, IntRank)) false;
  check_inst RustChar RustChar true;
  check_inst RealType RealType true;
  check_inst Float Float true;
  check_inst Double Double true;
  check_inst LongDouble LongDouble true;
  check_inst (StructType ("S", [])) (StructType ("S", [])) true;
  check_inst (StructType ("S1", [])) (StructType ("S2", [])) false;
  check_inst (UnionType "U") (UnionType "U") true;
  check_inst (UnionType "U1") (UnionType "U2") false;
  check_inst (PtrType Bool) (PtrType Bool) true;
  check_inst (RustRefType (StaticLifetime, Shared, Bool)) (RustRefType (StaticLifetime, Shared, Bool)) true;
  check_inst (RustRefType (StaticLifetime, Shared, Bool)) (RustRefType (StaticLifetime, Mutable, Bool)) false;
  check_inst (FuncType "f") (FuncType "f") true;
  check_inst (FuncType "f1") (FuncType "f2") false;
  check_inst (InlineFuncType (PtrType Void)) (InlineFuncType (PtrType Void)) true;
  check_inst (InductiveType ("I", [])) (InductiveType ("I", [])) true;
  check_inst (InductiveType ("I1", [])) (InductiveType ("I2", [])) false;
  check_inst (PredType ([], [Bool], Some 1, Inductiveness_Inductive)) (PredType ([], [Bool], Some 1, Inductiveness_Inductive)) true;
  check_inst (PureFuncType (Bool, Bool)) (PureFuncType (Bool, Bool)) true;
  check_inst (ObjType ("O", [])) (ObjType ("O", [])) true;
  check_inst (ObjType ("O1", [])) (ObjType ("O2", [])) false;
  check_inst (ArrayType Bool) (ArrayType Bool) true;
  check_inst (StaticArrayType (Bool, LiteralConstType (Z.of_int 5)))
             (StaticArrayType (Bool, LiteralConstType (Z.of_int 5))) true;
  check_inst (LiteralConstType (Z.of_int 42)) (LiteralConstType (Z.of_int 42)) true;
  check_inst (LiteralConstType (Z.of_int 42)) (LiteralConstType (Z.of_int 43)) false;
  check_inst BoxIdType BoxIdType true;
  check_inst HandleIdType HandleIdType true;
  check_inst AnyType AnyType true;
  check_inst (InferredRealType "a") Bool false;
  check_inst (GhostTypeParam "T") Bool true;
  check_inst (RealTypeParam "R") Bool true;
  
  let inf1 = InferredType (object end, ref (EqConstraint Bool)) in
  check_inst inf1 Bool true;
  let inf2 = InferredType (object end, ref Unconstrained) in
  check_inst inf2 Bool false;
  check_inst Bool inf1 true;

  (* inferred_type_constraint_le & meet *)
  check "le 1" (Ast.inferred_type_constraint_le Unconstrained Unconstrained = true);
  check "le 2" (Ast.inferred_type_constraint_le (ContainsAnyConstraint true) Unconstrained = true);
  check "le 3" (Ast.inferred_type_constraint_le Unconstrained (ContainsAnyConstraint true) = false);
  check "le 4" (Ast.inferred_type_constraint_le (ContainsAnyConstraint false) (ContainsAnyConstraint true) = true);
  check "le 5" (Ast.inferred_type_constraint_le (ContainsAnyConstraint true) (ContainsAnyConstraint false) = false);
  check "le 6" (Ast.inferred_type_constraint_le (ContainsAnyConstraint false) (ContainsAnyConstraint false) = true);
  check "meet" (Ast.inferred_type_constraint_meet Unconstrained (ContainsAnyConstraint true) = ContainsAnyConstraint true);

  (* string_of_data_model & type checks *)
  check "data model name" (Ast.string_of_data_model (List.hd (List.map snd Ast.data_models)) <> "(unnamed)");
  check "data model unnamed" (Ast.string_of_data_model {int_width = 1; long_width = 1; ptr_width = 1} = "(unnamed)");
  check "is_arithmetic_type true" (Ast.is_arithmetic_type (Int (Signed, IntRank)) && Ast.is_arithmetic_type RealType && Ast.is_arithmetic_type Float && Ast.is_arithmetic_type Double && Ast.is_arithmetic_type LongDouble);
  check "is_arithmetic_type false" (not (Ast.is_arithmetic_type Bool));
  check "is_inductive_type true" (Ast.is_inductive_type (InductiveType ("T", [])));
  check "is_inductive_type false" (not (Ast.is_inductive_type Bool));

  (* string_of_func_kind & tostring *)
  check "string_of_func_kind" (Ast.string_of_func_kind (Lemma (false, None)) = "lemma" && Ast.string_of_func_kind Regular = "regular" && Ast.string_of_func_kind Fixpoint = "fixpoint");
  check "tostring binding" (Ast.tostring Instance = "instance" && Ast.tostring Static = "static");
  check "type_expr_loc SliceTypeExpr" (Ast.type_expr_loc (SliceTypeExpr (dummy_loc, ManifestTypeExpr (dummy_loc, Bool))) = dummy_loc);

  (* expr_loc variants *)
  check "expr_loc Upcast" (Ast.expr_loc (Upcast (True dummy_loc, Bool, Bool)) = dummy_loc);
  check "expr_loc TypedExpr" (Ast.expr_loc (TypedExpr (True dummy_loc, Bool)) = dummy_loc);
  check "expr_loc Widened" (Ast.expr_loc (WidenedParameterArgument (True dummy_loc)) = dummy_loc);
  check "expr_loc ProverTypeConv" (Ast.expr_loc (ProverTypeConversion (ProverBool, ProverBool, True dummy_loc)) = dummy_loc);
  check "expr_loc Unbox" (Ast.expr_loc (Unbox (True dummy_loc, Bool)) = dummy_loc);
  check "expr_loc LetTypeAsn" (Ast.expr_loc (LetTypeAsn (dummy_loc, "x", Bool, ExprAsn (dummy_loc, True dummy_loc))) = dummy_loc);
  check "expr_loc WTypePredExpr" (Ast.expr_loc (WTypePredExpr (dummy_loc, Bool, "p")) = dummy_loc)

(* ========================================== *)
(* Suite 22: Lexer & Parser Exhaustive        *)
(* ========================================== *)
let test_lexer_and_parser_exhaustive () =
  (* Lexer make_utf8 *)
  check "make_utf8 ascii" (Lexer.utf8_to_file "hello" = "hello");
  check "make_utf8 latin1" (String.length (Lexer.utf8_to_file "hello Â  world") > 0);
  check "make_utf8 high" (String.length (Lexer.utf8_to_file "hello Ä world") > 0);

  (* Lexer split_into_words *)
  check "split_into_words empty" (Lexer.split_into_words "" = []);
  check "split_into_words spaces" (Lexer.split_into_words "   " = []);
  check "split_into_words words" (Lexer.split_into_words "foo bar" = ["foo"; "bar"]);
  check "split_into_words quotes" (Lexer.split_into_words {|foo "bar baz" qux|} = ["foo"; "bar baz"; "qux"]);
  check "split_into_words unclosed" (Lexer.split_into_words {|foo "unclosed|} = ["foo"; "unclosed"]);

  (* Parser file_specs *)
  check "file_specs jarsrc" (file_specs "lib.jarsrc" = (Ast.Java, None));
  check "file_specs jarspec" (file_specs "lib.jarspec" = (Ast.Java, None));
  check "file_specs javaspec" (file_specs "lib.javaspec" = (Ast.Java, None));
  check "file_specs scala" (file_specs "lib.scala" = (Ast.Java, None));
  check "file_specs hpp" (file_specs "lib.hpp" = (Ast.CLang, Some Ast.Cxx));

  (* Parser expand_macros, expand_path, concat_if_relative *)
  check "expand_macros none" (expand_macros [("FOO", "BAR")] "plain text" = "plain text");
  check "expand_macros hit" (expand_macros [("FOO", "BAR")] "prefix %FOO% suffix" = "prefix BAR suffix");
  let caught = ref false in (try let _ = expand_macros [] "prefix %BAZ% suffix" in () with Not_found -> caught := true); check "expand_macros miss" !caught;
  check "expand_path" (String.length (expand_path "%VERIFAST%/rt") > 0);
  check "concat_if_relative rel" (concat_if_relative "/dir" "sub/file" = "/dir/sub/file");
  check "concat_if_relative abs" (concat_if_relative "/dir" "/abs/file" = "/abs/file")

(* ========================================== *)
(* Suite 23: Util, Stats & Src_Loc Exhaustive *)
(* ========================================== *)
let test_util_and_stats_exhaustive () =
  (* num_of_hex_fraction *)
  check "hex fraction 1" (Num.eq_num (Util.num_of_hex_fraction "0x1.8p+2") (Num.num_of_string "6"));
  check "hex fraction 2" (Num.eq_num (Util.num_of_hex_fraction "0x1p2") (Num.num_of_string "4"));
  check "hex fraction 3" (Num.eq_num (Util.num_of_hex_fraction "0x10") (Num.num_of_string "16"));
  check "hex fraction 4" (Num.gt_num (Util.num_of_hex_fraction "0x1.4P-1") (Num.num_of_int 0));

  (* take, take_drop, drop_while, list_make *)
  check "take 0" (Util.take 0 [1; 2] = []);
  check "take more" (Util.take 5 [1; 2] = [1; 2]);
  check "take_drop more" (Util.take_drop 5 [1; 2] = ([1; 2], []));
  check "drop_while" (Util.drop_while (fun x -> x < 3) [1; 2; 3; 4; 1] = [3; 4; 1]);
  check "list_make 0" (Util.list_make 0 "x" = []);
  check "list_make 3" (Util.list_make 3 "x" = ["x"; "x"; "x"]);

  (* try_extract, compose, smart_compose, relative_path *)
  check "try_extract hit" (match Util.try_extract [1; 2; 3] (fun x -> x = 2) with Some (2, [1; 3]) -> true | _ -> false);
  check "try_extract miss" (Util.try_extract [1; 2; 3] (fun x -> x = 5) = None);
  check "compose rel" (Util.compose "base" "rel" = "base/rel");
  check "compose abs" (Util.compose "base" "/abs" = "/abs");
  check "smart_compose dot" (Util.smart_compose "." "rel" = "rel");
  check "smart_compose base" (Util.smart_compose "base" "rel" = "base/rel");
  check "relative_path" (String.length (Util.qualified_path [] "/a/b.c" ("/a", "c.h")) > 0);

  (* Stats methods *)
  let s = new Stats.stats in
  s#set_success_qualifier "verified";
  check "success qualifier" (s#success_qualifier = Some "verified");
  check "success message" (String.contains (s#get_success_message) 'v');
  s#recordFunctionTiming "my_fun" 0.5;
  check "function timings" (String.contains (s#getFunctionTimings) 'm');
  s#overhead ~path:"foo.c" ~nonGhostLineCount:10 ~ghostLineCount:5 ~mixedLineCount:2;
  s#printStats;
  Stats.clear_stats ();

  (* Src_loc_aux err desc & rel corner cases *)
  let p1 = ("f", 1, 1) in
  let p2 = ("f", 2, 1) in
  let p3 = ("f", 3, 1) in
  check "err desc 1" (Src_loc_aux.compare_err_desc (`IsWellFormedLoc0 "x") <> "");
  check "err desc 2" (Src_loc_aux.compare_err_desc (`TryCompareLoc "x") <> "");
  check "err desc 3" (Src_loc_aux.compare_err_desc (`TryCompareSrcPos "x") <> "");
  check "err desc 4" (Src_loc_aux.compare_err_desc (`IsWellFormedSrcPos "x") <> "");
  check "rel s1=e1=e2" (match Src_loc_aux.rel (p2, p2) (p1, p2) with Ok (Src_loc_aux.Disjoint {compare = 1}) -> true | _ -> false);
  check "rel s1=e1=s2" (match Src_loc_aux.rel (p2, p2) (p2, p3) with Ok (Src_loc_aux.Disjoint {compare = -1}) -> true | _ -> false);
  check "rel s1=e1=s2=e2" (match Src_loc_aux.rel (p2, p2) (p2, p2) with Ok (Src_loc_aux.Overlapping {kind = Src_loc_aux.Eq}) -> true | _ -> false)

let run () =
  passed_assertions := 0;
  test_ast_fold_traversals ();
  test_verifast0_exhaustive ();
  test_util ();
  test_ast_data_models ();
  test_lexer ();
  test_parser_c_and_ghost ();
  test_z ();
  test_ocaml_expr_and_ast ();
  test_ocaml_aux ();
  test_src_loc_aux ();
  test_stats ();
  test_ast_aux ();
  test_verifast0 ();
  test_ast_unify_and_helpers ();
  test_lexer_deep ();
  test_ocaml_expr_of_ast_deep ();
  test_json_module ();
  test_ast_exhaustive_locs_and_types ();
  test_src_loc_aux_exhaustive ();
  test_ast_is_instance_and_types_exhaustive ();
  test_lexer_and_parser_exhaustive ();
  test_util_and_stats_exhaustive ();
  !passed_assertions
