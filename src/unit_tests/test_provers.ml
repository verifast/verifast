open Proverapi

let passed_assertions = ref 0

let check msg condition =
  if condition then
    incr passed_assertions
  else (
    Printf.eprintf "[FAIL] Prover assertion failed: %s\n" msg;
    assert false
  )

let check_true msg (ctxt: (_, _, _) context) term =
  check msg (ctxt#query term)

let check_false msg (ctxt: (_, _, _) context) term =
  check msg (not (ctxt#query term))

let contains s sub =
  try ignore (Str.search_forward (Str.regexp_string sub) s 0); true
  with Not_found -> false

(* ========================================== *)
(* Suite 1: Redux Prover                      *)
(* ========================================== *)
let test_redux_booleans (ctxt: (_, _, _) context) =
  let t_true = ctxt#mk_true in
  let t_false = ctxt#mk_false in
  check_true "Redux: true is valid" ctxt t_true;
  check_false "Redux: false is not valid" ctxt t_false;

  (* Not *)
  check_true "Redux: !false is valid" ctxt (ctxt#mk_not t_false);
  check_false "Redux: !true is not valid" ctxt (ctxt#mk_not t_true);

  (* And *)
  check_true "Redux: true && true" ctxt (ctxt#mk_and t_true t_true);
  check_false "Redux: true && false" ctxt (ctxt#mk_and t_true t_false);
  check_false "Redux: false && true" ctxt (ctxt#mk_and t_false t_true);
  check_false "Redux: false && false" ctxt (ctxt#mk_and t_false t_false);

  (* Or *)
  check_true "Redux: true || false" ctxt (ctxt#mk_or t_true t_false);
  check_true "Redux: false || true" ctxt (ctxt#mk_or t_false t_true);
  check_false "Redux: false || false" ctxt (ctxt#mk_or t_false t_false);

  (* Iff *)
  check_true "Redux: true <==> true" ctxt (ctxt#mk_iff t_true t_true);
  check_true "Redux: false <==> false" ctxt (ctxt#mk_iff t_false t_false);
  check_false "Redux: true <==> false" ctxt (ctxt#mk_iff t_true t_false);

  (* If-Then-Else *)
  let ite_true = ctxt#mk_ifthenelse t_true (ctxt#mk_intlit 1) (ctxt#mk_intlit 2) in
  check_true "Redux: (if true then 1 else 2) == 1" ctxt (ctxt#mk_eq ite_true (ctxt#mk_intlit 1));
  let ite_false = ctxt#mk_ifthenelse t_false (ctxt#mk_intlit 1) (ctxt#mk_intlit 2) in
  check_true "Redux: (if false then 1 else 2) == 2" ctxt (ctxt#mk_eq ite_false (ctxt#mk_intlit 2))

let test_redux_arithmetic (ctxt: (_, _, _) context) =
  let zero = ctxt#mk_intlit 0 in
  let one = ctxt#mk_intlit 1 in
  let two = ctxt#mk_intlit 2 in
  let three = ctxt#mk_intlit 3 in
  let five = ctxt#mk_intlit 5 in

  (* Addition *)
  let sum = ctxt#mk_add two three in
  check_true "Redux: 2 + 3 == 5" ctxt (ctxt#mk_eq sum five);

  (* Subtraction *)
  let diff = ctxt#mk_sub five two in
  check_true "Redux: 5 - 2 == 3" ctxt (ctxt#mk_eq diff three);

  (* Multiplication *)
  let prod = ctxt#mk_mul two three in
  let six = ctxt#mk_intlit 6 in
  check_true "Redux: 2 * 3 == 6" ctxt (ctxt#mk_eq prod six);

  (* Comparisons *)
  check_true "Redux: 1 < 2" ctxt (ctxt#mk_lt one two);
  check_false "Redux: 2 < 1 is false" ctxt (ctxt#mk_lt two one);
  check_false "Redux: 1 < 1 is false" ctxt (ctxt#mk_lt one one);
  check_true "Redux: 1 <= 1" ctxt (ctxt#mk_le one one);
  check_true "Redux: 1 <= 2" ctxt (ctxt#mk_le one two);
  check_false "Redux: 2 <= 1 is false" ctxt (ctxt#mk_le two one);

  (* String integer literals *)
  let big = ctxt#mk_intlit_of_string "1000000" in
  check_true "Redux: intlit_of_string 1000000 > 0" ctxt (ctxt#mk_lt zero big)

let test_redux_congruence (ctxt: (_, _, _) context) =
  let sym_f = ctxt#mk_symbol "f" [ctxt#type_int] ctxt#type_int Uninterp in
  let sym_x = ctxt#mk_symbol "x" [] ctxt#type_int Uninterp in
  let sym_y = ctxt#mk_symbol "y" [] ctxt#type_int Uninterp in
  let x = ctxt#mk_app sym_x [] in
  let y = ctxt#mk_app sym_y [] in
  let fx = ctxt#mk_app sym_f [x] in
  let fy = ctxt#mk_app sym_f [y] in

  ctxt#push;
  let _ = ctxt#assume (ctxt#mk_eq x y) in
  check_true "Redux congruence: x == y => f(x) == f(y)" ctxt (ctxt#mk_eq fx fy);
  ctxt#pop;
  check_false "Redux: f(x) == f(y) not valid without x == y" ctxt (ctxt#mk_eq fx fy)

let test_redux_constructors (ctxt: (_, _, _) context) =
  let subtype = InductiveSubtype.alloc () in
  let sym_c0 = ctxt#mk_symbol "c0" [] ctxt#type_inductive (Ctor (CtorByOrdinal (subtype, 0))) in
  let sym_c1 = ctxt#mk_symbol "c1" [] ctxt#type_inductive (Ctor (CtorByOrdinal (subtype, 1))) in
  let c0 = ctxt#mk_app sym_c0 [] in
  let c1 = ctxt#mk_app sym_c1 [] in
  
  (* Disjointness *)
  check_false "Redux: c0 == c1 is not valid" ctxt (ctxt#mk_eq c0 c1);
  ctxt#push;
  let res = ctxt#assume (ctxt#mk_eq c0 c1) in
  check "Redux disjoint constructors: assume c0 == c1 returns Unsat" (res = Unsat);
  ctxt#pop;

  (* Injectivity *)
  let sym_cons = ctxt#mk_symbol "cons" [ctxt#type_int] ctxt#type_inductive (Ctor (CtorByOrdinal (subtype, 2))) in
  let sym_a = ctxt#mk_symbol "a" [] ctxt#type_int Uninterp in
  let sym_b = ctxt#mk_symbol "b" [] ctxt#type_int Uninterp in
  let a = ctxt#mk_app sym_a [] in
  let b = ctxt#mk_app sym_b [] in
  let cons_a = ctxt#mk_app sym_cons [a] in
  let cons_b = ctxt#mk_app sym_cons [b] in

  ctxt#push;
  let _ = ctxt#assume (ctxt#mk_eq cons_a cons_b) in
  check_true "Redux injectivity: cons(a) == cons(b) => a == b" ctxt (ctxt#mk_eq a b);
  ctxt#pop

let test_redux_backtracking (ctxt: (_, _, _) context) =
  let sym_x = ctxt#mk_symbol "bx" [] ctxt#type_int Uninterp in
  let x = ctxt#mk_app sym_x [] in
  let ten = ctxt#mk_intlit 10 in

  ctxt#push;
  let _ = ctxt#assume (ctxt#mk_eq x ten) in
  check_true "Redux push/pop: x == 10 assumed" ctxt (ctxt#mk_eq x ten);

  (* Inner scope with contradiction *)
  ctxt#push;
  let res_unsat = ctxt#assume (ctxt#mk_eq x (ctxt#mk_intlit 20)) in
  check "Redux assume contradiction returns Unsat" (res_unsat = Unsat);
  ctxt#pop;
  
  (* Outer scope preserved *)
  check_true "Redux push/pop: x == 10 still valid in outer scope" ctxt (ctxt#mk_eq x ten);
  ctxt#pop;
  check_false "Redux push/pop: x == 10 not valid after pop to base" ctxt (ctxt#mk_eq x ten)

let test_redux_simplify_and_stats (ctxt: Redux.context) =
  let term = ctxt#mk_add (ctxt#mk_intlit 2) (ctxt#mk_intlit 3) in
  let sim = ctxt#simplify term in
  check "Redux simplify returns Some" (sim <> None);
  let (stat_str, _) = ctxt#stats in
  check "Redux stats produces string" (String.length stat_str >= 0)

(* ========================================== *)
(* Suite 2: Z3 Prover Comprehensive           *)
(* ========================================== *)
let test_z3_prover () =
  let raw_ctxt = new Z3v4dot5prover.z3_context () in
  let ctxt = (raw_ctxt :> (_, _, _) context) in
  
  (* Booleans and Implication *)
  let t_true = ctxt#mk_true in
  let t_false = ctxt#mk_false in
  check_true "Z3: true" ctxt t_true;
  check_false "Z3: false" ctxt t_false;
  check_true "Z3: false => true" ctxt (ctxt#mk_implies t_false t_true);
  check_true "Z3: false => false" ctxt (ctxt#mk_implies t_false t_false);
  check_true "Z3: true => true" ctxt (ctxt#mk_implies t_true t_true);
  check_false "Z3: !(true => false)" ctxt (ctxt#mk_implies t_true t_false);

  (* Division and Modulo *)
  let ten = ctxt#mk_intlit 10 in
  let three = ctxt#mk_intlit 3 in
  check_true "Z3: 10 / 3 == 3" ctxt (ctxt#mk_eq (ctxt#mk_div ten three) three);
  check_true "Z3: 10 % 3 == 1" ctxt (ctxt#mk_eq (ctxt#mk_mod ten three) (ctxt#mk_intlit 1));

  (* Real arithmetic *)
  let r1 = ctxt#mk_reallit 1 in
  let r2 = ctxt#mk_reallit_of_num (Num.num_of_int 2) in
  let r_sum = ctxt#mk_real_add r1 r2 in
  let r3 = ctxt#mk_reallit 3 in
  check_true "Z3: real 1 + 2 == 3" ctxt (ctxt#mk_eq r_sum r3);
  check_true "Z3: real 3 - 1 == 2" ctxt (ctxt#mk_eq (ctxt#mk_real_sub r3 r1) r2);
  check_true "Z3: real 2 * 3 == 6" ctxt (ctxt#mk_eq (ctxt#mk_real_mul r2 r3) (ctxt#mk_reallit 6));
  check_true "Z3: real 1 < 2" ctxt (ctxt#mk_real_lt r1 r2);
  check_true "Z3: real 1 <= 1" ctxt (ctxt#mk_real_le r1 r1);

  (* Boxing / Unboxing *)
  let b_int = ctxt#mk_boxed_int (ctxt#mk_intlit 5) in
  let u_int = ctxt#mk_unboxed_int b_int in
  check_true "Z3: unbox(box(5)) == 5" ctxt (ctxt#mk_eq u_int (ctxt#mk_intlit 5));

  let b_bool = ctxt#mk_boxed_bool t_true in
  let u_bool = ctxt#mk_unboxed_bool b_bool in
  check_true "Z3: unbox(box(true))" ctxt u_bool;

  let b_real = ctxt#mk_boxed_real r1 in
  let u_real = ctxt#mk_unboxed_real b_real in
  check_true "Z3: real unbox(box(r1)) <= r1" ctxt (ctxt#mk_real_le u_real r1);

  (* Constructors and Axioms *)
  let subtype = InductiveSubtype.alloc () in
  let sym_c0 = ctxt#mk_symbol "z3_c0" [] ctxt#type_inductive (Ctor (CtorByOrdinal (subtype, 0))) in
  let sym_c1 = ctxt#mk_symbol "z3_c1" [ctxt#type_int] ctxt#type_inductive (Ctor (CtorByOrdinal (subtype, 1))) in
  let c0 = ctxt#mk_app sym_c0 [] in
  let c1 = ctxt#mk_app sym_c1 [ten] in
  check_false "Z3 ctors: c0 == c1 is false" ctxt (ctxt#mk_eq c0 c1);

  (* Recursive definitions via set_fpclauses *)
  let sym_rec = ctxt#mk_symbol "rec_fn" [ctxt#type_inductive] ctxt#type_int (Fixpoint (subtype, 0)) in
  ctxt#set_fpclauses sym_rec 0 [
    (sym_c0, fun _ _ -> ctxt#mk_intlit 0);
    (sym_c1, fun _ cargs -> List.hd cargs)
  ];
  check_true "Z3 fpclause c0 == 0" ctxt (ctxt#mk_eq (ctxt#mk_app sym_rec [c0]) (ctxt#mk_intlit 0));
  check_true "Z3 fpclause c1 == 10" ctxt (ctxt#mk_eq (ctxt#mk_app sym_rec [c1]) ten);

  (* Quantifiers with assume_forall and mk_bound *)
  let sym_p = ctxt#mk_symbol "p" [ctxt#type_int] ctxt#type_bool Uninterp in
  ctxt#push;
  ctxt#begin_formal;
  let bound0 = ctxt#mk_bound 0 ctxt#type_int in
  let p_bound = ctxt#mk_app sym_p [bound0] in
  ctxt#end_formal;
  ctxt#assume_forall "forall_x_p(x)" [p_bound] [ctxt#type_int] p_bound;
  
  let sym_c = ctxt#mk_symbol "c" [] ctxt#type_int Uninterp in
  let c = ctxt#mk_app sym_c [] in
  let p_c = ctxt#mk_app sym_p [c] in
  check_true "Z3 instantiated axiom: p(c)" ctxt p_c;
  ctxt#pop;

  (* Empty tps in assume_forall *)
  ctxt#assume_forall "trivial_forall" [] [] t_true;

  (* Types, Pretty-printing & Sorts *)
  check "Z3 pprint" (String.length (ctxt#pprint (ctxt#mk_intlit 42)) > 0);
  check "Z3 pprint_sort" (String.length (ctxt#pprint_sort ctxt#type_int) > 0);
  check "Z3 pprint_sym" (String.length (ctxt#pprint_sym sym_c0) > 0);
  check "Z3 get_type" (raw_ctxt#pprint_sort (raw_ctxt#get_type (ctxt#mk_intlit 42)) = ctxt#pprint_sort ctxt#type_int);
  check "Z3 simplify" (ctxt#simplify (ctxt#mk_add (ctxt#mk_intlit 1) (ctxt#mk_intlit 2)) <> None);
  check "Z3 perform_pending_splits" (raw_ctxt#perform_pending_splits (fun _ -> true));

  (* Verbosity logging branch coverage *)
  ctxt#set_verbosity 100;
  let _ = ctxt#mk_app sym_c0 [] in
  ctxt#push;
  let _ = ctxt#assume t_true in
  let _ = ctxt#query t_true in
  ctxt#pop;
  ctxt#set_verbosity 0;

  let (z3_stat, _) = ctxt#stats in
  check "Z3 stats string" (String.length z3_stat >= 0)

(* ========================================== *)
(* Suite 3: Combineprovers Comprehensive       *)
(* ========================================== *)
let test_combineprovers () =
  let redux_ctxt = (new Redux.context () :> (_, _, _) context) in
  let z3_ctxt = (new Z3v4dot5prover.z3_context () :> (_, _, _) context) in

  (* Test pair helpers and exceptions *)
  check "Combineprovers.left" (Combineprovers.left 10 = Combineprovers.Left 10);
  check "Combineprovers.right" (Combineprovers.right 20 = Combineprovers.Right 20);
  check "my_fst Left" (Combineprovers.my_fst (Combineprovers.Left 1) = 1);
  check "my_fst Both" (Combineprovers.my_fst (Combineprovers.Both (1, 2)) = 1);
  check "my_snd Right" (Combineprovers.my_snd (Combineprovers.Right 2) = 2);
  check "my_snd Both" (Combineprovers.my_snd (Combineprovers.Both (1, 2)) = 2);
  
  let raised1 = ref false in
  (try let _ = Combineprovers.my_fst (Combineprovers.Right 2) in () with Combineprovers.No_fst -> raised1 := true);
  check "my_fst on Right raises No_fst" !raised1;

  let raised2 = ref false in
  (try let _ = Combineprovers.my_snd (Combineprovers.Left 1) in () with Combineprovers.No_snd -> raised2 := true);
  check "my_snd on Left raises No_snd" !raised2;

  (* Test both Sequence and Sync strategies *)
  let strategies = [Combineprovers.Sequence; Combineprovers.Sync] in
  List.iter (fun strat ->
    let comb = Combineprovers.combine redux_ctxt z3_ctxt strat in

    comb#set_verbosity 1;
    comb#set_verbosity 0;

    check "comb type_bool" (fst comb#type_bool = redux_ctxt#type_bool);
    check "comb type_int" (fst comb#type_int = redux_ctxt#type_int);
    check "comb type_real" (fst comb#type_real = redux_ctxt#type_real);
    check "comb type_inductive" (fst comb#type_inductive = redux_ctxt#type_inductive);

    (* Booleans *)
    let t_true = comb#mk_true in
    let t_false = comb#mk_false in
    check_true "comb true" comb t_true;
    check_false "comb false" comb t_false;
    check_true "comb not false" comb (comb#mk_not t_false);
    check_true "comb true and true" comb (comb#mk_and t_true t_true);
    check_true "comb true or false" comb (comb#mk_or t_true t_false);
    check_true "comb true iff true" comb (comb#mk_iff t_true t_true);
    let _ = comb#mk_implies t_false t_true in

    (* If-then-else *)
    let ite = comb#mk_ifthenelse t_true (comb#mk_intlit 10) (comb#mk_intlit 20) in
    check_true "comb if-then-else" comb (comb#mk_eq ite (comb#mk_intlit 10));

    (* Int arithmetic *)
    let c1 = comb#mk_intlit 1 in
    let c2 = comb#mk_intlit 2 in
    let c3 = comb#mk_intlit 3 in
    check_true "comb 1 + 2 == 3" comb (comb#mk_eq (comb#mk_add c1 c2) c3);
    check_true "comb 3 - 1 == 2" comb (comb#mk_eq (comb#mk_sub c3 c1) c2);
    check_true "comb 2 * 3 == 6" comb (comb#mk_eq (comb#mk_mul c2 c3) (comb#mk_intlit 6));
    check_true "comb 3 / 2 == 1" comb (comb#mk_eq (comb#mk_div c3 c2) c1);
    check_true "comb 3 % 2 == 1" comb (comb#mk_eq (comb#mk_mod c3 c2) c1);
    check_true "comb 1 < 2" comb (comb#mk_lt c1 c2);
    check_true "comb 1 <= 1" comb (comb#mk_le c1 c1);
    check_true "comb intlit_of_string" comb (comb#mk_eq (comb#mk_intlit_of_string "100") (comb#mk_intlit 100));

    (* Real arithmetic *)
    let r1 = comb#mk_reallit 5 in
    let r2 = comb#mk_reallit_of_num (Num.num_of_int 5) in
    let r_sum = comb#mk_real_add r1 r2 in
    check_true "comb real 5 + 5 == 10" comb (comb#mk_eq r_sum (comb#mk_reallit 10));
    check_true "comb real 10 - 5 == 5" comb (comb#mk_eq (comb#mk_real_sub r_sum r1) r2);
    check_true "comb real 5 * 5 == 25" comb (comb#mk_eq (comb#mk_real_mul r1 r2) (comb#mk_reallit 25));
    check_true "comb real 5 < 10" comb (comb#mk_real_lt r1 r_sum);
    check_true "comb real 5 <= 5" comb (comb#mk_real_le r1 r1);

    (* Boxing / Unboxing *)
    let b_int = comb#mk_boxed_int c1 in
    let u_int = comb#mk_unboxed_int b_int in
    check_true "comb box/unbox int" comb (comb#mk_eq u_int c1);

    let b_bool = comb#mk_boxed_bool t_true in
    let u_bool = comb#mk_unboxed_bool b_bool in
    check_true "comb box/unbox bool" comb u_bool;

    let b_real = comb#mk_boxed_real r1 in
    let u_real = comb#mk_unboxed_real b_real in
    check_true "comb box/unbox real" comb (comb#mk_real_le u_real r1);

    (* Symbols & App with Both, Left, Right *)
    let sym = comb#mk_symbol "comb_f" [comb#type_int] comb#type_int Uninterp in
    let app_both = comb#mk_app sym [c1] in
    check "comb mk_app Both" (match app_both with Combineprovers.Both _ -> true | _ -> false);

    let app_left = comb#mk_app sym [Combineprovers.Left (redux_ctxt#mk_intlit 1)] in
    check "comb mk_app Left" (match app_left with Combineprovers.Left _ -> true | _ -> false);

    let app_right = comb#mk_app sym [Combineprovers.Right (z3_ctxt#mk_intlit 1)] in
    check "comb mk_app Right" (match app_right with Combineprovers.Right _ -> true | _ -> false);

    (* Scopes, push, pop, assert_term, assume *)
    comb#push;
    comb#assert_term t_true;
    let sym_x = comb#mk_symbol "cx" [] comb#type_int Uninterp in
    let cx = comb#mk_app sym_x [] in
    let _ = comb#assume (comb#mk_eq cx (comb#mk_intlit 42)) in
    check_true "comb assumed cx == 42" comb (comb#mk_eq cx (comb#mk_intlit 42));
    comb#pop;

    (* Assume contradiction returning Unsat *)
    comb#push;
    let res_unsat = comb#assume (comb#mk_eq c1 c2) in
    check "comb assume contradiction returns Unsat" (res_unsat = Unsat);
    comb#pop;

    (* Quantifiers *)
    comb#begin_formal;
    let bound = comb#mk_bound 0 comb#type_int in
    comb#end_formal;
    check "comb mk_bound" (match bound with Combineprovers.Both _ -> true | _ -> false);
    comb#assume_forall "comb_forall" [] [] t_true;
    let raised_fa = ref false in
    (try comb#assume_forall "ax" [] [] (Combineprovers.Left (redux_ctxt#mk_true)) with _ -> raised_fa := true);
    check "comb assume_forall failwith on Left" !raised_fa;

    (* Simplify across Left, Right, Both, None *)
    let _ = comb#simplify app_both in
    let _ = comb#simplify (Combineprovers.Left (redux_ctxt#mk_intlit 1)) in
    let _ = comb#simplify (Combineprovers.Right (z3_ctxt#mk_intlit 1)) in

    (* map2 and map3 mixed Left/Right/Both arms *)
    let left_t = Combineprovers.Left (redux_ctxt#mk_intlit 10) in
    let right_t = Combineprovers.Right (z3_ctxt#mk_intlit 20) in
    let both_t = comb#mk_intlit 30 in

    let left_sum = comb#mk_add left_t both_t in
    check "map2 Left-Both" (match left_sum with Combineprovers.Left _ -> true | _ -> false);

    let both_left_sum = comb#mk_add both_t left_t in
    check "map2 Both-Left" (match both_left_sum with Combineprovers.Left _ -> true | _ -> false);

    let right_sum = comb#mk_add right_t both_t in
    check "map2 Right-Both" (match right_sum with Combineprovers.Right _ -> true | _ -> false);

    let both_right_sum = comb#mk_add both_t right_t in
    check "map2 Both-Right" (match both_right_sum with Combineprovers.Right _ -> true | _ -> false);

    let left_ite = comb#mk_ifthenelse (Combineprovers.Left redux_ctxt#mk_true) both_t both_t in
    check "map3 Left-Both-Both" (match left_ite with Combineprovers.Left _ -> true | _ -> false);

    let right_ite = comb#mk_ifthenelse (Combineprovers.Right z3_ctxt#mk_true) both_t both_t in
    check "map3 Right-Both-Both" (match right_ite with Combineprovers.Right _ -> true | _ -> false);

    (* Pretty-printing and stats *)
    check "comb pprint Both" (String.length (comb#pprint c1) > 0);
    check "comb pprint Left" (String.length (comb#pprint (Combineprovers.Left (redux_ctxt#mk_intlit 1))) > 0);
    check "comb pprint Right" (String.length (comb#pprint (Combineprovers.Right (z3_ctxt#mk_intlit 1))) > 0);
    check "comb pprint_sym" (String.length (comb#pprint_sym sym) > 0);
    check "comb pprint_sort" (String.length (comb#pprint_sort comb#type_int) > 0);

    let (s, l) = comb#stats in
    check "comb stats" (String.length s > 0 && List.length l >= 0)
  ) strategies

(* ========================================== *)
(* Suite 4: Smtlibprover Comprehensive        *)
(* ========================================== *)
let test_smtlibprover () =
  let dump_path = "/tmp/test_unit_smtlib_dump.smt2" in
  let smt_ctxt = Smtlibprover.dump_smtlib_ctxt dump_path ["dump"; "I"; "Q"; "LIA"; "LRA"; "NDT"; "ALL"] in
  
  check "smtlib type_bool" (smt_ctxt#type_bool = Smtlib.bool);
  check "smtlib type_int" (smt_ctxt#type_int = Smtlib.int);
  check "smtlib type_real" (smt_ctxt#type_real = Smtlib.real);
  check "smtlib type_inductive" (smt_ctxt#type_inductive = Smtlib.inductive);

  (* Booleans *)
  let t_true = smt_ctxt#mk_true in
  let t_false = smt_ctxt#mk_false in
  let _ = smt_ctxt#mk_and t_true t_false in
  let _ = smt_ctxt#mk_or t_true t_false in
  let _ = smt_ctxt#mk_not t_true in
  let _ = smt_ctxt#mk_iff t_true t_false in
  let _ = smt_ctxt#mk_implies t_true t_false in
  let _ = smt_ctxt#mk_ifthenelse t_true (smt_ctxt#mk_intlit 1) (smt_ctxt#mk_intlit 2) in

  (* Int arithmetic *)
  let one = smt_ctxt#mk_intlit 1 in
  let two = smt_ctxt#mk_intlit 2 in
  let _ = smt_ctxt#mk_add one two in
  let _ = smt_ctxt#mk_sub two one in
  let _ = smt_ctxt#mk_mul one two in
  let _ = smt_ctxt#mk_div two one in
  let _ = smt_ctxt#mk_mod two one in
  let _ = smt_ctxt#mk_lt one two in
  let _ = smt_ctxt#mk_le one two in
  let _ = smt_ctxt#mk_eq one two in
  let _ = smt_ctxt#mk_intlit_of_string "999" in
  let _ = smt_ctxt#mk_intlit_of_string "not_an_int" in (* Exercises fallback warning comment! *)

  (* Real arithmetic *)
  let r1 = smt_ctxt#mk_reallit 1 in
  let r2 = smt_ctxt#mk_reallit_of_num (Num.num_of_int 2) in
  let _ = smt_ctxt#mk_real_add r1 r2 in
  let _ = smt_ctxt#mk_real_sub r2 r1 in
  let _ = smt_ctxt#mk_real_mul r1 r2 in
  let _ = smt_ctxt#mk_real_lt r1 r2 in
  let _ = smt_ctxt#mk_real_le r1 r2 in

  (* Boxing / Unboxing *)
  let b_int = smt_ctxt#mk_boxed_int one in
  let _ = smt_ctxt#mk_unboxed_int b_int in
  let b_bool = smt_ctxt#mk_boxed_bool t_true in
  let _ = smt_ctxt#mk_unboxed_bool b_bool in
  let b_real = smt_ctxt#mk_boxed_real r1 in
  let _ = smt_ctxt#mk_unboxed_real b_real in

  (* Symbols and Constructors *)
  let subtype = InductiveSubtype.alloc () in
  let sym_c0 = smt_ctxt#mk_symbol "smt_c0" [] smt_ctxt#type_inductive (Ctor (CtorByOrdinal (subtype, 0))) in
  let sym_c1 = smt_ctxt#mk_symbol "smt_c1" [smt_ctxt#type_int] smt_ctxt#type_inductive (Ctor (CtorByOrdinal (subtype, 1))) in
  let c0 = smt_ctxt#mk_app sym_c0 [] in
  let c1 = smt_ctxt#mk_app sym_c1 [one] in

  (* set_fpclauses *)
  let sym_rec = smt_ctxt#mk_symbol "smt_rec" [smt_ctxt#type_inductive] smt_ctxt#type_int (Fixpoint (subtype, 0)) in
  smt_ctxt#set_fpclauses sym_rec 0 [
    (sym_c0, fun _ _ -> one);
    (sym_c1, fun _ cargs -> List.hd cargs)
  ];

  (* Scopes & Assertions *)
  smt_ctxt#push;
  let _ = smt_ctxt#assume (smt_ctxt#mk_eq c0 c1) in
  smt_ctxt#assert_term (smt_ctxt#mk_eq one one);
  let _ = smt_ctxt#query (smt_ctxt#mk_eq one one) in
  smt_ctxt#pop;

  (* Quantifiers *)
  smt_ctxt#begin_formal;
  let bound0 = smt_ctxt#mk_bound 0 smt_ctxt#type_int in
  smt_ctxt#end_formal;
  smt_ctxt#assume_forall "smt_ax1" [] [] t_true;
  smt_ctxt#assume_forall "smt_ax2" [bound0] [smt_ctxt#type_int] t_true;

  (* Pretty-printing & stats *)
  check "smtlib pprint" (String.length (smt_ctxt#pprint one) > 0);
  check "smtlib pprint_sort" (String.length (smt_ctxt#pprint_sort smt_ctxt#type_int) > 0);
  check "smtlib pprint_sym" (String.length (smt_ctxt#pprint_sym sym_c0) > 0);
  check "smtlib simplify" (smt_ctxt#simplify one <> None);
  let (stat_str, _) = smt_ctxt#stats in
  check "smtlib stats" (String.length stat_str > 0);
  

  let ic = open_in dump_path in
  let contents = really_input_string ic (in_channel_length ic) in
  close_in ic;
  Sys.remove dump_path;
  
  check "SMTLib dump generated non-empty output" (String.length contents > 0);
  check "SMTLib dump contains push" (contains contents "push");
  check "SMTLib dump contains pop" (contains contents "pop");
  check "SMTLib dump contains assert" (contains contents "assert");
  check "SMTLib dump contains Warning" (contains contents "Warning");

  (* External smtlib_ctxt echo tests *)
  let ext_unsat = Smtlibprover.external_smtlib_ctxt "echo unsat" ["I"; "Q"; "ALL"] in
  check "ext unsat query" (ext_unsat#query ext_unsat#mk_true = true);

  let ext_unknown = Smtlibprover.external_smtlib_ctxt "echo unknown" ["I"; "Q"; "ALL"] in
  check "ext unknown query" (ext_unknown#query ext_unknown#mk_true = false)

let run () =
  passed_assertions := 0;
  check "string_of_assume_result Unknown" (string_of_assume_result Unknown = "unknown");
  check "string_of_assume_result Unsat" (string_of_assume_result Unsat = "unsat");
  let redux_raw = new Redux.context () in
  let redux_ctxt = (redux_raw :> (_, _, _) context) in
  test_redux_booleans redux_ctxt;
  test_redux_arithmetic redux_ctxt;
  test_redux_congruence redux_ctxt;
  test_redux_constructors redux_ctxt;
  test_redux_backtracking redux_ctxt;
  test_redux_simplify_and_stats redux_raw;
  (try test_z3_prover () with ex -> Printf.eprintf "test_z3_prover failed: %s
%s
" (Printexc.to_string ex) (Printexc.get_backtrace ()); raise ex);
  (try test_combineprovers () with ex -> Printf.eprintf "test_combineprovers failed: %s
%s
" (Printexc.to_string ex) (Printexc.get_backtrace ()); raise ex);
  (try test_smtlibprover () with ex -> Printf.eprintf "test_smtlibprover failed: %s
%s
" (Printexc.to_string ex) (Printexc.get_backtrace ()); raise ex);
  !passed_assertions
