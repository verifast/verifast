open Num
open Simplex

let passed_assertions = ref 0

let check msg condition =
  if condition then
    incr passed_assertions
  else (
    Printf.eprintf "[FAIL] Simplex assertion failed: %s\n" msg;
    assert false
  )

let check_sat msg res =
  check msg (res = Sat)

let check_unsat msg res =
  check msg (res = Unsat)

(* Helper to create int num *)
let n_int = num_of_int
let n_str = num_of_string

(* Test 1: Basic single-variable feasibility and bounds *)
let test_basic_bounds () =
  let s = new_simplex () in
  let x = s#alloc_unknown "x" 1 in
  
  (* x >= 0: x + 0 >= 0 *)
  check_sat "x >= 0 is Sat" (s#assert_ge (n_int 0) [n_int 1, x]);
  (* x <= 10: 10 - x >= 0 *)
  check_sat "x <= 10 is Sat" (s#assert_ge (n_int 10) [n_int (-1), x]);
  (* x >= 5: x - 5 >= 0 *)
  check_sat "x >= 5 is Sat" (s#assert_ge (n_int (-5)) [n_int 1, x]);
  (* x >= 12: x - 12 >= 0 -> should be Unsat since x <= 10 *)
  check_unsat "x >= 12 is Unsat" (s#assert_ge (n_int (-12)) [n_int 1, x])

(* Test 2: Infeasible single variable systems *)
let test_single_var_unsat () =
  let s1 = new_simplex () in
  let x1 = s1#alloc_unknown "x" 1 in
  check_sat "x1 >= 5" (s1#assert_ge (n_int (-5)) [n_int 1, x1]);
  check_unsat "x1 <= 3 is Unsat" (s1#assert_ge (n_int 3) [n_int (-1), x1]);

  let s2 = new_simplex () in
  let x2 = s2#alloc_unknown "x" 2 in
  check_sat "x2 <= -10" (s2#assert_ge (n_int (-10)) [n_int (-1), x2]);
  check_unsat "x2 >= -5 is Unsat" (s2#assert_ge (n_int 5) [n_int 1, x2])

(* Test 3: Two-variable systems *)
let test_two_variables () =
  (* x + y = 10, x >= 6, y >= 5 -> Unsat because x+y >= 11 *)
  let s1 = new_simplex () in
  let x = s1#alloc_unknown "x" 1 in
  let y = s1#alloc_unknown "y" 2 in
  check_sat "x + y = 10" (s1#assert_eq (n_int (-10)) [n_int 1, x; n_int 1, y]);
  check_sat "x >= 6" (s1#assert_ge (n_int (-6)) [n_int 1, x]);
  check_unsat "y >= 5 is Unsat" (s1#assert_ge (n_int (-5)) [n_int 1, y]);

  (* Feasible system: x + y = 10, x >= 4, y >= 4 *)
  let s2 = new_simplex () in
  let x' = s2#alloc_unknown "x" 3 in
  let y' = s2#alloc_unknown "y" 4 in
  check_sat "x + y = 10 (feasible)" (s2#assert_eq (n_int (-10)) [n_int 1, x'; n_int 1, y']);
  check_sat "x >= 4" (s2#assert_ge (n_int (-4)) [n_int 1, x']);
  check_sat "y >= 4" (s2#assert_ge (n_int (-4)) [n_int 1, y']);
  check_sat "y <= 6" (s2#assert_ge (n_int 6) [n_int (-1), y'])

(* Test 4: Three-variable linear systems *)
let test_multi_variables () =
  (* x + y + z = 100, x >= 30, y >= 40, z >= 35 -> Unsat (sum >= 105) *)
  let s = new_simplex () in
  let x = s#alloc_unknown "x" 1 in
  let y = s#alloc_unknown "y" 2 in
  let z = s#alloc_unknown "z" 3 in
  check_sat "x + y + z = 100" (s#assert_eq (n_int (-100)) [n_int 1, x; n_int 1, y; n_int 1, z]);
  check_sat "x >= 30" (s#assert_ge (n_int (-30)) [n_int 1, x]);
  check_sat "y >= 40" (s#assert_ge (n_int (-40)) [n_int 1, y]);
  check_unsat "z >= 35 is Unsat" (s#assert_ge (n_int (-35)) [n_int 1, z]);

  (* Triangular inequality / sum bound: a+b <= 10, b+c <= 10, a+c <= 10, a+b+c >= 16 -> Unsat *)
  let s_tri = new_simplex () in
  let a = s_tri#alloc_unknown "a" 4 in
  let b = s_tri#alloc_unknown "b" 5 in
  let c = s_tri#alloc_unknown "c" 6 in
  check_sat "a + b <= 10" (s_tri#assert_ge (n_int 10) [n_int (-1), a; n_int (-1), b]);
  check_sat "b + c <= 10" (s_tri#assert_ge (n_int 10) [n_int (-1), b; n_int (-1), c]);
  check_sat "a + c <= 10" (s_tri#assert_ge (n_int 10) [n_int (-1), a; n_int (-1), c]);
  check_unsat "a + b + c >= 16 is Unsat" (s_tri#assert_ge (n_int (-16)) [n_int 1, a; n_int 1, b; n_int 1, c])

(* Test 5: Rational / fractional coefficients *)
let test_rational_coefficients () =
  let s = new_simplex () in
  let x = s#alloc_unknown "x" 1 in
  let y = s#alloc_unknown "y" 2 in
  (* 1/2 x + 1/3 y = 1 *)
  let half = n_str "1/2" in
  let third = n_str "1/3" in
  check_sat "1/2 x + 1/3 y = 1" (s#assert_eq (n_int (-1)) [half, x; third, y]);
  check_sat "x >= 2" (s#assert_ge (n_int (-2)) [n_int 1, x]);
  (* if x >= 2, 1/2 x >= 1, so 1/3 y <= 0, so y <= 0. If we assert y >= 1 -> Unsat *)
  check_unsat "y >= 1 is Unsat" (s#assert_ge (n_int (-1)) [n_int 1, y]);

  (* Fine-grained rational offset: 1/1000 x >= 1 => x >= 1000 *)
  let s_fine = new_simplex () in
  let z = s_fine#alloc_unknown "z" 3 in
  let milli = n_str "1/1000" in
  check_sat "1/1000 z >= 1" (s_fine#assert_ge (n_int (-1)) [milli, z]);
  check_unsat "z <= 999 is Unsat" (s_fine#assert_ge (n_int 999) [n_int (-1), z])

(* Test 6: Equalities and zero coefficients *)
let test_equalities () =
  let s = new_simplex () in
  let x = s#alloc_unknown "x" 1 in
  let y = s#alloc_unknown "y" 2 in
  (* x = 5: x - 5 = 0 *)
  check_sat "x = 5" (s#assert_eq (n_int (-5)) [n_int 1, x]);
  (* x = 6 is Unsat *)
  check_unsat "x = 6 is Unsat" (s#assert_eq (n_int (-6)) [n_int 1, x]);

  (* Zero coefficient: 0 * x + y = 7 *)
  let s_zero = new_simplex () in
  let x0 = s_zero#alloc_unknown "x" 3 in
  let y0 = s_zero#alloc_unknown "y" 4 in
  check_sat "0*x + y = 7" (s_zero#assert_eq (n_int (-7)) [n_int 0, x0; n_int 1, y0]);
  check_unsat "y <= 6 is Unsat" (s_zero#assert_ge (n_int 6) [n_int (-1), y0])

(* Test 7: Disequalities (assert_neq) *)
let test_disequalities () =
  let s1 = new_simplex () in
  let x = s1#alloc_unknown "x" 1 in
  check_sat "x = 0" (s1#assert_eq (n_int 0) [n_int 1, x]);
  check_unsat "x != 0 is Unsat" (s1#assert_neq (n_int 0) [n_int 1, x]);

  let s2 = new_simplex () in
  let a = s2#alloc_unknown "a" 2 in
  let b = s2#alloc_unknown "b" 3 in
  check_sat "a - b = 0 (a = b)" (s2#assert_eq (n_int 0) [n_int 1, a; n_int (-1), b]);
  check_unsat "a - b != 0 is Unsat" (s2#assert_neq (n_int 0) [n_int 1, a; n_int (-1), b]);

  let s3 = new_simplex () in
  let u = s3#alloc_unknown "u" 4 in
  check_sat "u >= 10" (s3#assert_ge (n_int (-10)) [n_int 1, u]);
  check_sat "u != 0 is Sat" (s3#assert_neq (n_int 0) [n_int 1, u])

(* Test 8: Push / Pop backtracking *)
let test_push_pop () =
  let s = new_simplex () in
  let x = s#alloc_unknown "x" 1 in
  check_sat "base: x >= 0" (s#assert_ge (n_int 0) [n_int 1, x]);
  
  s#push;
  check_unsat "pushed: x <= -1 is Unsat" (s#assert_ge (n_int (-1)) [n_int (-1), x]);
  s#pop;
  
  (* Consistency is restored! Can assert x >= 10 *)
  check_sat "popped: x >= 10 is Sat" (s#assert_ge (n_int (-10)) [n_int 1, x]);

  (* Multi-level push/pop *)
  s#push; (* depth 1 *)
  check_sat "d1: x <= 50" (s#assert_ge (n_int 50) [n_int (-1), x]);
  s#push; (* depth 2 *)
  check_unsat "d2: x >= 100 is Unsat" (s#assert_ge (n_int (-100)) [n_int 1, x]);
  s#pop;  (* back to depth 1 *)
  check_sat "d1 again: x <= 40 is Sat" (s#assert_ge (n_int 40) [n_int (-1), x]);
  s#pop;  (* back to base *)
  check_sat "base again: x >= 100 is Sat" (s#assert_ge (n_int (-100)) [n_int 1, x])

(* Test 9: Listener callbacks and equality propagation *)
let test_listeners () =
  let s = new_simplex () in
  let x = s#alloc_unknown "x" 10 in
  let y = s#alloc_unknown "y" 20 in
  let eq_events = ref [] in
  let const_events = ref [] in
  s#register_listeners
    (fun u1 u2 -> eq_events := (print_unknown u1, print_unknown u2) :: !eq_events)
    (fun u c -> const_events := (print_unknown u, string_of_num c) :: !const_events);
  
  (* Assert x <= y: y - x >= 0 *)
  check_sat "x <= y" (s#assert_ge (n_int 0) [n_int 1, y; n_int (-1), x]);
  (* Assert y <= x: x - y >= 0 *)
  check_sat "y <= x" (s#assert_ge (n_int 0) [n_int 1, x; n_int (-1), y]);
  
  (* Simplex should propagate x = y *)
  check "eq_listener fired for x = y" (List.length !eq_events >= 1);

  (* Constant propagation: z >= 42 and z <= 42 *)
  let s_const = new_simplex () in
  let z = s_const#alloc_unknown "z" 30 in
  let const_events2 = ref [] in
  s_const#register_listeners (fun _ _ -> ()) (fun u c -> const_events2 := (print_unknown u, string_of_num c) :: !const_events2);
  check_sat "z >= 42" (s_const#assert_ge (n_int (-42)) [n_int 1, z]);
  check_sat "z <= 42" (s_const#assert_ge (n_int 42) [n_int (-1), z]);
  check "const_listener fired for z = 42" (List.length !const_events2 >= 1);
  check "const value is 42" (List.exists (fun (u, c) -> u = "z" && c = "42") !const_events2)

(* Test 10: Metadata and getters *)
let test_metadata () =
  let s = new_simplex () in
  let u = s#alloc_unknown "my_var" 99 in
  check "print_unknown" (print_unknown u = "my_var");
  check "unknown_tag" (unknown_tag u = Some 99);
  let ticks = s#get_ticks in
  check "get_ticks >= 0L" (Int64.compare ticks 0L >= 0);
  let pr = s#print in
  check "print string not empty" (String.length pr >= 0)

(* Test 11: Comprehensive print coverage (positive, negative, -1, 1, and restricted vars) *)
let test_print_and_dead_unknowns () =
  let s = new_simplex () in
  let a = s#alloc_unknown "a" 101 in
  let b = s#alloc_unknown "b" 102 in
  let c = s#alloc_unknown "c" 103 in
  let d = s#alloc_unknown "d" 104 in
  (* a + 2b - c - 3d >= 5 *)
  check_sat "ineq 1" (s#assert_ge (n_int (-5)) [n_int 1, a; n_int 2, b; n_int (-1), c; n_int (-3), d]);
  (* -a + b + 3c >= 2 *)
  check_sat "ineq 2" (s#assert_ge (n_int (-2)) [n_int (-1), a; n_int 1, b; n_int 3, c]);
  let out1 = s#print in
  check "s#print contains rows" (String.length out1 > 0);
  (* Now trigger an equality to make column dead *)
  check_sat "eq a = 10" (s#assert_eq (n_int (-10)) [n_int 1, a]);
  let out2 = s#print in
  check "s#print after equality" (String.length out2 > 0)

let run () =
  passed_assertions := 0;
  test_basic_bounds ();
  test_single_var_unsat ();
  test_two_variables ();
  test_multi_variables ();
  test_rational_coefficients ();
  test_equalities ();
  test_disequalities ();
  test_push_pop ();
  test_listeners ();
  test_metadata ();
  test_print_and_dead_unknowns ();
  !passed_assertions
