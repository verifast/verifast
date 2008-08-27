open Num
open Simplex

let mk_simplex () =
  let eqs: (string unknown * string unknown) list ref = ref [] in
  let consts: (string unknown * int) list ref = ref [] in
  let eqs_eq es2 = !eqs = es2 in
  let consts_eq cs2 = !consts = cs2 in
  let s =
  new simplex
    (fun u1 u2 -> print_endline ("Propagating equality between " ^ u1#print ^ " and " ^ u2#print); eqs := (u1, u2)::!eqs)
    (fun u n -> print_endline ("Propagating equality between unknown " ^ u#print ^ " and constant " ^ string_of_int n); consts := (u, n)::!consts)
  in
  (s, eqs_eq, consts_eq)

let alloc_unknown simplex name = simplex#alloc_unknown name (Some name)

let _ =
  let (s, eqs_eq, consts_eq) = mk_simplex() in
  let x = alloc_unknown s "x" in
  let y = alloc_unknown s "y" in
  
  let assert_ge c1 ts1 c2 ts2 =
    s#assert_ge (c2 - c1) (List.map (fun (n, u) -> (-n, u)) ts1 @ List.map (fun (n, u) -> (n, u)) ts2)
  in
  
  assert (assert_ge 0 [] 0 [1, x] = Sat); (* 0 <= x *)
  print_string s#print;
  assert (assert_ge 1 [1, x] 0 [1, y] = Sat); (* x < y *)
  print_string s#print;
  assert (assert_ge 0 [1, y] 0 [] = Unsat); (* y <= 0 *)
  
  ()

let _ =
  let (s, eqs_eq, consts_eq) = mk_simplex() in
  let x = alloc_unknown s "x" in
  let y = alloc_unknown s "y" in
  let z = alloc_unknown s "z" in
  
  let assert_ge c1 ts1 c2 ts2 =
    s#assert_ge (c2 - c1) (List.map (fun (n, u) -> (-n, u)) ts1 @ List.map (fun (n, u) -> (n, u)) ts2)
  in
  
  assert (assert_ge 0 [] 0 [1, x] = Sat); (* 0 <= x *)
  print_string s#print;
  assert (assert_ge 1 [1, x] 0 [1, y] = Sat); (* x < y *)
  print_string s#print;
  assert (assert_ge 1 [1, y] 0 [1, z] = Sat); (* y < z *)
  print_string s#print;
  assert (assert_ge 0 [1, z] 0 [1, y] = Unsat); (* z <= y *)
  
  ()

let _ =
  let (s, eqs_eq, consts_eq) = mk_simplex() in
  let x = alloc_unknown s "x" in
  
  let assert_ge c1 ts1 c2 ts2 =
    s#assert_ge (c2 - c1) (List.map (fun (n, u) -> (-n, u)) ts1 @ List.map (fun (n, u) -> (n, u)) ts2)
  in
  
  assert (assert_ge 0 [] 0 [1, x] = Sat); (* 0 <= x *)
  print_string s#print;
  print_endline "Should propagate x == 0:";
  assert (assert_ge 0 [1, x] 0 [] = Sat); (* x <= 0 *)
  print_string s#print;
  assert (eqs_eq []);
  assert (consts_eq [(x, 0)]);
  
  ()

let _ =
  let (s, eqs_eq, consts_eq) = mk_simplex() in
  let x = alloc_unknown s "x" in
  let y = alloc_unknown s "y" in
  
  let assert_ge c1 ts1 c2 ts2 =
    s#assert_ge (c2 - c1) (List.map (fun (n, u) -> (-n, u)) ts1 @ List.map (fun (n, u) -> (n, u)) ts2)
  in
  
  assert (assert_ge 0 [1, x] 0 [1, y] = Sat); (* x <= y *)
  print_string s#print;
  print_endline "Should propagate x == y";
  assert (assert_ge 0 [1, y] 0 [1, x] = Sat); (* y <= x *)
  print_string s#print;
  assert (eqs_eq [(y, x)]);
  assert (consts_eq []);
  
  ()

let _ =
  let (s, eqs_eq, consts_eq) = mk_simplex() in
  let x = alloc_unknown s "x" in
  let y = alloc_unknown s "y" in
  let z = alloc_unknown s "z" in
  
  let assert_ge c1 ts1 c2 ts2 =
    s#assert_ge (c2 - c1) (List.map (fun (n, u) -> (-n, u)) ts1 @ List.map (fun (n, u) -> (n, u)) ts2)
  in
  
  assert (assert_ge 0 [1, x] 0 [1, y; 1, z] = Sat); (* x <= y + z *)
  print_string s#print;
  assert (assert_ge 0 [1, y; 1, z] 0 [1, x] = Sat); (* y + z <= x *)
  print_string s#print;
  assert (assert_ge 0 [] 0 [1, y] = Sat); (* 0 <= y *)
  print_string s#print;
  print_endline "Should propagate x == z";
  assert (assert_ge 0 [1, y] 0 [] = Sat); (* y <= 0 *)
  assert (eqs_eq [(z, x)]);
  assert (consts_eq [(y, 0)]);
  
  ()

let _ =
  let (s, eqs_eq, consts_eq) = mk_simplex() in
  let x = alloc_unknown s "x" in
  
  assert (s#assert_eq (-5) [1, x] = Sat);
  assert (s#assert_eq 5 [1, x] = Unsat)

let _ =
  let (s, eqs_eq, consts_eq) = mk_simplex() in
  let x = alloc_unknown s "x" in
  
  s#push;
  assert (s#assert_eq (-5) [1, x] = Sat);
  assert (s#assert_eq 5 [1, x] = Unsat);
  s#pop;
  assert (s#assert_eq 5 [1, x] = Sat);
  assert (s#assert_eq (-5) [1, x] = Unsat)

let _ =
  let (s, eqs_eq, consts_eq) = mk_simplex() in
  let x = alloc_unknown s "x" in
  let y = alloc_unknown s "y" in
  let z = alloc_unknown s "z" in
  
  assert (s#assert_ge (2) [-1, x] = Sat);  (* x <= 2 *)
  s#push;
  assert (s#assert_ge (-10) [1, x; 1, y] = Sat);  (* 10 <= x + y *)
  assert (s#assert_ge 7 [-1, y] = Unsat); (* y <= 7 *)
  s#pop;
  assert (s#assert_ge (-5) [1, x; 1, y] = Sat);  (* 5 <= x + y *)
  assert (s#assert_ge 2 [-1, y] = Unsat); (* y <= 2 *)
  ()