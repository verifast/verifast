type term = Term of string * term list

    method infer_symbol_kind s =
      try
        let index = String.rindex s '/' in
        let suffix = String.sub s (index + 1)(String.length s - index - 1) in
        let k = int_of_string suffix in
        Fixpoint k
      with Not_found -> 
        match String.get s 0 with 'A'..'Z' | '0'..'9' -> Ctor | _ -> Uninterp

    method get_node2 s vs =
      self#get_node (self#infer_symbol_kind s) s vs
    
    method get_node2_value s vs =
      (self#get_node2 s vs)#value
      
    method eval_term t =
      match t with
        Term (s, ts) ->
        let vs = List.map (fun t -> (self#eval_term t)#value) ts in
        self#get_node2 s vs
    

    method assert_terms_eq t1 t2 =
      self#do_and_reduce (fun () -> self#assert_eq (self#eval_term t1)#value (self#eval_term t2)#value)
      
    method assert_terms_neq t1 t2 =
      self#do_and_reduce (fun () -> self#assert_neq (self#eval_term t1)#value (self#eval_term t2)#value)

let create_context() = new context

type token = Eof | Lparen | Rparen | Atom of string

class scanner txt =
  object (self)
    val text = txt
    val n = String.length txt
    val mutable k = 0
    val mutable token = Eof
    initializer self#next
    method next =
      token <- self#scan_next_token
    method token = token
    method scan_next_token =
      if k = n then
        Eof
      else
      begin
        let c = String.get text k in
        k <- k + 1;
        match c with
          ' ' -> self#scan_next_token
        | '(' -> Lparen
        | ')' -> Rparen
        | c -> self#symbol (k - 1)
      end
    method symbol k0 =
      if k = n then
        Atom (String.sub text k0 (k - k0))
      else
        let c = String.get text k in
        match c with
          ' '|')'|'(' -> Atom (String.sub text k0 (k - k0))
        | _ -> k <- k + 1; self#symbol k0
  end

class parser scanner =
  object (self)
    val scanner = scanner
    method fail = failwith "Bad input"
    method parse_term =
      match scanner#token with
        Atom a -> scanner#next; Term (a, [])
      | Lparen ->
        scanner#next;
        begin
        match scanner#token with
          Atom a ->
          scanner#next;
          let ts = self#parse_terms in
          begin
          match scanner#token with
            Rparen ->
            scanner#next;
            Term (a, ts)
          | _ -> self#fail
          end
        | _ -> self#fail
        end
      | _ -> self#fail
    method parse_terms =
      match scanner#token with
        Rparen -> []
      | _ ->
        let t = self#parse_term in
        t::self#parse_terms
    method parse_term_eof =
      let t = self#parse_term in
      match scanner#token with
        Eof -> t
      | _ -> self#fail
  end

let parse_term s = (new parser (new scanner s))#parse_term_eof

let fpclauses =
  [
    ("add/0:Nil", (fun ctxt [l; x] [] -> ctxt#get_node2_value "Cons" [x; ctxt#get_node2_value "Nil" []]));
    ("add/0:Cons", (fun ctxt [l; x] [h; t] -> ctxt#get_node2_value "Cons" [h; ctxt#get_node2_value "add/0" [t; x]]));
    ("len/0:Nil", (fun ctxt [l] [] -> ctxt#get_node2_value "Zero" []));
    ("len/0:Cons", (fun ctxt [l] [h; t] -> ctxt#get_node2_value "Succ" [ctxt#get_node2_value "len/0" [t]]));
    ("head/0:Cons", (fun ctxt [l] [h; t] -> h));
    ("tail/0:Cons", (fun ctxt [l] [h; t] -> t));
    ("nth/1:Zero", (fun ctxt [l; n] [] -> ctxt#get_node2_value "head/0" [l]));
    ("nth/1:Succ", (fun ctxt [l; n] [m] -> ctxt#get_node2_value "nth/1" [ctxt#get_node2_value "tail/0" [l]; m]));
    ("evillen/0:Cons", (fun ctxt [l; n] [h; t] -> ctxt#get_node2_value "evillen/0" [t; ctxt#get_node2_value "Succ" [n]])) (* To construct matching loops... *)
  ]

let _ =
  let ctxt = ref (new context fpclauses) in
  let eval s = !ctxt#eval_term (parse_term s) in
  let reset() = ctxt := new context fpclauses in
  let push() = !ctxt#push in
  let pop() = !ctxt#pop in
  let assert_eq s1 s2 = !ctxt#assert_terms_eq (parse_term s1) (parse_term s2) in
  let assert_neq s1 s2 = !ctxt#assert_terms_neq (parse_term s1) (parse_term s2) in

  let v1 = eval "(tree nil nil (succ zero))" in
  let v2 = eval "(tree nil nil (succ zero))" in
  assert (v1 = v2);
  let v3 = eval "(tree nil nil zero)" in
  assert (v3 <> v1);
  assert (assert_eq "fx" "(f x)" = Unknown);
  assert (assert_eq "fy" "(f y)" = Unknown);
  assert (assert_eq "x" "y" = Unknown);
  assert (assert_neq "fx" "fy" = Unsat);

  reset();
  assert (assert_eq "fxy" "(f x y)" = Unknown);
  assert (assert_eq "fyx" "(f y x)" = Unknown);
  assert (assert_eq "x" "y" = Unknown);
  assert (assert_neq "fxy" "fyx" = Unsat);
  
  reset();
  assert (assert_eq "x" "(f (g y))" = Unknown);
  assert (assert_eq "(f 5)" "3" = Unknown);
  assert (assert_eq "(g 7)" "z" = Unknown);
  assert (assert_eq "7" "y" = Unknown);
  assert (assert_eq "z" "5" = Unknown);
  assert (assert_neq "x" "3" = Unsat);

  reset();
  assert (assert_eq "fx" "(f x)" = Unknown);
  assert (assert_eq "fy" "(f y)" = Unknown);
  push();
  assert (assert_eq "x" "y" = Unknown);
  assert (assert_neq "fx" "fy" = Unsat);
  pop();
  assert (assert_neq "fx" "fy" = Unknown);
  assert (assert_neq "x" "y" = Unknown);
  
  reset();
  assert (assert_eq "x0" "x" = Unknown);
  assert (assert_eq "y0" "y" = Unknown);
  push();
  assert (assert_eq "x0" "y0" = Unknown);
  assert (assert_neq "x" "y" = Unsat);
  pop();
  push();
  assert (assert_neq "x0" "y0" = Unknown);
  assert (assert_eq "x" "y" = Unsat);
  pop();
  assert (assert_eq "x0" "y0" = Unknown);
  assert (assert_eq "x" "y" = Unknown);
  
  reset();
  assert (assert_eq "x0" "x" = Unknown);
  assert (assert_eq "y0" "y" = Unknown);
  push();
  assert (assert_eq "x0" "y0" = Unknown);
  assert (assert_neq "x" "y" = Unsat);
  pop();
  push();
  assert (assert_neq "x0" "y0" = Unknown);
  push();
  assert (assert_eq "x" "(f x1)" = Unknown);
  assert (assert_eq "y" "(f y1)" = Unknown);
  assert (assert_eq "x1" "y1" = Unsat);
  pop();
  push();
  assert (assert_eq "x1" "y1" = Unknown);
  pop();
  assert (assert_neq "x1" "y1" = Unknown);
  pop();
  assert (assert_eq "x0" "y0" = Unknown);
  assert (assert_eq "x" "y" = Unknown);
  
  reset();
  assert (assert_eq "1" "2" = Unsat);
  
  reset();
  assert (assert_neq "1" "2" = Unknown);
  
  reset();
  assert (assert_eq "(Succ (Succ (Succ (Zero))))" "(Succ (Succ (Zero)))" = Unsat);
  
  reset();
  assert (assert_eq "(Succ (Succ (x)))" "(Succ (Succ (y)))" = Unknown);
  assert (assert_neq "x" "y" = Unsat);
  
  reset();
  assert (assert_neq "(len/0 (add/0 (add/0 Nil 5) 10))" "(Succ (Succ Zero))" = Unsat);
  
  reset();
  assert (assert_neq "(nth/1 (add/0 (add/0 Nil 5) 10) Zero)" "5" = Unsat);
  
  reset();
  assert (assert_neq "(nth/1 (add/0 (add/0 Nil 5) 10) (Succ Zero))" "10" = Unsat);
  
  reset();
  assert (assert_neq "(add/0 (add/0 Nil 5) 10)" "(Cons 5 (Cons 10 Nil))" = Unsat);
  
  reset();
  assert (assert_eq "(add/0 (add/0 Nil 5) 10)" "(Cons 5 (Cons 10 (Cons 15 Nil)))" = Unsat);
  
  reset();
  assert (assert_eq "(len/0 (Cons h t))" "n1" = Unknown);
  assert (assert_eq "(len/0 t)" "n2" = Unknown);
  assert (assert_neq "(Succ n2)" "n1" = Unsat);
  
  (*
  Uncomment to get a nice matching loop...
  
  reset();
  assert (assert_eq "inf" "(Cons 5 inf)" = Unknown);
  assert (assert_eq "(evillen/0 inf Zero)" "x" = Unsat);
  *)