let rec try_assoc key al =
  match al with
    [] -> None
  | (k, v)::al -> if k = key then Some v else try_assoc key al

let flatmap f xs = List.concat (List.map f xs)

type term = Term of string * term list

type assert_result = Unknown | Unsat

type symbol_kind = Ctor | Fixpoint of int | Uninterp

class termnode ctxt knd s vs =
  object (self)
    val context = ctxt
    val kind = knd
    val symbol = s
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable children: valuenode list = vs
    val mutable value = new valuenode ctxt
    method symbol = symbol
    method children = children
    method push =
      if context#pushdepth <> pushdepth then
      begin
        popstack <- (pushdepth, children, value)::popstack;
        context#register_popaction (fun () -> self#pop);
        pushdepth <- context#pushdepth
      end
    method pop =
      match popstack with
        (pushdepth0, children0, value0)::popstack0 ->
        pushdepth <- pushdepth0;
        children <- children0;
        value <- value0;
        popstack <- popstack0
      | [] -> assert false
    method value = value
    method is_ctor = kind = Ctor
    initializer begin
      let rec iter k (vs: valuenode list) =
        match vs with
          [] -> ()
        | v::vs ->
          v#add_parent ((self :> termnode), k);
          iter (k + 1) vs
      in
      iter 0 vs;
      value#add_child (self :> termnode);
      if kind = Ctor then value#set_ctorchild (self :> termnode)
    end
    method set_value v =
      self#push;
      value <- v
    method set_child k v =
      let rec replace i vs =
        match vs with
          [] -> []
        | v0::vs -> if i = k then v::vs else v0::replace (i + 1) vs
      in
      self#push;
      children <- replace 0 children
    method matches s vs =
      symbol = s && children = vs
    method lookup_equivalent_parent_of v =
      v#lookup_parent symbol children
  end
and valuenode ctxt =
  object (self)
    val context = ctxt
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable children: termnode list = []
    val mutable parents: (termnode * int) list = []
    val mutable ctorchild: termnode option = None
    val mutable neqs: valuenode list = []
    method push =
      if ctxt#pushdepth <> pushdepth then
      begin
        popstack <- (pushdepth, children, parents, ctorchild, neqs)::popstack;
        ctxt#register_popaction (fun () -> self#pop);
        pushdepth <- ctxt#pushdepth
      end
    method pop =
      match popstack with
        (pushdepth0, children0, parents0, ctorchild0, neqs0)::popstack0 ->
        pushdepth <- pushdepth0;
        children <- children0;
        parents <- parents0;
        ctorchild <- ctorchild0;
        neqs <- neqs0;
        popstack <- popstack0
      | [] -> assert(false)
    method ctorchild = ctorchild
    method add_parent p =
      self#push;
      parents <- p::parents
    method set_ctorchild c =
      self#push;
      ctorchild <- Some c
    method add_child c =
      self#push;
      children <- c::children
    method neq v =
      match (ctorchild, v#ctorchild) with
        (Some n1, Some n2) when n1#symbol <> n2#symbol -> true
      | _ -> List.mem v neqs
    method add_neq v =
      self#push;
      neqs <- v::neqs
    method neq_merging_into vold vnew =
      self#push;
      neqs <- List.map (fun v0 -> if v0 = vold then vnew else vold) neqs;
      vnew#add_neq (self :> valuenode)
    method lookup_parent s vs =
      let rec iter ns =
        match ns with
          [] -> None
        | (n, _)::ns -> if n#matches s vs then Some n else iter ns
      in
      iter parents
    method merge_into v =
      List.iter (fun n -> n#set_value v) children;
      List.iter (fun n -> v#add_child n) children;
      List.iter (fun vneq -> vneq#neq_merging_into (self :> valuenode) v) neqs;
      List.iter (fun (n, k) -> n#set_child k v) parents;
      (* At this point self is referenced nowhere. *)
      (* It is possible that some of the nodes in 'parents' are now equivalent with nodes in v.parents. *)
      let redundant_parents =
        flatmap
          (fun (n, k) ->
             let result =
               match n#lookup_equivalent_parent_of v with
                 None ->
                 []
               | Some n' ->
                 [(n, n')]
             in
             v#add_parent (n, k);
             result
          )
          parents
      in
      let process_redundant_parents() =
        let rec iter rps =
          match rps with
            [] -> Unknown
          | (n, n')::rps ->
            begin
              (* print_endline "Doing a recursive assert_eq!"; *)
              let result = context#assert_eq n#value n'#value in
              (* print_endline "Returned from recursive assert_eq"; *)
              match result with
                Unsat -> Unsat
              | Unknown -> iter rps
            end
        in
        iter redundant_parents
      in
      match (ctorchild, v#ctorchild) with
        (None, _) -> process_redundant_parents()
      | (Some n, None) -> v#set_ctorchild n; process_redundant_parents()
      | (Some n, Some n') ->
        (* print_endline "Adding injectiveness edges..."; *)
        let rec iter vs =
          match vs with
            [] -> process_redundant_parents()
          | (v, v')::vs ->
            begin
            match context#assert_eq v v' with
              Unsat -> Unsat
            | Unknown -> iter vs
            end
        in
        iter (List.combine n#children n'#children)

  end
and context =
  object (self)
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable popactionlist: (unit -> unit) list = []
    val mutable leafnodemap: (string * termnode) list = []
    
    method pushdepth = pushdepth
    method push =
      popstack <- (pushdepth, popactionlist, leafnodemap)::popstack;
      pushdepth <- pushdepth + 1;
      popactionlist <- []
    
    method register_popaction action =
      popactionlist <- action::popactionlist

    method pop =
      match popstack with
        (pushdepth0, popactionlist0, leafnodemap0)::popstack0 ->
        List.iter (fun action -> action()) popactionlist;
        pushdepth <- pushdepth0;
        popactionlist <- popactionlist0;
        leafnodemap <- leafnodemap0
      | [] -> failwith "Popstack is empty"

    method eval_term t =
      match t with
        Term (s, ts) ->
        let kind =
          try
            let index = String.rindex s '/' in
            let suffix = String.sub s index (String.length s - index) in
            let k = int_of_string suffix in
            Fixpoint k
          with Not_found -> 
            match String.get s 0 with 'A'..'Z' | '0'..'9' -> Ctor | _ -> Uninterp
        in
        begin
        let vs = List.map self#eval_term ts in
        match vs with
          [] ->
          begin
          match try_assoc s leafnodemap with
            None ->
            let node = new termnode (self :> context) kind s vs in
            leafnodemap <- (s, node)::leafnodemap;
            node#value
          | Some n -> n#value
          end
        | v::_ ->
          begin
          match v#lookup_parent s vs with
            None ->
            let node = new termnode (self :> context) kind s vs in
            node#value
          | Some n -> n#value
          end
        end
    
    method assert_neq (v1: valuenode) (v2: valuenode) =
      if v1 = v2 then
        Unsat
      else if v1#neq v2 then
        Unknown
      else
      begin
        v1#add_neq v2;
        v2#add_neq v1;
        Unknown
      end

    method assert_eq v1 v2 =
      if v1 = v2 then
      begin
        (* print_endline "assert_eq: values already the same"; *)
        Unknown
      end
      else if v1#neq v2 then
      begin
        (* print_endline "assert_eq: values are neq"; *)
        Unsat
      end
      else
      begin
        (* print_endline "assert_eq: merging v1 into v2"; *)
        v1#merge_into v2
      end
    
    method assert_terms_eq t1 t2 =
      self#assert_eq (self#eval_term t1) (self#eval_term t2)
      
    method assert_terms_neq t1 t2 =
      self#assert_neq (self#eval_term t1) (self#eval_term t2)
  end

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

let _ =
  let ctxt = ref (create_context()) in
  let eval s = !ctxt#eval_term (parse_term s) in
  let reset() = ctxt := create_context() in
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
  assert (assert_neq "x" "y" = Unsat)