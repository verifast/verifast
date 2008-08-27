open Proverapi

let rec try_assoc key al =
  match al with
    [] -> None
  | (k, v)::al -> if k = key then Some v else try_assoc key al

let flatmap f xs = List.concat (List.map f xs)

type 'termnode term =
  TermNode of 'termnode
| Eq of 'termnode * 'termnode
| Not of 'termnode term

class symbol (kind: symbol_kind) (name: string) =
  object (self)
    method kind = kind
    method name = name
    val mutable node: termnode option = None (* Used only for nullary symbols. Assumes this symbol is used with one context only. *)
    method node = node
    method set_node n = node <- Some n
    val mutable fpclauses: (termnode term list -> termnode term list -> termnode term) array option = None
    method fpclauses = fpclauses
    method set_fpclauses cs =
      let a = Array.make (List.length cs) (fun _ _ -> assert false) in
      List.iter
        (fun (c, f) ->
           let k = match c#kind with Ctor k -> k | _ -> assert false in
           a.(k) <- f
        )
        cs;
      fpclauses <- Some a
  end
and termnode ctxt s initial_children =
  object (self)
    val context = ctxt
    val symbol: symbol = s
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable children: valuenode list = initial_children
    val mutable value = new valuenode ctxt
    val mutable reduced = false
    method kind = symbol#kind
    method symbol = symbol
    method children = children
    method push =
      if context#pushdepth <> pushdepth then
      begin
        popstack <- (pushdepth, children, value, reduced)::popstack;
        context#register_popaction (fun () -> self#pop);
        pushdepth <- context#pushdepth
      end
    method pop =
      match popstack with
        (pushdepth0, children0, value0, reduced0)::popstack0 ->
        pushdepth <- pushdepth0;
        children <- children0;
        value <- value0;
        reduced <- reduced0;
        popstack <- popstack0
      | [] -> assert false
    method value = value
    method is_ctor = match symbol#kind with Ctor _ -> true | _ -> false
    initializer begin
      let rec iter k (vs: valuenode list) =
        match vs with
          [] -> ()
        | v::vs ->
          v#add_parent ((self :> termnode), k);
          iter (k + 1) vs
      in
      iter 0 initial_children;
      value#set_initial_child (self :> termnode);
      match symbol#kind with
        Ctor j -> value#set_ctorchild (self :> termnode)
      | Fixpoint k ->
        let v = List.nth children k in
        begin
        match v#ctorchild with
          None -> ()
        | Some n -> ctxt#add_redex (self :> termnode)
        end
      | Uninterp ->
        begin
          match symbol#name with
            "==" ->
            begin
              match children with
                [v1; v2] -> if v1 = v2 then ignore (ctxt#assert_eq value ctxt#true_node#value)
            end
          | _ -> ()
        end
    end
    method set_value v =
      self#push;
      (* print_endline (string_of_int (Oo.id self) ^ ".value <- " ^ string_of_int (Oo.id v)); *)
      value <- v
    method set_child k v =
      let rec replace i vs =
        match vs with
          [] -> assert false
        | v0::vs -> if i = k then v::vs else v0::replace (i + 1) vs
      in
      self#push;
      children <- replace 0 children
    method matches s vs =
      symbol = s && children = vs
    method lookup_equivalent_parent_of v =
      v#lookup_parent symbol children
    method reduce =
      if not reduced then
      begin
        self#push;
        reduced <- true;
        match symbol#kind with
          Fixpoint k ->
          let clauses = match symbol#fpclauses with Some clauses -> clauses | None -> assert false in
          let v = List.nth children k in
          begin
          match v#ctorchild with
            Some n ->
            let s = n#symbol in
            let j = match s#kind with Ctor j -> j | _ -> assert false in
            let clause = clauses.(j) in
            let vs = n#children in
            let t = clause (List.map (fun v -> TermNode v#initial_child) children) (List.map (fun v -> TermNode v#initial_child) vs) in
            let tn = ctxt#termnode_of_term t in
            (* print_endline ("Assumed by reduction: " ^ self#pprint ^ " == " ^ tn#pprint); *)
            ctxt#assert_eq tn#value value
          | _ -> assert false
          end
        | _ -> assert false
      end
      else
        Unknown
    method pprint =
      "[" ^ string_of_int (Oo.id self) ^ "=" ^ string_of_int (Oo.id value) ^ "]" ^
      begin
      if initial_children = [] then symbol#name else
        symbol#name ^ "(" ^ String.concat ", " (List.map (fun v -> v#pprint) initial_children) ^ ")"
      end

  end
and valuenode ctxt =
  object (self)
    val context = ctxt
    val mutable initial_child: termnode option = None
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable children: termnode list = []
    val mutable parents: (termnode * int) list = []
    val mutable ctorchild: termnode option = None
    val mutable neqs: valuenode list = []
    method set_initial_child t =
      initial_child <- Some t;
      children <- [t]
    method initial_child = match initial_child with Some n -> n | None -> assert false
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
    method ctorchild_added =
      List.iter (fun (n, k) -> if n#kind = Fixpoint k then ctxt#add_redex n) parents
    method merge_into v =
      (* print_endline ("Merging " ^ string_of_int (Oo.id self) ^ " into " ^ string_of_int (Oo.id v)); *)
      List.iter (fun n -> n#set_value v) children;
      List.iter (fun n -> v#add_child n) children;
      List.iter (fun vneq -> vneq#neq_merging_into (self :> valuenode) v) neqs;
      List.iter (fun (n, k) -> n#set_child k v) parents;
      (* At this point self is referenced nowhere. *)
      (* It is possible that some of the nodes in 'parents' are now equivalent with nodes in v.parents. *)
      begin
        match (ctorchild, v#ctorchild) with
          (None, Some _) ->
          self#ctorchild_added
        | (Some _, None) ->
          v#ctorchild_added
        | _ -> ()
      end;
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
    method pprint =
      match initial_child with
        Some n -> n#pprint
      | None -> assert false
  end
and context =
  object (self)
    val eq_symbol = new symbol Uninterp "=="
    val not_symbol = new symbol Uninterp "!"
    val mutable intlitnodes: (int * termnode) list = []
    val mutable ttrue = None
    val mutable tfalse = None
    val mutable simplex = new Simplex.simplex
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable popactionlist: (unit -> unit) list = []
    val mutable simplex_eqs = []
    val mutable simplex_consts = []
    val mutable redexes = []
    
    initializer
      simplex#register_listeners (fun u1 u2 -> simplex_eqs <- (u1, u2)::simplex_eqs) (fun u n -> simplex_consts <- (u, n)::simplex_consts);
      ttrue <- Some (self#mk_app (self#mk_symbol "true" [] () (Ctor 0)) []);
      tfalse <- Some (self#mk_app (self#mk_symbol "false" [] () (Ctor 1)) [])
    
    method get_intlitnode n =
      match try_assoc n intlitnodes with
        None ->
        (* print_endline ("Creating intlit node for " ^ string_of_int n); *)
        let node = self#get_node (new symbol (Ctor n) (string_of_int n)) [] in
        intlitnodes <- (n, node)::intlitnodes;
        node
      | Some n -> n
      
    method true_node = let Some (TermNode ttrue) = ttrue in ttrue
    method false_node = let Some (TermNode tfalse) = tfalse in tfalse
    
    method type_bool = ()
    method type_int = ()
    method type_inductive = ()
    method mk_true: termnode term = let Some ttrue = ttrue in ttrue
    method mk_false: termnode term = let Some tfalse = tfalse in tfalse
    method mk_and (t1: termnode term) (t2: termnode term): termnode term = assert false
    method mk_or (t1: termnode term) (t2: termnode term): termnode term = assert false
    method mk_not (t: termnode term): termnode term = Not t
    method mk_ifthenelse (t1: termnode term) (t2: termnode term) (t3: termnode term): termnode term = assert false
    method mk_eq (t1: termnode term) (t2: termnode term): termnode term = Eq (self#termnode_of_term t1, self#termnode_of_term t2)
    method mk_intlit (n: int): termnode term = TermNode (self#get_intlitnode n)
    method mk_add (t1: termnode term) (t2: termnode term): termnode term = assert false
    method mk_sub (t1: termnode term) (t2: termnode term): termnode term = assert false
    method mk_lt (t1: termnode term) (t2: termnode term): termnode term = assert false
    method mk_le (t1: termnode term) (t2: termnode term): termnode term = assert false
    method assume (t: termnode term): assume_result =
      (* print_endline ("Assume: " ^ self#pprint t); *)
      let rec assume_true t =
        match t with
          TermNode t -> assert false
        | Eq (t1, t2) -> self#assume_eq t1 t2
        | Not t -> assume_false t
      and assume_false t =
        match t with
          TermNode t -> assert false
        | Eq (t1, t2) -> self#assume_neq t1 t2
        | Not t -> assume_true t
      in
      assume_true t
    method query (t: termnode term): bool =
      (* print_endline ("Query: " ^ self#pprint t); *)
      let rec query_true t =
        match t with
          TermNode t -> assert false
        | Eq (t1, t2) -> self#query_eq t1 t2
        | Not t -> query_false t
      and query_false t =
        match t with
          TermNode t -> assert false
        | Eq (t1, t2) -> self#query_neq t1 t2
        | Not t -> query_true t
      in
      query_true t
    
    method termnode_of_term t =
      match t with
        TermNode t -> t
      | _ -> assert false

    method pushdepth = pushdepth
    method push =
      (* print_endline "Push"; *)
      self#reduce;
      assert (redexes = []);
      popstack <- (pushdepth, popactionlist)::popstack;
      pushdepth <- pushdepth + 1;
      popactionlist <- []
    
    method register_popaction action =
      popactionlist <- action::popactionlist

    method pop =
      (* print_endline "Pop"; *)
      redexes <- [];
      match popstack with
        (pushdepth0, popactionlist0)::popstack0 ->
        List.iter (fun action -> action()) popactionlist;
        pushdepth <- pushdepth0;
        popactionlist <- popactionlist0;
        popstack <- popstack0
      | [] -> failwith "Popstack is empty"

    method add_redex n =
      redexes <- n::redexes
      
    method mk_symbol name (domain: unit list) (range: unit) kind =
      let s = new symbol kind name in if List.length domain = 0 then ignore (self#mk_app s []); s
    
    method set_fpclauses (s: symbol) (k: int) (cs: (symbol * (termnode term list -> termnode term list -> termnode term)) list) =
      s#set_fpclauses cs

    method query_eq (t1: termnode) (t2: termnode) = self#reduce; t1#value = t2#value
    
    method query_neq (t1: termnode) (t2: termnode) =
      self#push;
      let result = self#assume_eq t1 t2 in
      self#pop;
      match result with
        Unsat -> true
      | Unknown -> false

    method mk_app (s: symbol) (ts: termnode term list): termnode term =
      TermNode (self#get_node s (List.map (fun t -> (self#termnode_of_term t)#value) ts))
    
    method pprint (t: termnode term): string =
      match t with
        TermNode t -> t#pprint
      | Eq (t1, t2) -> t1#pprint ^ " = " ^ t2#pprint
      | Not t -> "!(" ^ self#pprint t ^ ")"
    
    method get_node s vs =
      match vs with
        [] ->
        begin
        match s#node with
          None ->
          let node = new termnode (self :> context) s vs in
          s#set_node node;
          node
        | Some n -> n
        end
      | v::_ ->
        begin
        match v#lookup_parent s vs with
          None ->
          let node = new termnode (self :> context) s vs in
          node
        | Some n -> n
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

    method assert_eq_and_reduce v1 v2 =
      self#do_and_reduce (fun () -> self#assert_eq v1 v2)
    
    method assume_eq (t1: termnode) (t2: termnode) = self#reduce; self#assert_eq_and_reduce t1#value t2#value
    
    method assert_neq_and_reduce v1 v2 =
      self#do_and_reduce (fun () -> self#assert_neq v1 v2)
      
    method assume_neq (t1: termnode) (t2: termnode) = self#reduce; self#assert_neq_and_reduce t1#value t2#value

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
    
    method reduce0 =
      let rec iter () =
        match redexes with
          [] -> Unknown
        | n::redexes0 ->
          redexes <- redexes0;
          match n#reduce with
            Unsat -> Unsat
          | Unknown -> iter ()
      in
      iter()
    
    method reduce =
      assert (self#reduce0 = Unknown)

    method do_and_reduce action =
      match action() with
        Unsat -> Unsat
      | Unknown -> self#reduce0
  end
