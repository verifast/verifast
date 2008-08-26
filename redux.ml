open Proverapi

let rec try_assoc key al =
  match al with
    [] -> None
  | (k, v)::al -> if k = key then Some v else try_assoc key al

let flatmap f xs = List.concat (List.map f xs)

class symbol (kind: symbol_kind) (name: string) =
  object (self)
    method kind = kind
    method name = name
    val mutable node: termnode option = None (* Used only for nullary symbols. Assumes this symbol is used with one context only. *)
    method node = node
    method set_node n = node <- Some n
    val mutable fpclauses: (termnode list -> termnode list -> termnode) array option = None
    method fpclauses = fpclauses
    method set_fpclauses cs = fpclauses <- cs
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
      value#add_child (self :> termnode);
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
      | Uninterp -> ()
    end
    method set_value v =
      self#push;
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
            let t = clause (List.map (fun v -> v#initial_child) children) (List.map (fun v -> v#initial_child) vs) in
            (* print_endline ("Assumed by reduction: " ^ self#pprint ^ " == " ^ v#initial_child#pprint); *)
            ctxt#assert_eq t#value value
          | _ -> assert false
          end
        | _ -> assert false
      end
      else
        Unknown
    method pprint =
      if initial_children = [] then symbol#name else
        symbol#name ^ "(" ^ String.concat ", " (List.map (fun v -> v#pprint) initial_children) ^ ")"

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
    method set_initial_child t = initial_child <- Some t
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
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable popactionlist: (unit -> unit) list = []
    val mutable redexes = []  (* TODO: Do we need to push this? *)
    
    method pushdepth = pushdepth
    method push =
      assert (redexes = []);
      popstack <- (pushdepth, popactionlist)::popstack;
      pushdepth <- pushdepth + 1;
      popactionlist <- []
    
    method register_popaction action =
      popactionlist <- action::popactionlist

    method pop =
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
      
    method alloc_symbol kind name = new symbol kind name
    
    method set_fpclauses (s: symbol) cs = s#set_fpclauses cs

    method value_eq (t1: termnode) (t2: termnode) = t1#value = t2#value
    
    method value_neq (t1: termnode) (t2: termnode) = t1#value#neq t2#value

    method get_termnode s (ts: termnode list) = self#get_node s (List.map (fun t -> t#value) ts)
    
    method pprint (t: termnode): string = t#pprint
    
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
    
    method assert_eq_and_reduce_terms (t1: termnode) (t2: termnode) = self#assert_eq_and_reduce t1#value t2#value
    
    method assert_neq_and_reduce v1 v2 =
      self#do_and_reduce (fun () -> self#assert_neq v1 v2)
      
    method assert_neq_and_reduce_terms (t1: termnode) (t2: termnode) = self#assert_neq_and_reduce t1#value t2#value

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
