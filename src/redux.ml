open Num
open Big_int
open Proverapi

let print_endline_disabled msg = ()

let rec try_assoc key al =
  match al with
    [] -> None
  | (k, v)::al -> if k = key then Some v else try_assoc key al

let flatmap f xs = List.concat (List.map f xs)

type ('symbol, 'termnode) term =
  TermNode of 'termnode
| Eq of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Le of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Lt of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Not of ('symbol, 'termnode) term
| And of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Or of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Add of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Sub of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| IntLit of int
| IntLitOfString of string
| RealLit of Num.num
| App of 'symbol * ('symbol, 'termnode) term list
| IfThenElse of ('symbol, 'termnode) term * ('symbol, 'termnode) term * ('symbol, 'termnode) term
| RealLe of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| RealLt of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| RealMul of ('symbol, 'termnode) term * ('symbol, 'termnode) term

module NumMap = Map.Make (struct type t = num let compare a b = compare_num a b end)

let zero_num = num_of_int 0
let unit_num = num_of_int 1
let neg_unit_num = num_of_int (-1)

let neg_unit_big_int = minus_big_int unit_big_int

class symbol (kind: symbol_kind) (name: string) =
  object (self)
    method kind = kind
    method name = name
    val mutable node: termnode option = None (* Used only for nullary symbols. Assumes this symbol is used with one context only. *)
    method node = node
    method set_node n = node <- Some n
    val mutable fpclauses: ((symbol, termnode) term list -> (symbol, termnode) term list -> (symbol, termnode) term) array option = None
    method fpclauses = fpclauses
    method set_fpclauses cs =
      let a = Array.make (List.length cs) (fun _ _ -> assert false) in
      List.iter
        (fun (c, f) ->
           let k = match c#kind with Ctor (CtorByOrdinal k) -> k | _ -> assert false in
           a.(k) <- f
        )
        cs;
      fpclauses <- Some a
  end
and termnode (ctxt: context) s initial_children =
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
        Ctor j -> ()
      | Fixpoint k ->
        let v = List.nth children k in
        begin
        match v#ctorchild with
          None -> ()
        | Some n -> ctxt#add_redex (fun () -> self#reduce)
        end
      | Uninterp ->
        print_endline_disabled ("Created uninterpreted termnode " ^ symbol#name);
        begin
          match (symbol#name, children) with
            ("==", [v1; v2]) ->
            begin
                if v1 = v2 then
                begin
                  print_endline_disabled ("Equality termnode: operands are equal");
                  ignore (ctxt#assert_eq value ctxt#true_node#value)
                end
                else if v1#neq v2 then
                begin
                  print_endline_disabled ("Equality termnode: operands are distinct");
                  ignore (ctxt#assert_eq value ctxt#false_node#value)
                end
                else
                  let pprint v =
                    v#initial_child#pprint ^ " (ctorchild: " ^
                    begin
                    match v#ctorchild with
                      None -> "none"
                    | Some t -> t#pprint
                    end
                    ^ ")"
                  in
                  print_endline_disabled ("Equality termnode: undecided: " ^ pprint v1 ^ ", " ^ pprint v2);
            end
          | ("||", [v1; v2]) ->
            begin
              if v1 = ctxt#true_node#value then
                ignore (ctxt#assert_eq value ctxt#true_node#value)
              else if v1 = ctxt#false_node#value then
                ignore (ctxt#assert_eq value v2)
              else if v2 = ctxt#true_node#value then
                ignore (ctxt#assert_eq value ctxt#true_node#value)
              else if v2 = ctxt#false_node#value then
                ignore (ctxt#assert_eq value v1)
            end
          | ("&&", [v1; v2]) ->
            begin
              if v1 = ctxt#true_node#value then
                ignore (ctxt#assert_eq value v2)
              else if v1 = ctxt#false_node#value then
                ignore (ctxt#assert_eq value ctxt#false_node#value)
              else if v2 = ctxt#true_node#value then
                ignore (ctxt#assert_eq value v1)
              else if v2 = ctxt#false_node#value then
                ignore (ctxt#assert_eq value ctxt#false_node#value)
            end
          | _ -> ()
        end
    end
    method set_value v =
      self#push;
      (* print_endline_disabled (string_of_int (Oo.id self) ^ ".value <- " ^ string_of_int (Oo.id v)); *)
      value <- v
    method set_child k v =
      let rec replace i vs =
        match vs with
          [] -> assert false
        | v0::vs -> if i = k then v::vs else v0::replace (i + 1) vs
      in
      self#push;
      children <- replace 0 children;
      if symbol#kind = Uninterp && symbol#name = "==" then
        match children with [v1; v2] when v1 = v2 -> ctxt#add_redex (fun () -> ctxt#assert_eq value ctxt#true_node#value) | _ -> ()
    method child_ctorchild_added k =
      if symbol#kind = Fixpoint k then
        ctxt#add_redex (fun () -> self#reduce)
      else if symbol#kind = Uninterp then
        match (symbol#name, children, k) with
          ("==", [v1; v2], _) ->
          begin
          match (v1#ctorchild, v2#ctorchild) with
            (Some t1, Some t2) when t1#symbol <> t2#symbol -> ctxt#add_redex (fun () -> ctxt#assert_eq value ctxt#false_node#value)
          | _ -> ()
          end
        | ("&&", [v1; v2], 0) ->
          let newNode = if v1#ctorchild = Some ctxt#true_node then v2#initial_child else ctxt#false_node in
          ctxt#add_redex (fun () -> ctxt#assert_eq value newNode#value)
        | ("&&", [v1; v2], 1) ->
          let newNode = if v2#ctorchild = Some ctxt#true_node then v1#initial_child else ctxt#false_node in
          ctxt#add_redex (fun () -> ctxt#assert_eq value newNode#value)
        | ("||", [v1; v2], 0) ->
          let newNode = if v1#ctorchild = Some ctxt#true_node then ctxt#true_node else v2#initial_child in
          ctxt#add_redex (fun () -> ctxt#assert_eq value newNode#value)
        | ("||", [v1; v2], 1) ->
          let newNode = if v2#ctorchild = Some ctxt#true_node then ctxt#true_node else v1#initial_child in
          ctxt#add_redex (fun () -> ctxt#assert_eq value newNode#value)
        | _ -> ()
    method parent_ctorchild_added =
      match (symbol#name, children) with
        ("==", [v1; v2]) ->
          begin
            match value#ctorchild with
              Some t when t = ctxt#true_node -> ctxt#add_redex (fun () -> ctxt#assert_eq v1#initial_child#value v2#initial_child#value)
            | Some t when t = ctxt#false_node -> ctxt#add_redex (fun () -> ctxt#assert_neq v1#initial_child#value v2#initial_child#value)
          end
      | ("<=", [v1; v2]) ->
        begin
          if value = ctxt#true_node#value then
            ctxt#add_redex (fun () -> ctxt#assert_le v1#initial_child zero_num v2#initial_child)
          else
            ctxt#add_redex (fun () -> ctxt#assert_le v2#initial_child unit_num v1#initial_child)
        end
      | ("<", [v1; v2]) ->
        begin
          if value = ctxt#true_node#value then
            ctxt#add_redex (fun () -> ctxt#assert_le v1#initial_child unit_num v2#initial_child)
          else
            ctxt#add_redex (fun () -> ctxt#assert_le v2#initial_child zero_num v1#initial_child)
        end
      | ("&&", [v1; v2]) ->
        if value = ctxt#true_node#value then
        begin
          ctxt#add_redex (fun () -> ctxt#assert_eq v1#initial_child#value ctxt#true_node#value);
          ctxt#add_redex (fun () -> ctxt#assert_eq v2#initial_child#value ctxt#true_node#value)
        end
      | ("||", [v1; v2]) ->
        if value = ctxt#false_node#value then
        begin
          ctxt#add_redex (fun () -> ctxt#assert_eq v1#initial_child#value ctxt#false_node#value);
          ctxt#add_redex (fun () -> ctxt#assert_eq v2#initial_child#value ctxt#false_node#value)
        end
      | _ -> ()
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
            let j = match s#kind with Ctor (CtorByOrdinal j) -> j | _ -> assert false in
            let clause = clauses.(j) in
            let vs = n#children in
            let t = clause (List.map (fun v -> TermNode v#initial_child) children) (List.map (fun v -> TermNode v#initial_child) vs) in
            print_endline_disabled ("Assumed by reduction: " ^ self#pprint ^ " = " ^ ctxt#pprint t);
            let tn = ctxt#termnode_of_term t in
            ctxt#assert_eq tn#value value
          | _ -> assert false
          end
        | _ -> assert false
      end
      else
        Unknown
    method pprint =
      (* "[" ^ string_of_int (Oo.id self) ^ "=" ^ string_of_int (Oo.id value) ^ "]" ^ *)
      begin
      if initial_children = [] then symbol#name else
        symbol#name ^ "(" ^ String.concat ", " (List.map (fun v -> v#pprint) initial_children) ^ ")"
      end
    method toString =
      if children = [] then symbol#name else
        match (symbol#name, children) with
          (("&&"|"||"|"+"|"-"|"=="|"<"|"<="|"</"|"<=/"), [v1; v2]) ->
          "(" ^ v1#representativeString ^ " " ^ symbol#name ^ " " ^ v2#representativeString ^ ")"
        | _ ->
          symbol#name ^ "(" ^ String.concat ", " (List.map (fun v -> v#representativeString) children) ^ ")"
  end
and valuenode (ctxt: context) =
  object (self)
    val context = ctxt
    val mutable initial_child: termnode option = None
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable children: termnode list = []
    val mutable parents: (termnode * int) list = []
    val mutable ctorchild: termnode option = None
    val mutable unknown: termnode Simplex.unknown option = None
    val mutable neqs: valuenode list = []
    (* For diagnostics only *)
    val mutable representative = None
    initializer begin
      ctxt#register_valuenode (self :> valuenode)
    end
    method set_initial_child t =
      initial_child <- Some t;
      begin
        match t#kind with
          Ctor _ -> ctorchild <- Some t
        | _ -> ()
      end;
      children <- [t]
    method initial_child = match initial_child with Some n -> n | None -> assert false
    method push =
      if ctxt#pushdepth <> pushdepth then
      begin
        popstack <- (pushdepth, children, parents, ctorchild, unknown, neqs)::popstack;
        ctxt#register_popaction (fun () -> self#pop);
        pushdepth <- ctxt#pushdepth
      end
    method pop =
      match popstack with
        (pushdepth0, children0, parents0, ctorchild0, unknown0, neqs0)::popstack0 ->
        pushdepth <- pushdepth0;
        children <- children0;
        parents <- parents0;
        ctorchild <- ctorchild0;
        neqs <- neqs0;
        unknown <- unknown0;
        popstack <- popstack0
      | [] -> assert(false)
    method ctorchild = ctorchild
    method unknown = unknown
    method mk_unknown =
      match unknown with
        None ->
        let u = ctxt#simplex#alloc_unknown ("u" ^ string_of_int (Oo.id self)) initial_child in
        self#push;
        unknown <- Some u;
        u
      | Some u -> u
    method add_parent p =
      self#push;
      parents <- p::parents
    method set_ctorchild c =
      self#push;
      ctorchild <- Some c
    method set_unknown u =
      self#push;
      unknown <- Some u
    method add_child c =
      self#push;
      children <- c::children
    method neq v =
      match (ctorchild, v#ctorchild) with
        (Some n1, Some n2) when n1#symbol <> n2#symbol -> true
      | _ -> List.mem v neqs
    method add_neq v =
      self#push;
      neqs <- v::neqs;
      match self#lookup_parent ctxt#eq_symbol [(self :> valuenode); v] with
        Some tn -> ctxt#add_redex (fun () -> ctxt#assert_eq tn#value ctxt#false_node#value)
      | None -> ()
    method neq_merging_into vold vnew =
      self#push;
      neqs <- List.map (fun v0 -> if v0 = vold then vnew else v0) neqs;
      vnew#add_neq (self :> valuenode)
    method lookup_parent s vs =
      let rec iter ns =
        match ns with
          [] -> None
        | (n, _)::ns -> if n#matches s vs then Some n else iter ns
      in
      iter parents
    method ctorchild_added =
      List.iter (fun (n, k) -> n#child_ctorchild_added k) parents;
      List.iter (fun n -> n#parent_ctorchild_added) children
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
        | (Some n, None) ->
          v#set_ctorchild n; assert (n#value = v); v#ctorchild_added (* TODO: Eliminate the redundancy caused by processing the newly acquired parents and children of v! *)
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
              (* print_endline_disabled "Doing a recursive assert_eq!"; *)
              let result = context#assert_eq n#value n'#value in
              (* print_endline_disabled "Returned from recursive assert_eq"; *)
              match result with
                Unsat -> Unsat
              | Unknown -> iter rps
            end
        in
        iter redundant_parents
      in
      let process_ctorchildren () =
        match (ctorchild, v#ctorchild) with
          (None, _) -> process_redundant_parents()
        | (Some n, None) -> process_redundant_parents()
        | (Some n, Some n') ->
          (* print_endline_disabled "Adding injectiveness edges..."; *)
          let rec iter vs =
            match vs with
              [] -> process_redundant_parents()
            | (v, v')::vs ->
              begin
              print_endline_disabled ("Adding injectiveness edge: " ^ v#pprint ^ " = " ^ v'#pprint);
              match context#assert_eq v#initial_child#value v'#initial_child#value with
                Unsat -> Unsat
              | Unknown -> iter vs
              end
          in
          iter (List.combine n#children n'#children)
      in
      begin
        match (unknown, v#unknown) with
          (Some u, None) -> v#set_unknown u; process_ctorchildren()
        | (Some u1, Some u2) ->
          begin
            (* print_endline ("Exporting equality to Simplex: " ^ u1#name ^ " = " ^ u2#name); *)
            match ctxt#simplex#assert_eq zero_num [unit_num, u1; neg_unit_num, u2] with
              Simplex.Unsat -> Unsat
            | Simplex.Sat -> process_ctorchildren()
          end
        | _ -> process_ctorchildren()
      end
    method pprint =
      match initial_child with
        Some n -> n#pprint
      | None -> assert false
    method representative_pair =
      match representative with
        Some (n, s) -> (n, s)
      | None ->
        let newrep =
          match ctorchild with
            Some n when n#children = [] -> n
          | _ ->
            begin
            match List.filter (fun n -> n#children = []) children with
              n::_ -> n
            | _ ->
              begin
              match initial_child with
                Some n -> n
              | None -> assert false
              end
            end
        in
          let pair = (newrep, newrep#toString) in
          representative <- Some pair;
          pair
    method representative = let (n, _) = self#representative_pair in n
    method representativeString = let (_, s) = self#representative_pair in s
    method dump_state =
      if List.tl children <> [] || neqs <> [] then
      begin
        print_endline (self#representativeString);
        List.iter (fun t -> if t <> self#representative then print_endline ("== " ^ t#toString)) children;
        List.iter (fun v -> print_endline ("!= " ^ v#representativeString)) neqs;
        print_newline()
      end
  end
and context =
  object (self)
    val eq_symbol = new symbol Uninterp "=="
    val and_symbol = new symbol Uninterp "&&"
    val or_symbol = new symbol Uninterp "||"
    val not_symbol = new symbol Uninterp "!"
    val add_symbol = new symbol Uninterp "+"
    val sub_symbol = new symbol Uninterp "-"
    val mul_symbol = new symbol Uninterp "*"
    val int_le_symbol = new symbol Uninterp "<="
    val int_lt_symbol = new symbol Uninterp "<"
    val real_le_symbol = new symbol Uninterp "<=/"
    val real_lt_symbol = new symbol Uninterp "</"
    
    val mutable numnodes: termnode NumMap.t = NumMap.empty (* Sorted *)
    val mutable ttrue = None
    val mutable tfalse = None
    val simplex = new Simplex.simplex
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable popactionlist: (unit -> unit) list = []
    val mutable simplex_eqs = []
    val mutable simplex_consts = []
    val mutable redexes = []
    (* For diagnostics only. *)
    val mutable values = []
    
    initializer
      simplex#register_listeners (fun u1 u2 -> simplex_eqs <- (u1, u2)::simplex_eqs) (fun u n -> simplex_consts <- (u, n)::simplex_consts);
      ttrue <- Some (self#get_node (self#mk_symbol "true" [] () (Ctor (CtorByOrdinal 0))) []);
      tfalse <- Some (self#get_node (self#mk_symbol "false" [] () (Ctor (CtorByOrdinal 1))) [])
    
    method simplex = simplex
    method eq_symbol = eq_symbol
    
    method register_valuenode v =
      values <- v::values
    
    method get_numnode n =
      try
        NumMap.find n numnodes
      with
        Not_found ->
        (* print_endline_disabled ("Creating intlit node for " ^ string_of_int n); *)
        let node = self#get_node (new symbol (Ctor (NumberCtor n)) (string_of_num n)) [] in
        numnodes <- NumMap.add n node numnodes;
        node

    method get_ifthenelsenode t1 t2 t3 =
      print_endline_disabled ("Producing ifthenelse termnode");
      let symname = "ifthenelse(" ^ self#pprint t2 ^ ", " ^ self#pprint t3 ^ ")" in
      let s = new symbol (Fixpoint 0) symname in
      s#set_fpclauses [
        (self#true_node#symbol, (fun _ _ -> t2));
        (self#false_node#symbol, (fun _ _ -> t3))
      ];
      new termnode (self :> context) s [(self#termnode_of_term t1)#value]

    method true_node = let Some ttrue = ttrue in ttrue
    method false_node = let Some tfalse = tfalse in tfalse
    
    method type_bool = ()
    method type_int = ()
    method type_real = ()
    method type_inductive = ()
    method mk_boxed_int (t: (symbol, termnode) term) = t
    method mk_unboxed_int (t: (symbol, termnode) term) = t
    method mk_boxed_real (t: (symbol, termnode) term) = t
    method mk_unboxed_real (t: (symbol, termnode) term) = t
    method mk_boxed_bool (t: (symbol, termnode) term) = t
    method mk_unboxed_bool (t: (symbol, termnode) term) = t
    method mk_true: (symbol, termnode) term = let Some ttrue = ttrue in TermNode ttrue
    method mk_false: (symbol, termnode) term = let Some tfalse = tfalse in TermNode tfalse
    method mk_and (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = And (t1, t2)
    method mk_or (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Or (t1, t2)
    method mk_not (t: (symbol, termnode) term): (symbol, termnode) term = Not t
    method mk_ifthenelse (t1: (symbol, termnode) term) (t2: (symbol, termnode) term) (t3: (symbol, termnode) term): (symbol, termnode) term =
      IfThenElse (t1, t2, t3)
    method mk_eq (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Eq (t1, t2)
    method mk_intlit (n: int): (symbol, termnode) term = IntLit n
    method mk_intlit_of_string (s: string): (symbol, termnode) term = IntLitOfString s
    method mk_add (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Add (t1, t2)
    method mk_sub (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Sub (t1, t2)
    method mk_mul (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = failwith "Redux does not yet support integer multiplication."
    method mk_lt (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Lt (t1, t2)
    method mk_le (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Le (t1, t2)
    method mk_reallit (n: int): (symbol, termnode) term = IntLit n
    method mk_reallit_of_num (n: Num.num): (symbol, termnode) term = RealLit n
    method mk_real_add (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Add (t1, t2)
    method mk_real_sub (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Sub (t1, t2)
    method mk_real_mul (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = RealMul (t1, t2)
    method mk_real_lt (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = RealLt (t1, t2)
    method mk_real_le (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = RealLe (t1, t2)
    method assume (t: (symbol, termnode) term): assume_result =
      (* print_endline ("Assume: " ^ self#pprint t); *)
      let rec assume_true t =
        match t with
          TermNode t -> self#assume_eq t self#true_node
        | Eq (t1, t2) -> self#assume_eq (self#termnode_of_term t1) (self#termnode_of_term t2)
        | Le (t1, t2) -> self#assume_le t1 zero_num t2
        | Lt (t1, t2) -> self#assume_le t1 unit_num t2
        | RealLe (t1, t2) -> self#assume_le t1 zero_num t2
        | RealLt (t1, t2) -> self#assume (And (Not (Eq (t1, t2)), (RealLe (t1, t2))))
        | And (t1, t2) ->
          begin
            match self#assume t1 with
              Unsat -> Unsat
            | Unknown -> self#assume t2
          end
        | Not t -> assume_false t
        | t -> self#assume_eq (self#termnode_of_term t) self#true_node
      and assume_false t =
        match t with
          TermNode t -> self#assume_eq t self#false_node
        | Eq (t1, t2) -> self#assume_neq (self#termnode_of_term t1) (self#termnode_of_term t2)
        | Le (t1, t2) -> self#assume_le t2 unit_num t1
        | Lt (t1, t2) -> self#assume_le t2 zero_num t1
        | RealLe (t1, t2) -> assume_true (RealLt (t2, t1))
        | RealLt (t1, t2) -> assume_true (RealLe (t2, t1))
        | Not t -> assume_true t
        | t -> self#assume_eq (self#termnode_of_term t) self#false_node
      in
      assume_true t
    method query (t: (symbol, termnode) term): bool =
      (* print_endline ("Query: " ^ self#pprint t); *)
      let rec query_true t =
        match t with
          TermNode t -> self#query_eq t self#true_node
        | Eq (t1, t2) -> self#query_eq (self#termnode_of_term t1) (self#termnode_of_term t2)
        | Le (t1, t2) -> self#query_le t1 zero_num t2
        | Lt (t1, t2) -> self#query_le t1 unit_num t2
        | RealLe (t1, t2) -> self#as_query (fun () -> self#assume (Not t))
        | RealLt (t1, t2) -> self#as_query (fun () -> self#assume (Not t))
        | Not t -> query_false t
        | t -> self#query_eq (self#termnode_of_term t) self#true_node
      and query_false t =
        match t with
          TermNode t -> assert false
        | Eq (t1, t2) -> self#query_neq (self#termnode_of_term t1) (self#termnode_of_term t2)
        | Le (t1, t2) -> self#query_le t2 unit_num t1
        | Lt (t1, t2) -> self#query_le t2 zero_num t1
        | RealLe (t1, t2) -> self#as_query (fun () -> self#assume t)
        | RealLt (t1, t2) -> self#as_query (fun () -> self#assume t)
        | Not t -> query_true t
        | t -> self#query_eq (self#termnode_of_term t) self#false_node
      in
      query_true t
    
    method get_type (term: (symbol, termnode) term) = ()
    
    method termnode_of_term t =
      let addition sym sign t1 t2 =
        let v1 = (self#termnode_of_term t1)#value in
        let v2 = (self#termnode_of_term t2)#value in
        let tn = self#get_node sym [v1; v2] in
        let uv1 = v1#mk_unknown in
        let uv2 = v2#mk_unknown in
        let utn = tn#value#mk_unknown in
        print_endline_disabled ("Exporting addition to Simplex: " ^ utn#name ^ " = " ^ uv1#name ^ " + " ^ uv2#name);
        ignore (simplex#assert_eq zero_num [neg_unit_num, utn; unit_num, uv1; num_of_int sign, uv2]);
        tn
      in
      let termnode_of_num n =
        let tn = self#get_numnode n in
        let v = tn#value in
        let u = v#mk_unknown in
        print_endline_disabled ("Exporting constant to Simplex: " ^ u#name ^ " = " ^ string_of_num n);
        ignore (simplex#assert_eq n [neg_unit_num, u]);
        tn
      in
      let real_mul n t =
        if eq_num n unit_num then t else
        let tn = termnode_of_num n in
        let v1 = tn#value in
        let v2 = t#value in
        let tmul = self#get_node mul_symbol [v1; v2] in
        let uv2 = v2#mk_unknown in
        let utmul = tmul#value#mk_unknown in
        ignore (simplex#assert_eq zero_num [neg_unit_num, utmul; n, uv2]);
        tmul
      in
      let get_node s ts = self#get_node s (List.map (fun t -> (self#termnode_of_term t)#value) ts) in
      match t with
        TermNode t -> t
      | Add (IntLit 0, t2) -> self#termnode_of_term t2
      | Add (t1, IntLit 0) -> self#termnode_of_term t1
      | Add (t1, t2) -> addition add_symbol 1 t1 t2
      | Sub (t1, t2) -> addition sub_symbol (-1) t1 t2
      | IntLit n -> termnode_of_num (num_of_int n)
      | RealLit n -> termnode_of_num n
      | IntLitOfString s -> termnode_of_num (num_of_string s)
      | App (s, ts) -> get_node s ts
      | IfThenElse (t1, t2, t3) -> self#get_ifthenelsenode t1 t2 t3
      | Eq (t1, t2) -> get_node eq_symbol [t1; t2]
      | Not t -> self#termnode_of_term (Eq (t, self#mk_false))
      | And (t1, t2) -> get_node and_symbol [t1; t2]
      | Or (t1, t2) -> get_node or_symbol [t1; t2]
      | Le (t1, t2) -> get_node int_le_symbol [t1; t2]
      | Lt (t1, t2) -> get_node int_lt_symbol [t1; t2]
      | RealLe (t1, t2) -> get_node real_le_symbol [t1; t2]
      | RealLt (t1, t2) -> get_node real_lt_symbol [t1; t2]
      | RealMul (t1, t2) ->
        let rec iter n t =
          match t with
            RealMul (RealLit n1, t) -> iter (mult_num n1 n) t
          | RealMul (t, RealLit n2) -> iter (mult_num n2 n) t
          | RealLit n0 -> termnode_of_num (mult_num n0 n)
          | RealMul (t1, t2) -> real_mul n (get_node mul_symbol [t1; t2])
          | t -> real_mul n (self#termnode_of_term t)
        in
        iter unit_num t
      | _ -> failwith ("Redux does not yet support this term: " ^ self#pprint t)

    method pushdepth = pushdepth
    method push =
      (* print_endline_disabled "Push"; *)
      print_endline_disabled "Push";
      self#reduce;
      assert (redexes = []);
      assert (simplex_eqs = []);
      assert (simplex_consts = []);
      popstack <- (pushdepth, popactionlist, values)::popstack;
      pushdepth <- pushdepth + 1;
      popactionlist <- [];
      simplex#push
    
    method register_popaction action =
      popactionlist <- action::popactionlist

    method pop =
      (* print_endline_disabled "Pop"; *)
      print_endline_disabled "Pop";
      redexes <- [];
      simplex_eqs <- [];
      simplex_consts <- [];
      simplex#pop;
      match popstack with
        (pushdepth0, popactionlist0, values0)::popstack0 ->
        List.iter (fun action -> action()) popactionlist;
        pushdepth <- pushdepth0;
        popactionlist <- popactionlist0;
        values <- values0;
        popstack <- popstack0
      | [] -> failwith "Popstack is empty"

    method add_redex n =
      redexes <- n::redexes
      
    method mk_symbol name (domain: unit list) (range: unit) kind =
      let s = new symbol kind name in if List.length domain = 0 then ignore (self#get_node s []); s
    
    method set_fpclauses (s: symbol) (k: int) (cs: (symbol * ((symbol, termnode) term list -> (symbol, termnode) term list -> (symbol, termnode) term)) list) =
      s#set_fpclauses cs

    method query_eq (t1: termnode) (t2: termnode) =
      self#reduce;
      let result = t1#value = t2#value in
      print_endline_disabled ("Equality query: " ^ t1#pprint ^ " = " ^ t2#pprint ^ ": " ^ (if result then "true" else "false"));
      if not result then self#dump_state;
      result
    
    method as_query f =
      self#reduce;
      self#push;
      let result = f() in
      if result = Unknown then self#dump_state;
      self#pop;
      match result with
        Unsat -> true
      | Unknown -> false
    
    method query_neq (t1: termnode) (t2: termnode) =
      self#as_query (fun _ -> self#assume_eq t1 t2)

    method query_le t1 offset t2 =
      self#as_query (fun _ -> self#assume_le t2 (sub_num unit_num offset) t1)
    
    method mk_app (s: symbol) (ts: (symbol, termnode) term list): (symbol, termnode) term = App (s, ts)
    
    method pprint (t: (symbol, termnode) term): string =
      match t with
        TermNode t -> t#pprint
      | Eq (t1, t2) -> self#pprint t1 ^ " = " ^ self#pprint t2
      | Le (t1, t2) -> self#pprint t1 ^ " <= " ^ self#pprint t2
      | Lt (t1, t2) -> self#pprint t1 ^ " < " ^ self#pprint t2
      | RealLe (t1, t2) -> self#pprint t1 ^ " </ " ^ self#pprint t2
      | RealLt (t1, t2) -> self#pprint t1 ^ " <=/ " ^ self#pprint t2
      | And (t1, t2) -> self#pprint t1 ^ " && " ^ self#pprint t2
      | Or (t1, t2) -> self#pprint t1 ^ " || " ^ self#pprint t2
      | Not t -> "!(" ^ self#pprint t ^ ")"
      | Add (t1, t2) -> "(" ^ self#pprint t1 ^ " + " ^ self#pprint t2 ^ ")"
      | Sub (t1, t2) -> "(" ^ self#pprint t1 ^ " - " ^ self#pprint t2 ^ ")"
      | App (s, ts) -> s#name ^ (if ts = [] then "" else "(" ^ String.concat ", " (List.map (fun t -> self#pprint t) ts) ^ ")")
      | IntLit n -> string_of_int n
      | IntLitOfString s -> "#\"" ^ s ^ "\""
      | RealLit n -> Num.string_of_num n
      | RealMul (t1, t2) -> Printf.sprintf "(%s * %s)" (self#pprint t1) (self#pprint t2)
      | IfThenElse (t1, t2, t3) -> "(" ^ self#pprint t1 ^ " ? " ^ self#pprint t2 ^ " : " ^ self#pprint t3 ^ ")"
    
    method get_node s vs =
      match vs with
        [] ->
        begin
        match s#node with
          None ->
          print_endline_disabled ("Creating node for nullary symbol " ^ s#name);
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
      else if v1 = self#true_node#value then
        self#assert_eq v2 self#false_node#value
      else if v1 = self#false_node#value then
        self#assert_eq v2 self#true_node#value
      else if v2 = self#true_node#value then
        self#assert_eq v1 self#false_node#value
      else if v2 = self#false_node#value then
        self#assert_eq v1 self#true_node#value
      else
      begin
        v1#add_neq v2;
        v2#add_neq v1;
        Unknown
      end

    method assert_eq_and_reduce v1 v2 =
      self#do_and_reduce (fun () -> self#assert_eq v1 v2)
    
    method assume_eq (t1: termnode) (t2: termnode) = self#reduce; self#assert_eq_and_reduce t1#value t2#value
    
    method assert_le t1 offset t2 =
      let u1 = t1#value#mk_unknown in
      let u2 = t2#value#mk_unknown in
      match simplex#assert_ge (minus_num offset) [neg_unit_num, u1; unit_num, u2] with
        Simplex.Unsat -> Unsat
      | Simplex.Sat -> Unknown

    method assume_le t1 offset t2 =   (* t1 + offset <= t2 *)
      self#reduce;
      self#do_and_reduce (fun () ->
        self#assert_le (self#termnode_of_term t1) offset (self#termnode_of_term t2)
      )
    
    method assert_neq_and_reduce v1 v2 =
      self#do_and_reduce (fun () -> self#assert_neq v1 v2)
      
    method assume_neq (t1: termnode) (t2: termnode) = self#reduce; self#assert_neq_and_reduce t1#value t2#value

    method assert_eq v1 v2 =
      if v1 = v2 then
      begin
        (* print_endline_disabled "assert_eq: values already the same"; *)
        Unknown
      end
      else if v1#neq v2 then
      begin
        Unsat
      end
      else
      begin
        (* print_endline_disabled "assert_eq: merging v1 into v2"; *)
        v1#merge_into v2
      end
    
    method reduce0 =
      let rec iter () =
        match simplex_eqs with
          [] ->
          begin
            match simplex_consts with
              [] ->
              begin
                match redexes with
                  [] -> Unknown
                | f::redexes0 ->
                  redexes <- redexes0;
                  match f() with
                    Unsat -> Unsat
                  | Unknown -> iter ()
              end
            | (u, c)::consts ->
              simplex_consts <- consts;
              let Some tn = u#tag in
              print_endline_disabled ("Importing constant from Simplex: " ^ tn#pprint ^ "(" ^ u#name ^ ") = " ^ string_of_num c);
              match self#assert_eq tn#value (self#get_numnode c)#value with
                Unsat -> Unsat
              | Unknown -> iter()
          end
        | (u1, u2)::eqs ->
          simplex_eqs <- eqs;
          let Some tn1 = u1#tag in
          let Some tn2 = u2#tag in
          print_endline_disabled ("Importing equality from Simplex: " ^ tn1#pprint ^ "(" ^ u1#name ^ ") = " ^ tn2#pprint ^ "(" ^ u2#name ^ ")");
          match self#assert_eq tn1#value tn2#value with
            Unsat -> Unsat
          | Unknown -> iter()
      in
      iter()
    
    method reduce =
      assert (self#reduce0 = Unknown)

    method do_and_reduce action =
      match action() with
        Unsat -> Unsat
      | Unknown -> self#reduce0
    
    method dump_state =
      (* print_endline ("==== Redux query failed: State report ====");
      List.iter (fun v -> if v#initial_child#value = v then (v#dump_state)) values; *)
      ()
  end
