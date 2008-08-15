let rec try_assoc key al =
  match al with
    [] -> None
  | (k, v)::al -> if k = key then Some v else try_assoc key al

let flatmap f xs = List.concat (List.map f xs)

type term = Term of string * term list

type assert_result = Unknown | Unsat

class node ctxt s vs v =
  object (self)
    val context = ctxt
    val symbol = s
    val mutable children: value list = vs
    val mutable value = v
    method value = value
    initializer begin
      let rec iter k (vs: value list) =
        match vs with
          [] -> ()
        | v::vs ->
          v#add_parent ((self :> node), k);
          iter (k + 1) vs
      in
      iter 0 vs;
      value#add_child (self :> node)
    end
    method set_value v =
      value <- v
    method set_child k v =
      let rec replace i vs =
        match vs with
          [] -> []
        | v0::vs -> if i = k then v::vs else v0::replace (i + 1) vs
      in
      children <- replace k children
    method matches s vs =
      symbol = s && children = vs
    method lookup_equivalent_parent_of v =
      v#lookup_parent symbol children
  end
and value =
  object
    val mutable children: node list = []
    val mutable parents: (node * int) list = []
    val mutable neqs: value list = []
    method add_parent p =
      parents <- p::parents
    method add_child c =
      children <- c::children
    method neq v =
      List.mem_assoc v neqs
    method add_neq v =
      neqs <- v::neqs
    method neq_merging_into vold vnew =
      neqs <- List.map (fun v0 -> if v0 = vold then vnew else vold) neqs;
      vnew#add_neq (self :> value)
    method lookup_parent s vs =
      let rec iter ns =
        match ns with
          [] -> None
        | n::ns -> if n#matches s vs then Some n else iter ns
      in
      iter parents
    method merge_into v =
      List.iter (fun n -> n#set_parent v) children;
      List.iter (fun n -> v#add_child n) children;
      List.iter (fun vneq -> vneq#neq_merging_into (self :> value) v) neqs;
      List.iter (fun (n, k) -> n#set_child k v) parents;
      (* At this point self is referenced nowhere. *)
      (* It is possible that some of the nodes in 'parents' are now equivalent with nodes in v.parents. *)
      let redundant_parents =
        flatmap
          (fun (n, k) ->
             match n#lookup_equivalent_parent_of v with
               None ->
               v#add_parent (n, k);
               []
             | Some n' ->
               [(n, n')]
          )
          parents
      in
      let rec iter rps =
        match rps with
          [] -> Unknown
        | (n, n')::rps ->
          begin
            match ctxt#assert_eq n#value n'#value with
              Unsat -> Unsat
            | Unknown -> iter rps
          end
      in
      iter redundant_parents

  end
and context =
  object (self)
    val mutable leafnodemap: (string * node) list = []
    
    method eval_term t =
      match t with
        Term (s, ts) ->
        begin
        let vs = List.map self#eval_term ts in
        match vs with
          [] ->
          begin
          match try_assoc s nodemap with
            None ->
            let v = new value in
            let node = new node (self :> context) s vs v in
            nodemap <- (s, node)::nodemap;
            v
          | Some n -> n#value
          end
        | v::_ ->
          match v#lookup_parent s vs with
            None ->
            let v = new value in
            let node = new node (self :> context) s vs v in
            v
          | Some n -> n#value
          end
        end
    
    method assert_neq v1 v2 =
      if v1 = v2 then
        Unsat
      else if v1#neq v2 then
        Unknown
      else
        v1#add_neq v2;
        v2#add_neq v1

    method assert_eq v1 v2 =
      if v1 = v2 then
        Unknown
      else if v1#neq v2 then
        Unsat
      else
        v1#merge_into v2
  end

let create_context() = new context

let _ =
  let ctxt = create_context() in
  let v1 = ctxt#eval_term (Term ("tree", [Term ("nil", []); Term ("nil", []); Term ("succ", [Term ("zero", [])])])) in
  let v2 = ctxt#eval_term (Term ("tree", [Term ("nil", []); Term ("nil", []); Term ("succ", [Term ("zero", [])])])) in
  assert (v1 = v2);
  let v3 = ctxt#eval_term (Term ("tree", [Term ("nil", []); Term ("nil", []); Term ("zero", [])])) in
  assert (v3 <> v1)
