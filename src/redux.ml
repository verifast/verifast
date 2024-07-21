open Num
open Big_int
open Simplex
open Proverapi
open Printf

let bool_subtype = InductiveSubtype.alloc ()
let number_subtype = InductiveSubtype.alloc ()
let boxed_bool_subtype = InductiveSubtype.alloc ()

let ctor_kind_subtype = function
  CtorByOrdinal (subtype, k) -> subtype
| NumberCtor _ -> number_subtype

let stopwatch = Stopwatch.create ()

let (|>) x f = f x

let the x = match x with Some x -> x

type assume_result3 = Unsat3 | Unknown3 | Valid3

let printff format = kfprintf (fun _ -> flush stdout) stdout format

let indentation = ref ""
let indentStack = ref []

let indent () = indentStack := !indentation::!indentStack; indentation := "  " ^ !indentation
let unindent () = let h::t = !indentStack in indentation := h; indentStack := t

let trace format = printf "%10.6fs: %s" (Perf.time ()) !indentation; kfprintf (fun _ -> print_newline ()) stdout format

let trace_entering format =
  ksprintf begin fun msg ->
    trace "Entering %s" msg;
    indent ()
  end format

let trace_exiting format =
  ksprintf begin fun msg ->
    unindent ();
    trace "Exiting %s" msg
  end format

let ($.) f x = f x

let with_timing msg f =
  printff "%s: begin\n" msg;
  let time0 = Sys.time() in
  let result = f() in
  printff "%s: end. Time: %f seconds\n" msg (Sys.time() -. time0);
  result
  
let rec try_assoc key al =
  match al with
    [] -> None
  | (k, v)::al -> if k = key then Some v else try_assoc key al

let flatmap f xs = List.concat (List.map f xs)

type ('symbol, 'termnode) term =
  TermNode of 'termnode
| Iff of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Eq of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Le of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Lt of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Not of ('symbol, 'termnode) term
| And of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Or of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Add of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Sub of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| Mul of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| NumLit of num
| App of 'symbol * ('symbol, 'termnode) term list * 'termnode option
| IfThenElse of ('symbol, 'termnode) term * ('symbol, 'termnode) term * ('symbol, 'termnode) term
| RealLe of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| RealLt of ('symbol, 'termnode) term * ('symbol, 'termnode) term
| True
| False
| BoundVar of int
| Implies of ('symbol, 'termnode) term * ('symbol, 'termnode) term

let term_subst bound_env t =
  let rec iter t =
    match t with
      TermNode _ -> t
    | Iff (t1, t2) -> Iff (iter t1, iter t2)
    | Eq (t1, t2) -> Eq (iter t1, iter t2)
    | Le (t1, t2) -> Le (iter t1, iter t2)
    | Lt (t1, t2) -> Lt (iter t1, iter t2)
    | Not t -> Not (iter t)
    | And (t1, t2) -> And (iter t1, iter t2)
    | Or (t1, t2) -> Or (iter t1, iter t2)
    | Add (t1, t2) -> Add (iter t1, iter t2)
    | Sub (t1, t2) -> Sub (iter t1, iter t2)
    | Mul (t1, t2) -> Mul (iter t1, iter t2)
    | NumLit n -> t
    | App (s, args, None) -> App (s, List.map iter args, None)
    | App (s, args, Some _) -> t
    | IfThenElse (t1, t2, t3) -> IfThenElse (iter t1, iter t2, iter t3)
    | RealLe (t1, t2) -> RealLe (iter t1, iter t2)
    | RealLt (t1, t2) -> RealLt (iter t1, iter t2)
    | True -> t
    | False -> t
    | BoundVar i -> TermNode (List.assoc i bound_env)
    | Implies (t1, t2) -> Implies (iter t1, iter t2)
  in
  iter t

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
           let k = match c#kind with Ctor (CtorByOrdinal (_, k)) -> k | _ -> assert false in
           a.(k) <- f
        )
        cs;
      fpclauses <- Some a
    val mutable apply_listeners = []
    method applied term = List.iter (fun listener -> listener term) apply_listeners
    method add_apply_listener ctxt listener =
      let listeners = apply_listeners in
      apply_listeners <- listener::listeners;
      ctxt#register_popaction (fun () -> apply_listeners <- listeners)
    method as_poly = None
  end
and poly_symbol (name: string) (poly: num * (termnode * num) list) =
  object (self)
    inherit symbol Uninterp name
    method! as_poly = Some poly
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
    method to_poly =
      match value#as_number with
        None -> (zero_num, [((self :> termnode), unit_num)])
      | Some n -> (n, [])
    method is_ctor subtype = match symbol#kind with Ctor ck -> subtype = ctor_kind_subtype ck | _ -> false
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
      symbol#applied (self :> termnode);
      match symbol#kind with
        Ctor _ -> ()
      | Fixpoint (subtype, k) ->
        let v = List.nth children k in
        begin
        match v#ctorchild subtype with
          None -> ()
        | Some n -> ctxt#add_redex (fun () -> self#reduce)
        end
      | Uninterp ->
        begin
          match (symbol#name, children) with
            (("=="|"<==>"), [v1; v2]) ->
            begin
                if v1 = v2 then
                begin
                  ignore (ctxt#assert_eq value ctxt#true_node#value)
                end
                else if v1#neq v2 then
                begin
                  ignore (ctxt#assert_eq value ctxt#false_node#value)
                end
                else
                  (*
                  let pprint v =
                    v#initial_child#pprint ^ " (ctorchild: " ^
                    begin
                    match v#ctorchild with
                      None -> "none"
                    | Some t -> t#pprint
                    end
                    ^ ")"
                  in
                  print_endline ("Equality termnode: undecided: " ^ pprint v1 ^ ", " ^ pprint v2);
                  *)
                  ()
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
          | ("*", [v1; v2]) ->
            ctxt#add_redex (fun () -> ctxt#assert_eq value (ctxt#get_mul_node v2#initial_child v1#initial_child)#value);
            let check_v1_child t =
              if not ctxt#creating_termnode_of_poly && t#value#as_number = None then
              match t#symbol#as_poly with
                Some (n, ts) -> ctxt#add_redex begin fun () ->
                  if t#value#as_number = None then begin
                    if ctxt#verbosity > 20 then trace "asserting mul distributivity for %s (poly: %s)" self#pprint (ctxt#pprint_poly (n, ts));
                    let rec evaluate_poly n0 output_ts input_ts =
                      match input_ts with
                        [] -> (n0, output_ts)
                      | (t, n)::input_ts ->
                        match t#value#as_number with
                          Some nt ->
                          evaluate_poly (n0 +/ nt */ n) output_ts input_ts
                        | None ->
                          evaluate_poly n0 ((t, n)::output_ts) input_ts
                    in
                    let (n, ts) = evaluate_poly n [] ts in
                    let poly_times_term n ts tv2 =
                      match tv2#value#as_number with
                        Some v ->
                        if sign_num v = 0 then ctxt#get_numnode zero_num else
                        ctxt#termnode_of_poly (n */ v) (ts |> List.map (fun (t, n) -> (t, n */ v)))
                      | None ->
                        let nv2 =
                          if sign_num n = 0 then [] else [tv2, n]
                        in
                        ctxt#termnode_of_poly zero_num (nv2 @ (ts |> List.map (fun (t, n) -> (ctxt#get_mul_node t tv2, n))))
                    in
                    let result =
                    ctxt#assert_eq value (poly_times_term n ts v2#initial_child)#value
                    in
                    if ctxt#verbosity > 20 then trace "done asserting mul distributivity";
                    result
                  end else
                    Valid3
                end
              | None -> ()
            in
            v1#children |> List.iter check_v1_child;
            () (* v1#add_child_listener check_v1_child *)
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
      children <- replace 0 children;
      if symbol#kind = Uninterp && (symbol#name = "==" || symbol#name = "<==>") then
        match children with [v1; v2] when v1 = v2 -> ctxt#add_redex (fun () -> ctxt#assert_eq value ctxt#true_node#value) | _ -> ()
    method child_ctorchild_added subtype k =
      if symbol#kind = Fixpoint (subtype, k) then
        ctxt#add_redex (fun () -> self#reduce)
      else if symbol#kind = Uninterp then
        match (symbol#name, children, k) with
          (("=="|"<==>"), [v1; v2], _) ->
          begin
          match (v1#ctorchild subtype, v2#ctorchild subtype) with
            (Some t1, Some t2) when t1#symbol <> t2#symbol -> ctxt#add_redex (fun () -> ctxt#assert_eq value ctxt#false_node#value)
          | _ -> ()
          end
        | ("&&", [v1; v2], 0) when subtype = bool_subtype ->
          let newNode = if v1#ctorchild bool_subtype = Some ctxt#true_node then v2#initial_child else ctxt#false_node in
          ctxt#add_redex (fun () -> ctxt#assert_eq value newNode#value)
        | ("&&", [v1; v2], 1) when subtype = bool_subtype ->
          let newNode = if v2#ctorchild bool_subtype = Some ctxt#true_node then v1#initial_child else ctxt#false_node in
          ctxt#add_redex (fun () -> ctxt#assert_eq value newNode#value)
        | ("||", [v1; v2], 0) when subtype = bool_subtype ->
          let newNode = if v1#ctorchild bool_subtype = Some ctxt#true_node then ctxt#true_node else v2#initial_child in
          ctxt#add_redex (fun () -> ctxt#assert_eq value newNode#value)
        | ("||", [v1; v2], 1) when subtype = bool_subtype ->
          let newNode = if v2#ctorchild bool_subtype = Some ctxt#true_node then ctxt#true_node else v1#initial_child in
          ctxt#add_redex (fun () -> ctxt#assert_eq value newNode#value)
        | ("*", [v1; v2], 0) when subtype = number_subtype ->
          let Some n1 = v1#as_number in
          if n1 =/ zero_num then
            ctxt#add_redex (fun () -> ctxt#assert_eq value (ctxt#get_numnode zero_num)#value)
          else
          begin match v2#as_number with
            None ->
            let t2 = v2#initial_child in
            ctxt#add_redex (fun () -> ctxt#simplex_assert_eq zero_num [neg_unit_num, value#mk_unknown; n1, t2#value#mk_unknown])
          | Some n2 ->
            ctxt#add_redex (fun () -> ctxt#assert_eq value (ctxt#get_numnode (n1 */ n2))#value)
          end
        | _ -> ()
    method parent_ctorchild_added subtype =
      match (symbol#name, children) with
        (("=="|"<==>"), [v1; v2]) when subtype = bool_subtype ->
          begin
            if value = ctxt#true_node#value then
              ctxt#add_redex (fun () -> ctxt#assert_eq v1#initial_child#value v2#initial_child#value)
            else
              ctxt#add_redex (fun () -> ctxt#assert_neq v1#initial_child#value v2#initial_child#value);
            if symbol#name = "<==>" then
              if value = ctxt#true_node#value then
                ctxt#add_pending_split (TermNode (v1#initial_child)) (Not (TermNode (v1#initial_child)))
              else
                ctxt#add_pending_split (And (TermNode (v1#initial_child), Not (TermNode (v2#initial_child)))) (And (TermNode (v2#initial_child), Not (TermNode (v1#initial_child))))
          end
      | ("<=", [v1; v2]) when subtype = bool_subtype ->
        begin
          if value = ctxt#true_node#value then
            ctxt#add_redex (fun () -> ctxt#assert_le v1#initial_child zero_num v2#initial_child)
          else
            ctxt#add_redex (fun () -> ctxt#assert_le v2#initial_child unit_num v1#initial_child)
        end
      | ("<", [v1; v2]) when subtype = bool_subtype ->
        begin
          if value = ctxt#true_node#value then
            ctxt#add_redex (fun () -> ctxt#assert_le v1#initial_child unit_num v2#initial_child)
          else
            ctxt#add_redex (fun () -> ctxt#assert_le v2#initial_child zero_num v1#initial_child)
        end
      | ("<=/", [v1; v2]) when subtype = bool_subtype ->
        begin
          if value = ctxt#true_node#value then
            ctxt#add_redex (fun () -> ctxt#assert_le v1#initial_child zero_num v2#initial_child)
          else begin
            ctxt#add_redex (fun () -> ctxt#assert_le v2#initial_child zero_num v1#initial_child);
            ctxt#add_redex (fun () -> ctxt#assert_neq v1#initial_child#value v2#initial_child#value)
          end
        end
      | ("</", [v1; v2]) when subtype = bool_subtype ->
        begin
          if value = ctxt#true_node#value then begin
            ctxt#add_redex (fun () -> ctxt#assert_le v1#initial_child zero_num v2#initial_child);
            ctxt#add_redex (fun () -> ctxt#assert_neq v1#initial_child#value v2#initial_child#value)
          end else
            ctxt#add_redex (fun () -> ctxt#assert_le v2#initial_child zero_num v1#initial_child)
        end
      | ("&&", [v1; v2]) when subtype = bool_subtype ->
        if value = ctxt#true_node#value then
        begin
          ctxt#add_redex (fun () -> ctxt#assert_eq v1#initial_child#value ctxt#true_node#value);
          ctxt#add_redex (fun () -> ctxt#assert_eq v2#initial_child#value ctxt#true_node#value)
        end
        else
        begin
          (* printff "Adding split for negative conjunction...\n"; *)
          ctxt#add_pending_split (Not (TermNode (v1#initial_child))) (Not (TermNode (v2#initial_child)))
        end
      | ("||", [v1; v2]) when subtype = bool_subtype ->
        if value = ctxt#false_node#value then
        begin
          ctxt#add_redex (fun () -> ctxt#assert_eq v1#initial_child#value ctxt#false_node#value);
          ctxt#add_redex (fun () -> ctxt#assert_eq v2#initial_child#value ctxt#false_node#value)
        end
        else
        begin
          (* printff "Adding split for positive disjunction...\n"; *)
          ctxt#add_pending_split (TermNode (v1#initial_child)) (TermNode (v2#initial_child))
        end
      | _ -> ()
    method matches s vs =
      List.mem symbol s && children = vs
    method lookup_equivalent_parent_of v =
      v#lookup_parent [symbol] children
    method reduce =
      if not reduced then
      begin
        self#push;
        reduced <- true;
        match symbol#kind with
          Fixpoint (subtype, k) ->
          let clauses = match symbol#fpclauses with Some clauses -> clauses | None -> assert false in
          let v = List.nth children k in
          begin
          match v#ctorchild subtype with
            Some n ->
            let s = n#symbol in
            let j = match s#kind with Ctor (CtorByOrdinal (_, j)) -> j | _ -> assert false in
            let clause = clauses.(j) in
            let vs = n#children in
            let t = clause (List.map (fun v -> TermNode v#initial_child) children) (List.map (fun v -> TermNode v#initial_child) vs) in
            (* print_endline ("Assumed by reduction: " ^ self#pprint ^ " = " ^ ctxt#pprint t); *)
            let tn = ctxt#termnode_of_term t in
            ctxt#assert_eq tn#value value
          | _ -> assert false
          end
        | _ -> assert false
      end
      else
        Valid3
    method pprint =
      (if (ctxt#verbosity land 1) = 1 then "[" ^ string_of_int (Oo.id self) ^ "=" ^ string_of_int (Oo.id value) ^ "]" else "") ^
      begin
      if initial_children = [] then symbol#name else
        symbol#name ^ "(" ^ String.concat ", " (List.map (fun v -> v#pprint) initial_children) ^ ")"
      end
    method toString =
      if children = [] then symbol#name else
        match (symbol#name, children) with
          (("&&"|"||"|"+"|"-"|"=="|"<==>"|"<"|"<="|"</"|"<=/"), [v1; v2]) ->
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
    val mutable ctorchildren: (InductiveSubtype.t * termnode) list = []
    val mutable unknown: termnode Simplex.unknown option = None
    val mutable neqs: valuenode list = []
    (* For diagnostics only *)
    val mutable representative = None
    val mutable child_listeners = []
    val mutable merge_listeners = []
    initializer begin
      ctxt#register_valuenode (self :> valuenode)
    end
    method merge_merge_listeners listeners =
      self#push;
      merge_listeners <- List.filter (fun listener -> listener ()) (listeners @ merge_listeners)
    method set_initial_child t =
      initial_child <- Some t;
      begin
        match t#kind with
          Ctor ck -> ctorchildren <- [ctor_kind_subtype ck, t]
        | _ -> ()
      end;
      children <- [t]
    method initial_child = match initial_child with Some n -> n | None -> assert false
    method push =
      if ctxt#pushdepth <> pushdepth then
      begin
        popstack <- (pushdepth, children, parents, ctorchildren, unknown, neqs, child_listeners, merge_listeners)::popstack;
        ctxt#register_popaction (fun () -> self#pop);
        pushdepth <- ctxt#pushdepth
      end
    method pop =
      match popstack with
        (pushdepth0, children0, parents0, ctorchildren0, unknown0, neqs0, child_listeners0, merge_listeners0)::popstack0 ->
        pushdepth <- pushdepth0;
        children <- children0;
        parents <- parents0;
        ctorchildren <- ctorchildren0;
        neqs <- neqs0;
        child_listeners <- child_listeners0;
        merge_listeners <- merge_listeners0;
        unknown <- unknown0;
        popstack <- popstack0
      | [] -> assert(false)
    method ctorchildren = ctorchildren
    method ctorchild subtype =
      let rec iter ctorchildren =
        match ctorchildren with
          [] -> None
        | (subtype', n)::ctorchildren ->
          if subtype = subtype' then Some n else
          if subtype < subtype' then None else
          iter ctorchildren
      in
      iter ctorchildren
    method unknown = unknown
    method as_number =
      match self#ctorchild number_subtype with
        None -> None
      | Some n ->
        match n#symbol#kind with
          Ctor (NumberCtor n) -> Some n
        | _ -> None
    method mk_unknown =
      match unknown with
        None ->
        let u = ctxt#simplex#alloc_unknown ("u" ^ string_of_int (Oo.id self)) self#initial_child in
        self#push;
        unknown <- Some u;
        u
      | Some u -> u
    method add_merge_listener listener =
      self#push;
      merge_listeners <- listener::merge_listeners
    method add_child_listener listener =
      self#push;
      child_listeners <- listener::child_listeners
    method add_parent p =
      self#push;
      parents <- p::parents
    method set_ctorchild subtype c =
      self#push;
      let rec insert ctorchildren =
        match ctorchildren with
          [] -> [subtype, c]
        | ((subtype', c') as entry)::ctorchildren' ->
          if InductiveSubtype.lt subtype' subtype then
            entry::insert ctorchildren'
          else
            (subtype, c)::ctorchildren
      in
      ctorchildren <- insert ctorchildren
    method set_unknown u =
      self#push;
      unknown <- Some u
    method add_child c =
      self#push;
      List.iter (fun listener -> listener c) child_listeners;
      children <- c::children
    method neq v =
      let rec iter cn1 cn2 =
        match cn1, cn2 with
          [], _ -> false
        | _, [] -> false
        | (subtype1, n1)::cn1', (subtype2, n2)::cn2' ->
          if subtype1 < subtype2 then
            iter cn1' cn2
          else if subtype1 = subtype2 then
            n1#symbol <> n2#symbol || iter cn1' cn2'
          else
            iter cn1 cn2'
      in
      iter ctorchildren v#ctorchildren || List.mem v neqs
    method add_neq v =
      self#push;
      neqs <- v::neqs;
      match self#lookup_parent [ctxt#eq_symbol; ctxt#iff_symbol] [(self :> valuenode); v] with
        Some tn -> ctxt#add_redex (fun () -> ctxt#assert_eq tn#value ctxt#false_node#value)
      | None -> ()
    method neq_merging_into vold vnew =
      self#push;
      neqs <- List.map (fun v0 -> if v0 = vold then vnew else v0) neqs;
      vnew#add_neq (self :> valuenode)
    method lookup_parent s vs =
      let result =
      let rec iter ns =
        match ns with
          [] -> None
        | (n, _)::ns -> if n#matches s vs then Some n else iter ns
      in
      iter parents
      in
      if ctxt#verbosity > 20 then trace "%d.lookup_parent %s returns %s" (Oo.id self) (String.concat ", " (List.map (fun s -> sprintf "%s(%d)" s#name (Oo.id s)) s)) (match result with None -> "None" | Some v -> v#pprint);
      result
    method parents = parents
    method children = children
    method merge_into fromSimplex v =
      if ctxt#verbosity > 8 then trace "%d.merge_into %d" (Oo.id self) (Oo.id v);
      if (self :> valuenode) = ctxt#true_node#value || (self :> valuenode) = ctxt#false_node#value then v#merge_into fromSimplex (self :> valuenode) else
      let ctorchild_added subtype parents children =
        List.iter (fun (n, k) -> n#child_ctorchild_added subtype k) parents;
        List.iter (fun n -> n#parent_ctorchild_added subtype) children
      in
      let vParents = v#parents in
      let vChildren = v#children in
      List.iter (fun listener -> List.iter (fun child -> listener child) vChildren) child_listeners;
      List.iter (fun n -> n#set_value v) children;
      List.iter (fun n -> v#add_child n) children;
      List.iter (fun listener -> v#add_child_listener listener) child_listeners;
      List.iter (fun vneq -> vneq#neq_merging_into (self :> valuenode) v) neqs;
      List.iter (fun (n, k) -> n#set_child k v) parents;
      (* At this point self is referenced nowhere. *)
      v#merge_merge_listeners merge_listeners;
      (* It is possible that some of the nodes in 'parents' are now equivalent with nodes in v.parents. *)
      if v == ctxt#true_node#value then ctxt#report_truenode_childcount (List.length v#children);
      if v == ctxt#false_node#value then ctxt#report_falsenode_childcount (List.length v#children);
      let check_export_constant v1 v2 =
        match v1#unknown, v2#ctorchild number_subtype with
          Some u, Some child ->
          let Ctor (NumberCtor n) = child#symbol#kind in
          context#add_redex begin fun () ->
            ctxt#reportExportingConstant;
            context#simplex_assert_eq n [(neg_unit_num, u)]
          end
        | _ -> ()
      in
      if not fromSimplex then begin
        check_export_constant (self :> valuenode) v;
        check_export_constant v (self :> valuenode)
      end;
      let lt_ccs subtype = function
        [] -> true
      | (subtype', _)::_ -> InductiveSubtype.lt subtype subtype'
      in
      let rec match_ctorchildren ccs vccs =
        match ccs, vccs with
          [], [] -> []
        | (subtype, n)::ccs, vccs when lt_ccs subtype vccs ->
          v#set_ctorchild subtype n; assert (n#value = v);
          ctorchild_added subtype vParents vChildren;
          match_ctorchildren ccs vccs
        | ccs, (vsubtype, vn)::vccs when lt_ccs vsubtype ccs ->
          ctorchild_added vsubtype parents children;
          match_ctorchildren ccs vccs
        | (subtype, n)::ccs, (vsubtype, vn)::vccs ->
          assert (subtype = vsubtype);
          (n, vn)::match_ctorchildren ccs vccs
      in
      let matching_ctorchildren = match_ctorchildren ctorchildren v#ctorchildren in
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
                Unsat3 -> Unsat
              | Unknown3|Valid3 -> iter rps
            end
        in
        iter redundant_parents
      in
      let rec process_matching_ctorchildren mccs =
        match mccs with
          [] -> process_redundant_parents()
        | (n, n')::mccs ->
          (* print_endline "Adding injectiveness edges..."; *)
          let rec iter vs =
            match vs with
              [] -> process_matching_ctorchildren mccs
            | (v, v')::vs ->
              begin
              (* print_endline ("Adding injectiveness edge: " ^ v#pprint ^ " = " ^ v'#pprint); *)
              match context#assert_eq v#initial_child#value v'#initial_child#value with
                Unsat3 -> Unsat
              | Unknown3|Valid3 -> iter vs
              end
          in
          iter (List.combine n#children n'#children)
      in
      let process_ctorchildren () = process_matching_ctorchildren matching_ctorchildren in
      begin
        match (unknown, v#unknown) with
          (Some u, None) -> v#set_unknown u; process_ctorchildren()
        | (Some u1, Some u2) when not fromSimplex ->
          begin
            (* print_endline ("Exporting equality to Simplex: " ^ u1#name ^ " = " ^ u2#name); *)
            ctxt#reportExportingEquality;
            match ctxt#simplex_assert_eq zero_num [unit_num, u1; neg_unit_num, u2] with
              Unsat3 -> Unsat
            | _ -> process_ctorchildren()
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
          match ctorchildren with
            (_, n)::_ when n#children = [] -> n
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
and context () =
  let initialPendingSplitsFrontNode = ref None in
  let boxed_bool_symbol = new symbol (Ctor (CtorByOrdinal (boxed_bool_subtype, 0))) "boxed_bool" in
  let unboxed_bool_symbol =
    let s = new symbol (Fixpoint (boxed_bool_subtype, 0)) "unboxed_bool" in
    s#set_fpclauses [boxed_bool_symbol, fun _ [b] -> b];
    s
  in
  let rec simplify t =
    match t with
    | Iff (t1, t2) -> Iff (simplify t1, simplify t2)
    | Eq (t1, t2) -> Eq (simplify t1, simplify t2)
    | Le (t1, t2) -> Le (simplify t1, simplify t2)
    | Lt (t1, t2) -> Lt (simplify t1, simplify t2)
    | Not t -> Not (simplify t)
    | And (t1, t2) -> And (simplify t1, simplify t2)
    | Or (t1, t2) -> Or (simplify t1, simplify t2)
    | Add (t1, t2) -> Add (simplify t1, simplify t2)
    | Sub (t1, t2) -> Sub (simplify t1, simplify t2)
    | Mul (t1, t2) -> Mul (simplify t1, simplify t2)
    | App (parent_sym, [target; App (parent_offset_sym, [], _) as parent_offset], cached) when parent_sym#name = "field_ptr_parent" -> 
      begin match simplify target with
      | App (child_sym, [child_target; _; App (child_offset_sym, [], _)], _) when child_sym#name = "field_ptr" && parent_offset_sym#name = child_offset_sym#name ->
        child_target
      | simpl -> 
        App (parent_sym, [simpl; parent_offset], cached)
      end
    | App (sym, terms, cached) -> 
      App (sym, terms |> List.map simplify, cached)
    | IfThenElse (t1, t2, t3) -> IfThenElse (simplify t1, simplify t2, simplify t3)
    | RealLe (t1, t2) -> RealLe (simplify t1, simplify t2)
    | Implies (t1, t2) -> Implies (simplify t1, simplify t2)
    | t -> t
  in
  object (self)
    val eq_symbol = new symbol Uninterp "=="
    val iff_symbol = new symbol Uninterp "<==>"
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
    val int_div_symbol = new symbol Uninterp "/"
    val int_mod_symbol = new symbol Uninterp "%"

    val mutable numnodes: termnode NumMap.t = NumMap.empty (* Sorted *)
    val mutable ttrue = None
    val mutable tfalse = None
    val simplex = Simplex.new_simplex ()
    val mutable popstack = []
    val mutable pushdepth = 0
    val mutable popactionlist: (unit -> unit) list = []
    val mutable simplex_eqs = []
    val mutable simplex_consts = []
    val mutable redexes = []
    val mutable unsat = false
    val mutable implications = []
    val mutable pending_splits_front = initialPendingSplitsFrontNode
    val mutable pending_splits_back = initialPendingSplitsFrontNode
    val mutable formal_depth = 0  (* If formal_depth = 0, App terms are eagerly turned into E-graph nodes. *)
    (* For diagnostics only. *)
    val mutable values = []
    val mutable creating_termnode_of_poly = false
    
    (* Statistics *)
    val mutable max_truenode_childcount = 0
    val mutable max_falsenode_childcount = 0
    val mutable assume_core_count = 0
    val mutable split_count = 0
    val mutable simplex_assert_ge_count = 0
    val mutable simplex_assert_eq_count = 0
    val mutable simplex_assert_neq_count = 0
    val mutable axioms: (string * int ref) list = []
    val assumes_with_pending_splits = Array.make 30 0
    val mutable assumes_with_more_pending_splits = 0
    
    val mutable verbosity = 0
    
    method verbosity = verbosity
    
    method set_verbosity v = verbosity <- v

    method creating_termnode_of_poly = creating_termnode_of_poly
    
    method report_truenode_childcount n =
      if n > max_truenode_childcount then max_truenode_childcount <- n
    method report_falsenode_childcount n =
      if n > max_falsenode_childcount then max_falsenode_childcount <- n
    method reportExportingEquality =
      simplex_assert_eq_count <- simplex_assert_eq_count + 1
    method reportExportingConstant =
      simplex_assert_eq_count <- simplex_assert_eq_count + 1
    method stats =
      let axiomTriggerCounts = axioms |> List.filter (fun (k, v) -> !v > 0) in
      let maxAxiomNameLength = List.fold_left (fun n (k, v) -> max n (String.length k)) 0 axiomTriggerCounts in
      let axiomTriggerCounts =
        axiomTriggerCounts
          |> List.sort (fun (k1, v1) (k2, v2) -> compare !v1 !v2)
          |> List.map (fun (k, v) -> Printf.sprintf "    %-*s %5d\n" maxAxiomNameLength k !v)
          |> String.concat ""
      in
      let assumesWithPendingSplits =
        assumes_with_pending_splits
          |> Array.fold_left (fun (i, xs) n -> (i + 1, (i, n)::xs))  (0, [])
          |> snd
          |> List.filter (fun (i, n) -> n > 0)
          |> List.rev
          |> List.map (fun (i, n) -> Printf.sprintf "%d (%d)" n i)
          |> String.concat ", "
      in
      let pendingSplitsInfo = Printf.sprintf "%s, %d (more than %d)" assumesWithPendingSplits assumes_with_more_pending_splits (Array.length assumes_with_pending_splits) in
      let text =
      Printf.sprintf
        "\
          # toplevel assumes and queries (with # pending case splits) = %s\n\
          assume_core_count = %d\n\
          number of case splits = %d\n\
          simplex_assert_ge_count = %d\n\
          simplex_assert_eq_count = %d\n\
          simplex_assert_neq_count = %d\n\
          max_truenode_childcount = %d\n\
          max_falsenode_childcount = %d\n\
          axiom triggered counts:\n%s\n\
        "
        pendingSplitsInfo
        assume_core_count
        split_count
        simplex_assert_ge_count
        simplex_assert_eq_count
        simplex_assert_neq_count
        max_truenode_childcount
        max_falsenode_childcount
        axiomTriggerCounts
      in
        (text, ["Time spent in query, assume, push, pop", Stopwatch.ticks stopwatch; "Time spent in Simplex", simplex#get_ticks])
    
    initializer
      let eq_listener u1 u2 =
        if verbosity > 10 then trace "Receiving equality from Simplex: %s(%s) = %s(%s)" (the (unknown_tag u1))#pprint (Simplex.print_unknown u1) (the (unknown_tag u2))#pprint (Simplex.print_unknown u2);
        simplex_eqs <- (u1, u2)::simplex_eqs
      in
      let const_listener u n =
        if verbosity > 10 then trace "Receiving constant from Simplex: %s(%s) = %s" (the (unknown_tag u))#pprint (Simplex.print_unknown u) (string_of_num n);
        simplex_consts <- (u, n)::simplex_consts
      in
      simplex#register_listeners eq_listener const_listener;
      ttrue <- Some (self#get_node (self#mk_symbol "true" [] () (Ctor (CtorByOrdinal (bool_subtype, 0)))) []);
      tfalse <- Some (self#get_node (self#mk_symbol "false" [] () (Ctor (CtorByOrdinal (bool_subtype, 1)))) [])
    
    method simplex = simplex
    method eq_symbol = eq_symbol
    method iff_symbol = iff_symbol
    
    method register_valuenode v =
      values <- v::values
    
    method get_numnode n =
      try
        NumMap.find n numnodes
      with
        Not_found ->
        (* print_endline ("Creating intlit node for " ^ string_of_int n); *)
        let node = self#get_node (new symbol (Ctor (NumberCtor n)) (string_of_num n)) [] in
        numnodes <- NumMap.add n node numnodes;
        node

    method get_ifthenelsenode t1 t2 t3 =
      (* print_endline ("Producing ifthenelse termnode"); *)
      let symname = "ifthenelse(" ^ self#pprint t2 ^ ", " ^ self#pprint t3 ^ ")" in
      let s = new symbol (Fixpoint (bool_subtype, 0)) symname in
      s#set_fpclauses [
        (self#true_node#symbol, (fun _ _ -> t2));
        (self#false_node#symbol, (fun _ _ -> t3))
      ];
      let tnode = self#termnode_of_term t1 in
      (* printff "Adding split for if-then-else term...\n"; *)
      self#add_pending_split (TermNode tnode) (Not (TermNode tnode));
      new termnode (self :> context) s [tnode#value]

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
    method mk_boxed_bool (t: (symbol, termnode) term) = self#mk_app boxed_bool_symbol [t]
    method mk_unboxed_bool (t: (symbol, termnode) term) = self#mk_app unboxed_bool_symbol [t]
    method mk_true: (symbol, termnode) term = True
    method mk_false: (symbol, termnode) term = False
    method mk_and (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = And (t1, t2)
    method mk_or (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Or (t1, t2)
    method mk_not (t: (symbol, termnode) term): (symbol, termnode) term = Not t
    method mk_ifthenelse (t1: (symbol, termnode) term) (t2: (symbol, termnode) term) (t3: (symbol, termnode) term): (symbol, termnode) term =
      IfThenElse (t1, t2, t3)
    method mk_iff (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Iff (t1, t2)
    method mk_implies (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Implies (t1, t2)
    method mk_eq (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Eq (t1, t2)
    method mk_intlit (n: int): (symbol, termnode) term = NumLit (num_of_int n)
    method mk_intlit_of_string (s: string): (symbol, termnode) term = NumLit (num_of_string s)
    method mk_add (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Add (t1, t2)
    method mk_sub (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Sub (t1, t2)
    method mk_mul (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Mul (t1, t2)
    method eval_term t =
      match t with
        NumLit n -> Some n
      | TermNode t -> t#value#as_number
      | Add (t1, t2) ->
        begin match self#eval_term t1, self#eval_term t2 with
          Some n1, Some n2 -> Some (n1 +/ n2)
        | _ -> None
        end
      | Sub (t1, t2) ->
        begin match self#eval_term t1, self#eval_term t2 with
          Some n1, Some n2 -> Some (n1 -/ n2)
        | _ -> None
        end
      | Mul (t1, t2) ->
        begin match self#eval_term t1, self#eval_term t2 with
          Some n1, Some n2 -> Some (n1 */ n2)
        | _ -> None
        end
      | _ -> None
    method mk_div (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term =
      match self#eval_term t1, self#eval_term t2 with
        Some n1, Some n2 -> NumLit (if sign_num n1 < 0 then minus_num (quo_num (minus_num n1) n2) else quo_num n1 n2)
      | _ -> self#mk_app int_div_symbol [t1;t2]
    method mk_mod(t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term =
      match self#eval_term t1, self#eval_term t2 with
        Some n1, Some n2 -> NumLit (if sign_num n1 < 0 then minus_num (mod_num (minus_num n1) n2) else mod_num n1 n2)
      | _ -> self#mk_app int_mod_symbol [t1;t2]
    method mk_lt (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Lt (t1, t2)
    method mk_le (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Le (t1, t2)
    method mk_reallit (n: int): (symbol, termnode) term = NumLit (num_of_int n)
    method mk_reallit_of_num (n: num): (symbol, termnode) term = NumLit n
    method mk_real_add (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Add (t1, t2)
    method mk_real_sub (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Sub (t1, t2)
    method mk_real_mul (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = Mul (t1, t2)
    method mk_real_lt (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = RealLt (t1, t2)
    method mk_real_le (t1: (symbol, termnode) term) (t2: (symbol, termnode) term): (symbol, termnode) term = RealLe (t1, t2)
    
    method string_of_simplex_poly n ts =
      Printf.sprintf "%s [%s]" (Num.string_of_num n) (String.concat "; " (List.map (fun (scale, u) -> Num.string_of_num scale ^ ", " ^ (the (Simplex.unknown_tag u))#pprint) ts))

    method simplex_assert_eq n ts =
      if verbosity > 10 then trace "Redux.simplex_assert_eq %s" (self#string_of_simplex_poly n ts);
      match simplex#assert_eq n ts with
        Simplex.Unsat -> Unsat3
      | Simplex.Sat -> Unknown3
    
    method simplex_assert_neq n ts =
      if verbosity > 10 then trace "Redux.simplex_assert_neq %s" (self#string_of_simplex_poly n ts);
      simplex#assert_neq n ts
    
    method assume_core (t: (symbol, termnode) term): assume_result3 =
      assume_core_count <- assume_core_count + 1;
      (* print_endline ("Assume: " ^ self#pprint t); *)
      let rec assume_true t =
        match t with
          TermNode t -> self#assume_eq t self#true_node
        | Eq (t1, t2) when self#is_poly t1 || self#is_poly t2 ->
          let (n, ts) = self#to_poly (Sub (t2, t1)) in
          begin match ts with
            [] -> if sign_num n = 0 then Valid3 else Unsat3
          | [(t, scale)] -> self#assume_eq t (self#get_numnode (minus_num n // scale))
          | _ ->
            self#do_and_reduce (fun () ->
              simplex_assert_eq_count <- simplex_assert_eq_count + 1;
              self#simplex_assert_eq n (List.map (fun (t, scale) -> (scale, t#value#mk_unknown)) ts)
            )
          end
        | Eq (t1, t2) -> self#assume_eq (self#termnode_of_term t1) (self#termnode_of_term t2)
        | Iff (True, t2) -> assume_true t2
        | Iff (t1, True) -> assume_true t1
        | Iff (False, t2) -> assume_false t2
        | Iff (t1, False) -> assume_false t1
        | Le (t1, t2) -> self#assume_le t1 zero_num t2
        | Lt (t1, t2) -> self#assume_le t1 unit_num t2
        | RealLe (t1, t2) -> self#assume_le t1 zero_num t2
        | RealLt (t1, t2) -> self#assume_core (And (Not (Eq (t1, t2)), (RealLe (t1, t2))))
        | And (t1, t2) ->
          begin
            match self#assume_core t1 with
              Unsat3 -> Unsat3
            | r ->
              match (r, self#assume_core t2) with
                (Valid3, Valid3) -> Valid3
              | (_, Unsat3) -> Unsat3
              | _ -> Unknown3
          end
        | Not t -> assume_false t
        | Implies (True, t2) -> assume_true t2
        | Implies (t1, t2) -> self#add_implication t1 t2; Unknown3
        | t -> self#assume_eq (self#termnode_of_term t) self#true_node
      and assume_false t =
        match t with
          TermNode t -> self#assume_eq t self#false_node
        | Iff (t1, True) -> assume_false t1
        | Iff (t1, False) -> assume_true t1
        | Iff (True, t2) -> assume_false t2
        | Iff (False, t2) -> assume_true t2
        | Eq (t1, t2) when self#is_poly t1 || self#is_poly t2 ->
          let (offset, terms) = self#to_poly (Sub (t2, t1)) in
          (* printff "assume_false(Eq): poly: %s\n" (self#pprint_poly (offset, terms)); *)
          begin match terms with
            [] -> if sign_num offset = 0 then Unsat3 else Valid3
          | [(t, n)] -> self#assume_neq t (self#get_numnode (minus_num offset // n))
          | terms ->
            self#do_and_reduce $. fun () ->
            simplex_assert_neq_count <- simplex_assert_neq_count + 1;
            match self#simplex_assert_neq offset (List.map (fun (t, scale) -> (scale, t#value#mk_unknown)) terms) with
              Simplex.Unsat -> Unsat3
            | Simplex.Sat -> Unknown3
          end
        | Eq (t1, t2) -> self#assume_neq (self#termnode_of_term t1) (self#termnode_of_term t2)
        | Le (t1, t2) -> self#assume_le t2 unit_num t1
        | Lt (t1, t2) -> self#assume_le t2 zero_num t1
        | RealLe (t1, t2) -> assume_true (RealLt (t2, t1))
        | RealLt (t1, t2) -> assume_true (RealLe (t2, t1))
        | Not t -> assume_true t
        | t -> self#assume_eq (self#termnode_of_term t) self#false_node
      in
      if verbosity > 3 then trace_entering "Redux.assume_core(%s)" (self#pprint t);
      let result = assume_true t in
      if verbosity > 3 then trace_exiting "Redux.assume_core";
      result
    
    method assume_with_implications t =
      if verbosity > 2 then begin trace_entering "Redux.assume_with_implications(%s)" (self#pprint t) end;
      let result =
      let result = self#assume_core t in
      match result with
        Unsat3 -> Unsat3
      | Valid3 -> Valid3
      | Unknown3 ->
        if self#perform_implications then Unsat3 else Unknown3
      in
      if verbosity > 2 then begin trace_exiting "Redux.assume_with_implications" end;
      result
    
    method assume_internal t =
      (* let time0 = if verbosity > 1 then begin trace_entering "Redux.assume_internal(%s)" (self#pprint t); Perf.time() end else 0.0 in *)
      let result =
      let result = if unsat then Unsat3 else self#assume_with_implications t in
      match result with
        Unsat3 -> Unsat
      | Valid3 -> Unknown
      | Unknown3 ->
        if self#perform_pending_splits (fun _ -> false) then Unsat else Unknown
      in
      (* if verbosity > 1 then begin let time1 = Perf.time() in trace_exiting "Redux.assume_internal: %.6f seconds" (time1 -. time0) end; *)
      result
    
    method register_pending_splits_count =
      let pendingSplitsCount = self#count_pending_splits in
      if pendingSplitsCount < Array.length assumes_with_pending_splits then
        assumes_with_pending_splits.(pendingSplitsCount) <- assumes_with_pending_splits.(pendingSplitsCount) + 1
      else
        assumes_with_more_pending_splits <- assumes_with_more_pending_splits + 1;
    
    method assert_term t =
      if formal_depth = 0 then
      let time0 = if verbosity > 0 then begin trace_entering "Redux.assert_term(%s)" (self#pprint t); Perf.time() end else 0.0 in
      Stopwatch.start stopwatch;
      self#register_pending_splits_count;
      let result = self#assume_internal t in
      Stopwatch.stop stopwatch;
      if verbosity > 0 && result = Unsat then trace "Redux.assert_term: dropping Unsat result!";
      if verbosity > 0 then begin let time1 = Perf.time() in trace_exiting "Redux.assert_term: %.6f seconds" (time1 -. time0) end
    
    method assume t =
      let time0 = if verbosity > 0 then begin trace_entering "Redux.assume(%s)" (self#pprint t); Perf.time() end else 0.0 in
      Stopwatch.start stopwatch;
      self#register_pending_splits_count;
      let result = self#assume_internal t in
      Stopwatch.stop stopwatch;
      if verbosity > 0 then begin let time1 = Perf.time() in trace_exiting "Redux.assume: %.6f seconds" (time1 -. time0) end;
      result

    method query (t: (symbol, termnode) term): bool =
      if verbosity > 0 then trace_entering "Redux.query(%s)" (self#pprint t);
      Stopwatch.start stopwatch;
      assert (not self#prune_pending_splits);
      self#register_pending_splits_count;
      self#push_internal;
      let result = self#assume_internal (Not t) in
      self#pop_internal;
      Stopwatch.stop stopwatch;
      if verbosity > 0 then trace_exiting "Redux.query";
      result = Unsat
    
    method get_type (term: (symbol, termnode) term) = ()

    method termnode_of_poly n ts =
      match ts with
        [] -> self#get_numnode n
      | [(t, scale)] when sign_num n = 0 && scale =/ num_of_int 1 -> t
      | _ ->
        creating_termnode_of_poly <- true;
        let s = "{" ^ self#pprint_poly (n, ts) ^ "}" in
        let symb = new poly_symbol s (n, ts) in
        let tnode = new termnode (self :> context) symb [] in
        symb#set_node tnode;
        let u = tnode#value#mk_unknown in
        ignore (self#simplex_assert_eq n ((neg_unit_num, u)::List.map (fun (t, scale) -> (scale, t#value#mk_unknown)) ts));
        assert (self#pump_simplex_eqs <> Unsat3);
        creating_termnode_of_poly <- false;
        tnode
    
    method termnode_of_term t =
      let get_node s ts = self#get_node s (List.map (fun t -> (self#termnode_of_term t)#value) ts) in
      match t with
        t when self#is_poly t ->
        let (n, ts) = self#to_poly t in
        let result = self#termnode_of_poly n ts in
        if verbosity > 20 then trace "termnode_of_term %s = %s" (self#pprint t) result#pprint;
        result
      | TermNode t -> t
      | True -> self#true_node
      | False -> self#false_node
      | App (s, ts, None) -> get_node s ts
      | App (s, ts, Some t) -> if verbosity > 20 then trace "termnode_of_term: using cached App termnode %s" t#pprint; t
      | IfThenElse (t1, t2, t3) -> self#get_ifthenelsenode t1 t2 t3
      | Iff (t1, t2) -> get_node iff_symbol [t1; t2]
      | Eq (t1, t2) -> get_node eq_symbol [t1; t2]
      | Not t -> self#termnode_of_term (Eq (t, self#mk_false))
      | And (t1, t2) -> get_node and_symbol [t1; t2]
      | Or (t1, t2) -> get_node or_symbol [t1; t2]
      | Le (t1, t2) -> get_node int_le_symbol [t1; t2]
      | Lt (t1, t2) -> get_node int_lt_symbol [t1; t2]
      | RealLe (t1, t2) -> get_node real_le_symbol [t1; t2]
      | RealLt (t1, t2) -> get_node real_lt_symbol [t1; t2]
      | _ -> failwith ("Redux does not yet support this term: " ^ self#pprint t)

    method pushdepth = pushdepth
    method push =
      Stopwatch.start stopwatch;
      self#push_internal;
      Stopwatch.stop stopwatch
    
    method push_internal =
      (* print_endline "Push"; *)
      self#reduce;
      if not unsat then begin
        assert (redexes = []);
        assert (simplex_eqs = []);
        assert (simplex_consts = [])
      end;
      popstack <- (pushdepth, popactionlist, values, unsat)::popstack;
      pushdepth <- pushdepth + 1;
      popactionlist <- [];
      simplex#push
    
    method register_popaction action =
      popactionlist <- action::popactionlist

    method pop =
      Stopwatch.start stopwatch;
      self#pop_internal;
      Stopwatch.stop stopwatch
      
    method pop_internal =
      (* print_endline "Pop"; *)
      redexes <- [];
      simplex_eqs <- [];
      simplex_consts <- [];
      simplex#pop;
      match popstack with
        (pushdepth0, popactionlist0, values0, unsat0)::popstack0 ->
        List.iter (fun action -> action()) popactionlist;
        pushdepth <- pushdepth0;
        popactionlist <- popactionlist0;
        values <- values0;
        unsat <- unsat0;
        popstack <- popstack0
      | [] -> failwith "Popstack is empty"

    method add_redex n =
      redexes <- redexes @ [n] (* Add to end; order matters due to axiom precondition checks. *)
    
    method add_implication p q =
      let is = implications in
      implications <- (p, q)::implications;
      self#register_popaction (fun () -> implications <- is)
    
    method perform_implications =
      match implications with
        [] -> false
      | (p, q)::is as is0 ->
        implications <- is;
        self#register_popaction (fun () -> implications <- is0);
        let rec holds p =
          match p with
            And (p1, p2) -> holds p1 && holds p2
          | p ->
            self#push_internal;
            let result = self#assume_core (Not p) in
            self#pop_internal;
            result = Unsat3
        in
        holds p && self#assume_core q = Unsat3 || self#perform_implications
    
    method add_pending_split branch1 branch2 =
      (* printff "Adding pending split: (%s, %s)\n" (self#pprint branch1) (self#pprint branch2); *)
      let back = pending_splits_back in
      assert (!back = None);
      self#register_popaction (fun () -> back := None; pending_splits_back <- back);
      pending_splits_back <- ref None;
      back := Some (`SplitNode (branch1, branch2, pending_splits_back))
(*    
    method prune_pending_splits =
      let rec iter () =
        let rec iter0 badSplits splits =
          match splits with
            [] -> Unknown
          | ((branch1, branch2) as split)::splits ->
            let is_unsat t =
              self#push;
              let result = self#assume_core t in
              self#pop;
              result = Unsat
            in
            if is_unsat branch1 then
            begin
              pending_splits <- splits @ badSplits;
              let result = self#assume_core branch2 in
              if result = Unsat then Unsat else iter ()
            end
            else if is_unsat branch2 then
            begin
              pending_splits <- splits @ badSplits;
              let result = self#assume_core branch1 in
              if result = Unsat then Unsat else iter ()
            end
            else
              iter0 (split::badSplits) splits
        in
        iter0 [] pending_splits
      in
      iter ()
*)
    
    method count_pending_splits =
      let rec iter n node =
        match !node with
          None -> n
        | Some (`SplitNode (branch1, branch2, nextNode)) ->
          iter (n + 1) nextNode
      in
      iter 0 pending_splits_front
    
    (** If this method returns true, then the current theory is unsatisfiable. *)
    method perform_pending_splits cont =
      let rec iter assumptions currentNode =
        match !currentNode with
          None -> cont assumptions
        | Some (`SplitNode (branch1, branch2, nextNode)) as currentNodeValue->
          split_count <- split_count + 1;
          if verbosity >= 2 then trace_entering "splitting on (%s, %s) (depth: %d)" (self#pprint branch1) (self#pprint branch2) (List.length assumptions);
          self#push_internal;
          if verbosity >= 2 then begin trace "First branch: %s" (self#pprint branch1); indent () end;
          let result = self#assume_with_implications branch1 in
          if verbosity >= 2 then begin unindent (); trace "Branch yields %s" (match result with Unsat3 -> "Unsat" | Unknown3 -> "Unknown" | Valid3 -> "Valid") end;
          let continue = result = Unsat3 || result = Valid3 && assumptions = [] || iter (branch1::assumptions) nextNode in
          self#pop_internal;
          if assumptions = [] && result <> Unknown3 then
          begin
            if verbosity >= 2 then trace "Pruning split";
            self#register_popaction (fun () -> pending_splits_front <- currentNode);
            pending_splits_front <- nextNode;
            let result = if result = Unsat3 then self#assume_with_implications branch2 else Valid3 in
            let continue = result = Unsat3 || iter [] nextNode in
            if verbosity >= 2 then trace_exiting "splitting";
            continue
          end
          else
          let continue = continue && (result = Valid3 ||
            begin
              self#push_internal;
              if verbosity >= 2 then begin trace "Second branch %s" (self#pprint branch2); indent () end;
              let result = self#assume_with_implications branch2 in
              if verbosity >= 2 then begin unindent (); trace "Branch yields %s" (match result with Unsat3 -> "Unsat" | Unknown3 -> "Unknown" | Valid3 -> "Valid") end;
              let continue = result = Unsat3 || iter (branch2::assumptions) nextNode in
              self#pop_internal;
              if assumptions = [] && not continue then
              begin
                match result with
                  Unsat3 ->
                  (* Next time, immediately assume the first branch. *)
                  self#register_popaction (fun () -> currentNode := currentNodeValue);
                  currentNode := Some (`SplitNode (False, branch1, nextNode))
                | Valid3 ->
                  self#register_popaction (fun () -> pending_splits_front <- currentNode);
                  pending_splits_front <- nextNode
                | Unknown3 -> ()
              end;
              continue
            end
            )
          in
          if verbosity >= 2 then trace_exiting "splitting";
          continue
      in
      iter [] pending_splits_front
    
    method prune_pending_splits =
      let rec iter () =
        let pendingSplitsFront = pending_splits_front in
        match !pendingSplitsFront with
          Some (`SplitNode (False, branch2, nextNode)) ->
          self#register_popaction (fun () -> pending_splits_front <- pendingSplitsFront);
          pending_splits_front <- nextNode;
          self#assume_with_implications branch2 = Unsat3 || iter ()
        | _ -> false
      in
      iter ()
    
    method mk_symbol name (domain: unit list) (range: unit) kind =
      let s = new symbol kind name in if List.length domain = 0 then ignore (self#get_node s []); s
    
    method set_fpclauses (s: symbol) (k: int) (cs: (symbol * ((symbol, termnode) term list -> (symbol, termnode) term list -> (symbol, termnode) term)) list) =
      s#set_fpclauses cs

    method mk_app (s: symbol) (ts: (symbol, termnode) term list): (symbol, termnode) term =
      let termnode =
        if formal_depth = 0 then
          let ts = List.map self#termnode_of_term ts in
          let vs = List.map (fun t -> t#value) ts in
          let t = self#get_node s vs in
          if verbosity > 20 then trace "mk_app: caching termnode %s" t#pprint;
          Some t
        else
          None
      in
      App (s, ts, termnode)
    
    method pprint (t: (symbol, termnode) term): string =
      match t with
        TermNode t -> t#pprint
      | True -> "true"
      | False -> "false"
      | Iff (t1, t2) -> self#pprint t1 ^ " <==> " ^ self#pprint t2
      | Eq (t1, t2) -> self#pprint t1 ^ " = " ^ self#pprint t2
      | Le (t1, t2) -> self#pprint t1 ^ " <= " ^ self#pprint t2
      | Lt (t1, t2) -> self#pprint t1 ^ " < " ^ self#pprint t2
      | RealLe (t1, t2) -> self#pprint t1 ^ " <=/ " ^ self#pprint t2
      | RealLt (t1, t2) -> self#pprint t1 ^ " </ " ^ self#pprint t2
      | And (t1, t2) -> self#pprint t1 ^ " && " ^ self#pprint t2
      | Or (t1, t2) -> self#pprint t1 ^ " || " ^ self#pprint t2
      | Not t -> "!(" ^ self#pprint t ^ ")"
      | Add (t1, t2) -> "(" ^ self#pprint t1 ^ " + " ^ self#pprint t2 ^ ")"
      | Sub (t1, t2) -> "(" ^ self#pprint t1 ^ " - " ^ self#pprint t2 ^ ")"
      | App (s, ts, _) -> s#name ^ (if ts = [] then "" else "(" ^ String.concat ", " (List.map (fun t -> self#pprint t) ts) ^ ")")
      | NumLit n -> string_of_num n
      | Mul (t1, t2) -> Printf.sprintf "(%s * %s)" (self#pprint t1) (self#pprint t2)
      | IfThenElse (t1, t2, t3) -> "(" ^ self#pprint t1 ^ " ? " ^ self#pprint t2 ^ " : " ^ self#pprint t3 ^ ")"
      | BoundVar i -> Printf.sprintf "bound.%i" i
      | Implies (t1, t2) -> self#pprint t1 ^ " ==> " ^ self#pprint t2
    
    method pprint_sym (s : symbol) : string = s#name
    method pprint_sort (s : unit) : string = "()"
    
    method get_node s vs =
      match vs with
        [] ->
        begin
        match s#node with
          None ->
          (* print_endline ("Creating node for nullary symbol " ^ s#name); *)
          let node = new termnode (self :> context) s vs in
          s#set_node node;
          node
        | Some n -> n
        end
      | v::_ ->
        begin
        match v#lookup_parent [s] vs with
          None ->
          let node = new termnode (self :> context) s vs in
          node
        | Some n -> n
        end
    
    method assert_neq (v1: valuenode) (v2: valuenode) =
      if verbosity > 7 then trace "assert_neq %s %s" (v1#pprint) (v2#pprint);
      if v1 = v2 then
        Unsat3
      else if v1#neq v2 then
        Valid3
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
        Unknown3
      end

    method assert_eq_and_reduce v1 v2 =
      self#do_and_reduce (fun () -> self#assert_eq v1 v2)
    
    method assume_eq (t1: termnode) (t2: termnode) = self#reduce; self#assert_eq_and_reduce t1#value t2#value
    
    method assert_ge c ts =
      if verbosity > 10 then trace "simplex#assert_ge %s [%s]" (string_of_num c) (String.concat "; " (List.map (fun (c, u) -> Printf.sprintf "%s*%s(%s)" (string_of_num c) (the (unknown_tag u))#pprint (print_unknown u)) ts));
      simplex#assert_ge c ts
    
    method assert_le t1 offset t2 =
      let (n1, ts1) = t1#to_poly in
      let (n2, ts2) = t2#to_poly in
      let offset = n2 -/ n1 -/ offset in
      let ts1 = List.map (fun (t, scale) -> (minus_num scale, t#value#mk_unknown)) ts1 in
      let ts2 = List.map (fun (t, scale) -> (scale, t#value#mk_unknown)) ts2 in
      simplex_assert_ge_count <- simplex_assert_ge_count + 1;
      match self#assert_ge offset (ts1 @ ts2) with
        Simplex.Unsat -> Unsat3
      | Simplex.Sat -> Unknown3

    method is_poly t =
      match t with
        NumLit _ -> true
      | Add (_, _) -> true
      | Sub (_, _) -> true
      | Mul (_, _) -> true
      | _ -> false
    
    method pprint_poly (offset, terms) =
      String.concat " + " (string_of_num offset::List.map (fun (t, scale) -> Printf.sprintf "%s*%s" (string_of_num scale) (t#pprint)) terms)

    method get_mul_node t1 t2 =
      match t1#value#as_number with
        Some n1 ->
        if n1 =/ zero_num then
          self#get_numnode zero_num
        else
          begin match t2#value#as_number with
            Some n2 -> self#get_numnode (n1 */ n2)
          | None ->
            self#termnode_of_poly zero_num [(t2, n1)]
          end
      | None ->
        match t2#value#as_number with
          Some n2 ->
          if n2 =/ zero_num then
            self#get_numnode zero_num
          else
            self#termnode_of_poly zero_num [(t1, n2)]
        | None ->
          self#get_node mul_symbol [t1#value; t2#value]

    method to_poly t =
      let merge_term t scale ts =
        let rec iter ts =
          match ts with
            [] -> [(t, scale)]
          | ((t', scale') as term)::ts ->
            if t#value = t'#value then
              let scale'' = add_num scale scale' in
              if sign_num scale'' = 0 then ts else (t, scale'')::ts
            else
              term::iter ts
        in
        iter ts
      in
      let rec merge_terms ts1 ts2 =
        match ts1 with
          [] -> ts2
        | (t, scale)::ts1 -> merge_terms ts1 (merge_term t scale ts2)
      in
      let scale_poly scale n ts =
        if sign_num scale = 0 then (zero_num, []) else
        (mult_num scale n, List.map (fun (v, scale') -> (v, mult_num scale scale')) ts)
      in
      let rec iter scale t =
        match t with
          NumLit n -> (mult_num scale n, [])
        | Add (t1, t2) ->
          let (n1, ts1) = iter scale t1 in
          let (n2, ts2) = iter scale t2 in
          (add_num n1 n2, merge_terms ts1 ts2)
        | Sub (t1, t2) ->
          let (n1, ts1) = iter scale t1 in
          let (n2, ts2) = iter (minus_num scale) t2 in
          (add_num n1 n2, merge_terms ts1 ts2)
        | Mul (t1, t2) ->
          let (n1, ts1) = iter unit_num t1 in
          let (n2, ts2) = iter unit_num t2 in
          if ts1 = [] then
            scale_poly (mult_num scale n1) n2 ts2
          else if ts2 = [] then
            scale_poly (mult_num scale n2) n1 ts1
          else
            let tn1 = self#termnode_of_poly n1 ts1 in
            let tn2 = self#termnode_of_poly n2 ts2 in
            (zero_num, [(self#get_mul_node tn1 tn2, scale)])
        | _ ->
          let t = self#termnode_of_term t in
          begin match t#value#as_number with
            None -> (zero_num, [(t, scale)])
          | Some n -> (mult_num scale n, [])
          end
      in
      iter unit_num t
    
    method assume_le t1 offset t2 =   (* t1 + offset <= t2 *)
      let (offset', terms) = self#to_poly (Sub (t2, t1)) in
      let offset = sub_num offset' offset in
      if terms = [] then if sign_num offset < 0 then Unsat3 else Valid3 else
      begin
      self#do_and_reduce (fun () ->
        simplex_assert_ge_count <- simplex_assert_ge_count + 1;
        match self#assert_ge offset (List.map (fun (t, scale) -> (scale, t#value#mk_unknown)) terms) with
          Simplex.Unsat -> Unsat3
        | Simplex.Sat -> Unknown3
      )
      end
    
    method assert_neq_and_reduce v1 v2 =
      self#do_and_reduce (fun () -> self#assert_neq v1 v2)
      
    method assume_neq (t1: termnode) (t2: termnode) = self#reduce; self#assert_neq_and_reduce t1#value t2#value

    method assert_eq v1 v2 =
      if verbosity > 7 then trace "assert_eq %s %s" (v1#pprint) (v2#pprint);
      self#assert_eq_core false v1 v2
    
    method assert_eq_core fromSimplex v1 v2 =
      (* printff "assert_eq %s %s\n" (v1#pprint) (v2#pprint); *)
      if v1 = v2 then
      begin
        (* print_endline "assert_eq: values already the same"; *)
        Valid3
      end
      else if v1#neq v2 then
      begin
        Unsat3
      end
      else
      begin
        (* print_endline "assert_eq: merging v1 into v2"; *)
        if v1#merge_into fromSimplex v2 = Unsat then Unsat3 else Unknown3
      end
    
    val mutable reducing = false
    
    method pump_simplex_eqs =
      let rec iter result =
        match simplex_eqs with
          [] ->
          begin
            match simplex_consts with
              [] -> result
            | (u, c)::consts ->
              simplex_consts <- consts;
              let Some tn = unknown_tag u in
              if verbosity > 7 then trace "Importing constant from Simplex: %s(%s) = %s" tn#pprint (Simplex.print_unknown u) (string_of_num c);
              match (self#assert_eq_core true tn#value (self#get_numnode c)#value, result) with
                (Unsat3, _) -> Unsat3
              | (r, Valid3) -> iter r
              | _ -> iter Unknown3
          end
        | (u1, u2)::eqs ->
          simplex_eqs <- eqs;
          let Some tn1 = unknown_tag u1 in
          let Some tn2 = unknown_tag u2 in
          if verbosity > 7 then trace "Importing equality from Simplex: %s(%s) = %s(%s)" tn1#pprint (Simplex.print_unknown u1) tn2#pprint (Simplex.print_unknown u2);
          match (self#assert_eq_core true tn1#value tn2#value, result) with
            (Unsat3, _) -> Unsat3
          | (r, Valid3) -> iter r
          | _ -> iter Unknown3
      in
      iter Valid3
    
    method reduce0 =
      let rec reduce_step result =
        match redexes with
          [] -> result
        | f::redexes0 ->
          redexes <- redexes0;
          match (f(), result) with
            (Unsat3, _) -> Unsat3
          | (r, Valid3) -> iter r
          | _ -> iter Unknown3
      and iter result =
        match (self#pump_simplex_eqs, result) with
          (Unsat3, _) -> Unsat3
        | (r, Valid3) -> reduce_step r
        | _ -> reduce_step Unknown3
      in
      reducing <- true;
      let result = iter Valid3 in
      reducing <- false;
      result
    
    method reduce =
      let do_trace = verbosity > 4 && redexes <> [] || verbosity > 20 in
      if do_trace then trace_entering "Redux.reduce";
      let result =
      if not reducing then
        unsat <-
            unsat
          ||
              self#reduce0 = Unsat3
            &&
              begin
                printff "%s"
                  begin
                    "redux: INFO: Detected an inconsistency after axiom " ^
                    "instantiations triggered by the construction of new " ^
                    "terms (rather than after adding a new assumption). " ^
                    "This might indicate an inconsistency in the axioms. " ^
                    "Call 'verifast -verbose 10' to diagnose.\n"
                  end;
                true
              end
      in
      if do_trace then trace_exiting "Redux.reduce";
      result
    
    method do_and_reduce action =
      match action() with
        Unsat3 -> Unsat3
      | r ->
        match (r, self#reduce0) with
          (_, Unsat3) -> Unsat3
        | (Valid3, r) -> r
        | _ -> Unknown3
    
    method dump_state =
      (* print_endline ("==== Redux query failed: State report ====");
      List.iter (fun v -> if v#initial_child#value = v then (v#dump_state)) values; *)
      ()
      
    method begin_formal = formal_depth <- formal_depth + 1
    method end_formal = formal_depth <- formal_depth - 1
    method mk_bound (i: int) (s: unit): (symbol, termnode) term = BoundVar i
    method assume_forall (description: string) (pats: ((symbol, termnode) term) list) (tps: unit list) (body: (symbol, termnode) term): unit =
      if tps = [] then ignore (self#assume body) else
      let pats =
        if pats = [] then
          let check_pat pat =
            let env = Array.make (List.length tps) false in
            let rec iter pat =
              match pat with
                App (s, args, _) ->
                List.for_all iter args
              | BoundVar i ->
                env.(i) <- true;
                true
              | NumLit n -> true
              | _ -> false
            in
            if iter pat && List.for_all (fun b -> b) (Array.to_list env) then
              [pat]
            else
              []
          in
          let rec find_terms pat =
            match pat with
              TermNode tn -> []
            | Iff (t1, t2) -> find_terms t1 @ find_terms t2
            | Eq (t1, t2) -> find_terms t1 @ find_terms t2
            | Le (t1, t2) -> find_terms t1 @ find_terms t2
            | Lt (t1, t2) -> find_terms t1 @ find_terms t2
            | Not t -> find_terms t
            | And (t1, t2) -> find_terms t1 @ find_terms t2
            | Or (t1, t2) -> find_terms t1 @ find_terms t2
            | Add (t1, t2) -> find_terms t1 @ find_terms t2
            | Sub (t1, t2) -> find_terms t1 @ find_terms t2
            | Mul (t1, t2) -> find_terms t1 @ find_terms t2
            | NumLit n -> []
            | App (s, args, _) -> check_pat pat
            | IfThenElse (t1, t2, t3) -> []
            | RealLe (t1, t2) -> find_terms t1 @ find_terms t2
            | RealLt (t1, t2) -> find_terms t1 @ find_terms t2
            | True -> []
            | False -> []
            | BoundVar i -> []
            | Implies (t1, t2) -> find_terms t1 @ find_terms t2
          in
          find_terms body
        else
          pats
      in
      if pats = [] then failwith (Printf.sprintf "Redux could not find suitable triggers for axiom %s" (self#pprint body));
      (* printff "Axiom (%s) %s asserted\n" (String.concat ", " (List.map self#pprint pats)) (self#pprint body); *)
      let triggeredCounter = ref 0 in
      axioms <- (description, triggeredCounter)::axioms;
      pats |> List.iter (fun pat ->
        match pat with
          App (symb, args, _) ->
          (* We ignore existing applications of this symbol for now. *)
          symb#add_apply_listener (self :> context) (fun term ->
            (* printff "Axiom %s: toplevel symbol listener triggered\n" (self#pprint body); *)
            let rec match_pats bound_env oldvals pats cont =
              match (oldvals, pats) with
                ([], []) -> cont bound_env
              | (oldval::oldvals, pat::pats) ->
                match_pat bound_env oldval#initial_child#value pat (fun bound_env -> match_pats bound_env oldvals pats cont)
            and match_pat bound_env value pat cont =
              let term = value#initial_child in
              match pat with
                BoundVar i ->
                begin match try_assoc i bound_env with
                  None -> cont ((i, term)::bound_env)
                | Some term' ->
                  if term#value = term'#value then
                    cont bound_env
                  else
                    term#value#add_merge_listener (fun () -> if term#value = term'#value then (cont bound_env; false) else true)
                end
              | App (symb, args, _) ->
                let match_term term =
                  if term#symbol = symb then
                    match_pats bound_env term#children args cont
                in
                value#children |> List.iter match_term;
                value#add_child_listener match_term
              | NumLit n ->
                let nnode = self#get_numnode n in
                if nnode#value = term#value then
                  cont bound_env
                else
                  term#value#add_merge_listener (fun () -> if term#value = nnode#value then (cont bound_env; false) else true)
              | _ -> failwith (Printf.sprintf "Redux does not support subpattern %s; it currently supports only symbol applications and bound variables as subpatterns." (self#pprint pat))
            in
            match_pats [] term#children args (fun bound_env ->
              incr triggeredCounter;
              if verbosity >= 3 then trace "Redux: Axiom %s triggered" description;
              if verbosity >= 4 then trace "Redux: Axiom %s triggered with" (self#pprint body);
              let body = term_subst bound_env body in
              if verbosity >= 4 then List.iter (fun (i, t) -> trace "            bound.%d = %s" i t#pprint) bound_env;
              self#add_redex (fun () ->
                (* printff "Asserting axiom body %s\n" (self#pprint body); *)
                self#assume_core body
              )
            )
          )
        | _ -> failwith "Redux supports only symbol applications at the top level of axiom triggers."
      )
    method simplify (t: (symbol, termnode) term): ((symbol, termnode) term) option = Some (simplify t)
  end
