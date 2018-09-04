(* #load "nums.cma" *)

open Big_int
open Num

let stopwatch = Stopwatch.create ()

let rec try_assoc k0 kvs =
  match kvs with
    [] -> None
  | (k, v)::kvs ->
    if k = k0 then Some v else try_assoc k0 kvs

type ('a, 'b) unknown_pos =
  Row of 'a | Column of 'b
  
type result = Sat | Unsat

class ['tag] unknown (context: 'tag simplex) (name: string) (restricted: bool) (tag: 'tag option) (nonzero: bool) =
  object (self)
    val mutable pos: ('tag row, 'tag column) unknown_pos option = None
    
    method name = name
    method tag = tag
    method restricted = restricted
    method nonzero = nonzero
    method set_pos p =
      let oldpos = pos in
      context#register_popaction (fun () -> pos <- oldpos);
      pos <- Some p
    method pos = match pos with None -> assert false | Some pos -> pos
    method print =
      if restricted then "[" ^ name ^ "]" else name
  end
and ['tag] coeff (context: 'tag simplex) v =
  object (self)
    val mutable value: num = v
    
    method value = value
    method set_value v =
      let oldvalue = value in
      context#register_popaction (fun () -> value <- oldvalue);
      value <- v
    method add a = self#set_value (value +/ a)
    method divide_by a = self#set_value (value // a)
  end
and ['tag] row context own c =
  object (self)
    val mutable owner: 'tag unknown = own
    val mutable constant: num = c
    val mutable terms: ('tag column * 'tag coeff) list = []
    val mutable closed: bool = false

    method print =
      owner#print ^ " = " ^ string_of_num constant ^ " + " ^ String.concat " + " (List.map (fun (col, coef) -> string_of_num coef#value ^ "*" ^ col#owner#print) terms)
    method constant = constant
    method owner = owner
    method closed = closed
    method set_owner u =
      let oldowner = owner in
      context#register_popaction (fun () -> owner <- oldowner);
      owner <- u
    method terms = terms
    method set_constant v =
      let oldconstant = constant in
      context#register_popaction (fun () -> constant <- oldconstant);
      constant <- v
    method add_row a r =
      self#set_constant (constant +/ (r#constant */ a));
      List.iter (fun (col, b) -> self#add (b#value */ a) col) r#terms
    method set_terms ts =
      let oldterms = terms in
      context#register_popaction (fun () -> terms <- oldterms);
      terms <- ts
    method add a col =
      match try_assoc col terms with
        None -> let coef = new coeff context a in self#set_terms ((col, coef)::terms); col#term_added (self :> 'tag row) coef
      | Some coef -> coef#add a
        
    method solve_for column =
      let c0 = minus_num (List.assoc column terms)#value in
      self#set_constant (constant // c0);
      List.iter
        (fun (col, coef) ->
           if col = column then
             coef#set_value (num_of_int (-1) // c0)
           else
             coef#divide_by c0
        )
        terms
    
    method try_close =
      if sign_num constant = 0 && List.for_all (fun (col, coef) -> col#dead || sign_num coef#value = 0 || col#owner#restricted && sign_num coef#value < 0) terms then self#close
    
    method close =
      assert (not closed);
      context#register_popaction (fun () -> closed <- false);
      closed <- true;
      List.iter (fun (col, coef) -> if not col#dead && sign_num coef#value < 0 then col#die) terms
    
    method live_terms =
      List.filter (fun (col, coef) -> not col#dead && sign_num coef#value <> 0) terms

    method propagate_eq =
      let live_terms = self#live_terms in
      begin
        match live_terms with
          [(col, coef)] ->
          if owner#tag <> None && col#owner#tag <> None && sign_num constant = 0 && coef#value =/ num_of_int 1 then context#propagate_equality owner col#owner
        | [] -> if owner#tag <> None then context#propagate_eq_constant owner constant else if owner#nonzero && sign_num constant = 0 then context#set_unsat
        | _ -> ()
      end;
      if owner#tag <> None && not context#unsat then begin
        match live_terms with
          [] -> ()
        | (col0, coef0)::_ ->
          let row_equals (c1, ts1) (c2, ts2) =
            c1 =/ c2 &&
            List.length ts1 = List.length ts2 &&
            let rec iter ts =
              match ts with
                [] -> true
              | (col0, coef0)::ts ->
                begin
                match try_assoc col0 ts2 with
                  None -> false
                | Some coef1 -> coef0#value =/ coef1#value && iter ts
                end
            in
            iter ts1
          in
          List.iter
            (fun (row, coef1) ->
               if
                 row <> (self :> 'tag row) &&
                 row#owner#tag <> None &&
                 coef0#value =/ coef1#value &&
                 row_equals (constant, live_terms) (row#constant, row#live_terms)
               then
                 context#propagate_equality owner row#owner
            )
            col0#terms
      end
  end
and ['tag] column context own =
  object (self)
    val mutable owner: 'tag unknown = own
    val mutable terms: ('tag row * 'tag coeff) list = []
    val mutable dead: bool = false
    
    method owner = owner
    method set_owner u =
      let oldowner = owner in
      context#register_popaction (fun () -> owner <- oldowner);
      owner <- u
    method terms = terms
    method term_added row coef =
      let oldterms = terms in
      context#register_popaction (fun () -> terms <- oldterms);
      terms <- (row, coef)::terms
    method dead = dead
    
    method die =
      assert (not dead);
      context#register_popaction (fun () -> dead <- false);
      dead <- true;
      if owner#nonzero then context#set_unsat else
      begin
      if owner#tag <> None then
        context#propagate_eq_constant owner (num_of_int 0);
      List.iter (fun (row, coef) -> if (row#owner#tag <> None || row#owner#nonzero) && sign_num coef#value <> 0 then row#propagate_eq) terms;
      List.iter (fun (row, coef) -> if row#owner#restricted && not row#closed && sign_num coef#value > 0 then row#try_close) terms
      end
  end
and ['tag] simplex () =
  object (self)
    val mutable eq_listener = (fun _ _ -> ())
    val mutable const_listener = (fun _ _ -> ())
    val mutable uniqueCounter: int = 0
    val mutable unsat: bool = false
    val mutable rows: 'tag row list = []
    val mutable columns: 'tag column list = []
    val mutable popactions: (unit -> unit) list = []
    val mutable popstack = []
    
    method unsat = unsat
    method set_unsat = unsat <- true
    
    method register_listeners feqs fconsts =
      eq_listener <- feqs;
      const_listener <- fconsts

    method register_popaction f = popactions <- f::popactions
    method push =
      assert (not unsat);
      popstack <- (rows, columns, popactions)::popstack;
      popactions <- []
    method pop =
      List.iter (fun f -> f()) popactions;
      match popstack with
        [] -> assert false
      | (oldrows, oldcolumns, oldpopactions)::oldpopstack ->
        unsat <- false;
        rows <- oldrows;
        columns <- oldcolumns;
        popactions <- oldpopactions;
        popstack <- oldpopstack

    method get_unique_index () =
      let u = uniqueCounter in
      uniqueCounter <- u + 1;
      u
    
    method print =
      "Rows:\n" ^ String.concat "" (List.map (fun row -> row#print ^ "\n") rows)

    method pivot (row: 'tag row) (col: 'tag column) =
      let rowOwner = row#owner in
      let colOwner = col#owner in
      row#set_owner colOwner;
      rowOwner#set_pos (Column col);
      col#set_owner rowOwner;
      colOwner#set_pos (Row row);
      row#solve_for col;
      List.iter
        (fun (r, coef) ->
           if r = row then
             ()
           else
             let v = coef#value in
             coef#set_value (num_of_int 0);
             r#add_row v row
        )
        col#terms

    method alloc_unknown name tag =
      let u = new unknown (self :> 'tag simplex) name false (Some tag) false in
      let col = new column (self :> 'tag simplex) u in
      u#set_pos (Column col);
      columns <- col::columns;
      u
      
    method find_pivot_row sign col =
      let rec iter cand ts =
        match ts with
          [] -> cand
        | (r, coef)::ts ->
          if r#owner#restricted && sign_num coef#value * sign < 0 then
            let delta = r#constant // abs_num coef#value in
            let new_cand =
              match cand with
                None -> Some (r, delta)
              | Some (r', delta') ->
                if delta' <=/ delta then Some (r', delta') else Some (r, delta)
            in
            iter new_cand ts
          else
            iter cand ts
      in
      iter None col#terms

    method sign_of_max_of_unknown (u: 'tag unknown): int =
      match u#pos with
        Row r -> self#sign_of_max_of_row r
      | Column col ->
        begin
          match self#find_pivot_row 1 col with
            None -> (* column is manifestly unbounded. *)
            1
          | Some (row, _) ->
            self#pivot row col;
            self#sign_of_max_of_row row
        end

    method sign_of_max_of_row row =
      let rec maximize_row () =
        if sign_num row#constant > 0 then
          1
        else
        begin
          (* Note: in the Simplify TR, columns with unrestricted owners are preferred over columns with restricted owners. *)
          let rec find_pivot_col ts =
            match ts with
              [] -> None
            | (col, coef)::ts ->
              if col#dead then
                find_pivot_col ts
              else
                let sign = sign_num coef#value in
                if sign <> 0 && (not col#owner#restricted || sign > 0) then
                  Some (col, sign)
                else
                  find_pivot_col ts
          in
          match find_pivot_col row#terms with
            None -> (* row is manifestly maximized  *) sign_num row#constant  
          | Some (col, sign) ->
            match self#find_pivot_row sign col with
              None ->
              (* col is manifestly unbounded *)
              self#pivot row col;
              1
            | Some (r, _) ->
              self#pivot r col;
              maximize_row()
        end
      in
      maximize_row()
    
    method propagate_equality u1 u2 =
      eq_listener u1 u2

    method propagate_eq_constant u n =
      const_listener u n
      
    method assert_ge (c: num) (ts: (num * 'tag unknown) list) =
      Stopwatch.start stopwatch;
      let y = new unknown (self :> 'tag simplex) ("r" ^ string_of_int (self#get_unique_index())) true None false in
      let row = new row (self :> 'tag simplex) y c in
      rows <- row::rows;
      y#set_pos (Row row);
      List.iter
        (fun (a, u) ->
           match u#pos with
             Row r ->
             row#add_row a r
           | Column col ->
             row#add a col
        )
        ts;
      let result =
        match self#sign_of_max_of_row row with
          -1 -> Unsat
        | 0 -> row#close; if unsat then Unsat else Sat
        | 1 -> Sat
        | _ -> assert false
      in
      Stopwatch.stop stopwatch;
      result
    
    method get_ticks: int64 = Stopwatch.ticks stopwatch
    
    method assert_eq (c: num) (ts: (num * 'tag unknown) list) =
      match self#assert_ge c ts with
        Unsat -> Unsat
      | Sat -> self#assert_ge (minus_num c) (List.map (fun (a, u) -> (minus_num a, u)) ts)
    
    method assert_neq (c: num) (ts: (num * 'tag unknown) list) =
      let u = new unknown (self :> 'tag simplex) ("nz" ^ string_of_int (self#get_unique_index())) false None true in
      let col = new column (self :> 'tag simplex) u in
      u#set_pos (Column col);
      columns <- col::columns;
      self#assert_eq c ((num_of_int (-1), u)::ts)
  end

type 'tag simplex0 = <
  register_listeners:
    ('tag unknown -> 'tag unknown -> unit) ->
    ('tag unknown -> Num.num -> unit) ->
    unit;
  push: unit;
  pop: unit;
  alloc_unknown: string -> 'tag -> 'tag unknown;
  assert_ge: Num.num -> (Num.num * 'tag unknown) list -> result;
  assert_eq: Num.num -> (Num.num * 'tag unknown) list -> result;
  assert_neq: Num.num -> (Num.num * 'tag unknown) list -> result;
  get_ticks: int64;
  print: string
>

let print_unknown u = u#print
let unknown_tag (u: 'tag unknown): 'tag option = u#tag
let new_simplex () = (new simplex () :> 'tag simplex0)