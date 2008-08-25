(* #load "nums.cma" *)

open Num

let rec try_assoc k0 kvs =
  match kvs with
    [] -> None
  | (k, v)::kvs ->
    if k = k0 then Some v else try_assoc k0 kvs

type ('a, 'b) unknown_pos =
  Row of 'a | Column of 'b
  
type result = Sat | Unsat

class unknown (name: string) (restr: bool) =
  object (self)
    val restricted = restr
    val mutable pos: (row, column) unknown_pos option = None
    
    method name = name
    method restricted = restricted
    method set_pos p = pos <- Some p
    method pos = match pos with None -> assert false | Some pos -> pos
    method print =
      if restricted then "[" ^ name ^ "]" else name
  end
and coeff v =
  object (self)
    val mutable value: num = v
    
    method value = value
    method set_value v = value <- v
    method add a = value <- value +/ a
    method divide_by a = value <- value // a
  end
and row own c =
  object (self)
    val mutable owner: unknown = own
    val mutable constant: num = c
    val mutable terms: (column * coeff) list = []

    method print =
      owner#print ^ " = " ^ string_of_num constant ^ " + " ^ String.concat " + " (List.map (fun (col, coef) -> string_of_num coef#value ^ "*" ^ col#owner#print) terms)
    method constant = constant
    method owner = owner
    method set_owner u = owner <- u
    method terms = terms
    method add_row a r =
      constant <- constant +/ (r#constant */ a);
      List.iter (fun (col, b) -> self#add (b#value */ a) col) r#terms
    method add a col =
      match try_assoc col terms with
        None -> let coef = new coeff a in terms <- (col, coef)::terms; col#term_added (self :> row) coef
      | Some coef -> coef#add a
        
    method solve_for column =
      let c0 = minus_num (List.assoc column terms)#value in
      constant <- constant // c0;
      List.iter
        (fun (col, coef) ->
           if col = column then
             coef#set_value (num_of_int (-1) // c0)
           else
             coef#divide_by c0
        )
        terms
  end
and column own =
  object (self)
    val mutable owner: unknown = own
    val mutable terms: (row * coeff) list = []
    
    method owner = owner
    method set_owner u = owner <- u
    method terms = terms
    method term_added row coef =
      terms <- (row, coef)::terms
  end
and simplex =
  object (self)
    val mutable uniqueCounter: int = 0
    val mutable rows: row list = []
    val mutable columns: column list = []
    
    method get_unique_index () =
      let u = uniqueCounter in
      uniqueCounter <- u + 1;
      u
    
    method print =
      "Rows:\n" ^ String.concat "" (List.map (fun row -> row#print ^ "\n") rows)

    method pivot (row: row) (col: column) =
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

    method alloc_unknown name =
      let u = new unknown name false in
      let col = new column u in
      u#set_pos (Column col);
      columns <- col::columns;
      u
      
    method assert_ge (c: num) (ts: (num * unknown) list) =
      let y = new unknown ("r" ^ string_of_int (self#get_unique_index())) true in
      let row = new row y c in
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
      let rec maximize_row () =
        print_endline "Maximizing the new row...";
        print_string self#print;
        if sign_num row#constant >= 0 then
          Sat
        else
        begin
          let rec find_pivot_col ts =
            match ts with
              [] -> None
            | (col, coef)::ts ->
              if col#owner#restricted then
                if sign_num coef#value > 0 then
                  Some col
                else
                  find_pivot_col ts
              else
                if sign_num coef#value <> 0 then
                  Some col
                else
                  find_pivot_col ts
          in
          match find_pivot_col row#terms with
            None -> Unsat  (* row is manifestly maximized at a negative value *)
          | Some col ->
            let rec find_pivot_row cand ts =
              match ts with
                [] -> cand
              | (r, coef)::ts ->
                if r#owner#restricted then
                  if sign_num coef#value < 0 then
                    let delta = r#constant // minus_num coef#value in
                    let new_cand =
                      match cand with
                        None -> Some (r, delta)
                      | Some (r', delta') ->
                        if delta' <=/ delta then Some (r', delta') else Some (r, delta)
                    in
                    find_pivot_row new_cand ts
                  else
                    find_pivot_row cand ts
                else
                  find_pivot_row cand ts
            in
            match find_pivot_row None col#terms with
              None ->
              (* col is manifestly unbounded *)
              self#pivot row col;
              Sat
            | Some (r, _) ->
              self#pivot r col;
              maximize_row()
        end
      in
      maximize_row()

  end

let _ =
  let s = new simplex in
  let x = s#alloc_unknown "x" in
  let y = s#alloc_unknown "y" in
  let z = s#alloc_unknown "z" in
  
  let assert_ge c1 ts1 c2 ts2 =
    s#assert_ge (num_of_int (c2 - c1)) (List.map (fun (n, u) -> (num_of_int (-n), u)) ts1 @ List.map (fun (n, u) -> (num_of_int n, u)) ts2)
  in
  
  assert (assert_ge 0 [] 0 [1, x] = Sat); (* 0 <= x *)
  print_string s#print;
  assert (assert_ge 1 [1, x] 0 [1, y] = Sat); (* x < y *)
  print_string s#print;
  assert (assert_ge 0 [1, y] 0 [] = Unsat); (* y <= 0 *)
  
  ()

let _ =
  let s = new simplex in
  let x = s#alloc_unknown "x" in
  let y = s#alloc_unknown "y" in
  let z = s#alloc_unknown "z" in
  
  let assert_ge c1 ts1 c2 ts2 =
    s#assert_ge (num_of_int (c2 - c1)) (List.map (fun (n, u) -> (num_of_int (-n), u)) ts1 @ List.map (fun (n, u) -> (num_of_int n, u)) ts2)
  in
  
  assert (assert_ge 0 [] 0 [1, x] = Sat); (* 0 <= x *)
  print_string s#print;
  assert (assert_ge 1 [1, x] 0 [1, y] = Sat); (* x < y *)
  print_string s#print;
  assert (assert_ge 1 [1, y] 0 [1, z] = Sat); (* y < z *)
  print_string s#print;
  assert (assert_ge 0 [1, z] 0 [1, y] = Unsat); (* z <= y *)
  
  ()