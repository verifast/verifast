(* This file defines a way to combine two provers following the prover
   API defined in proverapi.ml, the result does itself follow the API. *)

open Proverapi

(* The term for the combined prover is either a term of the first
   prover, a term of the second prover, or one of each in a pair.
   Most of the time, we are in the last case, the two other cases are
   used in the "set_fpclauses" method in which we have only half of
   the information (or when reduce returns None in one of the
   provers). For sorts and symbols, we simply take pairs of sorts and
   pairs of symbols. *)
type ('a, 'b) my_pair = Left of 'a | Right of 'b | Both of ('a * 'b)
let left x = Left x
let right y = Right y

exception No_fst
exception No_snd

let my_fst = function
  | Left x | Both (x, _) -> x
  | Right _ -> raise No_fst

let my_snd = function
  | Right y | Both (_, y) -> y
  | Left _ -> raise No_snd

(* We fully trust both provers so if one of them answers Unsat, we
   consider the result to be Unsat. *)
let combine_assume_result = function
  | (Unsat, _) | (_, Unsat) -> Unsat
  | (Unknown, Unknown) -> Unknown

(* This is used in methods assume and query bellow *)
type combination_strategy =
  | Sync                        (* Always ask both provers, this is
                                   useful for comparing the provers *)
  | Sequence                    (* Run the second prover only if the
                                   first answers Unknown *)
(* other strategies of interest:
     - run the provers in parallel (if one answers unsat, stop the other one)
     - run the provers in sequence but the first is stopped after a timeout *)

(* In Ocaml, we cannot directly pass a polymorphic function as
   argument but we can encapsulate it in a record. These are the
   record types used in function map, map2, and map3 bellow. *)
type poly_map = {f : 'a 'b 'c. ('a, 'b, 'c) context -> 'c -> 'c}
type poly_map2 = {f : 'a 'b 'c. ('a, 'b, 'c) context -> 'c -> 'c -> 'c}
type poly_map3 = {f : 'a 'b 'c. ('a, 'b, 'c) context -> 'c -> 'c -> 'c -> 'c}

(* ['a, 'b, 'c, 'd, 'e, 'f] combined_context is an
   ('a * 'd, 'b * 'e, ('c, 'f) my_pair) context *)
class ['a, 'b, 'c, 'd, 'e, 'f] combined_context (p1 : ('a, 'b, 'c) context)
        (p2: ('d, 'e, 'f) context) (combination_strategy : combination_strategy) =
  let map (r : poly_map) = function
    | Left x -> Left (r.f p1 x)
    | Right y -> Right (r.f p2 y)
    | Both (x, y) -> Both (r.f p1 x, r.f p2 y) in
  let map2 (r : poly_map2) a b = match (a, b) with
    | (Both (a1, a2), Both (b1, b2)) ->
       Both (r.f p1 a1 b1, r.f p2 a2 b2)
    | ((Left a | Both (a, _)), (Left b | Both (b, _))) ->
       Left (r.f p1 a b)
    | ((Right a | Both (_, a)), (Right b | Both (_, b))) ->
       Right (r.f p2 a b)
    | (Left _, Right _) | (Right _, Left _) -> failwith "map2"
  in
  let map3 (r : poly_map3) a b c = match (a, b, c) with
    | (Both (a1, a2), Both (b1, b2), Both (c1, c2)) ->
       Both (r.f p1 a1 b1 c1, r.f p2 a2 b2 c2)
    | ((Left a | Both (a, _)), (Left b | Both (b, _)), (Left c | Both (c, _))) ->
       Left (r.f p1 a b c)
    | ((Right a | Both (_, a)), (Right b | Both (_, b)), (Right c | Both (_, c))) ->
       Right (r.f p2 a b c)
    | _ -> failwith "map3"
  in
object
  (* All methods but "set_fpclauses" are trivial. The
     combination_strategy is used in methods "query" and "assume". *)
  method set_verbosity v =
    p1#set_verbosity v;
    p2#set_verbosity v
  method type_bool = (p1#type_bool, p2#type_bool)
  method type_int = (p1#type_int, p2#type_int)
  method type_real = (p1#type_real, p2#type_real)
  method type_inductive = (p1#type_inductive, p2#type_inductive)
  method mk_boxed_int = map {f = fun p -> p#mk_boxed_int}
  method mk_unboxed_int = map {f = fun p -> p#mk_unboxed_int}
  method mk_boxed_real = map {f = fun p -> p#mk_boxed_real}
  method mk_unboxed_real = map {f = fun p -> p#mk_unboxed_real}
  method mk_boxed_bool = map {f = fun p -> p#mk_boxed_bool}
  method mk_unboxed_bool = map {f = fun p -> p#mk_unboxed_bool}
  method mk_symbol s l (ty1, ty2) k =
    (p1#mk_symbol s (List.map fst l) ty1 k,
     p2#mk_symbol s (List.map snd l) ty2 k)
  method mk_app (s1, s2) l =
    try
      let l1 = List.map my_fst l in
      try
        let l2 = List.map my_snd l in
        Both (p1#mk_app s1 l1, p2#mk_app s2 l2)
      with No_snd ->
        Left (p1#mk_app s1 l1)
    with No_fst ->
      Right (p2#mk_app s2 (List.map my_snd l))
  method mk_true = Both (p1#mk_true, p2#mk_true)
  method mk_false = Both (p1#mk_false, p2#mk_false)
  method mk_and = map2 {f = fun p -> p#mk_and}
  method mk_or = map2 {f = fun p -> p#mk_or}
  method mk_not = map {f = fun p -> p#mk_not}
  method mk_ifthenelse = map3 {f = fun p -> p#mk_ifthenelse}
  method mk_iff = map2 {f = fun p -> p#mk_iff}
  method mk_implies = map2 {f = fun p -> p#mk_implies}
  method mk_eq = map2 {f = fun p -> p#mk_eq}
  method mk_intlit i = Both (p1#mk_intlit i, p2#mk_intlit i)
  method mk_intlit_of_string s = Both (p1#mk_intlit_of_string s, p2#mk_intlit_of_string s)
  method mk_add = map2 {f = fun p -> p#mk_add}
  method mk_sub = map2 {f = fun p -> p#mk_sub}
  method mk_mul = map2 {f = fun p -> p#mk_mul}
  method mk_div = map2 {f = fun p -> p#mk_div}
  method mk_mod = map2 {f = fun p -> p#mk_mod}
  method mk_lt = map2 {f = fun p -> p#mk_lt}
  method mk_le = map2 {f = fun p -> p#mk_le}
  method mk_reallit n = Both (p1#mk_reallit n, p2#mk_reallit n)
  method mk_reallit_of_num n = Both (p1#mk_reallit_of_num n, p2#mk_reallit_of_num n)
  method mk_real_add = map2 {f = fun p -> p#mk_real_add}
  method mk_real_sub = map2 {f = fun p -> p#mk_real_sub}
  method mk_real_mul = map2 {f = fun p -> p#mk_real_mul}
  method mk_real_lt = map2 {f = fun p -> p#mk_real_lt}
  method mk_real_le = map2 {f = fun p -> p#mk_real_le}
  method set_fpclauses ((fc1 : 'b), (fc2 : 'e)) (k : int) cs =
    (* This method is used to register a recursive definition: the function fc is defined by recursion on its
       argument number k; cs is the list of cases; each case is a pair
       composed of a constructor and a function from the other
       function arguments and the constructor parameters to the branch
       body hence the type cs: ('symbol * ('termnode list -> 'termnode
       list -> 'termnode)) list *)
    let fpclause1 ((csym1, csym2), fbody) =
      (csym1,
       fun xs ys ->
       (* we are defining function
          fc1(x_1, ..., x_k-1, csym1(ys), x_k+1, ..., x_n) = f(xs, ys) *)
       my_fst (fbody (List.map left xs) (List.map left ys)))
    in
    let fpclause2 ((csym1, csym2), fbody) =
      (csym2,
       fun xs ys ->
       my_snd (fbody (List.map right xs) (List.map right ys)))
    in
    p1#set_fpclauses fc1 k (List.map fpclause1 cs);
    p2#set_fpclauses fc2 k (List.map fpclause2 cs)
  method pprint t =
    let (s1, s2) = match t with
      | Left x -> (p1#pprint x, "")
      | Right y -> ("", p2#pprint y)
      | Both (x, y) -> (p1#pprint x, p2#pprint y)
    in
    Printf.sprintf "<%s;%s>" s1 s2
  method pprint_sym (s1, s2) = Printf.sprintf "<%s;%s>" (p1#pprint_sym s1) (p2#pprint_sym s2)
  method pprint_sort (s1, s2) = Printf.sprintf "<%s;%s>" (p1#pprint_sort s1) (p2#pprint_sort s2)
  method push = p1#push; p2#push
  method pop = p1#pop; p2#pop
  method assume = function
    | Both (t1, t2) -> begin
        match combination_strategy with
        | Sync ->
           combine_assume_result (p1#assume t1, p2#assume t2)
        | Sequence ->
           begin match p1#assume t1 with
           | Unknown ->
              p2#assume t2
           | Unsat ->
              p2#assert_term t2; Unsat
           end
      end
    | Left _ | Right _ -> failwith "Combineprovers.assume"
  method query = function
    | Both (t1, t2) -> begin
        match combination_strategy with
        | Sync ->
           let r1 = p1#query t1 in
           let r2 = p2#query t2 in
           r1 || r2
        | Sequence ->
           (* Remark: the "||" operator is lazy *)
           p1#query t1 || p2#query t2
      end
    | Left _ | Right _ -> failwith "Combineprovers.query"
  method assert_term = function
    | Both (t1, t2) -> begin
        p1#assert_term t1;
        p2#assert_term t2
      end
    | Left _ | Right _ -> failwith "Combineprovers.assert_term"
  method stats =
    let (s1, l1) = p1#stats in
    let (s2, l2) = p2#stats in
    let combine_stat (s1, i1) (s2, i2) =
      if i1 < i2 then ("P2: " ^ s2, i2)
      else ("P1: " ^ s1, i1)
    in
    let rec combine_stats = function
      | ([], l) | (l, []) -> l
      | (st1 :: l1, st2 :: l2) ->
         combine_stat st1 st2 :: combine_stats (l1, l2)
    in
    (Printf.sprintf "<P1: %s, P2: %s>" s1 s2, combine_stats (l1, l2))
  method begin_formal = p1#begin_formal; p2#begin_formal
  method end_formal = p1#end_formal; p2#end_formal
  method mk_bound i (ty1, ty2) = Both (p1#mk_bound i ty1, p2#mk_bound i ty2)
  method assume_forall s ts tys = function
    | Both (t1, t2) -> begin
        p1#assume_forall s (List.map my_fst ts) (List.map fst tys) t1;
        p2#assume_forall s (List.map my_snd ts) (List.map snd tys) t2
      end
    | Left _ | Right _ -> failwith "Combineprovers.assume_forall"
  method simplify = function
    | Left x ->
       begin match p1#simplify x with Some xx -> Some (Left xx) | None -> None end
    | Right y ->
       begin match p2#simplify y with Some yy -> Some (Right yy) | None -> None end
    | Both (x, y) ->
       begin match (p1#simplify x, p2#simplify y) with
       | (Some xx, Some yy) -> Some (Both (xx, yy))
       | (Some xx, None) -> Some (Left xx)
       | (None, Some yy) -> Some (Right yy)
       | (None, None) -> None
       end
end

let combine
      (p1 : ('a, 'b, 'c) context)
      (p2 : ('d, 'e, 'f) context)
      (combination_strategy : combination_strategy)
    : ('a * 'd, 'b * 'e, ('c, 'f) my_pair) context =
  (new combined_context p1 p2 combination_strategy
   : ('a, 'b, 'c, 'd, 'e, 'f) combined_context :> ('a * 'd, 'b * 'e, ('c, 'f) my_pair) context)
