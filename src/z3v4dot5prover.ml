open Proverapi
open Num
open Printf

let fprintff format = kfprintf (fun chan -> flush chan) format
let printff format = fprintff stdout format

type sexpr = Atom of string | List of sexpr list | String of char list

let parse_sexpr text =
  let rec parse_sexpr i =
    match text.[i] with
      '(' -> let (es, i) = parse_sexprs (i + 1) in (List es, i)
    | ' '|'\r'|'\n'|'\t' -> parse_sexpr (i + 1)
    | c -> parse_atom i (i + 1)
  and parse_atom start i =
    if i = String.length text then
      (Atom (String.sub text start (i - start)), i)
    else
      match text.[i] with
        ')' | ' ' | '\r' | '\n' | '\t' -> (Atom (String.sub text start (i - start)), i)
      | c -> parse_atom start (i + 1)
  and parse_sexprs i =
    match text.[i] with
      ')' -> ([], i + 1)
    | ' '|'\r'|'\n'|'\t' -> parse_sexprs (i + 1)
    | c -> let (e, i) = parse_sexpr i in let (es, i) = parse_sexprs i in (e::es, i)
  in
  let (e, _) = parse_sexpr 0 in e

let rec simplify e =
  match e with
    Atom "chars_nil" -> String []
  | List [Atom "chars_cons" as a0; Atom a as a1; e1] ->
    begin try
      let c = int_of_string a in
      match simplify e1 with
        String cs when 0 <= c && c < 255 -> String (char_of_int c::cs)
      | e1 -> List [a0; a1; e1]
    with Failure _ -> List [a0; a1; simplify e1]
    end
  | List es -> List (List.map simplify es)
  | a -> a

let rec string_of_sexpr e =
  let string_of_char c =
    if int_of_char c < 32 then
      match c with
        '\r' -> "\\r"
      | '\n' -> "\\n"
      | '\t' -> "\\t"
      | c -> Printf.sprintf "\\%o" (int_of_char c)
    else
      Printf.sprintf "%c" c
  in
  match e with
    Atom a -> a
  | List es -> "(" ^ String.concat " " (List.map string_of_sexpr es) ^ ")"
  | String cs -> "\"" ^ String.concat "" (List.map string_of_char cs) ^ "\""

module Z3 = struct

    let mk_func_decl ctxt symbol sorts sort = Z3native.mk_func_decl ctxt symbol (Array.length sorts) (Array.to_list sorts) sort
    let mk_fresh_func_decl ctxt name sorts sort = Z3native.mk_fresh_func_decl ctxt name (Array.length sorts) (Array.to_list sorts) sort
    let mk_app ctxt f args = Z3native.mk_app ctxt f (Array.length args) (Array.to_list args)
    let mk_pattern ctxt ts = Z3native.mk_pattern ctxt (Array.length ts) (Array.to_list ts)
    let mk_forall ctxt weight pats sorts names body =
      if Array.length names <> Array.length sorts then failwith "Internal error";
      Z3native.mk_forall ctxt weight (Array.length pats) (Array.to_list pats) (Array.length sorts) (Array.to_list sorts) (Array.to_list names) body

end

class z3_context () =
  let () = Z3native.global_param_set "smt.auto_config" "false" in
  let () = Z3native.global_param_set "smt.mbqi" "false" in
  let cfg = Z3native.mk_config () in
  let () = Z3native.set_param_value cfg "auto_config" "false" in
  let () = Z3native.set_param_value cfg "model" "false" in
  let () = Z3native.set_param_value cfg "type_check" "true" in
  let () = Z3native.set_param_value cfg "well_sorted_check" "true" in
(*
  let _ = Z3native.set_param_value cfg "VERBOSE" "1000" in
  let _ = Z3native.set_param_value cfg "STATISTICS" "true" in
*)
  let ctxt = Z3native.mk_context cfg in
  (* let () = Gc.finalise Z3native.del_context ctxt in *)
  (* let () = Gc.finalise Z3native.del_config cfg in *)
  (* let _ = Z3native.trace_to_stdout ctxt in *)
  let bool_type = Z3native.mk_bool_sort ctxt in
  let int_type = Z3native.mk_int_sort ctxt in
  let real_type = Z3native.mk_real_sort ctxt in
  let ttrue = Z3native.mk_true ctxt in
  let tfalse = Z3native.mk_false ctxt in
  (* HACK: for now, all inductive values have the same Z3 type. *)
  let inductive_type = Z3native.mk_uninterpreted_sort ctxt (Z3native.mk_string_symbol ctxt "inductive") in
  let tag_func = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "ctortag") [| inductive_type |] int_type in
  let ctor_counter = ref 0 in
  let get_ctor_tag () = let k = !ctor_counter in ctor_counter := k + 1; k in
  let mk_unary_app f t = Z3.mk_app ctxt f [| t |] in
  let solver = Z3native.mk_simple_solver ctxt in
  let assert_term t =
    Z3native.solver_assert ctxt solver t;
    match Z3enums.lbool_of_int (Z3native.solver_check ctxt solver) with
      Z3enums.L_FALSE -> Unsat
    | Z3enums.L_UNDEF -> Unknown
    | Z3enums.L_TRUE -> Unknown
  in
  let query t =
    Z3native.solver_push ctxt solver;
    let result = assert_term (Z3native.mk_not ctxt t) = Unsat in
    Z3native.solver_pop ctxt solver 1;
    result
  in
  let assume_is_inverse f1 f2 dom2 =
    let name = Z3native.mk_int_symbol ctxt 0 in
    let x = Z3native.mk_bound ctxt 0 dom2 in
    let app1 = Z3.mk_app ctxt f2 [| x |] in
    let app2 = Z3.mk_app ctxt f1 [| app1 |] in
    let pat = Z3.mk_pattern ctxt [| app1 |] in
    Z3native.solver_assert ctxt solver (Z3.mk_forall ctxt 0 [| pat |] [| dom2 |] [| name |] (Z3native.mk_eq ctxt app2 x))
  in
  let boxed_int = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "(intbox)") [| int_type |] inductive_type in
  let unboxed_int = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "(int)") [| inductive_type |] int_type in
  let () = assume_is_inverse unboxed_int boxed_int int_type in
  let () = assume_is_inverse boxed_int unboxed_int inductive_type in
  let boxed_bool = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "(boolbox)") [| bool_type |] inductive_type in
  let unboxed_bool = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "(bool)") [| inductive_type |] bool_type in
  let () = assume_is_inverse unboxed_bool boxed_bool bool_type in
  let boxed_real = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "(realbox)") [| real_type |] inductive_type in
  let unboxed_real = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "(real)") [| inductive_type |] real_type in
  let () = assume_is_inverse unboxed_real boxed_real real_type in
  let () = assume_is_inverse boxed_real unboxed_real inductive_type in
  let div = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "div") [| int_type; int_type |] int_type in
  let modulo = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt "mod") [| int_type; int_type |] int_type in
  object
    val mutable verbosity = 0
    method set_verbosity v = verbosity <- v
    method type_bool = bool_type
    method type_int = int_type
    method type_real = real_type
    method type_inductive = inductive_type
    method mk_boxed_int t = Z3.mk_app ctxt boxed_int [| t |]
    method mk_unboxed_int t = Z3.mk_app ctxt unboxed_int [| t |]
    method mk_boxed_bool t = Z3.mk_app ctxt boxed_bool [| t |]
    method mk_unboxed_bool t = Z3.mk_app ctxt unboxed_bool [| t |]
    method mk_boxed_real t = Z3.mk_app ctxt boxed_real [| t |]
    method mk_unboxed_real t = Z3.mk_app ctxt unboxed_real [| t |]
    method mk_symbol name domain range kind =
      let tps = Array.of_list domain in
      let c = Z3.mk_func_decl ctxt (Z3native.mk_string_symbol ctxt name) tps range in
      begin
        match kind with
          Ctor k ->
          begin
            let tag = Z3native.mk_int ctxt (get_ctor_tag()) int_type in
            let xs = Array.init (Array.length tps) (fun j -> Z3native.mk_bound ctxt j tps.(j)) in
            let app = Z3.mk_app ctxt c xs in
            if domain = [] then
              Z3native.solver_assert ctxt solver (Z3native.mk_eq ctxt (mk_unary_app tag_func app) tag)
            else
            begin
              let names = Array.init (Array.length tps) (Z3native.mk_int_symbol ctxt) in
              let pat = Z3.mk_pattern ctxt [| app |] in
              (* disjointness axiom *)
              (* (forall (x1 ... xn) (PAT (C x1 ... xn)) (EQ (tag (C x1 ... xn)) Ctag)) *)
              Z3native.solver_assert ctxt solver (Z3.mk_forall ctxt 0 [| pat |] tps names (Z3native.mk_eq ctxt (mk_unary_app tag_func app) tag));
            end
          end;
          for i = 0 to Array.length tps - 1 do
            let names = Array.init (Array.length tps) (Z3native.mk_int_symbol ctxt) in
            let xs = Array.init (Array.length tps) (fun j -> Z3native.mk_bound ctxt j tps.(j)) in
            let app = Z3.mk_app ctxt c xs in
            let finv = Z3.mk_fresh_func_decl ctxt "ctorinv" [| inductive_type |] tps.(i) in
            let pat = Z3.mk_pattern ctxt [| app |] in
            (* injectiveness axiom *)
            (* (forall (x1 ... x2) (PAT (C x1 ... xn)) (EQ (finv (C x1 ... xn)) xi)) *)
            Z3native.solver_assert ctxt solver (Z3.mk_forall ctxt 0 [| pat |] tps names (Z3native.mk_eq ctxt (mk_unary_app finv app) (xs.(i))))
          done
        | Fixpoint j -> ()
        | Uninterp -> ()
      end;
      c
          
    method set_fpclauses fc k cs =
      List.iter
        (fun (csym, fbody) ->
           let n = Z3native.get_domain_size ctxt fc in
           let ftps = Array.init n (Z3native.get_domain ctxt fc) in
           let m = Z3native.get_domain_size ctxt csym in
           let ctps = Array.init m (Z3native.get_domain ctxt csym) in
           let l = m + n - 1 in
           let tps = Array.init l (fun i -> if i < m then ctps.(i) else if i < m + k then ftps.(i - m) else ftps.(i + 1 - m)) in
           let xs = Array.init l (fun i -> Z3native.mk_bound ctxt i tps.(i)) in
           let names = Array.init l (Z3native.mk_int_symbol ctxt) in
           let cargs = Array.init m (fun i -> xs.(i)) in
           let capp = Z3.mk_app ctxt csym cargs in
           let fargs = Array.init n (fun j -> if j < k then xs.(m + j) else if j = k then capp else xs.(m + j - 1)) in
           let fapp = Z3.mk_app ctxt fc fargs in
           let pat = Z3.mk_pattern ctxt [| fapp |] in
           let body = fbody (Array.to_list fargs) (Array.to_list cargs) in
           if l = 0 then
             Z3native.solver_assert ctxt solver (Z3native.mk_eq ctxt fapp body)
           else
             (* (FORALL (x1 ... y1 ... ym ... xn) (PAT (f x1 ... (C y1 ... ym) ... xn)) (EQ (f x1 ... (C y1 ... ym) ... xn) body)) *)
             Z3native.solver_assert ctxt solver (Z3.mk_forall ctxt 0 [| pat |] tps names (Z3native.mk_eq ctxt fapp body))
        )
        cs

    method mk_app s ts = Z3.mk_app ctxt s (Array.of_list ts)
    method mk_true = ttrue
    method mk_false = tfalse
    method mk_and t1 t2 = Z3native.mk_and ctxt 2 [t1; t2]
    method mk_or t1 t2 = Z3native.mk_or ctxt 2 [t1; t2]
    method mk_not t = Z3native.mk_not ctxt t
    method mk_ifthenelse t1 t2 t3 = Z3native.mk_ite ctxt t1 t2 t3
    method mk_iff t1 t2 = Z3native.mk_eq ctxt t1 t2
    method mk_implies t1 t2 = Z3native.mk_implies ctxt t1 t2
    method mk_eq t1 t2 = Z3native.mk_eq ctxt t1 t2
    method mk_intlit n =
      if n land (lnot 0x7fffffff) = 0 then (* See issue #138 *)
        Z3native.mk_int ctxt n int_type
      else
        Z3native.mk_numeral ctxt (string_of_int n) int_type
    method mk_intlit_of_string s = Z3native.mk_numeral ctxt s int_type
    method mk_add t1 t2 = Z3native.mk_add ctxt 2 [t1; t2]
    method mk_sub t1 t2 = Z3native.mk_sub ctxt 2 [t1; t2]
    method mk_mul t1 t2 = Z3native.mk_mul ctxt 2 [t1; t2]
    method mk_div t1 t2 = Z3.mk_app ctxt div [| t1; t2 |]
    method mk_mod t1 t2 = Z3.mk_app ctxt modulo [| t1; t2 |]
    method mk_lt t1 t2 = Z3native.mk_lt ctxt t1 t2
    method mk_le t1 t2 = Z3native.mk_le ctxt t1 t2
    method mk_reallit n = Z3native.mk_int ctxt n real_type
    method mk_reallit_of_num n = Z3native.mk_numeral ctxt (string_of_num n) real_type
    method mk_real_add t1 t2 = Z3native.mk_add ctxt 2 [t1; t2]
    method mk_real_sub t1 t2 = Z3native.mk_sub ctxt 2 [t1; t2]
    method mk_real_mul t1 t2 = Z3native.mk_mul ctxt 2 [t1; t2]
    method mk_real_lt t1 t2 = Z3native.mk_lt ctxt t1 t2
    method mk_real_le t1 t2 = Z3native.mk_le ctxt t1 t2
    method get_type t = Z3native.get_sort ctxt t
    method pprint t = string_of_sexpr (simplify (parse_sexpr (Z3native.ast_to_string ctxt t)))
    method pprint_sort (s : Z3native.sort) = Z3native.ast_to_string ctxt s
    method pprint_sym (s : Z3native.func_decl) = Z3native.ast_to_string ctxt s
    method assert_term t = Z3native.solver_assert ctxt solver t
    method query t =
      (* printf "Z3prover.query (%s)... " (Z3native.ast_to_string ctxt t); *)
      let t0 = if verbosity >= 1 then Perf.time() else 0.0 in
      let result = query t in
      if verbosity >= 1 then begin let t1 = Perf.time() in Printf.printf "%10.6fs: Z3 query %s: %.6f seconds\n" t0 (Z3native.ast_to_string ctxt t) (t1 -. t0) end;
      result
    method assume t =
      (* printf "Z3prover.assume (%s)\n" (Z3native.ast_to_string ctxt t); *)
      let t0 = if verbosity >= 1 then Perf.time() else 0.0 in
      let result = assert_term t in
      if verbosity >= 1 then begin let t1 = Perf.time() in Printf.printf "%10.6fs: Z3 assume %s: %.6f seconds\n" t0 (Z3native.ast_to_string ctxt t) (t1-. t0) end;
      result
    method push =
      Z3native.solver_push ctxt solver
    method pop =
      Z3native.solver_pop ctxt solver 1
    method perform_pending_splits (cont: Z3native.ast list -> bool) = cont []
    method stats: string * (string * int64) list = "(no statistics for Z3)", []
    method begin_formal = ()
    method end_formal = ()
    method mk_bound (i: int) (tp: Z3native.sort) = Z3native.mk_bound ctxt i tp
    method assume_forall (description: string) (triggers: Z3native.ast list) (tps: Z3native.sort list) (body: Z3native.ast): unit = 
      if List.length tps = 0 then
        Z3native.solver_assert ctxt solver body
      else
        let pats = (
          match triggers with
            [] -> [| |]
           | _ -> [|(Z3.mk_pattern ctxt (Array.of_list triggers))|]
        ) in
        let quant = (Z3.mk_forall ctxt 0 pats (Array.of_list tps) (Array.init (List.length tps) (Z3native.mk_int_symbol ctxt)) (body)) in
        (* printf "%s\n" (string_of_sexpr (simplify (parse_sexpr (Z3native.ast_to_string ctxt quant)))); *)
        Z3native.solver_assert ctxt solver quant
   method simplify (t: Z3native.ast): Z3native.ast option = Some(Z3native.simplify ctxt t)
  end
