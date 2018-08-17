open Proverapi
open Num
open Printf

let fprintff format = kfprintf (fun chan -> flush chan) format
let printff format = fprintff stdout format

let display_version() =
  begin
    let (major, minor, build, revision)=Z3.get_version() in
    printf "Unsing Z3 version %d.%d.%d.%d.\n" major minor build revision;
  end;;

let rec ast_contains_var_core ctxt ref ast =
  begin
    printf "ast_contains_var ast: %s\n%!" (Z3.ast_to_string ctxt ast);
    match (Z3.get_ast_kind ctxt ast) with
      Z3.APP_AST -> ( printf "pattern.App\n%!";
                      let args = Z3.get_app_args ctxt (Z3.to_app ctxt ast) in
                      Array.iter (ast_contains_var_core ctxt ref) args;
                      printf "arguments: %i\n%!" (Array.length args)
                    )
    | Z3.VAR_AST -> ref := true; printf "pattern.Var\n%!"
    | _          -> printf "--- pattern.other\n%!"
  end;;

let ast_contains_var ctxt ast =
  begin
    let ast_contains_var_ref = ref false in
    ast_contains_var_core ctxt ast_contains_var_ref ast;
    !ast_contains_var_ref
  end;;

let validate_pattern ctxt p =
  begin
    printf "*** Checking pattern: %s\n%!" (Z3.pattern_to_string ctxt p);
    let ast = Z3.pattern_to_ast ctxt p in
    match (Z3.get_pattern_num_terms ctxt p) with
      0 ->  printf "Warning: no terms in pattern!\n%!"; [| |]
    | _ ->  ( match (ast_contains_var ctxt ast) with
                true  -> printf "pattern seems valid.\n%!"; [| p |]
              | false -> printf "Warning: no vars in pattern!\n%!"; [| |] )
  end;;

(* we either have to filter out applies-terms excluding equality checks,
ertc from body, or we drop this stuff at all. *)
let rec get_terms_from_body_core ctxt ref body =
  begin
   printf "get_terms_from_body ast: %s\n%!" (Z3.ast_to_string ctxt body);
   match (Z3.get_ast_kind ctxt body) with
     Z3.APP_AST -> ( printf "body.App: %s\n%!" (Z3.ast_to_string ctxt body);
                     let args = Z3.get_app_args ctxt (Z3.to_app ctxt body) in
                     Array.iter (get_terms_from_body_core ctxt ref) args;
                     printf "body.arguments: %i\n%!" (Array.length args)
                    )
   | Z3.VAR_AST -> ( (* ref := (List.append !ref [body]); *)
                     printf "body.Var: %s\n%!" (Z3.ast_to_string ctxt body)
                   )
   | _          -> printf "--- body.ast.other\n%!"
  end;;

let get_terms_from_body ctxt body =
  begin
   let terms_ref  = ref [] in
   get_terms_from_body_core ctxt terms_ref body;
   !terms_ref
  end;;

let dbg_check ctxt solver =
  begin
    printf "dbg_check -- SOLVER:\n%sEND OF SOLVER\n%!"
      (Z3.solver_to_string ctxt solver);
    let result = Z3.solver_check ctxt solver in
    begin
     match result with
       Z3.L_FALSE -> printf "Z3.false\n%!"
     | Z3.L_UNDEF -> printf "Z3.unknown: %s\n%!" (Z3.solver_get_reason_unknown ctxt solver)
     | Z3.L_TRUE  -> printf "Z3.true\n%!";
    end
  end;;

let assert_cnstr ctxt solver cnstr =
  begin
    printf "Z3.solver_assert (%s)\n%!" (Z3.ast_to_string ctxt cnstr);  (*dbg*)
    let result = Z3.solver_assert ctxt solver cnstr in
    begin
     dbg_check ctxt solver;
     result
    end
  end;;


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
    with Failure "int_of_string" -> List [a0; a1; simplify e1]
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

class z3_context () =
  let cfg = [ ("AUTO_CONFIG", "false");
              ("MODEL", "true");
              ("MBQI", "false");
              ("MBQI_TRACE", "false");
(*              ("PROOF_MODE", "2");
              ("MBQI_MAX_ITERATIONS", "10");
              ("ARITH_PROCESS_ALL_EQS", "true");
              ("ARITH_EQ_BOUNDS", "true");
              ("ARITH_PROCESS_ALL_EQS", "true");
              ("DISTRIBUTE_FORALL", "true"); *)
  (* debug options: *)
              ("VERBOSE", "1000");
              ("TRACE", "false");
              ("DISPLAY_UNSAT_CORE", "true");
              ("DISPLAY_PROOF", "true");
              ("DISPLAY_CONFIG", "true");
              ("SOFT_TIMEOUT", "0");
              ("NL_ARITH_ROUNDS", "1024") ] in

  let ctxt = Z3.mk_context cfg in
  let apm = Z3.set_ast_print_mode ctxt Z3.PRINT_SMTLIB_COMPLIANT in
  let solver = Z3.mk_solver ctxt in

  let bool_type = Z3.mk_bool_sort ctxt in
  let int_type = Z3.mk_int_sort ctxt in
  let real_type = Z3.mk_real_sort ctxt in
  let ttrue = Z3.mk_true ctxt in
  let tfalse = Z3.mk_false ctxt in
  (* HACK: for now, all inductive values have the same Z3 type. *)
  let inductive_type = Z3.mk_uninterpreted_sort ctxt (Z3.mk_string_symbol ctxt "inductive") in
  let tag_func = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt "ctortag") [| inductive_type |] int_type in
  let ctor_counter = ref 0 in
  let get_ctor_tag () = let k = !ctor_counter in ctor_counter := k + 1; k in
  let mk_unary_app f t = Z3.mk_app ctxt f [| t |] in
  let assert_term t =
    printf "assert_term:\n%!";
    assert_cnstr ctxt solver t;
    match Z3.solver_check ctxt solver with
      Z3.L_FALSE -> Unsat
    | Z3.L_UNDEF -> Unknown
    | Z3.L_TRUE -> Unknown
  in
  let query t =
    Z3.solver_push ctxt solver;
    let result = assert_term (Z3.mk_not ctxt t) = Unsat in
    Z3.solver_pop ctxt solver 1;
    result
  in
  let assume_is_inverse f1 f2 dom2 =
    printf "assume_is_inverse:\n%!";
    let name = Z3.mk_int_symbol ctxt 0 in
    let x = Z3.mk_bound ctxt 0 dom2 in
    let app1 = Z3.mk_app ctxt f2 [| x |] in
    let app2 = Z3.mk_app ctxt f1 [| app1 |] in
    let pat = Z3.mk_pattern ctxt [| app1 |] in
    assert_cnstr ctxt solver (Z3.mk_forall ctxt 0 (validate_pattern ctxt pat) [| dom2 |] [| name |] (Z3.mk_eq ctxt app2 x))
  in
  let boxed_int = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt "(intbox)") [| int_type |] inductive_type in
  let unboxed_int = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt "(int)") [| inductive_type |] int_type in
  let () = assume_is_inverse unboxed_int boxed_int int_type in
  let () = assume_is_inverse boxed_int unboxed_int inductive_type in
  let boxed_bool = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt "(boolbox)") [| bool_type |] inductive_type in
  let unboxed_bool = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt "(bool)") [| inductive_type |] bool_type in
  let () = assume_is_inverse unboxed_bool boxed_bool bool_type in
  let boxed_real = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt "(realbox)") [| real_type |] inductive_type in
  let unboxed_real = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt "(real)") [| inductive_type |] real_type in
  let () = assume_is_inverse unboxed_real boxed_real real_type in
  let () = assume_is_inverse boxed_real unboxed_real inductive_type in  
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
      let c = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt name) tps range in
      begin
        match kind with
          Ctor k ->
          begin
            let tag = Z3.mk_int ctxt (get_ctor_tag()) int_type in
            let xs = Array.init (Array.length tps) (fun j -> Z3.mk_bound ctxt j tps.(j)) in
            let app = Z3.mk_app ctxt c xs in
            if domain = [] then
              assert_cnstr ctxt solver (Z3.mk_eq ctxt (mk_unary_app tag_func app) tag)
            else
            begin
              let names = Array.init (Array.length tps) (Z3.mk_int_symbol ctxt) in
              let pat = Z3.mk_pattern ctxt [| app |] in
              (* disjointness axiom *)
              (* (forall (x1 ... xn) (PAT (C x1 ... xn)) (EQ (tag (C x1 ... xn)) Ctag)) *)
              assert_cnstr ctxt solver (Z3.mk_forall ctxt 0 (validate_pattern ctxt pat) tps names (Z3.mk_eq ctxt (mk_unary_app tag_func app) tag));
              dbg_check ctxt solver; (*dbg*)
            end
          end;
          for i = 0 to Array.length tps - 1 do
            let names = Array.init (Array.length tps) (Z3.mk_int_symbol ctxt) in
            let xs = Array.init (Array.length tps) (fun j -> Z3.mk_bound ctxt j tps.(j)) in
            let app = Z3.mk_app ctxt c xs in
            let finv = Z3.mk_fresh_func_decl ctxt "ctorinv" [| inductive_type |] tps.(i) in
            let pat = Z3.mk_pattern ctxt [| app |] in
            (* injectiveness axiom *)
            (* (forall (x1 ... x2) (PAT (C x1 ... xn)) (EQ (finv (C x1 ... xn)) xi)) *)
            assert_cnstr ctxt solver (Z3.mk_forall ctxt 0 (validate_pattern ctxt pat) tps names (Z3.mk_eq ctxt (mk_unary_app finv app) (xs.(i))));
          done
        | Fixpoint j -> ()
        | Uninterp -> ()
      end;
      c
          
    method set_fpclauses fc k cs =
      List.iter
        (fun (csym, fbody) ->
           let n = Z3.get_domain_size ctxt fc in
           let ftps = Array.init n (Z3.get_domain ctxt fc) in
           let m = Z3.get_domain_size ctxt csym in
           let ctps = Array.init m (Z3.get_domain ctxt csym) in
           let l = m + n - 1 in
           let tps = Array.init l (fun i -> if i < m then ctps.(i) else if i < m + k then ftps.(i - m) else ftps.(i + 1 - m)) in
           let xs = Array.init l (fun i -> Z3.mk_bound ctxt i tps.(i)) in
           let names = Array.init l (Z3.mk_int_symbol ctxt) in
           let cargs = Array.init m (fun i -> xs.(i)) in
           let capp = Z3.mk_app ctxt csym cargs in
           let fargs = Array.init n (fun j -> if j < k then xs.(m + j) else if j = k then capp else xs.(m + j - 1)) in
           let fapp = Z3.mk_app ctxt fc fargs in
           let pat = Z3.mk_pattern ctxt [| fapp |] in
           let body = fbody (Array.to_list fargs) (Array.to_list cargs) in
           if l = 0 then
             assert_cnstr ctxt solver (Z3.mk_eq ctxt fapp body)
           else
             (* (FORALL (x1 ... y1 ... ym ... xn) (PAT (f x1 ... (C y1 ... ym) ... xn)) (EQ (f x1 ... (C y1 ... ym) ... xn) body)) *)
             assert_cnstr ctxt solver (Z3.mk_forall ctxt 0 (validate_pattern ctxt pat) tps names (Z3.mk_eq ctxt fapp body))
        )
        cs

    method mk_app s ts = Z3.mk_app ctxt s (Array.of_list ts)
    method mk_true = ttrue
    method mk_false = tfalse
    method mk_and t1 t2 = Z3.mk_and ctxt [| t1; t2 |]
    method mk_or t1 t2 = Z3.mk_or ctxt [| t1; t2 |]
    method mk_not t = Z3.mk_not ctxt t
    method mk_ifthenelse t1 t2 t3 = Z3.mk_ite ctxt t1 t2 t3
    method mk_iff t1 t2 = Z3.mk_eq ctxt t1 t2
    method mk_implies t1 t2 = Z3.mk_implies ctxt t1 t2
    method mk_eq t1 t2 = Z3.mk_eq ctxt t1 t2
    method mk_intlit n = Z3.mk_int ctxt n int_type
    method mk_intlit_of_string s = Z3.mk_numeral ctxt s int_type
    method mk_add t1 t2 = Z3.mk_add ctxt [| t1; t2 |]
    method mk_sub t1 t2 = Z3.mk_sub ctxt [| t1; t2 |]
    method mk_mul t1 t2 = Z3.mk_mul ctxt [| t1; t2 |]
    method mk_div t1 t2 = Z3.mk_div ctxt t1 t2
    method mk_mod t1 t2 = Z3.mk_mod ctxt t1 t2
    method mk_lt t1 t2 = Z3.mk_lt ctxt t1 t2
    method mk_le t1 t2 = Z3.mk_le ctxt t1 t2
    method mk_reallit n = Z3.mk_int ctxt n real_type
    method mk_reallit_of_num n = Z3.mk_numeral ctxt (string_of_num n) real_type
    method mk_real_add t1 t2 = Z3.mk_add ctxt [| t1; t2 |]
    method mk_real_sub t1 t2 = Z3.mk_sub ctxt [| t1; t2 |]
    method mk_real_mul t1 t2 = Z3.mk_mul ctxt [| t1; t2 |]
    method mk_real_lt t1 t2 = Z3.mk_lt ctxt t1 t2
    method mk_real_le t1 t2 = Z3.mk_le ctxt t1 t2
    method get_type t = Z3.get_sort ctxt t
    method pprint t = string_of_sexpr (simplify (parse_sexpr (Z3.ast_to_string ctxt t)))
    method pprint_sort (s : Z3.sort) = Z3.ast_to_string ctxt s
    method pprint_sym (s : Z3.func_decl) = Z3.ast_to_string ctxt s
    method query t =
      printf "Z3prover.query (%s)... " (Z3.ast_to_string ctxt t); (*dbg*)
      let t0 = if verbosity >= 1 then Perf.time() else 0.0 in
      let result = query t in
      if verbosity >= 1 then begin let t1 = Perf.time() in Printf.printf "%10.6fs: Z3 query %s: %.6f seconds\n" t0 (Z3.ast_to_string ctxt t) (t1 -. t0) end;
      result
    method assume t =
      printf "Z3prover.assume (%s)\n" (Z3.ast_to_string ctxt t);  (*dbg*)
      let t0 = if verbosity >= 1 then Perf.time() else 0.0 in
      let result = assert_term t in
      if verbosity >= 1 then begin let t1 = Perf.time() in Printf.printf "%10.6fs: Z3 assume %s: %.6f seconds\n" t0 (Z3.ast_to_string ctxt t) (t1-. t0) end;
      result
    method assert_term t = assert_cnstr ctxt solver t
    method push =
      Z3.solver_push ctxt solver
    method pop =
      Z3.solver_pop ctxt solver 1
    method perform_pending_splits (cont: Z3.ast list -> bool) = cont []
    method stats: string * (string * int64) list = "(no statistics for Z3)", []
    method begin_formal = ()
    method end_formal = ()
    method mk_bound (i: int) (tp: Z3.sort) = Z3.mk_bound ctxt i tp
    method assume_forall (description: string) (triggers: Z3.ast list) (tps: Z3.sort list) (body: Z3.ast): unit = 
      let pats = (
        match (List.append triggers (get_terms_from_body ctxt body)) with
          [] -> printf "*** empty trigger and body!\n"; [| |]
         | _ -> (validate_pattern ctxt (Z3.mk_pattern ctxt (Array.of_list (List.append triggers (get_terms_from_body ctxt body)))))
      ) in
      let quant = (Z3.mk_forall ctxt 0 pats (Array.of_list tps) (Array.init (List.length tps) (Z3.mk_int_symbol ctxt)) (body)) in
      printf "%s\n" (string_of_sexpr (simplify (parse_sexpr (Z3.ast_to_string ctxt quant)))); (*dbg*)
      assert_cnstr ctxt solver quant
   method simplify (t: Z3.ast): Z3.ast option = Some(Z3.simplify ctxt t)
  end
