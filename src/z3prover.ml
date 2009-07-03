open Proverapi

class z3_context () =
  let ctxt = Z3.mk_context (Z3.mk_config ()) in
  (* let _ = Z3.trace_to_stdout ctxt in *)
  let bool_type = Z3.mk_bool_type ctxt in
  let int_type = Z3.mk_int_type ctxt in
  let real_type = Z3.mk_real_type ctxt in
  let ttrue = Z3.mk_true ctxt in
  let tfalse = Z3.mk_false ctxt in
  (* HACK: for now, all inductive values have the same Z3 type. *)
  let inductive_type = Z3.mk_uninterpreted_type ctxt (Z3.mk_string_symbol ctxt "inductive") in
  let tag_func = Z3.mk_func_decl ctxt (Z3.mk_string_symbol ctxt "ctortag") [| inductive_type |] int_type in
  let ctor_counter = ref 0 in
  let get_ctor_tag () = let k = !ctor_counter in ctor_counter := k + 1; k in
  let mk_unary_app f t = Z3.mk_app ctxt f [| t |] in
  let assert_term t =
    Z3.assert_cnstr ctxt t;
    match Z3.check ctxt with
      Z3.L_FALSE -> Unsat
    | Z3.L_UNDEF -> Unknown
    | Z3.L_TRUE -> Unknown
  in
  let query t =
    Z3.push ctxt;
    let result = assert_term (Z3.mk_not ctxt t) = Unsat in
    Z3.pop ctxt 1;
    result
  in
  object
    method type_bool = bool_type
    method type_int = int_type
    method type_real = real_type
    method type_inductive = inductive_type
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
              Z3.assert_cnstr ctxt (Z3.mk_eq ctxt (mk_unary_app tag_func app) tag)
            else
            begin
              let names = Array.init (Array.length tps) (Z3.mk_int_symbol ctxt) in
              let pat = Z3.mk_pattern ctxt [| app |] in
              (* disjointness axiom *)
              (* (forall (x1 ... xn) (PAT (C x1 ... xn)) (EQ (tag (C x1 ... xn)) Ctag)) *)
              Z3.assert_cnstr ctxt (Z3.mk_forall ctxt 0 [| pat |] tps names (Z3.mk_eq ctxt (mk_unary_app tag_func app) tag));
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
            Z3.assert_cnstr ctxt (Z3.mk_forall ctxt 0 [| pat |] tps names (Z3.mk_eq ctxt (mk_unary_app finv app) (xs.(i))))
          done
        | Fixpoint j -> ()
        | Uninterp -> ()
      end;
      c
          
    method assume_is_inverse f1 f2 =
      let f1domain = Z3.get_domain ctxt f2 0 in
      let name = Z3.mk_int_symbol ctxt 0 in
      let x = Z3.mk_bound ctxt 0 f1domain in
      let app1 = Z3.mk_app ctxt f2 [| x |] in
      let app2 = Z3.mk_app ctxt f1 [| app1 |] in
      let pat = Z3.mk_pattern ctxt [| app1 |] in
      Z3.assert_cnstr ctxt (Z3.mk_forall ctxt 0 [| pat |] [| f1domain |] [| name |] (Z3.mk_eq ctxt app2 x))
    
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
             Z3.assert_cnstr ctxt (Z3.mk_eq ctxt fapp body)
           else
             (* (FORALL (x1 ... y1 ... ym ... xn) (PAT (f x1 ... (C y1 ... ym) ... xn)) (EQ (f x1 ... (C y1 ... ym) ... xn) body)) *)
             Z3.assert_cnstr ctxt (Z3.mk_forall ctxt 0 [| pat |] tps names (Z3.mk_eq ctxt fapp body))
        )
        cs

    method mk_app s ts = Z3.mk_app ctxt s (Array.of_list ts)
    method mk_true = ttrue
    method mk_false = tfalse
    method mk_and t1 t2 = Z3.mk_and ctxt [| t1; t2 |]
    method mk_or t1 t2 = Z3.mk_or ctxt [| t1; t2 |]
    method mk_not t = Z3.mk_not ctxt t
    method mk_ifthenelse t1 t2 t3 = Z3.mk_ite ctxt t1 t2 t3
    method mk_eq t1 t2 = Z3.mk_eq ctxt t1 t2
    method mk_intlit n = Z3.mk_int ctxt n int_type
    method mk_intlit_of_string s = Z3.mk_numeral ctxt s int_type
    method mk_add t1 t2 = Z3.mk_add ctxt [| t1; t2 |]
    method mk_sub t1 t2 = Z3.mk_sub ctxt [| t1; t2 |]
    method mk_mul t1 t2 = Z3.mk_mul ctxt [| t1; t2 |]
    method mk_lt t1 t2 = Z3.mk_lt ctxt t1 t2
    method mk_le t1 t2 = Z3.mk_le ctxt t1 t2
    method mk_reallit n = Z3.mk_int ctxt n real_type
    method mk_reallit_of_num n = Z3.mk_numeral ctxt (Num.string_of_num n) real_type
    method mk_real_add t1 t2 = Z3.mk_add ctxt [| t1; t2 |]
    method mk_real_sub t1 t2 = Z3.mk_sub ctxt [| t1; t2 |]
    method mk_real_mul t1 t2 = Z3.mk_mul ctxt [| t1; t2 |]
    method mk_real_lt t1 t2 = Z3.mk_lt ctxt t1 t2
    method mk_real_le t1 t2 = Z3.mk_le ctxt t1 t2
    method get_type t = Z3.get_type ctxt t
    method pprint t = Z3.ast_to_string ctxt t
    method query t = query t
    method assume t = assert_term t
    method push = Z3.push ctxt
    method pop = Z3.pop ctxt 1
  end
