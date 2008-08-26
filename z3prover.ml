open Proverapi

class z3_context () =
  let ctxt = Z3.mk_context (Z3.mk_config ()) in
  (* let _ = Z3.trace_to_stdout ctxt in *)
  (* HACK: for now, all inductive values have the same Z3 type. *)
  let int_type = Z3.mk_int_type ctxt in
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
    method alloc_symbol arity kind name =
      let s = Z3.mk_string_symbol ctxt name in
      let tps = Array.make arity inductive_type in
      let c = Z3.mk_func_decl ctxt s tps inductive_type in
      begin
        match kind with
          Ctor k ->
          begin
            let tag = Z3.mk_int ctxt (get_ctor_tag()) int_type in
            let xs = Array.init arity (fun j -> Z3.mk_bound ctxt j inductive_type) in
            let app = Z3.mk_app ctxt c xs in
            if arity = 0 then
              Z3.assert_cnstr ctxt (Z3.mk_eq ctxt (mk_unary_app tag_func app) tag)
            else
            begin
              let names = Array.init arity (Z3.mk_int_symbol ctxt) in
              let pat = Z3.mk_pattern ctxt [| app |] in
              (* disjointness axiom *)
              (* (forall (x1 ... xn) (PAT (C x1 ... xn)) (EQ (tag (C x1 ... xn)) Ctag)) *)
              Z3.assert_cnstr ctxt (Z3.mk_forall ctxt 0 [| pat |] tps names (Z3.mk_eq ctxt (mk_unary_app tag_func app) tag));
            end
          end;
          for i = 0 to arity - 1 do
            let names = Array.init arity (Z3.mk_int_symbol ctxt) in
            let xs = Array.init arity (fun j -> Z3.mk_bound ctxt j inductive_type) in
            let app = Z3.mk_app ctxt c xs in
            let finv = Z3.mk_fresh_func_decl ctxt "ctorinv" [| inductive_type |] inductive_type in
            let pat = Z3.mk_pattern ctxt [| app |] in
            (* injectiveness axiom *)
            (* (forall (x1 ... x2) (PAT (C x1 ... xn)) (EQ (finv (C x1 ... xn)) xi)) *)
            Z3.assert_cnstr ctxt (Z3.mk_forall ctxt 0 [| pat |] tps names (Z3.mk_eq ctxt (mk_unary_app finv app) (xs.(i))))
          done
        | Fixpoint j -> ()
        | Uninterp -> ()
      end;
      c
          
    method set_fpclauses fc k cs =
      List.iter
        (fun (csym, fbody) ->
           let n = Z3.get_domain_size ctxt fc in
           let m = Z3.get_domain_size ctxt csym in
           let l = m + n - 1 in
           let xs = Array.init l (fun i -> Z3.mk_bound ctxt i inductive_type) in
           let names = Array.init l (Z3.mk_int_symbol ctxt) in
           let tps = Array.make l inductive_type in
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
    method get_termnode s ts =
      Z3.mk_app ctxt s (Array.of_list ts)
    method pprint t =
      Z3.ast_to_string ctxt t
    method query_eq t1 t2 = query (Z3.mk_eq ctxt t1 t2)
    method query_neq t1 t2 = query (Z3.mk_not ctxt (Z3.mk_eq ctxt t1 t2))
    method assume_eq t1 t2 =
      assert_term (Z3.mk_eq ctxt t1 t2)
    method assume_neq t1 t2 =
      assert_term (Z3.mk_not ctxt (Z3.mk_eq ctxt t1 t2))
    method push =
      Z3.push ctxt
    method pop =
      Z3.pop ctxt 1
  end
