open Proverapi

(* A generic prover using the SMTLib language. Depending on the
   parameters input_fun and output, this can be used as either:

   - an interface for SMT solvers that have no OCaml binding such as
   CVC4; communication with the solver process is done through a
   pipe. See the function dump_smtlib_ctxt.

   - a simple SMTLib dump of all SMT queries, it cannot work alone
   since Verifast workflow requires interaction with the prover.  To
   use it, combine it with a real prover using the Combineprovers
   module. See the function external_smtlib_ctxt. *)

(* This code is largely inspired from the modules for the Z3 prover. *)

class smtlib_context input_fun output (features : string list) =
  let statements : Smtlib.statement list ref = ref [] in
  let dump_fmt = Format.formatter_of_out_channel output in
  let add_statement st =
    Format.fprintf dump_fmt "%a@\n" Smtlib.print_statement st;
    flush output;
    statements := st :: !statements
  in
  let has_features l =
    List.for_all (fun f -> List.mem f features) l
  in
  let maybe_add_statement st =
    if has_features (Smtlib.St.features st) then
      add_statement st;
  in
  (* /!\ The argument "ALL" to "set-logic" is quite new in SMTlib
     (version 2.5+). At time of writing, it is not yet supported by
     VeriT. It would probably be better to be more explicit about the
     required theories. Unfortunately, the union of required features
     (quantifiers + uninterpreted functions + non-linear integer and
     real arithmetic), UFNIRA, is not an official SMTLib logic
     (http://smtlib.cs.uiowa.edu/logics.shtml); "(set-logic UFNIRA)"
     is allowed by Z3 and CVC4 but not VeriT. Moreover, I guess that
     non-linear arithmetic is not often used and maybe it makes the
     SMT solver slow. *)
  let () = add_statement (Smtlib.set_logic "ALL") in
  let bool_type = Smtlib.bool in
  let int_type = Smtlib.int in
  let real_type = Smtlib.real in
  let ttrue = Smtlib.ttrue in
  let tfalse = Smtlib.tfalse in
  (* true iff we have all features in l *)
  let inductive_type =
    maybe_add_statement (Smtlib.declare_sort Smtlib.inductive);
    Smtlib.inductive
  in
  let declare_fun s sorts sort =
    let f = Smtlib.fresh_symbol s sorts sort in
    maybe_add_statement (Smtlib.declare_fun f);
    f
  in
  let tag_func = declare_fun "ctortag" [ inductive_type ] int_type in
  let ctor_counter = ref Big_int.zero_big_int in
  let get_ctor_tag () =
    let k = !ctor_counter in
    ctor_counter := Big_int.succ_big_int k;
    k
  in
  (* We remember the last answer as long as it is still valid, that is
     until we add an assertion or pop the stack. We do that to avoid
     asking the prover the same question several times. *)
  let last_prover_answer = ref None in
  let check () =
    match !last_prover_answer with
    | None ->
       add_statement Smtlib.check_sat;
       input_fun ()
    | Some ans -> ans
  in
  let add_assert t =
    (* Only add an assertion if the prover has the required features to understand it *)
    if has_features (Smtlib.T.features t) then
      begin
        last_prover_answer := None;
        add_statement (Smtlib.sassert t)
      end
  in
  let assert_term t = add_assert t; check () in
  let query t =
    if has_features (Smtlib.T.features t) then
      begin
        add_statement Smtlib.push;
        let result = assert_term (Smtlib.tnot t) = Unsat in
        add_statement (Smtlib.pop 1);
        result
      end
    else false   (* Same as an "unknown" answer *)
  in
  let assume_is_inverse f1 f2 dom2 =
    let x = Smtlib.mk_var 0 dom2 in
    let vx = Smtlib.var x in
    let app1 = Smtlib.app f2 [ vx ] in
    let app2 = Smtlib.app f1 [ app1 ] in
    add_assert (Smtlib.forall [ x ] [ app1 ] (Smtlib.eq app2 vx))
  in
  let boxed_int = declare_fun "box_int" [ int_type ] inductive_type in
  let unboxed_int = declare_fun "unbox_int" [ inductive_type ] int_type in
  let () = assume_is_inverse unboxed_int boxed_int int_type in
  let () = assume_is_inverse boxed_int unboxed_int inductive_type in
  let boxed_bool = declare_fun "box_bool" [ bool_type ] inductive_type in
  let unboxed_bool = declare_fun "unbox_bool" [ inductive_type ] bool_type in
  let () = assume_is_inverse unboxed_bool boxed_bool bool_type in
  let boxed_real = declare_fun "box_real" [ real_type ] inductive_type in
  let unboxed_real = declare_fun "unbox_real" [ inductive_type ] real_type in
  let () = assume_is_inverse unboxed_real boxed_real real_type in
  let () = assume_is_inverse boxed_real unboxed_real inductive_type in
  object
    val mutable verbosity = 0
    method features = features
    method set_verbosity v = verbosity <- v
    method type_bool = bool_type
    method type_int = int_type
    method type_real = real_type
    method type_inductive = inductive_type
    method mk_boxed_int = Smtlib.uapp boxed_int
    method mk_unboxed_int = Smtlib.uapp unboxed_int
    method mk_boxed_bool = Smtlib.uapp boxed_bool
    method mk_unboxed_bool = Smtlib.uapp unboxed_bool
    method mk_boxed_real = Smtlib.uapp boxed_real
    method mk_unboxed_real = Smtlib.uapp unboxed_real
    method mk_symbol name domain range kind =
      let c = declare_fun name domain range in
      begin
        match kind with
          Ctor k ->
          let tag = Smtlib.T.int (get_ctor_tag()) in
          let xs = List.mapi Smtlib.mk_var domain in
          let app = Smtlib.app c (List.map Smtlib.var xs) in
          begin
            add_statement (Smtlib.comment "disjointness axiom");
            if domain = [] then
              add_assert (Smtlib.eq (Smtlib.uapp tag_func app) tag)
            else
            begin
              (* disjointness axiom *)
              (* (forall (x1 ... xn) (PAT (C x1 ... xn)) (EQ (tag (C x1 ... xn)) Ctag)) *)
              add_assert (Smtlib.forall xs [ app ] (Smtlib.eq (Smtlib.uapp tag_func app) tag));
            end
          end;
          add_statement (Smtlib.comment "injectiveness axioms");
          List.iter
            begin fun var ->
              let finv =
                declare_fun "ctorinv" [ inductive_type ] (Smtlib.var_get_sort var)
              in
              (* injectiveness axiom *)
              (* (forall (x1 ... x2) (PAT (C x1 ... xn)) (EQ (finv (C x1 ... xn)) xi)) *)
              add_assert (Smtlib.forall xs [ app ] (Smtlib.eq (Smtlib.uapp finv app) (Smtlib.var var)))
            end
            xs
        | Fixpoint j -> ()
        | Uninterp -> ()
      end;
      c

    method set_fpclauses (fc : Smtlib.symbol) (k : int) cs : unit =
      add_statement (Smtlib.comment "set_fpclauses");
      add_statement (Smtlib.comment ("function " ^ Smtlib.Sym.to_string fc));
      add_statement (Smtlib.comment ("switching on argument number " ^ string_of_int k));
      let ftps = Smtlib.get_domain fc in
      let n = List.length ftps in
      List.iter
        (fun (csym, fbody) ->
           add_statement (Smtlib.comment ("constructor " ^ Smtlib.Sym.to_string csym));
           let ctps = Smtlib.get_domain csym in
           let m = List.length ctps in
           let l = m + n - 1 in
           let small_dom = Util.take k ftps in
           let small_xs = List.mapi Smtlib.mk_var small_dom in
           let ys = List.mapi (fun i -> Smtlib.mk_var (i+k)) ctps in
           let big_dom = Util.drop (k+1) ftps in
           let big_xs = List.mapi (fun i -> Smtlib.mk_var (i+m+k)) big_dom in
           let cargs = List.map Smtlib.var ys in
           let capp = Smtlib.app csym cargs in
           let fargs =
             List.map Smtlib.var small_xs @ capp :: List.map Smtlib.var big_xs
           in
           let fapp = Smtlib.app fc fargs in
           let body = fbody fargs cargs in
           if l = 0 then
             add_assert (Smtlib.eq fapp body)
           else
             (* (FORALL (x1 ... y1 ... ym ... xn) (PAT (f x1 ... (C y1 ... ym) ... xn)) (EQ (f x1 ... (C y1 ... ym) ... xn) body)) *)
             add_assert
               (Smtlib.forall
                  (small_xs @ ys @ big_xs)
                  [ fapp ]
                  (Smtlib.eq fapp body))
        )
        cs

    method mk_app = Smtlib.app
    method mk_true = ttrue
    method mk_false = tfalse
    method mk_and = Smtlib.tand
    method mk_or = Smtlib.tor
    method mk_not = Smtlib.tnot
    method mk_ifthenelse = Smtlib.tite
    method mk_iff = Smtlib.iff
    method mk_implies = Smtlib.timp
    method mk_eq = Smtlib.eq
    method mk_intlit n = Smtlib.T.int (Big_int.big_int_of_int n)
    method mk_intlit_of_string s =
      try
        Smtlib.T.int (Big_int.big_int_of_string s)
      with Failure _ ->
        add_statement
          (Smtlib.comment
             (Printf.sprintf
                "Warning: Failed to read \"%s\" as an integer, using 0 instead"
                s));
        Smtlib.T.int Big_int.zero_big_int
    method mk_add = Smtlib.add
    method mk_sub = Smtlib.sub
    method mk_mul = Smtlib.mul
    method mk_div = Smtlib.div
    method mk_mod = Smtlib.tmod
    method mk_lt = Smtlib.lt
    method mk_le = Smtlib.le
    method mk_reallit n = Smtlib.T.real (Num.Int n)
    method mk_reallit_of_num = Smtlib.T.real
    method mk_real_add = Smtlib.radd
    method mk_real_sub = Smtlib.rsub
    method mk_real_mul = Smtlib.rmul
    method mk_real_lt = Smtlib.rlt
    method mk_real_le = Smtlib.rle
    method pprint = Smtlib.T.to_string
    method pprint_sort = Smtlib.Sort.to_string
    method pprint_sym = Smtlib.Sym.to_string
    method query t =
      add_statement
        (Smtlib.comment (Printf.sprintf "Query: %s" (Smtlib.T.to_string t)));
      query t
    method assume t =
      add_statement
        (Smtlib.comment (Printf.sprintf "Assume: %s" (Smtlib.T.to_string t)));
      assert_term t
    method assert_term t =
      add_statement
        (Smtlib.comment (Printf.sprintf "Assert: %s" (Smtlib.T.to_string t)));
      add_assert t
    method push = add_statement (Smtlib.push)
    method pop = last_prover_answer := None; add_statement (Smtlib.pop 1)
    method perform_pending_splits (cont: Smtlib.term list -> bool) = cont []
    method stats: string * (string * int64) list = "(no statistiques for SMTlib)", []
    method begin_formal = ()
    method end_formal = ()
    method mk_bound (i: int) (tp: Smtlib.sort) =
      Smtlib.var (Smtlib.mk_var i tp)
    method assume_forall
             (description: string)
             (triggers: Smtlib.term list)
             (tps: Smtlib.sort list)
             (body: Smtlib.term) : unit =
      if List.length tps = 0 then
        add_assert body
      else
        let quant = (Smtlib.forall (List.mapi Smtlib.mk_var tps) triggers body) in
        add_assert quant
   method simplify (t : Smtlib.term) = Some t
  end

let dump_smtlib_ctxt filename features =
  (new smtlib_context
     (fun _ -> Unknown)
     (open_out filename)
     features
   : smtlib_context :> (Smtlib.sort, Smtlib.symbol, Smtlib.term) context)

let external_smtlib_ctxt command features =
  let (input, output) = Unix.open_process command in
  (new smtlib_context
     (fun _ ->
       match input_line input with
       | "unsat" -> Unsat
       | "unknown" -> Unknown
       | _ -> assert false)
     output
     features
   : smtlib_context :> (Smtlib.sort, Smtlib.symbol, Smtlib.term) context)
