open Proverapi
open Big_int
open Printf
open Num (* rational numbers *)
open Util
open Stats
open Ast
open Parser
open Verifast0
open Verifast1

module Assertions(VerifyProgramArgs: VERIFY_PROGRAM_ARGS) = struct
  
  include VerifyProgram1(VerifyProgramArgs)
  
  type auto_lemma_info =
      string option (* fraction *)
    * string list (* type parameters *)
    * string list (* index patterns *)
    * string list (* argument patterns *)
    * asn (* pre *)
    * asn (* post *)
  let auto_lemmas: (string, auto_lemma_info) Hashtbl.t = Hashtbl.create 10

  let lemma_rules = ref []

  let add_lemma_rule symb rule = 
    (begin match try_assq symb !lemma_rules with
      None -> lemma_rules := (symb, ref [rule]) :: !lemma_rules
    | Some(rs) -> rs := rule :: !rs end)
  
  module CheckFile_Assertions(CheckFileArgs: CHECK_FILE_ARGS) = struct
  
  include CheckFile1(CheckFileArgs)
  
  let _ = if options.option_verbose = -1 then Printf.printf "%10.6fs: >> verification of %s \n" (Perf.time()) filepath  

  (* Region: production of assertions *)
  
  let rec is_pure_spatial_assertion a =
    match a with
      ExprAsn(_, _) -> true
    | Sep(_, a1, a2) -> (is_pure_spatial_assertion a1) && (is_pure_spatial_assertion a2)
    | IfAsn(_, _, a1, a2) -> (is_pure_spatial_assertion a1) && (is_pure_spatial_assertion a2)
    | EmpAsn _ -> true
    | ForallAsn _ -> true
    | WMatchAsn _ -> true
    | _ -> false
  
  let rec assert_expr env e h env l msg url = 
    let t = eval None env e in
    if query_term t then
      ()
    else begin
      ignore (assert_expr_split e h env l msg url); ()
    end
  
  and branch cont1 cont2 =
    !stats#branch;
    let oldForest = !currentForest in
    let leftForest = ref [] in
    let rightForest = ref [] in
    oldForest := Node (BranchNode, rightForest)::Node (BranchNode, leftForest)::!oldForest;
    currentForest := leftForest;
    push_context (Branching LeftBranch);
    execute_branch cont1;
    pop_context ();
    if !leftForest = [] then leftForest := [Node (SuccessNode, ref [])];
    currentForest := rightForest;
    push_context (Branching RightBranch);
    execute_branch cont2;
    pop_context ();
    if !rightForest = [] then rightForest := [Node (SuccessNode, ref [])];
    currentForest := oldForest;
    SymExecSuccess
  
  and assert_expr_split e h env l msg url = 
    match e with
      IfExpr(l0, con, e1, e2) -> 
        branch
           (fun () -> assume (eval None env con) (fun () -> assert_expr_split e1 h env l msg url))
           (fun () -> assume (ctxt#mk_not (eval None env con)) (fun () -> assert_expr_split e2 h env l msg url))
    | WOperation(l0, And, [e1; e2], t) ->
      branch
        (fun () -> assert_expr_split e1 h env l msg url)
        (fun () -> assert_expr_split e2 h env l msg url)
    | _ -> with_context (Executing (h, env, expr_loc e, "Consuming expression")) (fun () -> assert_term (eval None env e) h env l msg url; SymExecSuccess)
  
  let rec evalpat ghost ghostenv env pat tp0 tp cont =
    match pat with
      LitPat e -> cont ghostenv env (prover_convert_term (eval None env e) tp0 tp)
    | VarPat (_, x) when not (List.mem_assoc x env) -> let t = get_unique_var_symb_ x tp ghost in cont (x::ghostenv) (update env x (prover_convert_term t tp tp0)) t
    | VarPat(_, x) -> cont (x :: ghostenv) env (List.assoc x env)
    | DummyPat|DummyVarPat -> let t = get_unique_var_symb_ "dummy" tp ghost in cont ghostenv env t
    | WCtorPat (l, i, targs, g, ts0, ts, pats, _) ->
      let (_, inductive_tparams, ctormap, _, _, _, _, _) = List.assoc i inductivemap in
      let (_, (_, _, _, _, (symb, _))) = List.assoc g ctormap in
      evalpats ghostenv env pats ts ts0 $. fun ghostenv env vs ->
      cont ghostenv env (prover_convert_term (ctxt#mk_app symb vs) tp0 tp)
  and evalpats ghostenv env pats tps0 tps cont =
    match (pats, tps0, tps) with
      ([], [], []) -> cont ghostenv env []
    | (pat::pats, tp0::tps0, tp::tps) -> evalpat true ghostenv env pat tp0 tp (fun ghostenv env t -> evalpats ghostenv env pats tps0 tps (fun ghostenv env ts -> cont ghostenv env (t::ts)))

  let evalpat_ ghost ghostenv env pat tp0 tp cont =
    if pat = DummyPat && not ghost then
      cont ghostenv env None
    else
      evalpat ghost ghostenv env pat tp0 tp $. fun ghostenv env t ->
      cont ghostenv env (Some t)

  let real_mul l t1 t2 =
    if t1 == real_unit then t2 else if t2 == real_unit then t1 else
    let t = ctxt#mk_real_mul t1 t2 in
    if is_dummy_frac_term t1 || is_dummy_frac_term t2 then dummy_frac_terms := t::!dummy_frac_terms;
    t
  
  let real_div l t1 t2 =
    if t2 == real_unit then t1 else static_error l "Real division not yet supported." None
  
  let definitely_equal t1 t2 =
    let result = if t1 == t2 then (!stats#definitelyEqualSameTerm; true) else (!stats#definitelyEqualQuery; ctxt#query (ctxt#mk_eq t1 t2)) in
    (* print_endline ("Checking definite equality of " ^ ctxt#pprint t1 ^ " and " ^ ctxt#pprint t2 ^ ": " ^ (if result then "true" else "false")); *)
    result
  
  let predname_eq g1 g2 =
    match (g1, g2) with
      ((g1, literal1), (g2, literal2)) -> if literal1 && literal2 then g1 == g2 else definitely_equal g1 g2
  
  let assume_field h0 env fparent tparams fname frange targs fghost tp tv tcoef cont =
    let ((_, (_, _, _, _, symb, _, _)), p__opt) = List.assoc (fparent, fname) field_pred_map in
    let tpenv = List.combine tparams targs in
    let frange = instantiate_type tpenv frange in
    if fghost = Real then begin
      match tv with
        Some tv -> assume_bounds tv frange
      | None -> ()
    end;
    (* automatic generation of t1 != t2 if t1.f |-> _ &*& t2.f |-> _ *)
    begin fun cont ->
      if tcoef != real_unit && tcoef != real_half then
        assume (ctxt#mk_real_lt real_zero tcoef) cont
      else
        cont()
    end $. fun () ->
    let pred_symb = (symb, true) in
    let is_related_pred_symb =
      match p__opt with
        None -> fun g -> predname_eq g pred_symb
      | Some (_, (_, _, _, _, symb_, _, _)) ->
        let pred__symb = (symb_, true) in
        fun g -> predname_eq g pred_symb || predname_eq g pred__symb
    in
    let rec iter h =
      match h with
        [] ->
        let chunk =
          match tv, p__opt with
            Some tv, _ ->
            Chunk ((symb, true), targs, tcoef, [tp; tv], None)
          | None, Some (_, (_, _, _, _, symb_, _, _)) ->
            let tv = get_unique_var_symb_ "dummy" (option_type frange) (fghost = Ghost) in
            Chunk ((symb_, true), targs, tcoef, [tp; tv], None)
          | None, None ->
            let tv = get_unique_var_symb_ "dummy" frange (fghost = Ghost) in
            Chunk ((symb, true), targs, tcoef, [tp; tv], None)
        in
        cont (chunk::h0)
      | Chunk (g, targs', tcoef', [tp'; tv'], _) as chunk::h when is_related_pred_symb g && List.for_all2 unify targs targs' ->
        if tcoef == real_unit || tcoef' == real_unit then
          assume_neq (mk_ptr_address tp) (mk_ptr_address tp') (fun _ -> iter h)
        else if definitely_equal tp tp' then
        begin
          let cont coef = 
            let cont new_chunk = cont (new_chunk::List.filter (fun ch -> ch != chunk) h0) in
            match tv, predname_eq g pred_symb with
              Some tv, true ->
              assume (ctxt#mk_eq tv tv') $. fun () ->
              cont (Chunk ((symb, true), targs, coef, [tp'; tv'], None))
            | None, true ->
              cont (Chunk ((symb, true), targs, coef, [tp'; tv'], None))
            | Some tv, false ->
              assume (ctxt#mk_eq (mk_some frange tv) tv') $. fun () ->
              cont (Chunk ((symb, true), targs, coef, [tp; tv], None))
            | None, false ->
              cont (Chunk (g, targs, coef, [tp'; tv'], None))
          in
          if tcoef == real_half && tcoef' == real_half then cont real_unit else
          if is_dummy_frac_term tcoef then
            cont tcoef'
          else if is_dummy_frac_term tcoef' then
            cont tcoef
          else
            let newcoef = (ctxt#mk_real_add tcoef tcoef') in (assume (ctxt#mk_real_le newcoef real_unit) $. fun () -> cont newcoef)
        end
        else
          iter h
      | _::h -> iter h
    in
    begin fun cont ->
      match language with
        Java ->
        if not (ctxt#query (ctxt#mk_not (ctxt#mk_eq tp (ctxt#mk_intlit 0)))) then
          assume_neq tp (ctxt#mk_intlit 0) cont
        else
          cont ()
      | _ ->
        let (_, tparams, Some (_, fmap, _), _, _) = List.assoc fparent structmap in
        let (lf, gh, y, offset_opt, _) = List.assoc fname fmap in
        match offset_opt with
          Some offsetFunc ->
          assume (mk_field_pointer_within_limits tp (ctxt#mk_app offsetFunc (List.map (typeid_of_core lf env) targs))) cont
        | None -> cont ()
    end $. fun () ->
    iter h0

  let produce_chunk h g_symb targs coef inputParamCount ts size cont =
    if inputParamCount = None || coef == real_unit then
      cont (Chunk (g_symb, targs, coef, ts, size)::h)
    else
      let Some n = inputParamCount in
      let rec iter hdone htodo =
        match htodo with
          [] -> cont (Chunk (g_symb, targs, coef, ts, size)::h)
        | Chunk (g_symb', targs', coef', ts', size') as chunk::htodo ->
          if predname_eq g_symb g_symb' && List.for_all2 unify targs targs' && for_all_take2 definitely_equal n ts ts' then
            let assume_all_eq ts ts' cont =
              let rec iter ts ts' =
                match (ts, ts') with
                  (t::ts, t'::ts') -> assume (ctxt#mk_eq t t') (fun () -> iter ts ts')
                | ([], []) -> cont ()
              in
              iter ts ts'
            in
            assume_all_eq (drop n ts) (drop n ts') $. fun () ->
            let h = if List.length hdone < List.length htodo then hdone @ htodo else htodo @ hdone in
            let coef =
              if coef == real_half && coef' == real_half then real_unit else
              if is_dummy_frac_term coef then
                if is_dummy_frac_term coef' then
                  coef'
                else begin
                  ctxt#assert_term (ctxt#mk_lt real_zero coef);
                  ctxt#mk_real_add coef coef'
                end
              else
                if is_dummy_frac_term coef' then begin
                  ctxt#assert_term (ctxt#mk_lt real_zero coef');
                  ctxt#mk_real_add coef coef'
                end else
                  ctxt#mk_real_add coef coef'
            in
            cont (Chunk (g_symb, targs, coef, ts, size)::h)
          else
            iter (chunk::hdone) htodo
      in
      iter [] h

  let produce_points_to_chunk l h type_ coef addr value cont =
    begin fun cont ->
      if coef != real_unit && coef != real_half then
        assume (ctxt#mk_real_lt real_zero coef) cont
      else
        cont()
    end $. fun () ->
    match try_pointee_pred_symb type_ with
      Some symb ->
      produce_chunk h (symb, true) [] coef (Some 1) [addr; value] None cont
    | None ->
    match int_rank_and_signedness type_ with
      Some (k, signedness) ->
      produce_chunk h (integer__symb (), true) [] coef (Some 3) [addr; rank_size_term k; mk_bool (signedness = Signed); value] None cont
    | None ->
      produce_chunk h (generic_points_to_symb (), true) [type_] coef (Some 1) [addr; value] None cont

  let produce_uninit_points_to_chunk l h type_ coef addr cont =
    begin fun cont ->
      if coef != real_unit && coef != real_half then
        assume (ctxt#mk_real_lt real_zero coef) cont
      else
        cont()
    end $. fun () ->
    match try_pointee_pred_symb0 type_ with
      Some (_, _, _, _, _, _, _, _, _, uninit_predsym, _, _) ->
      produce_chunk h (uninit_predsym, true) [] coef (Some 1) [addr; get_unique_var_symb_ "dummy" (option_type type_) true] None cont
    | None ->
    match int_rank_and_signedness type_ with
      Some (k, signedness) ->
        produce_chunk h (integer___symb (), true) [] coef (Some 3) [addr; rank_size_term k; mk_bool (signedness = Signed); get_unique_var_symb_ "dummy" (option_type type_) true] None cont
    | None ->
      produce_chunk h (generic_points_to__symb (), true) [type_] coef (Some 1) [addr; get_unique_var_symb_ "dummy" (option_type type_) true] None cont

  let produce_points_to_chunk_ l h type_ coef addr value cont =
    match value with
      None -> produce_uninit_points_to_chunk l h type_ coef addr cont
    | Some v -> produce_points_to_chunk l h type_ coef addr v cont

  let produce_instance_predicate_chunk l h symbol coef target index family arguments size_first cont =
    let family_target = 
      match language, dialect with
      | CLang, Some Cxx ->
        base_addr l target family
      | _ -> snd target
    in
    produce_chunk h (symbol, true) [] coef (Some 2) (family_target :: index :: arguments) size_first @@ fun h ->
    cont h family_target

  let rec produce_asn_core_with_post tpenv h ghostenv env p coef size_first size_all (assuming: bool) cont_with_post: symexec_result =
    let cont h env ghostenv = cont_with_post h env ghostenv None in
    let with_context_helper cont =
      match p with
        Sep (_, _, _) -> cont()
      | _ ->
        with_context ~verbosity_level:2 (Executing (h, env, asn_loc p, "Producing assertion")) cont
    in
    with_context_helper (fun _ ->
    let ev = eval None env in
    match p with
    | WPointsTo (l, WRead (lr, e, fparent, tparams, fname, frange, targs, fstatic, fvalue, fghost), tp, rhs) ->
      if fstatic then
        let (_, (_, _, _, _, symb, _, _)), p__opt = List.assoc (fparent, fname) field_pred_map in
        evalpat (fghost = Ghost) ghostenv env rhs tp tp $. fun ghostenv env t ->
        produce_chunk h (symb, true) [] coef (Some 0) [t] None $. fun h ->
        cont h ghostenv env
      else
        let te = ev e in
        evalpat_ (fghost = Ghost) ghostenv env rhs tp (instantiate_type tpenv tp) $. fun ghostenv env t ->
        assume_field h env fparent tparams fname frange (List.map (instantiate_type tpenv) targs) fghost te t coef $. fun h ->
        cont h ghostenv env
    | WPointsTo (l, WReadArray (la, ea, _, ei), tp, rhs) ->
      let a = ev ea in
      let i = ev ei in
      evalpat false ghostenv env rhs tp tp $. fun ghostenv env t ->
      let slice = Chunk ((array_element_symb(), true), [instantiate_type tpenv tp], coef, [a; i; t], None) in
      cont (slice::h) ghostenv env
    | WPointsTo (l, WVar (lv, x, GlobalName), tp, rhs) -> 
      let (_, type_, symbn, _) = List.assoc x globalmap in    
      evalpat false ghostenv env rhs tp tp $. fun ghostenv env t ->
      produce_points_to_chunk l h type_ coef symbn t $. fun h ->
      cont h ghostenv env
    | WPointsTo (l, WDeref(ld, e, td), tp, rhs) ->  
      let symbn = eval None env e in
      let tp' = instantiate_type tpenv tp in
      evalpat_ false ghostenv env rhs tp tp' $. fun ghostenv env t ->
      produce_points_to_chunk_ l h tp' coef symbn t $. fun h ->
      cont h ghostenv env
    | WPredAsn (l, g, is_global_predref, targs, pats0, pats) ->
      let (g_symb, pats0, pats, types, auto_info) =
        if not is_global_predref then 
          let Some term = try_assoc g#name env in ((term, false), pats0, pats, g#domain, None)
       else
          begin match try_assoc g#name predfammap with
            Some (_, _, _, declared_paramtypes, symb, _, _) -> ((symb, true), pats0, pats, g#domain, Some (g#name, declared_paramtypes))
          | None ->
            let PredCtorInfo (_, tparams, ps1, ps2, inputParamCount, body, funcsym) = List.assoc g#name predctormap in
            if tparams <> [] then static_error l "Generic predicate constructor assertions are not yet supported" None;
            let ctorargs = List.map (function (LitPat e | WCtorPat (_, _, _, _, _, _, _, Some e)) -> ev e | _ -> static_error l "Patterns are not supported in predicate constructor argument positions." None) pats0 in
            let g_symb = mk_app funcsym ctorargs in
            let (symbol, symbol_term) = funcsym in
            register_pred_ctor_application g_symb symbol symbol_term [] ctorargs inputParamCount;
            ((g_symb, false), [], pats, List.map snd ps2, None)
          end
      in
      let targs = instantiate_types tpenv targs in
      let domain = instantiate_types tpenv types in
      evalpats ghostenv env (pats0 @ pats) types domain (fun ghostenv env ts ->
        let input_param_count = match g#inputParamCount with None -> None | Some c -> Some (c + (List.length pats0)) in
        let do_assume_chunk () = produce_chunk h g_symb targs coef input_param_count ts size_first (fun h -> cont h ghostenv env) in
        match
          if assuming then None else
          match auto_info with
            None -> None
          | Some (predName, declared_paramtypes) ->
            try
              Some (Hashtbl.find auto_lemmas predName, declared_paramtypes)
            with Not_found -> None
        with
          None -> do_assume_chunk ()
        | Some ((frac, tparams, xs1, xs2, pre, post), declared_paramtypes) ->
          let ts = List.map (fun (t, (tp0, tp)) -> prover_convert_term t tp0 tp) (zip2 ts (zip2 domain declared_paramtypes)) in
          let produce_post env' =
            let env'' = env' @ zip2 (xs1@xs2) ts in
            with_context PushSubcontext $. fun () ->
            with_context (Executing (h, env'', l, "Applying autolemma")) $. fun () ->
            produce_asn_core_with_post (zip2 tparams targs) h [] env'' post real_unit size_first size_all true $. fun h_ _ _ _ ->
            with_context PopSubcontext $. fun () ->
            cont h_ ghostenv env
          in
          match frac with
            None -> 
            if coef == real_unit then 
              produce_post []
            else
              do_assume_chunk ()
          | Some(f) ->
            produce_post [(f, coef)]
      )
    | WInstPredAsn (l, e_opt, st, cfin, tn, g, index, pats) ->
        let (pmap, pred_symb) =
          try
          match dialect with
          | None ->
            begin match try_assoc tn classmap1 with
              Some (lcn, abstract, fin, methods, fds_opt, ctors, super, tparams, interfs, preds, pn, ilist) ->
              let (_, pmap, _, symb, _) = List.assoc g preds in (pmap, symb)
            | None ->
              match try_assoc tn classmap0 with
                Some {cpreds} ->
                let (_, pmap, _, symb, _) = List.assoc g cpreds in (pmap, symb)
              | None ->
                match try_assoc tn interfmap1 with
                  Some (li, fields, methods, preds, interfs, pn, ilist, tparams) -> let (_, pmap, family, symb) = List.assoc g preds in (pmap, symb)
                | None ->
                  let InterfaceInfo (li, fields, methods, preds, interfs, tparams) = List.assoc tn interfmap0 in
                  let (_, pmap, family, symb) = List.assoc g preds in
                  (pmap, symb)
            end
          | Some Cxx ->
            let preds = List.assoc tn cxx_inst_pred_map in
            let _, pmap, _, symb, _ = List.assoc g preds in
            pmap, symb
          with Not_found -> assert_false h env l ("Definition of predicate " ^ g ^ " is missing from implementing class") None
        in
        let target = match e_opt with None -> List.assoc "this" env | Some e -> ev e in
        let index = ev index in
        begin fun cont -> if cfin = FinalClass && language = Java then assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [target]) (List.assoc st classterms)) cont else cont () end $. fun () ->
        let types = List.map snd pmap in
        evalpats ghostenv env pats types types $. fun ghostenv env args ->
        produce_instance_predicate_chunk l h pred_symb coef (st, target) index tn args size_first @@ fun h target ->
        assume (ctxt#mk_not (ctxt#mk_eq target (null_pointer_term ()))) @@ fun () ->
        cont h ghostenv env
    | ExprAsn (l, e) -> assume (ev e) (fun _ -> cont h ghostenv env)
    | WMatchAsn (l, e, pat, tp) ->
      let v = ev e in
      evalpat true ghostenv env pat tp tp $. fun ghostenv env v' ->
      let f = if tp = Bool then ctxt#mk_iff v v' else ctxt#mk_eq v v' in
      assume f $. fun () ->
      cont h ghostenv env
    | LetTypeAsn (l, x, tp, p) ->
      produce_asn_core_with_post ((x, tp)::tpenv) h ghostenv env p coef size_first size_all assuming cont_with_post
    | Sep (l, p1, p2) ->
      produce_asn_core_with_post tpenv h ghostenv env p1 coef size_first size_all assuming $. fun h ghostenv env post ->
      if post <> None then assert_false h env l "Left-hand side of separating conjunction cannot specify a postcondition." None;
      produce_asn_core_with_post tpenv h ghostenv env p2 coef size_all size_all assuming cont_with_post
    | IfAsn (l, e, p1, p2) ->
      let cont_with_post h ghostenv1 env1 post =
        let ghostenv, env =
          if post = None then ghostenv, env else ghostenv1, env1
        in
        cont_with_post h ghostenv env post
      in
      branch
        (fun _ -> assume (ev e) (fun _ -> produce_asn_core_with_post tpenv h ghostenv env p1 coef size_all size_all assuming cont_with_post))
        (fun _ -> assume (ctxt#mk_not (ev e)) (fun _ -> produce_asn_core_with_post tpenv h ghostenv env p2 coef size_all size_all assuming cont_with_post))
    | WSwitchAsn (l, e, i, cs) ->
      let cont_with_post h ghostenv1 env1 post =
        let ghostenv, env =
          if post = None then ghostenv, env else ghostenv1, env1
        in
        cont_with_post h ghostenv env post
      in
      let t = ev e in
      let (_, tparams, ctormap, _, _, _, _, _) = List.assoc i inductivemap in
      let rec iter cs =
        match cs with
          WSwitchAsnClause (lc, cn, pats, patsInfo, p)::cs ->
          branch
            (fun _ ->
               let (_, (_, tparams, _, tps, cs)) = List.assoc cn ctormap in
               let Some pts = zip pats tps in
               let xts =
                 if tparams = [] then
                   List.map (fun (x, (name, (tp: type_))) -> let term = get_unique_var_symb x tp in (x, term, term)) pts
                 else
                   let Some pts = zip pts patsInfo in
                   List.map
                     (fun ((x, (name, tp)), info) ->
                      match info with
                        None -> let term = get_unique_var_symb x tp in (x, term, term)
                      | Some proverType ->
                        let term = ctxt#mk_app (mk_symbol x [] (typenode_of_provertype proverType) Uninterp) [] in
                        let term' = convert_provertype term proverType ProverInductive in
                        (x, term', term)
                     )
                     pts
               in
               let xenv = List.map (fun (x, _, t) -> (x, t)) xts in
               assume_eq t (mk_app cs (List.map (fun (x, t, _) -> t) xts)) (fun _ -> produce_asn_core_with_post tpenv h (pats @ ghostenv) (xenv @ env) p coef size_all size_all assuming cont_with_post))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpAsn l -> cont h ghostenv env
    | ForallAsn (l, ManifestTypeExpr(_, tp), i, e) ->
      in_temporary_context begin fun () ->
        ctxt#begin_formal;
        let forall = (eval None ((i, ctxt#mk_bound 0 (typenode_of_provertype (provertype_of_type tp))) :: env) e) in
        ctxt#end_formal;
        ctxt#assume_forall "forall_ assertion" [] [(typenode_of_provertype (provertype_of_type tp))] forall;
        cont h ghostenv env
      end
    | CoefAsn (l, DummyPat, body) ->
      produce_asn_core_with_post tpenv h ghostenv env body (get_dummy_frac_term ()) size_first size_all assuming cont_with_post
    | CoefAsn (l, DummyVarPat, body) ->
      static_error l "Producing a dummy variable pattern fraction is not yet supported" None
    | CoefAsn (l, coef', body) ->
      evalpat true ghostenv env coef' RealType RealType $. fun ghostenv env coef' ->
      produce_asn_core_with_post tpenv h ghostenv env body (real_mul l coef coef') size_first size_all assuming cont_with_post
    | EnsuresAsn (l, body) ->
      cont_with_post h ghostenv env (Some body)
    | WPredExprAsn (l, e, pts, inputParamCount, pats) ->
      let symb = eval None env e in
      let pts' = instantiate_types tpenv pts in
      evalpats ghostenv env pats pts pts' $. fun ghostenv env ts ->
      produce_chunk h (symb, false) [] coef inputParamCount ts None @@ fun h ->
      cont h ghostenv env
    )
  
  let rec produce_asn_core tpenv h ghostenv env p coef size_first size_all (assuming: bool) cont: symexec_result =
    produce_asn_core_with_post tpenv h ghostenv env p coef size_first size_all (assuming: bool) (fun h env ghostenv post -> cont h env ghostenv)
    
  let produce_asn tpenv h ghostenv (env: (string * termnode) list) p coef size_first size_all cont =
    produce_asn_core_with_post tpenv h ghostenv env p coef size_first size_all false (fun h env ghostenv post -> cont h env ghostenv)
  
  let produce_asn_with_post tpenv h ghostenv (env: (string * termnode) list) p coef size_first size_all cont =
    produce_asn_core_with_post tpenv h ghostenv env p coef size_first size_all false cont
  
  (* Region: consumption of assertions *)
  
  let rec match_pat h l ghostenv env env' isInputParam pat tp0 tp t cont_nomatch cont =
    let match_terms v t =
      if
        if tp = Bool then
          v == t || ctxt#query (ctxt#mk_iff v t)
        else
          definitely_equal v t
      then
        cont ghostenv env env'
      else if isInputParam then
        cont_nomatch ()
      else
        assert_false h env l (Printf.sprintf "Cannot prove %s == %s" (ctxt#pprint t) (ctxt#pprint v)) None
    in
    match pat with
    | SrcPat (LitPat (WVar (lx, x, LocalVar))) ->
      begin match try_assoc x env with
        Some t' -> match_terms (prover_convert_term t' tp0 tp) t
      | None -> let binding = (x, prover_convert_term t tp tp0) in cont ghostenv (binding::env) (binding::env')
      end
    | SrcPat (LitPat e) ->
      match_terms (prover_convert_term (eval None env e) tp0 tp) t
    | TermPat t0 -> match_terms (prover_convert_term t0 tp0 tp) t
    | SrcPat (VarPat (_, x)) -> cont (x::ghostenv) ((x, prover_convert_term t tp tp0)::env) env'
    | SrcPat (DummyPat|DummyVarPat) -> cont ghostenv env env'
    | SrcPat (WCtorPat (l, i, targs, g, ts0, ts, pats, _)) ->
      let t = prover_convert_term t tp tp0 in
      let (_, inductive_tparams, ctormap, _, _, _, _, _) = List.assoc i inductivemap in
      let cont () =
        let (_, (_, _, _, _, (symb, _))) = List.assoc g ctormap in
        let vs = map3 begin fun tp0 tp pat ->
            let x =
              match pat with
                VarPat (_, x) -> x
              | _ -> "value"
            in
            let v = get_unique_var_symb x tp in
            (v, prover_convert_term v tp tp0)
          end ts0 ts pats
        in
        let formula = ctxt#mk_eq t (ctxt#mk_app symb (List.map snd vs)) in
        assume formula $. fun () ->
        let inputParamCount = if isInputParam then max_int else 0 in
        let pats = List.map (fun pat -> SrcPat pat) pats in
        match_pats h l ghostenv env env' inputParamCount 0 pats ts ts (List.map fst vs) cont_nomatch cont
      in
      let rec check_not_other_ctors (cs : (string * (inductive_ctor_info)) list) =
        match cs with
          [] -> cont ()
        | (g', (_, (_, _, _, param_names_and_types, (symb, _))))::cs ->
          let (_, ts0) = List.split param_names_and_types in
          if
            g' = g ||
            in_temporary_context begin fun () ->
              let vs = List.map (fun t -> get_unique_var_symb "value" t) ts0 in
              ctxt#assume (ctxt#mk_eq t (ctxt#mk_app symb vs)) = Unsat
            end
          then
            check_not_other_ctors cs
          else
            if isInputParam then
              cont_nomatch ()
            else
              assert_false h env l (Printf.sprintf "Cannot prove that '%s' is not an instance of constructor '%s'" (ctxt#pprint t) g') None
      in
      check_not_other_ctors ctormap
  and match_pats h l ghostenv env env' inputParamCount index pats tps0 tps ts cont_nomatch cont =
    match (pats, tps0, tps, ts) with
      (pat::pats, tp0::tps0, tp::tps, t::ts) ->
      let isInputParam = index < inputParamCount in
      match_pat h l ghostenv env env' isInputParam pat tp0 tp t cont_nomatch @@ fun ghostenv env env' ->
      match_pats h l ghostenv env env' inputParamCount (index + 1) pats tps0 tps ts cont_nomatch cont
    | ([], [], [], []) -> cont ghostenv env env'
  
  (** Checks if the specified predicate assertion matches the specified chunk. If not, returns None. Otherwise, returns the environment updated with new bindings and other stuff.
      Parameters:
        ghostenv (ghostEnvironment): string list -- The list of all variables that are ghost variables (i.e., not real variables). match_chunk adds all new bindings to this
          list. (Or, more correctly, it returns an updated list obtained by adding all new bindings.
        h (heap): chunk list -- Passed in only so that it can be passed to assert_false when an error is detected.
        env (environment): (string * term) list -- The environment used to evaluate expressions in the predicate assertion, and updated with new bindings.
        env' (environment'): (string * term) list -- The list of bindings of unbound variables. When closing a chunk, the user need not specify values for all arguments.
          As a result, the predicate body gets evaluated with an incomplete environment. This is okay so long as all unspecified (i.e. unbound) parameters appear in
          special positions where VeriFast knows how to derive their value, e.g. in the position of an output argument of a precise predicate assertion.
          match_chunk updates this list with new bindings.
        l (sourceLocation): loc -- The appropriate source location to use when reporting an error
        g (predicateName): (term * bool) -- Predicate name specified in the predicate assertion, against which to compare the predicate name of the chunk
        targs (typeArguments): type_ list -- (For a predicate with type parameters) The type arguments specified in the predicate assertion, possibly further
          instantiated with type variable bindings from the environment of this operation, e.g. from an outer type-parameterized predicate.
        coef (baseCoefficient): term -- A term denoting a real number. The base coefficient with which the coefficient specified in the predicate assertion should
          be multiplied before comparing with the coefficient of the chunk. The base coefficient is typically 1, but can be something else if a coefficient is
          specified in a close statement, e.g. "close [1/2]foo();".
        coefpat (coefficientPattern): pat0 -- Coefficient pattern specified in the predicate assertion
        inputParamCount (inputParameterCount): int option -- In case of a precise predicate, specified the number of input parameters
        pats (argumentPatterns): pat0 list -- Predicate arguments specified in the predicate assertion
        tps0 (semiinstantiatedParameterTypes): type_ list -- Parameter types of the predicate when instantiating its type parameters with the type arguments specified in
          the predicate assertion. Note that these may themselves contain type variables declared by e.g. the predicate that contains the predicate assertion. The
          latter are not instantiated. The predicate argument expressions have been typechecked against these partially-instantiated types. Therefore, the environment
          used to evaluate the predicate arguments must be boxed correctly for these types. (Boxing is necessary because the SMT solvers do not support generics.)
        tps (instantiatedParameterTypes): type_ list -- Parameter types of the predicate, after instantiation with both the type parameter bindings specified in
          the predicate assertion and any additional type parameter bindings from the environment. The chunk argument terms are of these types.
        chunk: chunk -- The chunk against which to match the predicate assertion
      Returns:
        None -- no match
        Some (chunk, coef0, ts0, size0, ghostenv, env, env', newChunks)
          chunk: chunk -- The chunk that was matched
          coef0, ts0, size0 -- Coefficient, arguments, size of the chunk that was matched (duplicates stuff from 'chunk')
          ghostenv -- Updated ghost environment
          env -- Updated environment
          env' -- Updated list of bindings of unbound variables
          newChunks -- Any new chunks generated by this match; in particular, auto-splitting of fractional permissions.
   *)
  let match_chunk ghostenv h env env' l g targs coef coefpat inputParamCount pats tps0 tps (Chunk (g', targs0, coef0, ts0, size0) as chunk) cont =
    let match_coef ghostenv env cont =
      if coef == real_unit && coefpat == real_unit_pat && coef0 == real_unit then cont chunk ghostenv env coef0 [] else
      let match_term_coefpat t =
        let t = real_mul l coef t in
        if definitely_equal t coef0 then
          cont chunk ghostenv env coef0 []
        else
          let half_coef0 = ctxt#mk_real_mul real_half coef0 in
          if definitely_equal t half_coef0 then
            let chunk' = Chunk (g', targs0, half_coef0, ts0, size0) in
            cont chunk' ghostenv env half_coef0 [chunk']
          else if ctxt#query (ctxt#mk_real_lt real_zero t) && ctxt#query (ctxt#mk_real_lt t coef0) then
            cont (Chunk (g', targs0, t, ts0, size0)) ghostenv env t [Chunk (g', targs0, ctxt#mk_real_sub coef0 t, ts0, size0)]
          else
            None
            (*if inputParamCount = None then
              None
            else
              assert_false h env l (Printf.sprintf "Fraction mismatch: cannot prove %s == %s or 0 < %s < %s" (ctxt#pprint t) (ctxt#pprint coef0) (ctxt#pprint t) (ctxt#pprint coef0)) (Some "fractionmismatch")*)
      in
      match coefpat with
        SrcPat (LitPat e) -> match_term_coefpat (eval None env e)
      | TermPat t -> match_term_coefpat t
      | SrcPat (VarPat (_, x)) -> cont chunk (x::ghostenv) (update env x (real_div l coef0 coef)) coef0 []
      | SrcPat DummyPat ->
        if is_dummy_frac_term coef0 then
          let dummy' = get_dummy_frac_term () in
          cont (Chunk (g', targs0, dummy', ts0, size0)) ghostenv env dummy' [Chunk (g', targs0, get_dummy_frac_term (), ts0, size0)]
        else
          cont chunk ghostenv env coef0 []
      | SrcPat DummyVarPat ->
        static_error l "Consuming a dummy variable pattern fraction is not yet supported" None
    in
    if not (predname_eq g g' && List.for_all2 unify targs targs0) then cont None else
    let inputParamCount = match inputParamCount with None -> max_int | Some n -> n in
    match_pats h l ghostenv env env' inputParamCount 0 pats tps0 tps ts0 (fun () -> cont None) $. fun ghostenv env env' ->
    cont (match_coef ghostenv env $. fun chunk ghostenv env coef0 newChunks -> Some (chunk, coef0, ts0, size0, ghostenv, env, env', newChunks))
  
  let lookup_points_to_chunk_core h0 f_symb targs t =
    let rec iter h =
      match h with
        [] -> None
      | Chunk ((g, true), targs', coef, [t0; v], _)::_ when g == f_symb && List.for_all2 unify targs targs' && definitely_equal t0 t -> Some v
      | Chunk ((g, false), targs', coef, [t0; v], _):: _ when definitely_equal g f_symb && List.for_all2 unify targs targs' && definitely_equal t0 t -> Some v
      | _::h -> iter h
    in
    iter h0

  let lookup_integer__chunk_core h0 addr k signedness =
    let integer__symb = integer__symb () in
    let size = rank_size_term k in
    let signed = mk_bool (signedness = Signed) in
    let rec iter h =
      match h with
        [] -> None
      | Chunk ((g, true), targs, coef, [addr0; size0; signed0; v], _)::_ when g == integer__symb && definitely_equal addr0 addr && definitely_equal size0 size && definitely_equal signed0 signed -> Some v
      | Chunk ((g, false), targs, coef, [addr0; size0; signed0; v], _):: _ when definitely_equal g integer__symb && definitely_equal addr0 addr && definitely_equal size0 size && definitely_equal signed0 signed -> Some v
      | _::h -> iter h
    in
    iter h0

  let lookup_points_to_chunk h0 env l f_symb targs t =
    match lookup_points_to_chunk_core h0 f_symb targs t with
      None ->
        let targs = if targs = [] then "" else "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">" in
        assert_false h0 env l ("No matching points-to chunk: " ^ (ctxt#pprint f_symb) ^ targs ^ "(" ^ (ctxt#pprint t) ^ ", _)") None
    | Some v -> v

  let lookup_integer__chunk h0 env l tp t =
    let (k, signedness) =
      match int_rank_and_signedness tp with
        Some (k, signedness) -> k, signedness
      | None -> static_error l ("Dereferencing a pointer of type " ^ string_of_type tp ^ " is not yet supported.") None
    in
    match lookup_integer__chunk_core h0 t k signedness with
      None -> assert_false h0 env l ("No matching points-to chunk: integer_(" ^ ctxt#pprint t ^ ", " ^ ctxt#pprint (rank_size_term k) ^ ", " ^ (if signedness = Signed then "true" else "false") ^ ", _)") None
    | Some v -> v

  let read_field h env l t fparent targs fname =
    let (_, (_, _, _, _, f_symb, _, _)), _ = List.assoc (fparent, fname) field_pred_map in
    lookup_points_to_chunk h env l f_symb targs t
  
  let read_static_field h env l fparent fname =
    let (_, (_, _, _, _, f_symb, _, _)), _ = List.assoc (fparent, fname) field_pred_map in
    match extract (function Chunk (g, targs, coef, arg0::args, size) when predname_eq (f_symb, true) g -> Some arg0 | _ -> None) h with
      None -> assert_false h env l ("No matching heap chunk: " ^ ctxt#pprint f_symb) None
    | Some (v, _) -> v
  
  let try_read_java_array h env l a i tp =
    head_flatmap
      begin function
        Chunk ((g, true), [tp], coef, [a'; i'; v], _)
          when g == array_element_symb() && definitely_equal a' a && definitely_equal i' i ->
          [v]
      | Chunk ((g, true), [tp], coef, [a'; istart; iend; vs], _)
          when g == array_slice_symb() && definitely_equal a' a && ctxt#query (ctxt#mk_and (ctxt#mk_le istart i) (ctxt#mk_lt i iend)) ->
          [mk_nth tp (ctxt#mk_sub i istart) vs]
     (* | Chunk ((g, true), [tp;tp2;tp3], coef, [a'; istart; iend; p; info; elems; vs], _)
          when g == array_slice_deep_symb() && definitely_equal a' a && ctxt#query (ctxt#mk_and (ctxt#mk_le istart i) (ctxt#mk_lt i iend)) ->
          let (_, _, _, _, nth_symb) = List.assoc "nth" purefuncmap in
          [apply_conversion ProverInductive (provertype_of_type tp) (mk_app nth_symb [ctxt#mk_sub i istart; vs])]*)
      | _ -> []
      end
      h
  
  let try_update_java_array h env l a i tp new_value =
    let rec try_update_java_array_core todo seen = 
      match todo with
        [] -> None
      | Chunk ((g, true), [tp], coef, [a'; i'; v], b) :: rest
          when g == array_element_symb() && definitely_equal a' a && definitely_equal i' i && definitely_equal coef real_unit ->
        Some(seen @ ((Chunk ((g, true), [tp], coef, [a'; i'; new_value], b)) :: rest))
      | Chunk ((g, true), [tp], coef, [a'; istart; iend; vs], b) :: rest
          when g == array_slice_symb() && definitely_equal a' a && ctxt#query (ctxt#mk_and (ctxt#mk_le istart i) (ctxt#mk_lt i iend)) && definitely_equal coef real_unit ->
        let (_, _, _, _, update_symb) = List.assoc "update" purefuncmap in
        let converted_new_value = apply_conversion (provertype_of_type tp) ProverInductive new_value in
        let updated_vs = (mk_app update_symb [ctxt#mk_sub i istart; converted_new_value; vs]) in
        Some(seen @ ((Chunk ((g, true), [tp], coef, [a'; istart; iend; updated_vs], b)) :: rest))
      | chunk :: rest ->
        try_update_java_array_core rest (seen @ [chunk])
    in
      try_update_java_array_core h [] 
  
  let read_java_array h env l a i tp =
    let slices = try_read_java_array h env l a i tp in
    match slices with
      None -> assert_false h env l "No matching array element or array slice chunk" None
    | Some v -> v
  
  let pointee_pred_symb l pointeeType =
    match try_pointee_pred_symb pointeeType with
      Some symb -> symb
    | None -> static_error l ("Dereferencing pointers of type " ^ string_of_type pointeeType ^ " is not yet supported.") None
  
  let read_integer__array h env l a i tp =
    let (k, signedness) =
      match int_rank_and_signedness tp with
        Some (k, signedness) -> k, signedness
      | None -> static_error l ("Dereferencing array elements of type " ^ string_of_type tp ^ " is not yet supported.") None
    in
    let integers__symb = integers__symb () in
    let size = rank_size_term k in
    let signed = mk_bool (signedness = Signed) in
    let slices =
      head_flatmap
        begin function
          Chunk (g, [], coef, [a'; size'; signed'; n'; vs'], _)
            when
              predname_eq g (integers__symb, true) &&
              definitely_equal a' a &&
              definitely_equal size' size &&
              definitely_equal signed' signed &&
              ctxt#query (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) i) (ctxt#mk_lt i n')) ->
            [mk_nth tp i vs']
        | _ -> []
        end
        h
    in
    match slices with
      None ->
        begin match lookup_integer__chunk_core h (mk_ptr_add_ l a i tp) k signedness with
          None ->
          assert_false h env l
            (sprintf "No matching array chunk: integers_(%s, %s, %s, 0<=%s<n, _)"
               (ctxt#pprint a)
               (ctxt#pprint size)
               (ctxt#pprint signed)
               (ctxt#pprint i))
            None
        | Some v -> v
        end
    | Some v -> v

  let read_c_array h env l a i tp =
    match try_pointee_pred_symb0 tp with
      None -> read_integer__array h env l a i tp
    | Some (_, predsym, _, array_predsym, _, _, _, _, _, _, _, _) ->
    let slices =
      head_flatmap
        begin function
          Chunk (g, [], coef, [a'; n'; vs'], _)
            when
              predname_eq g (array_predsym, true) &&
              definitely_equal a' a &&
              ctxt#query (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) i) (ctxt#mk_lt i n')) ->
            [mk_nth tp i vs']
        | _ -> []
        end
        h
    in
    match slices with
      None ->
        begin match lookup_points_to_chunk_core h predsym [] (mk_ptr_add_ l a i tp) with
          None ->
          assert_false h env l
            (sprintf "No matching array chunk: %s(%s, 0<=%s<n, _)"
               (ctxt#pprint array_predsym)
               (ctxt#pprint a)
               (ctxt#pprint i))
            None
        | Some v -> v
        end
    | Some v -> v
  
  let read_array h env l a i tp = 
    match language with 
      Java -> read_java_array h env l a i tp
    | CLang -> read_c_array h env l a i tp
  
  let deref_pointer h env l pointerTerm pointeeType =
    match try_pointee_pred_symb pointeeType with
      None -> lookup_integer__chunk h env l pointeeType pointerTerm
    | Some predsym -> lookup_points_to_chunk h env l predsym [] pointerTerm
  
  let lists_disjoint xs ys =
    List.for_all (fun x -> not (List.mem x ys)) xs
  
  let with_updated_ref r f body =
    let value = !r in
    r := f value;
    do_finally body (fun () -> r := value)
  
  let string_of_chunk_asn env g targs coef coefpat pats =
    let predname = match g with (g, _) -> ctxt#pprint g in
    let targs =
      match targs with
        [] -> ""
      | _ -> Printf.sprintf "<%s>" (String.concat ", " (List.map string_of_type targs))
    in
    let patvars = ref [] in
    let rec string_of_pat pat =
      match pat with
      | LitPat (WVar (_, x, LocalVar)) -> if List.mem_assoc x env then ctxt#pprint (List.assoc x env) else "_"
      | LitPat e -> if !patvars = [] || lists_disjoint !patvars (vars_used e) then ctxt#pprint (eval None env e) else "<expr>"
      | DummyPat -> "_"
      | DummyVarPat -> "?_"
      | VarPat (_, x) -> patvars := x::!patvars; "_"
      | WCtorPat (_, i, targs, g, ts0, ts, pats, _) -> Printf.sprintf "%s(%s)" g (String.concat ", " (List.map string_of_pat pats))
    in
    let string_of_pat0 pat0 =
      match pat0 with
        TermPat t -> ctxt#pprint t
      | SrcPat pat -> string_of_pat pat
    in
    let coef =
      if coef == real_unit then
        if coefpat == real_unit_pat then
          ""
        else
          "[" ^ string_of_pat0 coefpat ^ "]"
      else
        if coefpat == real_unit_pat then
          "[" ^ ctxt#pprint coef ^ "]"
        else
          "[" ^ ctxt#pprint coef ^ " * " ^ string_of_pat0 coefpat ^ "]"
    in
    Printf.sprintf "%s%s%s(%s)" coef predname targs (String.concat ", " (List.map string_of_pat0 pats))

  let consume_chunk_recursion_depth = ref 0
  
  (** consume_chunk_core attempts to consume a chunk matching the specified predicate assertion from the specified heap.
      If no matching chunk is found in the heap, automation rules are tried (e.g. auto-open and auto-close rules).
      Parameters:
        rules -- The automation rules
        h (heap): chunk list -- The heap
        ghostenv (ghostEnvironment): string list -- The list of ghost variables. Used to check that ghost variables are not used in real code.
        env (environment): (string * term) list -- The environment that binds variable names to their symbolic value. Updated with new bindings.
        env' (unboundVariableBindings): (string * term) list -- Bindings of variables that were declared but not bound. (Happens when you do not specify values for all predicate parameters when closing a chunk.)
        l (sourceLocation): loc -- Appropriate source location to use when reporting an error.
        g (predicateName): (term * bool) -- Predicate name specified in the predicate assertion.
        targs (typeArguments): type_ list -- Type arguments specified in the predicate assertion, instantiated with any type variable bindings currently in effect
        coef (baseCoefficient): term -- Base coefficient in effect. The coefficient specified in the predicate assertion should be multiplied by this base coefficient
          before comparing with a chunk found in the heap. Typically 1, unless e.g. a coefficient is specified in a close statement ('close [1/2]foo();').
        coefpat (coefficientPattern): pat0 -- Coefficient specified in the predicate assertion.
        inputParamCount (inputParameterCount): int option -- If the predicate is precise, specifies the number of input parameters.
        pats (argumentPatterns): pat0 list -- Predicate arguments specified in the predicate assertion.
        tps0 (semiinstantiatedParameterTypes): type_ list -- Predicate parameter types, after instantiation with the type arguments specified in the predicate
          assertion, but without further instantiation. Argument expressions in 'pats' are typechecked against these types and expect that terms are boxed correctly
          with respect to these types.
        tps (instantiatedParameterTypes): type_ list -- Predicate parameter types, after instantiation with the type arguments specified in the predicate assertion,
          as well as any additional type variable bindings currently in effect (e.g. type arguments of an outer predicate, as in 'close foo<int>();').
        cont: continuation called if successful. Typical call:
          [cont chunk h coef ts size ghostenv env env']
            chunk: chunk -- chunk that was consumed (used by the 'leak' command to re-produce all consumed chunks with dummy fraction coefficients)
            h -- heap obtained by removing the consumed chunk (as well as applying any automation rules)
            coef, ts, size -- Coefficient, arguments, size of consumed chunk (duplicates info from 'chunk')
            ghostenv: string list -- Updated ghost environment
            env: (string * term) list -- Updated environment
            env': (string * term) list -- Updated list of bindings of declared but unbound variables
    *)
  let consume_chunk_core rules h ghostenv env env' l g targs coef coefpat inputParamCount pats tps0 tps cont =
    if !verbosity >= 4 then printff "%10.6fs: Consuming chunk %s\n" (Perf.time ()) (string_of_chunk_asn env g targs coef coefpat pats);
    let old_depth = !consume_chunk_recursion_depth in
    let rec consume_chunk_core_core h =
      begin fun cont ->
      let rec iter hprefix h =
        match h with
          [] -> cont []
        | chunk::h ->
          match_chunk ghostenv h env env' l g targs coef coefpat inputParamCount pats tps0 tps chunk $. fun result ->
          match result with
            None -> iter (chunk::hprefix) h
          | Some (chunk, coef, ts, size, ghostenv, env, env', newChunks) -> cont [(chunk, newChunks @ hprefix @ h, coef, ts, size, ghostenv, env, env')]
      in
      iter [] h
      end $. fun matching_chunks ->
      match matching_chunks with
        [] ->
        begin fun cont ->
          if !consume_chunk_recursion_depth > 20 then begin
            if !verbosity >= 2 then printff "%10.6fs: Recursively consuming chunk: maximum recursion depth exceeded; giving up\n" (Perf.time());
            cont ()
          end else begin
          if !verbosity >= 2 && !consume_chunk_recursion_depth > 0 then printff "%10.6fs: Recursively consuming chunk (recursion depth %d)\n" (Perf.time()) !consume_chunk_recursion_depth;
          incr consume_chunk_recursion_depth;
          let (g, inputParamCount) = match inputParamCount with 
            Some (n) -> (g, inputParamCount)
          | None when not (snd g) ->
            begin match try_find (fun (_, (_, _, _, _, symb, _, _)) -> symb == fst(g)) predfammap with
              Some (_, (_, _, _, _, symb, inputParamCount, _)) -> ((symb, true), inputParamCount)
            | None -> begin match try_assq (fst g) !pred_ctor_applications with
                None -> (g, None)
              | Some (funsym, funterm, targs, args, inputParamCount) -> (g, inputParamCount)
              end
            end
          | None -> (g, None)
          in 
          if inputParamCount = None then begin cont () end else
          begin fun cont' ->
            let Some inputParamCount = inputParamCount in
            let rec iter n ts pats tps0 tps =
              if n = 0 then cont' (List.rev ts) else
              match (pats, tps0, tps) with
              | (pat::pats, tp0::tps0, tp::tps) ->
                let ok t = iter (n - 1) (prover_convert_term t tp0 tp::ts) pats tps0 tps in
                match pat with
                  SrcPat (LitPat e | WCtorPat (_, _, _, _, _, _, _, Some e)) -> ok (eval None env e)
                | TermPat t -> ok t
                | _ -> cont ()
            in
            iter inputParamCount [] pats tps0 tps
          end $. fun ts ->
          match g with
            (g, _) ->
            let try_rules rules ts = 
              let terms_are_well_typed = List.for_all (function SrcPat (LitPat (WidenedParameterArgument _)) -> false | _ -> true) pats in
             (* let _ = print_endline ("#rules for " ^ (ctxt#pprint g) ^ "=" ^ (string_of_int (List.length rules))) in *)
              let rec iter rules =
                let coefpat = match coefpat with SrcPat (LitPat e) -> TermPat (eval None env e) | _ -> coefpat in 
                match rules with
                 [] -> cont ()
                | rule::rules ->
                  rule l h env targs terms_are_well_typed coef coefpat ts $. fun h ->
                  match h with
                    None -> iter rules
                  | Some h ->
                    with_context (Executing (h, env, l, "Consuming chunk (retry)")) $. fun () ->
                    consume_chunk_core_core h
              in
                iter rules
            in
            let open_close_rules = match try_assq g ! rules with None -> [] | Some(rules) -> !rules in
            let lemma_rules = match try_assq g !lemma_rules with None -> [] | Some(rules) -> !rules in
            begin match open_close_rules @ lemma_rules with
              [] ->  begin match try_assq g ! pred_ctor_applications with 
                | Some (_, symbol_term, [], ctor_args, _) -> 
                  begin match try_assq symbol_term ! rules with
                    Some rules -> try_rules !rules (ctor_args @ ts)
                  | None -> cont ()
                  end
                | _ -> cont ()
              end
            | rules -> try_rules rules ts
            end
          end
        end $. fun () ->
        let message =
          Printf.sprintf "No matching heap chunks: %s" (string_of_chunk_asn env g targs coef coefpat pats)
        in
        assert_false h env l message (Some "nomatchingheapchunks")
  (*      
      | [(h, ts, ghostenv, env)] -> cont h ts ghostenv env
      | _ -> assert_false h env l "Multiple matching heap chunks." None
  *)
      | (chunk, h, coef, ts, size, ghostenv, env, env')::_ ->
        consume_chunk_recursion_depth := old_depth;
        cont chunk h coef ts size ghostenv env env'
    in
    consume_chunk_core_core h
  
  (** [cont] is called as [cont chunk h coef ts size ghostenv env env']. See docs at consume_chunk_core. *)
  let consume_chunk rules h ghostenv env env' l g targs coef coefpat inputParamCount pats cont =
    let tps = List.map (fun _ -> intType) pats in (* dummies, to indicate that no prover type conversions are needed *)
    consume_chunk_core rules h ghostenv env env' l g targs coef coefpat inputParamCount pats tps tps cont
  
  let srcpat pat = SrcPat pat
  let srcpats pats = List.map srcpat pats

  let dummypat = SrcPat DummyPat
  
  let consume_points_to_chunk__core rules h ghostenv env env' l type0 type_ coef coefpat addr rhs consumeUninitChunk cont =
    let tp0, tp =
      if consumeUninitChunk && rhs = dummypat then
        option_type type0, option_type type_
      else
        type0, type_
    in
    match try_pointee_pred_symb0 type_ with
      Some (_, predsym, _, _, _, _, _, _, _, uninit_predsym, _, _) ->
      consume_chunk_core rules h ghostenv env env' l ((if consumeUninitChunk && rhs = dummypat then uninit_predsym else predsym), true) [] coef coefpat (Some 1) [TermPat addr; rhs] [voidPtrType; tp0] [voidPtrType; tp]
        (fun chunk h coef [_; value] size ghostenv env env' -> cont chunk h coef value ghostenv env env')
    | None ->
    match int_rank_and_signedness type_ with
      Some (k, signedness) ->
      consume_chunk_core rules h ghostenv env env' l ((if consumeUninitChunk && rhs = dummypat then integer___symb () else integer__symb ()), true) [] coef coefpat (Some 3)
        [TermPat addr; TermPat (rank_size_term k); TermPat (mk_bool (signedness = Signed)); rhs] [voidPtrType; intType; Bool; tp0] [voidPtrType; intType; Bool; tp]
        (fun chunk h coef [_; _; _; value] size ghostenv env env' -> cont chunk h coef value ghostenv env env')
    | None ->
      consume_chunk_core rules h ghostenv env env' l ((if consumeUninitChunk && rhs = dummypat then generic_points_to__symb () else generic_points_to_symb ()), true) [type_] coef coefpat (Some 1)
        [TermPat addr; rhs] [voidPtrType; tp0] [voidPtrType; tp]
        (fun chunk h coef [_; value] size ghostenv env env' -> cont chunk h coef value ghostenv env env')

  let consume_points_to_chunk_ rules h ghostenv env env' l type_ coef coefpat addr rhs consumeUninitChunk cont =
    consume_points_to_chunk__core rules h ghostenv env env' l type_ type_ coef coefpat addr rhs consumeUninitChunk cont
  
  let consume_points_to_chunk rules h ghostenv env env' l type_ coef coefpat addr rhs cont =
    consume_points_to_chunk_ rules h ghostenv env env' l type_ coef coefpat addr rhs false cont

  let consume_instance_predicate_chunk rules h ghostenv env env' l symbol (target_type, target) (index_type, index) family coef coefpat pats types cont =
    let family_target, family_target_type =
      match dialect, target_type with
      | Some Cxx, PtrType (StructType (target_type_name, [])) ->
        base_addr l (target_type_name, target) family, PtrType (StructType (family, []))
      | _ -> 
        target, target_type
    in
    let consume_types = family_target_type :: index_type :: types in
    let consume_pats = TermPat family_target :: TermPat index :: srcpats pats in 
    consume_chunk_core rules h ghostenv env env' l (symbol, true) [] coef coefpat (Some 2) consume_pats consume_types consume_types cont


  let rec consume_asn_core_with_post rules tpenv h ghostenv env env' p checkDummyFracs coef cont_with_post =
    let cont chunks h ghostenv env env' size_first = cont_with_post chunks h ghostenv env env' size_first None in
    let with_context_helper cont =
      match p with
        Sep (_, _, _) -> cont()
      | _ ->
        with_context ~verbosity_level:2 (Executing (h, env, asn_loc p, "Consuming assertion")) cont
    in
    with_context_helper (fun _ ->
    let ev = eval None env in
    let check_dummy_coefpat l coefpat coef =
      if language = CLang && checkDummyFracs then
      match coefpat with
        SrcPat DummyPat -> if not (is_dummy_frac_term coef) then assert_false h env l "Cannot match a non-dummy fraction chunk against a dummy fraction pattern. First leak the chunk using the 'leak' command." None
      | _ -> ()
    in
    let points_to l coefpat e tp rhs =
      match e with
        WRead (lr, e, fparent, tparams, fname, frange, targs, fstatic, fvalue, fghost) ->
        let (_, (_, _, _, _, symb, _, _)), p__opt = List.assoc (fparent, fname) field_pred_map in
        let (inputParamCount, pats, tps0, tps) =
          if fstatic then
            (Some 0, [rhs], [tp], [tp])
          else
            (Some 1, [SrcPat (LitPat e); rhs], [voidPtrType; tp], [voidPtrType; instantiate_type tpenv tp])
        in
        let symb_used =
          match rhs, p__opt with
            SrcPat DummyPat, Some ((_, (_, _, _, _, symb_, _, _))) ->
            symb_
          | _ ->
            symb
        in
        let targs = List.map (instantiate_type tpenv) targs in
        consume_chunk_core rules h ghostenv env env' l (symb_used, true) targs coef coefpat inputParamCount pats tps0 tps
          (fun chunk h coef ts size ghostenv env env' -> check_dummy_coefpat l coefpat coef; cont [chunk] h ghostenv env env' size)
      | WReadArray (la, ea, _, ei) ->
        let pats = [SrcPat (LitPat ea); SrcPat (LitPat ei); rhs] in
        consume_chunk rules h ghostenv env env' l (array_element_symb(), true) [instantiate_type tpenv tp] coef coefpat (Some 2) pats $.
        fun chunk h coef ts size ghostenv env env' ->
        check_dummy_coefpat l coefpat coef;
        cont [chunk] h ghostenv env env' size
      | WVar (lv, x, GlobalName) -> 
        let (_, type_, symbn, _) = List.assoc x globalmap in  
        consume_points_to_chunk_ rules h ghostenv env env' l type_ coef coefpat symbn rhs true
          (fun chunk h coef _ ghostenv env env' -> check_dummy_coefpat l coefpat coef; cont [chunk] h ghostenv env env' None)
      | WDeref(ld, e, td) ->  
        let symbn = eval None env e in
        let td' = instantiate_type tpenv td in
        consume_points_to_chunk__core rules h ghostenv env env' l td td' coef coefpat symbn rhs true
          (fun chunk h coef _ ghostenv env env' -> check_dummy_coefpat l coefpat coef; cont [chunk] h ghostenv env env' None)
    in
    let pred_asn l coefpat g is_global_predref targs pats0 pats =
      if g#name = "junk" && is_global_predref then
        cont h [] ghostenv env env' None
      else
      let (g_symb, pats0, pats, types) =
        if is_global_predref then
           match try_assoc g#name predfammap with
            Some (_, _, _, _, symb, _, _) -> ((symb, true), pats0, pats, g#domain)
          | None -> 
            let PredCtorInfo (_, tparams, ps1, ps2, inputParamCount, body, funcsym) = List.assoc g#name predctormap in
            if tparams <> [] then static_error l "Generic predicate constructor assertions are not yet supported" None;
            let ctorargs = List.map (function SrcPat (LitPat e | WCtorPat (_, _, _, _, _, _, _, Some e)) -> ev e | _ -> static_error l "Patterns are not supported in predicate constructor argument positions." None) pats0 in
            let g_symb = mk_app funcsym ctorargs in
            let (symbol, symbol_term) = funcsym in
            register_pred_ctor_application g_symb symbol symbol_term targs ctorargs inputParamCount;
            ((g_symb, false), [], pats, List.map snd ps2)
        else
          match try_assoc g#name env with
            None -> assert_false [] env l (Printf.sprintf "Unbound variable '%s'" g#name) None
          | Some term -> ((term, false), pats0, pats, g#domain)
      in
      let targs = instantiate_types tpenv targs in
      let domain = instantiate_types tpenv types in
      let inputParamCount = match g#inputParamCount with None -> None | Some n -> Some (List.length pats0 + n) in
      consume_chunk_core rules h ghostenv env env' l g_symb targs coef coefpat inputParamCount (pats0 @ pats) types domain (fun chunk h coef ts size ghostenv env env' ->
        check_dummy_coefpat l coefpat coef;
        cont [chunk] h ghostenv env env' size
      )
    in
    let inst_call_pred l coefpat e_opt static_type tn g index pats =
      let (pmap, pred_symb, ctparams) =
        match dialect with
        | None ->
          begin match try_assoc tn classmap1 with
            Some (lcn, abstract, fin, methods, fds_opt, ctors, super, tparams, interfs, preds, pn, ilist) ->
            let (_, pmap, _, symb, _) = List.assoc g preds in (pmap, symb, tparams)
          | None ->
            match try_assoc tn classmap0 with
              Some {cpreds; ctpenv} ->
              let (_, pmap, _, symb, _) = List.assoc g cpreds in (pmap, symb, ctpenv)
            | None ->
              match try_assoc tn interfmap1 with
                Some (li, fields, methods, preds, interfs, pn, ilist, tparams) -> let (_, pmap, family, symb) = List.assoc g preds in (pmap, symb, tparams)
              | None ->
                let InterfaceInfo (li, fields, methods, preds, interfs, tparams) = List.assoc tn interfmap0 in
                let (_, pmap, family, symb) = List.assoc g preds in
                (pmap, symb, tparams)
          end
        | Some Cxx ->
          let preds = List.assoc tn cxx_inst_pred_map in
          let _, pmap, _, symb, _ = List.assoc g preds in
          pmap, symb, []
      in
      let target = match e_opt with None -> List.assoc "this" env | Some e -> ev e in
      let types = List.map snd pmap in
      let target_type, index_type =
        match dialect with
        | Some Cxx ->
          PtrType (StructType (static_type, [])), type_info_ref_type
        | _ ->
          ObjType (tn, (List.map (fun tparam -> RealTypeParam tparam) ctparams)), ObjType ("java.lang.Class", [])
      in
      let index = ev index in
      consume_instance_predicate_chunk rules h ghostenv env env' l pred_symb (target_type, target) (index_type, index) tn coef coefpat pats types @@ fun chunk h coef ts size ghostenv env env' ->
      check_dummy_coefpat l coefpat coef;
      cont [chunk] h ghostenv env env' size
    in
    let pred_expr_asn l coefpat e pts inputParamCount pats =
      let g_symb = (ev e, false) in
      let pts' = instantiate_types tpenv pts in
      consume_chunk_core rules h ghostenv env env' l g_symb [] coef coefpat inputParamCount (srcpats pats) pts pts' @@ fun chunk h coef ts size ghostenv env env' ->
      check_dummy_coefpat l coefpat coef;
      cont [chunk] h ghostenv env env' size
    in
    match p with
    | WPointsTo (l, e, tp, rhs) -> points_to l real_unit_pat e tp (SrcPat rhs)
    | WPredAsn (l, g, is_global_predref, targs, pats0, pats) -> pred_asn l real_unit_pat g is_global_predref targs (srcpats pats0) (srcpats pats)
    | WInstPredAsn (l, e_opt, st, cfin, tn, g, index, pats) ->
      inst_call_pred l real_unit_pat e_opt st tn g index pats
    | ExprAsn (l, WOperation (lo, Eq, [WVar (lx, x, LocalVar); e], tp)) ->
      begin match try_assoc x env with
        Some t -> assert_term (if tp = Bool then ctxt#mk_iff t (ev e) else ctxt#mk_eq t (ev e)) h env l "Cannot prove condition." None; cont [] h ghostenv env env' None
      | None -> let binding = (x, ev e) in cont [] h ghostenv (binding::env) (binding::env') None
      end
    | ExprAsn (l, e) ->
      assert_expr env e h env l "Cannot prove condition." None; cont [] h ghostenv env env' None
    | WMatchAsn (l, e, pat, tp) ->
      let v = ev e in
      match_pat h l ghostenv env env' false (SrcPat pat) tp tp v (fun () -> assert false) $. fun ghostenv env env' ->
      cont [] h ghostenv env env' None
    | LetTypeAsn (l, x, tp, p) ->
      consume_asn_core_with_post rules ((x, tp)::tpenv) h ghostenv env env' p checkDummyFracs coef cont_with_post
    | Sep (l, p1, p2) ->
      consume_asn_core_with_post rules tpenv h ghostenv env env' p1 checkDummyFracs coef (fun chunks h ghostenv env env' size post ->
        if post <> None then static_error l "Left-hand operand of separating conjunction cannot specify a postcondition." None;
        consume_asn_core_with_post rules tpenv h ghostenv env env' p2 checkDummyFracs coef (fun chunks' h ghostenv env env' _ post ->
          cont_with_post (chunks @ chunks') h ghostenv env env' size post
        )
      )
    | IfAsn (l, e, p1, p2) ->
      let cont_with_post chunks h ghostenv1 env1 env'' _ post =
        let ghostenv, env =
          if post = None then ghostenv, env else ghostenv1, env1
        in
        cont_with_post chunks h ghostenv (env'' @ env) (env'' @ env') None post
      in
      let env' = [] in
      branch
        (fun _ ->
           assume (ev e) (fun _ ->
             consume_asn_core_with_post rules tpenv h ghostenv env env' p1 checkDummyFracs coef cont_with_post))
        (fun _ ->
           assume (ctxt#mk_not (ev e)) (fun _ ->
             consume_asn_core_with_post rules tpenv h ghostenv env env' p2 checkDummyFracs coef cont_with_post))
    | WSwitchAsn (l, e, i, cs) ->
      let cont_with_post chunks h ghostenv1 env1 env'' _ post =
        let ghostenv, env =
          if post = None then ghostenv, env else ghostenv1, env1
        in
        cont_with_post chunks h ghostenv (env'' @ env) (env'' @ env') None post
      in
      let env' = [] in
      let t = ev e in
      let (_, tparams, ctormap, _, _, _, _, _) = List.assoc i inductivemap in
      let rec iter cs =
        match cs with
          WSwitchAsnClause (lc, cn, pats, patsInfo, p)::cs ->
          let (_, (_, tparams, _, tps, ctorsym)) = List.assoc cn ctormap in
          let Some pts = zip pats tps in
          let (xs, xenv) =
            if tparams = [] then
              let xts = List.map (fun (x, (name, tp)) -> (x, get_unique_var_symb x tp)) pts in
              let xs = List.map (fun (x, t) -> t) xts in
              (xs, xts)
            else
              let Some pts = zip pts patsInfo in
              let xts =
                List.map
                  (fun ((x, (name, tp)), info) ->
                   match info with
                     None -> let term = get_unique_var_symb x tp in (x, term, term)
                   | Some proverType ->
                     let term = ctxt#mk_app (mk_symbol x [] (typenode_of_provertype proverType) Uninterp) [] in
                     let term' = convert_provertype term proverType ProverInductive in
                     (x, term', term)
                  )
                  pts
              in
              let xs = List.map (fun (x, t, _) -> t) xts in
              let xenv = List.map (fun (x, _, t) -> (x, t)) xts in
              (xs, xenv)
          in
          branch
            (fun _ -> assume_eq t (mk_app ctorsym xs) (fun _ -> consume_asn_core_with_post rules tpenv h (pats @ ghostenv) (xenv @ env) env' p checkDummyFracs coef cont_with_post))
            (fun _ -> iter cs)
        | [] -> success()
      in
      iter cs
    | EmpAsn l -> cont [] h ghostenv env env' None
    | ForallAsn (l, ManifestTypeExpr(_, tp), i, e) -> 
      let fresh_term = get_unique_var_symb i tp in
      assert_expr ((i, fresh_term) :: env) e h ((i, fresh_term) :: env) l "Cannot prove condition." None;
      cont [] h ghostenv env env' None
    | CoefAsn (l, coefpat, WPointsTo (_, e, tp, rhs)) -> points_to l (SrcPat coefpat) e tp (SrcPat rhs)
    | CoefAsn (l, coefpat, WPredAsn (_, g, is_global_predref, targs, pat0, pats)) -> pred_asn l (SrcPat coefpat) g is_global_predref targs (srcpats pat0) (srcpats pats)
    | CoefAsn (l, coefpat, WInstPredAsn (_, e_opt, st, cfin, tn, g, index, pats)) -> inst_call_pred l (SrcPat coefpat) e_opt st tn g index pats
    | EnsuresAsn (l, body) ->
      cont_with_post [] h ghostenv env env' None (Some body)
    | WPredExprAsn (l, e, pts, inputParamCount, pats) -> pred_expr_asn l real_unit_pat e pts inputParamCount pats
    | CoefAsn (l, coefpat, WPredExprAsn (_, e, pts, inputParamCount, pats)) -> pred_expr_asn l (SrcPat coefpat) e pts inputParamCount pats
    )
  
  let rec consume_asn_core rules tpenv h ghostenv env env' p checkDummyFracs coef cont =
    consume_asn_core_with_post rules tpenv h ghostenv env env' p checkDummyFracs coef $. fun chunks h ghostenv env env' size_first post ->
    cont chunks h ghostenv env env' size_first
  
  let consume_asn rules tpenv h ghostenv env p checkDummyFracs coef cont =
    consume_asn_core_with_post rules tpenv h ghostenv env [] p checkDummyFracs coef $. fun chunks h ghostenv env env' size_first post ->
    cont chunks h ghostenv env size_first

  let rec consume_asn_with_post rules tpenv h ghostenv env p checkDummyFracs coef cont =
    consume_asn_core_with_post rules tpenv h ghostenv env [] p checkDummyFracs coef $. fun chunks h ghostenv env env' size_first post ->
    cont chunks h ghostenv env size_first post
  
  let term_of_pred_index =
    match language with
      Java -> fun cn -> List.assoc cn classterms
    | CLang ->
      match dialect with
        Some Rust ->
        fun sn ->
        let _, [], _, _, s = List.assoc sn structmap in
        ctxt#mk_app s []
      | _ -> fun fn -> List.assoc fn funcnameterms
  
  let predinstmap_by_predfamsymb =
    flatmap
      begin fun ((p, fns), (env, l, predinst_tparams, xs, symb, inputParamCount, wbody)) ->
        if fns = [] && predinst_tparams = [] && env = [] then
          [(symb, (xs, wbody))]
        else
          []
      end
      predinstmap
  
  let typeid_env_of_tpenv l env tpenv =
    tpenv |> flatmap @@ fun (tparam, tp) ->
      if tparam_carries_typeid tparam then
        [(tparam ^ "_typeid", typeid_of_core l env tp)]
      else
        []

  (* Those predicate instances that, under certain conditions on the input parameters, are likely to be closeable. *)
  let empty_preds =
    flatmap
      begin fun (((p, fns), (env, l, predinst_tparams, xs, symb, inputParamCount, wbody)) as predinst) ->
        let fsymbs = List.map term_of_pred_index fns in
        match inputParamCount with
          None -> []
        | Some n ->
          let inputVars = List.map fst (take n xs) in
          let rec iter conds wbody cont =
            match wbody with
            | Sep (_, asn1, asn2) ->
              iter conds asn1 (fun conds -> iter conds asn2 cont)
            | IfAsn (_, cond, asn1, asn2) ->
              if expr_is_fixed inputVars cond then
                iter (cond::conds) asn1 cont @ iter (WOperation (dummy_loc, Not, [cond], boolt)::conds) asn2 cont
              else
                []
            | ExprAsn (_, WOperation (_, Eq, [WVar (_, x, _); e], _)) when not (List.mem x inputVars) && expr_is_fixed inputVars e ->
              cont conds
            | ExprAsn (_, e) when expr_is_fixed inputVars e ->
              cont (e::conds)
            | EmpAsn _ -> cont conds
            (*| ForallAsn _ -> cont conds*)
            | WSwitchAsn(_, e, i, cases) when expr_is_fixed inputVars e ->
              flatmap 
                (fun (WSwitchAsnClause (l, casename, args, boxinginfo, asn)) ->
                  if (List.length args) = 0 then
                    let cond = WOperation (l, Eq, [e; WVar (l, casename, PureFuncName [])], AnyType) in
                    iter (cond :: conds) asn cont
                  else 
                   []
                )
                cases
            | _ -> []
          in
          let conds = iter [] wbody (fun conds -> [conds]) in
          if conds <> [] then [(symb, fsymbs, conds, predinst)] else []
      end
      predinstmap
  
  (*let _ =
    begin print_endline "empty predicates:";
    List.iter
      (fun (from_symb, from_indices, conditions_list, _) ->
        begin 
          print_endline (ctxt#pprint from_symb);
          List.iter (fun conds -> 
            print_endline (string_of_int (List.length conds));
            (*List.iter (fun con -> print_endline ("    " ^ (ctxt#pprint con))) conds;*)
            print_endline "  or";
          ) 
          conditions_list;
        end
      )
      empty_preds
    end
  in*)

  let rec expr_of_fixed_pat pat =
    match pat with
      LitPat e -> e
    | WCtorPat (l, i, targs, g, ts0, ts, pats, Some e) -> e
  
  (** Find nested predicates in wbody0 *)
  let find_edges construct_edge inputParameters xs wbody0 =
    let rec iter coef conds wbody =
      match wbody with
        WPointsTo(_, WRead(lr, e, fparent, tparams, fname, frange, targs, fstatic, fvalue, fghost), tp, v) ->
        if expr_is_fixed inputParameters e || fstatic then
          let (_, (_, _, _, _, qsymb, _, _)), p__opt = List.assoc (fparent, fname) field_pred_map in
          let qsymb_used =
            match v, p__opt with
              DummyPat, Some ((_, (_, _, _, _, qsymb_, _, _))) -> qsymb_
            | _ -> qsymb
          in
          construct_edge qsymb_used coef None targs [] (if fstatic then [] else [voidPtrType]) (if fstatic then [] else [e]) conds
        else
          []
      | WPredAsn(_, q, true, qtargs, qfns, qpats) ->
          begin match try_assoc q#name predfammap with
            Some (_, qtparams, _, qtps, qsymb, _, _) ->
            begin match q#inputParamCount with
              None -> assert false;
            | Some qInputParamCount ->
              let qIndices = List.map (fun (LitPat e) -> e) qfns in
              let qInputActuals = List.map expr_of_fixed_pat (take qInputParamCount qpats) in
              if List.for_all (fun e -> expr_is_fixed inputParameters e) (qIndices @ qInputActuals) then
               construct_edge qsymb coef None qtargs qIndices (take qInputParamCount q#domain) qInputActuals conds
              else
                []
            end
          | None ->
            begin match try_assoc q#name predctormap with
              None -> []
            | Some(PredCtorInfo (l, tparams, ps1, ps2, inputParamCount, wbody, (funcsym, vsymb))) ->
              begin match inputParamCount with
              | Some qInputParamCount when tparams = [] ->
                let qIndices = List.map (fun (LitPat e) -> e) qfns in
                let qInputActuals = List.map expr_of_fixed_pat (take qInputParamCount qpats) in
                if List.for_all (fun e -> expr_is_fixed inputParameters e) (qIndices @ qInputActuals) then
                let inputParamTypes = List.map snd ps1 @ take qInputParamCount (List.map snd ps2) in
                construct_edge vsymb coef None [] [] inputParamTypes (qIndices @ qInputActuals) conds
                else
                  []
              | _ -> []
              end
            end
          end
      | WInstPredAsn(l2, target_opt, static_type_name, static_type_finality, family_type_string, instance_pred_name, index, args) ->
        let qsymb =
          match dialect with
          | None ->
            begin match try_assoc family_type_string classmap1 with
            | Some (lcn, abstract, fin, methods, fds_opt, ctors, super, tparams, interfs, preds, pn, ilist) ->
              let (_, _, _, symb, _) = List.assoc instance_pred_name preds in
              symb
            | None ->
              match try_assoc family_type_string classmap0 with
              | Some {cpreds} ->
                let (_, _, _, symb, _) = List.assoc instance_pred_name cpreds in
                symb
              | None ->
                match try_assoc family_type_string interfmap1 with
                | Some (li, fields, methods, preds, interfs, pn, ilist, tparams) -> 
                  let (_, _, family, symb) = List.assoc instance_pred_name preds in 
                  symb
                | None ->
                  let InterfaceInfo (li, fields, methods, preds, interfs, tparams) = List.assoc family_type_string interfmap0 in
                  let (_, pmap, family, symb) = List.assoc instance_pred_name preds in
                  symb
            end
          | Some Cxx ->
            let preds = List.assoc family_type_string cxx_inst_pred_map in 
            let _, _, _, symb, _ = List.assoc instance_pred_name preds in
            symb
        in
        if match target_opt with Some e -> expr_is_fixed inputParameters e | None -> true then begin
          let target = match target_opt with Some e -> Some e | None -> Some (WVar(l2, "this", LocalVar)) in
          let inner_info = target |> Option.map @@ fun target -> family_type_string, static_type_name, target in
          construct_edge qsymb coef inner_info [] [index] [] [] conds
        end else
          []
      | CoefAsn(_, DummyPat, asn) ->
        iter (Some DummyPat) conds asn
      | CoefAsn(_, LitPat(frac), asn) when expr_is_fixed inputParameters frac -> (* extend to arbitrary fractions? *)
        let new_coef = 
          match coef with
            None -> Some (LitPat frac)
          | Some DummyPat -> Some DummyPat
          | Some (LitPat coef) -> Some (LitPat (WOperation(dummy_loc, Mul, [frac;coef], RealType)))
        in
        iter new_coef conds asn
      | Sep(_, asn1, asn2) ->
        (iter coef conds asn1) @ (iter coef conds asn2)
      | IfAsn(_, cond, asn1, asn2) ->
        if expr_is_fixed inputParameters cond then
          (iter coef (cond :: conds) asn1) @ (iter coef (WOperation(dummy_loc, Not, [cond], boolt) :: conds) asn2)
        else
          (iter coef conds asn1) @ (iter coef conds asn2) (* replace this with []? *)
      | _ -> []
    in
    iter None [] wbody0
  
  (** direct edges from a precise predicate or predicate family to other precise predicates 
     - each element of path is of the form:
      (
        outer_l, 
        outer_symb, 
        outer_nb_curried, 
        outer_fun_sym_opt,        | Present for predicate constructor
        outer_inst_pred_info_opt, | Family name if outer is instance predicate
        outer_formal_targs, 
        outer_actual_indices,     | List of strings. E.g., class/struct name for instance predicate
        outer_formal_args, 
        outer_formal_input_args, 
        outer_wbody, 
        inner_frac_expr_opt, 
        inner_inst_pred_info_opt, | (inner_family_name, inner_target_expr_static_type_name, inner_target_expr) if inner is instance predicate
        inner_formal_targs, 
        inner_formal_indices, 
        inner_input_exprs, 
        conds                     | List of expressions that must hold in order to take the path
      )
  *)
  let pred_fam_contains_edges =
    flatmap
      (fun ((p, fns), (env, l, predinst_tparams, xs, psymb, inputParamCount, wbody0)) ->
        let pindices = List.map term_of_pred_index fns in
        match inputParamCount with
          None -> [] (* predicate is not precise *)
        | Some nbInputParameters ->
          let inputParameters = List.map fst (take nbInputParameters xs) in
          let inputFormals = (take nbInputParameters xs) in
          let construct_edge qsymb coef inner_inst_pred_info_opt qtargs qIndices qInputParamTypes qInputActuals conds =
            [(psymb, pindices, qsymb, [(l, (psymb, true), 0, None, None, predinst_tparams, fns, xs, inputFormals, wbody0, coef, inner_inst_pred_info_opt, qtargs, qIndices, List.combine qInputParamTypes qInputActuals, conds)])]
          in
          find_edges construct_edge inputParameters xs wbody0
      )
      predinstmap
  
  let predicate_ctor_contains_edges = 
    predctormap |> flatmap
      (fun (g, PredCtorInfo (l, tparams, ps1, ps2, inputParamCount, wbody0, (psymbol, psymbol_term))) ->
        if tparams <> [] then [] else
        match inputParamCount with
          None -> []
        | Some(nbInputParameters) ->
          let nbInputParameters = (List.length ps1) + nbInputParameters in
          let predinst_tparams = [] in
          let fns = [] in
          let xs = ps1 @ ps2 in
          let inputParameters = List.map fst (take nbInputParameters xs) in
          let inputFormals = (take nbInputParameters xs) in
          let outer_nb_curried = (List.length ps1) in
          let construct_edge qsymb coef inner_inst_pred_info_opt qtargs qIndices qInputParamTypes qInputActuals conds =
            [(psymbol_term, [], qsymb, [(l, (psymbol_term, true), outer_nb_curried, Some(psymbol), None, predinst_tparams, fns, xs, inputFormals, wbody0, coef, inner_inst_pred_info_opt, qtargs, qIndices, List.combine qInputParamTypes qInputActuals, conds)])]
          in
          find_edges construct_edge inputParameters xs wbody0
      )

  let instance_predicate_find_edges class_name index =
    fun (g, (l, pmap, family, psymb, wbody_opt)) ->
      match wbody_opt with None -> [] | Some wbody0 ->
      let pindices = [index] in
      let instpred_tparams = [] in
      let fns = [class_name] in
      let xs = pmap in
      let inputParameters = ["this"] in
      let inputFormals = [] in
      let construct_edge qsymb coef inner_inst_pred_info_opt qtargs qIndices qInputParamTypes qInputActuals conds =
        [(psymb, pindices, qsymb, [(l, (psymb, true), 0, None, Some family, instpred_tparams, fns, xs, inputFormals, wbody0, coef, inner_inst_pred_info_opt, qtargs, qIndices, List.combine qInputParamTypes qInputActuals, conds)])]
      in
      find_edges construct_edge inputParameters xs wbody0

  let instance_predicate_contains_edges = 
    match language, dialect with
    | CLang, Some Cxx ->
      cxx_inst_pred_map |> flatmap begin fun (sn, preds_map) ->
        let _, [], _, _, type_info = List.assoc sn structmap in
        preds_map |> flatmap (instance_predicate_find_edges sn (ctxt#mk_app type_info []))
      end
    | Java, _ ->
      classmap1 |> flatmap 
        (fun (cn, (l, abstract, fin, meths, fds, cmap, super, tparams, interfs, preds, pn, ilist)) ->
          preds |> flatmap (instance_predicate_find_edges cn @@ List.assoc cn classterms)
        )
    | _ -> []  
  
  let contains_edges = pred_fam_contains_edges @ instance_predicate_contains_edges @ predicate_ctor_contains_edges
    
  let close1_ edges =
    flatmap
    (fun (from_symb, from_indices, to_symb, path) ->
      flatmap 
        (fun (from_symb0, from_indices0, to_symb0, (((outer_l0, outer_symb0, outer_nb_curried0, outer_fun_sym0, outer_inst_pred_info_opt0, outer_formal_targs0, outer_actual_indices0, outer_formal_args0, outer_formal_input_args0, outer_wbody0, inner_frac_expr_opt0, inner_inst_pred_info_opt0, inner_formal_targs0, inner_formal_indices0, inner_input_exprs0, conds0) :: rest) as path0)) ->
          if to_symb == from_symb0 then
            let rec add_extra_conditions path = 
              match path with
              | [(outer_l, outer_symb, outer_nb_curried, outer_fun_sym, outer_inst_pred_info_opt, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_inst_pred_info_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, conds)] ->
                let extra_conditions: expr list = List.map2 (fun cn e2 -> 
                  match language with 
                  | Java -> 
                    WOperation(dummy_loc, Eq, [ClassLit(dummy_loc, cn); e2], ObjType ("java.lang.Class", []))
                  | CLang ->
                    begin match dialect, outer_inst_pred_info_opt, inner_inst_pred_info_opt with
                    | Some Cxx, Some _, _
                    | Some Cxx, _, Some _ ->
                      WOperation (outer_l0, Eq, [TypeInfo (outer_l0, StructType (cn, [])); e2], type_info_ref_type)
                    | _ ->
                      WOperation(dummy_loc, Eq, [WVar(dummy_loc, cn, FuncName); e2], PtrType Void)
                    end
                ) outer_actual_indices0 inner_formal_indices in
                (* these extra conditions ensure that the actual indices match the expected ones *)
                [(outer_l, outer_symb, outer_nb_curried, outer_fun_sym, outer_inst_pred_info_opt, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_inst_pred_info_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, extra_conditions @ conds)]
              | head :: rest -> head :: (add_extra_conditions rest)
            in
            let new_path = add_extra_conditions path in
            let new_edge = (from_symb, from_indices, to_symb0, new_path @ path0) in
            if List.exists (fun (from_symb1, from_indices1, to_symb1, _) -> 
                 from_symb1 == from_symb && 
                 (for_all2 (fun t1 t2 -> t1 == t2) from_indices from_indices1) && 
                 to_symb1 == to_symb0) edges then
              []
              (* todo: improve by taking path into account *)
              (* todo: avoid cycles in the path? *)
              (* todo: avoid duplicate entries? *)
            else 
              [new_edge]
          else
            []
        )
        edges
    )
    edges
  
  let transitive_contains_edges_ = 
    let rec close edges =
      let new_edges = close1_ edges in
      if new_edges = [] then
        edges
      else
        close (new_edges @ edges)
    in
    close contains_edges
  
  (*let _ =
    print_endline "transitive_edges:";
    List.iter
      (fun (from_symb, from_indices, to_symb, path) ->
        print_endline ((ctxt#pprint from_symb) ^ " -> " ^ (ctxt#pprint to_symb));
      )
    contains_edges *)
  
 let rules_cell = ref [] (* A hack to allow the rules to recursively use the rules *)
  
 let rules =
    let rulemap = ref [] in
    let add_rule predSymb rule =
      match try_assq predSymb !rulemap with
        None ->
        rulemap := (predSymb, ref [rule])::!rulemap
      | Some rules ->
        rules := rule::!rules
    in
    let index_target family_term ~family_name ~index_name =
      match dialect with
      | Some Cxx ->
        let field_ptr_parent_symb = get_pure_func_symb "field_ptr_parent" |> fst in
        let rec family_to_derived_offsets derived_type_name found_offsets =
          if derived_type_name = family_name then
            found_offsets
          else
            let _, [], Some (bases, _, _), _, _ = List.assoc derived_type_name structmap in
            let base_name, (_, _, base_offset) = bases |> List.find @@ fun (base, _) -> 
              match List.assoc_opt base cxx_inst_pred_map with
              | None -> false
              | Some base_preds -> 
                base_preds |> List.exists @@ fun (_, (_, _, base_family, _, _)) -> base_family = family_name
            in
            family_to_derived_offsets base_name (base_offset :: found_offsets)
        in      
        let offsets = family_to_derived_offsets index_name [] in
        offsets |> List.fold_left (fun addr offset -> ctxt#mk_app field_ptr_parent_symb [addr; offset]) family_term
      | _ ->
        family_term
    in
    let env_with_this_opt this_opt env = this_opt |> Option.fold ~none:env ~some:(fun (_, this_term) -> ("this", this_term) :: env) in
    (* transitive auto-close rules for precise predicates and predicate families *)
    List.iter
      (fun (from_symb, indices, to_symb, path) ->
        let transitive_auto_close_rule l h typeid_env wanted_targs terms_are_well_typed wanted_coef wanted_coefpat wanted_indices_and_input_ts cont =
          (*let _ = print_endline ("trying to auto-close:" ^ (ctxt#pprint from_symb)) in*)
          let rec can_apply_rule wanted_coef current_this_opt current_targs current_indices current_input_args path =
            let is_chunk_candidate (Chunk (found_symb, found_targs, found_coef, found_terms, _)) =
              let expected_terms = (current_this_opt |> Option.map snd |> Option.to_list) @ current_indices @ current_input_args in
              if predname_eq found_symb (to_symb, true) then
                for_all2 definitely_equal (take (List.length (expected_terms)) found_terms) expected_terms
              else
                let (fsymb, literal) = found_symb in 
                match try_assq fsymb !pred_ctor_applications with
                | None -> false
                | Some (symbol, symbol_term, targs, ctor_args, _) ->
                  targs = [] &&
                  let found_terms = ctor_args @ found_terms in
                  if to_symb == symbol_term then
                    for_all2 definitely_equal (take (List.length (expected_terms)) found_terms) expected_terms
                  else
                    false
            in
            let is_empty_pred_candidate (symb, fsymbs, conds, ((p, fns), (env, l, predinst_tparams, xs, _, inputParamCount, wbody))) =
              to_symb == symb &&
              (for_all2 definitely_equal fsymbs current_indices) &&
              (
                let Some inputParamCount = inputParamCount in
                let Some tpenv = zip predinst_tparams current_targs in
                let env = List.map2 
                  (fun (x, tp0) actual -> 
                    let tp = instantiate_type tpenv tp0 in 
                    (x, prover_convert_term actual tp tp0)) 
                  (take inputParamCount xs) 
                  current_input_args 
                in 
                let env = env |> env_with_this_opt current_this_opt in
                conds |> List.exists @@ for_all_rev @@ fun cond -> ctxt#query (eval None env cond)
              )
            in
            match path with
            | [] -> 
              begin match try_find is_chunk_candidate h with
              | None -> (* check whether the wanted predicate is an empty predicate? *)
                if empty_preds |> List.exists is_empty_pred_candidate then
                  Some (fun h cont -> cont h real_unit)
                else
                  None
              | Some (Chunk (found_symb, found_targs, found_coef, found_ts, _)) ->
                Some (fun h cont -> cont h found_coef)
              end
            | (outer_l, outer_symb, outer_nb_curried, outer_fun_sym, outer_inst_pred_info_opt, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_inst_pred_info_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, conds) :: path ->
              let Some tpenv = zip outer_formal_targs current_targs in
              let env = typeid_env_of_tpenv l typeid_env tpenv in
              let env = env @ List.map2 
                (fun (x, tp0) actual -> 
                  let tp = instantiate_type tpenv tp0 in 
                  (x, prover_convert_term actual tp tp0)) 
                outer_formal_input_args 
                current_input_args 
              in
              let current_this_opt =
                match dialect, outer_actual_indices with 
                | Some Cxx, [outer_index_name] ->
                  (* 'this' term inside instance predicate body *)
                  current_this_opt |> Option.map @@ fun this_type_name_and_term ->
                    outer_index_name, base_addr outer_l this_type_name_and_term outer_index_name
                | _ -> 
                  current_this_opt
              in
              let env = env |> env_with_this_opt current_this_opt in
              if conds |> for_all_rev @@ fun cond -> ctxt#query (eval None env cond) then
                let new_wanted_coef = Option.bind wanted_coef @@ fun wanted_coef ->
                  match inner_frac_expr_opt with
                    None -> Some wanted_coef
                  | Some DummyPat -> None
                  | Some (LitPat f) ->
                    let fterm = eval None env f in
                    Some (ctxt#mk_real_mul fterm wanted_coef)
                  | Some _ -> None
                in
                let new_this_opt = inner_inst_pred_info_opt |> Option.map @@ fun (_, this_type, this_expr) -> this_type, eval None env this_expr in
                let new_actual_targs = inner_formal_targs |> List.map @@ instantiate_type tpenv in
                let new_actual_indices = inner_formal_indices |> List.map @@ eval None env in
                let new_actual_input_args = inner_input_exprs |> List.map @@ fun (tp, e) -> prover_convert_term (eval None env e) tp (instantiate_type tpenv tp) in
                match can_apply_rule new_wanted_coef new_this_opt new_actual_targs new_actual_indices new_actual_input_args path with
                | None -> None
                | Some exec_rule -> Some (fun h cont ->
                    exec_rule h (fun h coef ->
                      let rules = rules_cell in
                      let ghostenv = [] in
                      let checkDummyFracs = true in
                      with_context PushSubcontext @@ fun () ->
                        let new_coef = 
                          match inner_frac_expr_opt with
                          | None -> coef
                          | Some DummyPat -> real_unit
                          | Some (LitPat (RealLit(_, n, _))) -> ctxt#mk_real_mul coef (ctxt#mk_reallit_of_num ((num_of_big_int unit_big_int) // n))
                          | Some (LitPat f) -> (* ideally: newcoef = coef / f, but real_div is not supported yet *)
                            let fterm = (eval None env f) in
                            if ctxt#query (ctxt#mk_real_le fterm coef) then
                              real_unit
                            else
                              coef 
                          | Some _ -> coef (* todo *)
                        in
                        let new_coef = wanted_coef |> Option.value ~default:new_coef in
                        with_context (Executing (h, env, outer_l, ("Auto-closing predicate with coefficient " ^ ctxt#pprint new_coef))) @@ fun () ->
                        consume_asn rules tpenv h ghostenv env outer_wbody checkDummyFracs new_coef @@ fun _ h ghostenv env2 size_first ->
                          let outputParams = outer_formal_args |> drop @@ List.length outer_formal_input_args in
                          let outputArgs = List.map (fun (x, tp0) -> let tp = instantiate_type tpenv tp0 in (prover_convert_term (List.assoc x env2) tp0 tp)) outputParams in
                          with_context (Executing (h, [], outer_l, "Producing auto-closed chunk")) @@ fun () ->
                            let input_param_count = List.length current_indices + List.length current_input_args in
                            begin fun cont ->
                              match outer_fun_sym, outer_inst_pred_info_opt, current_this_opt with
                              | Some (funsym), _, _ -> 
                                assert (List.length current_indices = 0);
                                let ctor_args, chunk_args = take_drop outer_nb_curried (current_input_args @ outputArgs) in
                                let input_param_count, symb, args = input_param_count - outer_nb_curried, (ctxt#mk_app funsym ctor_args, false), chunk_args in 
                                produce_chunk h symb current_targs new_coef (Some input_param_count) args None cont
                              | None, Some family, Some this_type_name_and_term ->
                                let index, other_indices = List.hd current_indices, List.tl current_indices in
                                let args = other_indices @ current_input_args @ outputArgs in
                                produce_instance_predicate_chunk outer_l h (fst outer_symb) new_coef this_type_name_and_term index family args None @@ fun h target ->
                                cont h
                              | _ ->
                                let args = current_indices @ current_input_args @ outputArgs in
                                produce_chunk h outer_symb current_targs new_coef (Some input_param_count) args None cont
                            end @@ fun h ->
                            with_context PopSubcontext @@ fun () ->
                            cont h new_coef (* todo: properly set the size *)
                    )
                  )
              else
                None (* conditions do not hold, so give up *)
          in
          let wanted_indices = match List.hd path with
          | (_, _, _, _, Some _, _, _, _, _, _, _, _, _, _, _, _) -> (* outer is instance predicate *)
             (take (List.length indices) (List.tl wanted_indices_and_input_ts))
          | (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) -> 
             (take (List.length indices) wanted_indices_and_input_ts)
          in
          if terms_are_well_typed && (for_all2 definitely_equal indices wanted_indices) then (* check that you are actually looking for from_symb at indices *)
            let wanted_target_opt, wanted_indices, wanted_inputs = 
              match List.hd path with
              | (_, _, _, _, (Some family_name), _, [index_name], _, _, _, _, _, _, _, _, _) -> 
                let family_this_term = List.hd wanted_indices_and_input_ts in
                let parent_ptr = index_target family_this_term ~family_name ~index_name in
                (Some (index_name, parent_ptr), (take (List.length indices) (List.tl wanted_indices_and_input_ts)),
                (drop (List.length indices) (List.tl wanted_indices_and_input_ts)))
              | (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) -> 
                (None, (take (List.length indices) wanted_indices_and_input_ts), (drop (List.length indices) wanted_indices_and_input_ts))
            in
            let wanted_coef =
              match wanted_coefpat with
              | TermPat coef -> if wanted_coef == real_unit then Some coef else Some (ctxt#mk_real_mul wanted_coef coef)
              | _ -> None
            in
            match can_apply_rule wanted_coef wanted_target_opt wanted_targs wanted_indices wanted_inputs path with
              None -> cont None
            | Some exec_rule -> exec_rule h (fun h _ -> cont (Some h))
          else
            cont None
        in
        add_rule from_symb transitive_auto_close_rule
      )
      transitive_contains_edges_;
    (* transitive auto-open rules for precise predicates and predicate families *)
    let transitive_auto_open_rules =
    List.map
      (fun (from_symb, indices, to_symb, path) ->
        let transitive_auto_open_rule l h typeid_env wanted_targs terms_are_well_typed wanted_coef wanted_coefpat wanted_indices_and_input_ts cont =
          (*let _ = print_endline ("trying to auto-open : " ^ (ctxt#pprint from_symb)) in *)
          (* Check if we can obtain the 'wanted' chunk by transitively opening each predicate in the rule's path *)
          let rec try_apply_rule_core actual_this_opt actual_targs actual_indices actual_input_args path = 
            match path with
            | [] ->
              (* path is empty, check if the terms that we obtained match the wanted terms *)
              if for_all2 definitely_equal wanted_indices_and_input_ts ((actual_this_opt |> Option.map snd |> Option.to_list) @ actual_indices @ actual_input_args) then
                Some (fun h_opt cont -> cont h_opt)
              else
                None
            | (outer_l, outer_symb, outer_nb_curried, outer_fun_sym, outer_inst_pred_info_opt, outer_formal_targs, outer_actual_indices, outer_formal_args, outer_formal_input_args, outer_wbody, inner_frac_expr_opt, inner_inst_pred_info_opt, inner_formal_targs, inner_formal_indices, inner_input_exprs, conds) :: path ->
              (* evaluate the relevant predicate in the body *)
              let actual_input_args = actual_input_args |> take @@ List.length outer_formal_input_args in (* to fix first call *)
              let Some tpenv = zip outer_formal_targs actual_targs in
              let outer_typeid_env = typeid_env_of_tpenv l typeid_env tpenv in
              let env = outer_typeid_env @ List.map2 (fun (x, tp0) actual -> 
                let tp = instantiate_type tpenv tp0 in (x, prover_convert_term actual tp tp0))
                outer_formal_input_args 
                actual_input_args 
              in
              let actual_this_opt =
                match dialect, outer_actual_indices with
                | Some Cxx, [outer_index_name] ->
                  (* actual 'this' when opening the instance predicate *)
                  actual_this_opt |> Option.map @@ fun this_type_name_and_term ->
                    outer_index_name, base_addr outer_l this_type_name_and_term outer_index_name
                | _ ->
                  actual_this_opt
              in
              let env = env |> env_with_this_opt actual_this_opt in
              if conds |> for_all_rev @@ fun cond -> ctxt#query (eval None env cond) then
                let new_this_opt = inner_inst_pred_info_opt |> Option.map @@ fun (_, this_type, this_expr) ->
                  this_type, eval None env this_expr
                in
                let new_actual_targs = inner_formal_targs |> List.map @@ instantiate_type tpenv in
                let new_actual_indices = inner_formal_indices |> List.map @@ eval None env in
                let new_actual_input_args = inner_input_exprs |> List.map @@ fun (tp, e) -> prover_convert_term (eval None env e) tp (instantiate_type tpenv tp) in
                let new_this_opt = new_this_opt |> Option.map @@ fun this_type_name_and_term ->
                  begin match dialect, path, inner_inst_pred_info_opt with
                  | Some Cxx, [], Some (family, _, _) ->
                    (* Path is empty. Hence, in the next recursive call the 'wanted' terms will be checked against the 'actual' terms.
                       Therefore, we compute the family target term that is present in the predicate chunk as when we could close it. *)
                    family, base_addr outer_l this_type_name_and_term family
                  | _ ->
                    this_type_name_and_term
                  end
                in
                (* recursively continue *)
                match try_apply_rule_core new_this_opt new_actual_targs new_actual_indices new_actual_input_args path with
                | None -> None
                | Some(exec_rule) ->
                  Some (fun h_opt cont ->
                    begin match h_opt with
                    | None -> cont None
                    | Some h ->
                      (* consume from_symb *)
                      let result_opt =
                        let rec iter hdone htodo =
                          match htodo with
                            [] -> None (* todo: can happen if predicate is only present under conditions that contain non-input variables *)
                          | (Chunk (found_symb, found_targs, found_coef, found_ts, _) as chunk)::htodo ->
                            let actual_this_opt = actual_this_opt |> Option.map @@ fun this_type_name_and_term ->
                              begin match dialect, outer_inst_pred_info_opt with
                              | Some Cxx, Some family ->
                                (* Compute family target term *)
                                family, base_addr outer_l this_type_name_and_term family
                              | _ ->
                                this_type_name_and_term
                              end
                            in
                            let actuals = (actual_this_opt |> Option.map snd |> Option.to_list) @ actual_indices @ actual_input_args in
                            if predname_eq outer_symb found_symb && for_all2 definitely_equal (take (List.length actuals) found_ts) actuals then
                               Some ((chunk, hdone @ htodo, found_targs, found_coef, found_ts))
                            else
                              let (osymb, _) = outer_symb in
                              let (fsymb, literal) = found_symb in 
                              begin match try_assq fsymb !pred_ctor_applications with
                                None -> iter (chunk::hdone) htodo
                              | Some (symbol, symbol_term, targs, ctor_args, _) -> 
                                if symbol_term == osymb && targs = [] then
                                  if for_all2 definitely_equal (take (List.length actuals) (ctor_args @ found_ts)) actuals then
                                    Some ((chunk, hdone @ htodo, found_targs, found_coef, ctor_args @ found_ts))
                                  else 
                                    iter (chunk::hdone) htodo
                                else 
                                  iter (chunk::hdone) htodo
                              end
                        in
                        iter [] h
                      in
                      begin match result_opt with
                        None -> cont None
                      | Some ((Chunk (consumed_symb, consumed_targs, consumed_coef, consumed_ts, consumed_size), h, found_targs, found_coef, found_ts)) -> 
                        (* produce from_symb body *)
                        let full_env = outer_typeid_env @ List.map2 
                          (fun (x, tp0) t -> 
                            let tp = instantiate_type tpenv tp0 in 
                            (x, prover_convert_term t tp tp0)) 
                            outer_formal_args 
                            (drop ((List.length actual_indices) + (match actual_this_opt with None -> 0 | Some _ -> 1)) found_ts) 
                        in 
                        let full_env = full_env |> env_with_this_opt actual_this_opt in
                        let ghostenv = [] in
                        let produce_coef = if is_dummy_frac_term found_coef then get_dummy_frac_term () else found_coef in
                        with_context PushSubcontext @@ fun () ->
                        with_context (Executing (h, full_env, outer_l, "Auto-opening predicate")) @@ fun () ->
                          produce_asn tpenv h ghostenv full_env outer_wbody produce_coef None None @@ fun h ghostenv env ->
                            with_context PopSubcontext @@ fun () ->
                            (* perform remaining opens *)
                            if is_dummy_frac_term found_coef then
                              exec_rule (Some (Chunk(consumed_symb, consumed_targs, get_dummy_frac_term () , consumed_ts, consumed_size) :: h)) cont
                            else
                              exec_rule (Some h) cont
                      end
                    end
                  )
              else
                (* conditions were not met *)
                None
          in
          let try_apply_rule hdone htodo =
            (* Find a heap chunk with the correct name and indices to apply the rule *)
            let rec try_apply_rule_aux hdone htodo = 
              match htodo with
              | [] -> None
              | ((Chunk (actual_name, actual_targs, actual_coef, actual_ts, _)) as chnk) :: rest ->
                  (* Check if chunk name and indices match the ones we need to apply the rule *)
                  if (predname_eq actual_name (from_symb, true)) && (
                       let indices0 = match List.hd path with
                         (_, _, _, _, Some _, _, _, _, _, _, _, _, _, _, _, _) ->  (take (List.length indices) (List.tl actual_ts)) (* outer is instance pred *)
                       | (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) -> (take (List.length indices) actual_ts)
                       in
                        (for_all2 definitely_equal indices0 indices)
                       ) 
                  then
                    (* match found, find out if we can apply the rule *)
                    let (actual_target_opt, actual_indices, actual_inputs) = 
                      match List.hd path with
                      | (_, _, _, _, Some family_name, _, [index_name], _, _, _, _, _, _, _, _, _) ->  
                          let family_this_term = List.hd actual_ts in
                          let parent_ptr = index_target family_this_term ~family_name ~index_name in
                          (Some (index_name, parent_ptr), indices, (drop (List.length indices) (List.tl actual_ts)))
                      | (_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _) -> (None, indices, (drop (List.length indices) actual_ts))
                    in
                    begin match try_apply_rule_core actual_target_opt actual_targs actual_indices actual_inputs path with
                    | None -> try_apply_rule_aux (chnk :: hdone) rest
                    | Some exec_rule -> Some exec_rule
                    end
                  else  
                    (* match not found, check if we can use a ctor application in order to apply the rule *)
                    let (fsymb, literal) = actual_name in 
                    begin match try_assq fsymb !pred_ctor_applications with
                    | None -> try_apply_rule_aux (chnk :: hdone) rest
                    | Some (symbol, symbol_term, targs, ctor_args, _) -> 
                      if from_symb == symbol_term && targs = [] then
                        begin match try_apply_rule_core None actual_targs [] (ctor_args @ actual_ts) path with
                        | None -> try_apply_rule_aux (chnk :: hdone) rest
                        | Some exec_rule -> Some exec_rule
                        end
                      else
                        try_apply_rule_aux (chnk :: hdone) rest
                    end
            in
            try_apply_rule_aux hdone htodo
          in
          if terms_are_well_typed then
            match try_apply_rule [] h with
              None -> cont None
            | Some exec_rule -> exec_rule (Some h) cont
          else
            cont None
         in
         add_rule to_symb transitive_auto_open_rule;
         (to_symb, transitive_auto_open_rule)
      )
      transitive_contains_edges_
    in
    (* rules for obtaining underscore (i.e. possibly uninitialized) field chunks *)
    field_pred_map |> List.iter begin function (_, (_, None)) -> () | ((sn, fn), ((_, (_, _, _, [_; ft], symb, _, _)), Some (_, (_, _, _, _, symb_, _, _)))) ->
      let (_, tparams, Some (_, fmap, _), _, structTypeidFunc) = List.assoc sn structmap in
      let (_, gh, _, offset_opt, _) = List.assoc fn fmap in
      begin match offset_opt with
        None -> ()
      | Some offsetFunc ->
      match try_pointee_pred_symb ft with
        Some pointee_pred_symb ->
        let pointee_chunk_to_field_chunk__rule l h typeid_env wanted_targs terms_are_well_typed wanted_coef wanted_coefpat wanted_indices_and_input_ts cont =
          let [tp] = wanted_indices_and_input_ts in
          let targ_typeids = List.map (typeid_of l) wanted_targs in
          let structTypeid = ctxt#mk_app structTypeidFunc targ_typeids in
          let offset = ctxt#mk_app offsetFunc targ_typeids in
          let field_address = mk_field_ptr tp structTypeid offset in
          match extract
            begin function
              (Chunk ((g, is_symb), [], coef, [tp'; tv], _)) when g == pointee_pred_symb && definitely_equal tp' field_address -> Some (coef, tv)
            | _ -> None
            end
            h
          with
            None -> cont None
          | Some ((coef, tv), h) ->
            cont (Some (Chunk ((symb_, true), wanted_targs, coef, [tp; mk_some ft tv], None)::h))
        in
        add_rule symb_ pointee_chunk_to_field_chunk__rule
      | None ->
      match int_rank_and_signedness ft with
        Some (rank, signedness) ->
        let integer__symb = integer__symb () in
        let tsize = rank_size_term rank in
        let tsigned = match signedness with Signed -> true_term | Unsigned -> false_term in
        let pointee_chunk_to_field_chunk__rule l h typeid_env wanted_targs terms_are_well_typed wanted_coef wanted_coefpat wanted_indices_and_input_ts cont =
          let [tp] = wanted_indices_and_input_ts in
          let field_address = mk_field_ptr_ l [] tp wanted_targs structTypeidFunc offsetFunc in
          match extract
            begin function
              (Chunk ((g, is_symb), [], coef, [tp'; tsize'; tsigned'; tv], _)) when
              g == integer__symb &&
              definitely_equal tp' field_address &&
              definitely_equal tsize' tsize &&
              definitely_equal tsigned' tsigned
              -> Some (coef, tv)
            | _ -> None
            end
            h
          with
            None -> cont None
          | Some ((coef, tv), h) ->
            cont (Some (Chunk ((symb_, true), [], coef, [tp; mk_some ft tv], None)::h))
        in
        add_rule symb_ pointee_chunk_to_field_chunk__rule
      | None -> ()
      end;
      let field_chunk_to_field_chunk__rule l h typeid_env wanted_targs terms_are_well_typed wanted_coef wanted_coefpat wanted_indices_and_input_ts cont =
        let [tp] = wanted_indices_and_input_ts in
        match extract
          begin function
            Chunk ((g, is_symb), targs', coef, [tp'; tv], _) when g == symb && List.for_all2 unify wanted_targs targs' && definitely_equal tp' tp -> Some (coef, tv)
          | _ -> None
          end
          h
        with
          None -> cont None
        | Some ((coef, tv), h) ->
          let tpenv = List.combine tparams wanted_targs in
          let ft = instantiate_type tpenv ft in
          let tv_ = mk_some ft tv in
          cont (Some (Chunk ((symb_, true), wanted_targs, coef, [tp; tv_], None)::h))
      in
      add_rule symb_ field_chunk_to_field_chunk__rule;
      transitive_auto_open_rules |> List.iter begin fun (to_symb, rule) ->
        if to_symb == symb then
          let combined_rule l h typeid_env wanted_targs terms_are_well_typed wanted_coef wanted_coefpat wanted_indices_and_input_ts cont =
            rule l h typeid_env wanted_targs terms_are_well_typed wanted_coef wanted_coefpat wanted_indices_and_input_ts $. function
              None -> cont None
            | Some h ->
              field_chunk_to_field_chunk__rule l h typeid_env wanted_targs terms_are_well_typed wanted_coef wanted_coefpat wanted_indices_and_input_ts cont
          in
          add_rule symb_ combined_rule
      end
    end;
    (* rules for closing empty chunks *)
    List.iter
      begin fun (symb, fsymbs, conds, ((p, fns), (env, l, predinst_tparams, xs, _, inputParamCount, wbody))) ->
        let g = (symb, true) in
        let indexCount = List.length fns in
        let Some n = inputParamCount in
        let (inputParams, outputParams) = take_drop n xs in
        let autoclose_rule =
          let match_func h targs ts =
            let (indices, inputArgs) = take_drop indexCount ts in
            List.for_all2 definitely_equal indices fsymbs &&
            let Some tpenv = zip predinst_tparams targs in
            let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) inputParams inputArgs in
            List.exists (fun conds -> for_all_rev (fun cond -> ctxt#query (eval None env cond)) conds) conds
          in
          let exec_func h targs coef coefpat ts cont =
            let rules = rules_cell in
            let (indices, inputArgs) = take_drop indexCount ts in
            let Some tpenv = zip predinst_tparams targs in
            let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) inputParams inputArgs in
            let ghostenv = [] in
            let checkDummyFracs = true in
            let coef = match coefpat with TermPat f -> (real_mul dummy_loc coef f) | SrcPat (DummyPat) -> get_dummy_frac_term () | SrcPat (LitPat _) -> assert false; | SrcPat (VarPat(_, x)) -> real_unit  in
            with_context PushSubcontext $. fun () ->
            with_context (Executing (h, env, l, "Auto-closing predicate")) $. fun () ->
            consume_asn rules tpenv h ghostenv env wbody checkDummyFracs coef $. fun _ h ghostenv env size_first ->
            let outputArgs = List.map (fun (x, tp0) -> let tp = instantiate_type tpenv tp0 in (prover_convert_term (List.assoc x env) tp0 tp)) outputParams in
            with_context (Executing (h, [], l, "Producing auto-closed chunk")) $. fun () ->
            with_context PopSubcontext $. fun () ->
            cont (Chunk (g, targs, coef, inputArgs @ outputArgs, None)::h)
          in
          let rule l h typeid_env targs terms_are_well_typed coef coefpat ts cont =
            (*let _ = print_endline "trying to close empty predicate" in*)
            if terms_are_well_typed && match_func h targs ts then exec_func h targs coef coefpat ts (fun h -> cont (Some h)) else cont None
          in
          rule
        in
        add_rule symb autoclose_rule
      end
      empty_preds;
    (* rules for array slices *)
    begin if language = Java then
      let array_element_symb = array_element_symb () in
      let array_slice_symb = array_slice_symb () in
      let array_slice_deep_symb = array_slice_deep_symb () in
      let get_element_rule l h typeid_env [elem_tp] terms_are_well_typed coef coefpat [arr; index] cont =
        match extract
          begin function
            (Chunk ((g, is_symb), elem_tp'::targs_rest, coef, arr'::istart'::iend'::args_rest, _)) when
              (g == array_slice_symb || g == array_slice_deep_symb) &&
              definitely_equal arr' arr && ctxt#query (ctxt#mk_and (ctxt#mk_le istart' index) (ctxt#mk_lt index iend')) &&
              unify elem_tp elem_tp' ->
            Some (g, targs_rest, coef, istart', iend', args_rest)
          | _ -> None
          end
          h
        with
          None -> cont None
        | Some ((g, targs_rest, coef, istart', iend', args_rest), h) ->
          if g == array_slice_symb then
            let [elems] = args_rest in
            let split_after elems h =
              let elem = get_unique_var_symb_non_ghost "elem" elem_tp in
              let elems_tail = get_unique_var_symb "elems" (InductiveType ("list", [elem_tp])) in
              assume (ctxt#mk_eq elems (mk_cons elem_tp elem elems_tail)) $. fun () ->
              let chunk1 = Chunk ((array_element_symb, true), [elem_tp], coef, [arr; index; elem], None) in
              let chunk2 = Chunk ((array_slice_symb, true), [elem_tp], coef, [arr; ctxt#mk_add index (ctxt#mk_intlit 1); iend'; elems_tail], None) in
              cont (Some (chunk1::chunk2::h))
            in
            if ctxt#query (ctxt#mk_eq istart' index) then
              split_after elems h
            else
              let elems1 = mk_take (ctxt#mk_sub index istart') elems in
              let elems2 = mk_drop (ctxt#mk_sub index istart') elems in
              assume (ctxt#mk_eq elems (mk_append elems1 elems2)) $. fun () ->
              let chunk0 = Chunk ((array_slice_symb, true), [elem_tp], coef, [arr; istart'; index; elems1], None) in
              split_after elems2 (chunk0::h)
          else
            let [ta; tv] = targs_rest in
            let [p; a; elems; vs] = args_rest in
            let n1 = ctxt#mk_sub index istart' in
            let elems1 = mk_take n1 elems in
            let vs1 = mk_take n1 vs in
            let elems2 = mk_drop n1 elems in
            let vs2 = mk_drop n1 vs in
            let elem = get_unique_var_symb "elem" elem_tp in
            let tail_elems2 = get_unique_var_symb "elems" (InductiveType ("list", [elem_tp])) in
            let v = get_unique_var_symb "value" tv in
            let tail_vs2 = get_unique_var_symb "values" (InductiveType ("list", [tv])) in
            assume (ctxt#mk_eq elems2 (mk_cons elem_tp elem tail_elems2)) $. fun () ->
            assume (ctxt#mk_eq vs2 (mk_cons tv v tail_vs2)) $. fun () ->
            let before_chunks = 
              if definitely_equal istart' index then
                []
              else
                [Chunk ((array_slice_deep_symb, true), [elem_tp; ta; tv], coef, [arr; istart'; index; p; a; elems1; vs1], None)]
            in
            let after_chunks = 
              if definitely_equal (ctxt#mk_add index (ctxt#mk_intlit 1)) iend' then
                []
              else
                [Chunk ((array_slice_deep_symb, true), [elem_tp; ta; tv], coef, [arr; ctxt#mk_add index (ctxt#mk_intlit 1); iend'; p; a; tail_elems2; tail_vs2], None)]
            in
            let element_chunk = Chunk ((array_element_symb, true), [elem_tp], coef, [arr; index; elem], None) in
            let h = element_chunk :: before_chunks @ after_chunks @ h in
            match try_assq p predinstmap_by_predfamsymb with
              None -> cont (Some (Chunk ((p, false), [], coef, [a; elem; v], None)::h))
            | Some (xs, wbody) ->
              let tpenv = [] in
              let ghostenv = [] in
              let Some env = zip (List.map fst xs) [a; elem; v] in
              produce_asn tpenv h ghostenv env wbody coef None None $. fun h _ _ ->
              cont (Some h)
      in
      let get_slice_upcast_rule l h typeid_env [elem_tp] terms_are_well_typed coef coefpat [arr; istart; iend] cont =
        match unfold_inferred_type elem_tp with
          ObjType _ | ArrayType _ ->
          begin match extract
            begin function
              Chunk ((g', is_symb), [elem_tp'], coef', [arr'; istart'; iend'; elems'], _) when
                g' == array_slice_symb && definitely_equal arr' arr && definitely_equal istart' istart && definitely_equal iend' iend &&
                is_assignable_to None elem_tp' elem_tp ->
              Some (elem_tp', coef', elems')
            | _ -> None
            end
            h
          with
            None -> cont None
          | Some ((elem_tp', coef', elems'), h') ->
            let f1 = get_unique_var_symb "f" RealType in
            let f2 = get_unique_var_symb "f" RealType in
            let c1 = Chunk ((array_slice_symb, true), [elem_tp], f1, [arr; istart; iend; elems'], None) in
            let c2 = Chunk ((array_slice_symb, true), [elem_tp'], f2, [arr; istart; iend; elems'], None) in
            with_context (Executing (h, [], l, "Auto-upcasting array slice (leaking a fraction)")) $. fun () ->
            cont (Some (c1::c2::h'))
          end
        | _ ->
          cont None
      in
      let get_slice_rule l h typeid_env [elem_tp] terms_are_well_typed coef coefpat [arr; istart; iend] cont =
        let extract_slice h cond cont' =
          match extract
            begin function
              Chunk ((g', is_symb), [elem_tp'], coef', [arr'; istart'; iend'; elems'], _) when
                g' == array_slice_symb && unify elem_tp elem_tp' &&
                definitely_equal arr' arr && cond coef' istart' (Some iend') ->
              Some (Some (coef', istart', iend', elems'), None)
            | Chunk ((g', is_symb), [elem_tp'], coef', [arr'; index; elem], _) when
                g' == array_element_symb && unify elem_tp elem_tp' && definitely_equal arr' arr && cond coef' index None ->
              Some (None, Some (coef', index, elem))
            | _ -> None
            end
            h
          with
            None -> cont None
          | Some ((Some slice, None), h) -> cont' (slice, h)
          | Some ((None, Some (coef', index, elem)), h) ->
            (* Close a unit array_slice chunk *)
            cont' ((coef', index, ctxt#mk_add index (ctxt#mk_intlit 1), mk_list elem_tp [elem]), h)
        in
        if definitely_equal istart iend then (* create empty array by default *)
          cont (Some (Chunk ((array_slice_symb, true), [elem_tp], real_unit, [arr; istart; iend; mk_nil()], None)::h))
        else
          if not (ctxt#query (ctxt#mk_le istart iend)) then
            cont None
          else
          extract_slice h
            begin fun coef' istart' iend' ->
              match iend' with
                None -> definitely_equal istart istart'
              | Some iend' -> ctxt#query (ctxt#mk_and (ctxt#mk_le istart' istart) (ctxt#mk_le istart iend'))
            end $.
          fun ((coef, istart0, iend0, elems0), h) ->
          let mk_chunk istart iend elems remove_if_empty =
            if remove_if_empty && (definitely_equal istart iend) then
              []
            else
              [Chunk ((array_slice_symb, true), [elem_tp], coef, [arr; istart; iend; elems], None)]
          in
          let before_length = ctxt#mk_sub istart istart0 in
          let elems0_before = mk_take before_length elems0 in
          let elems0_notbefore = mk_drop before_length elems0 in
          assume (ctxt#mk_eq elems0 (mk_append elems0_before elems0_notbefore)) $. fun () ->
          let chunks_before = mk_chunk istart0 istart elems0_before true in
          let slices = [(istart, iend0, elems0_notbefore)] in
          let rec find_slices slices curr_end h cont' =
            if ctxt#query (ctxt#mk_le iend curr_end) then
              (* found a list of chunks all the way to the end *)
              cont' (slices, h)
            else
              (* need to consume more chunks *)
            extract_slice h (fun coef'' istart'' end'' -> definitely_equal coef coef'' && definitely_equal istart'' curr_end) $.
            fun ((_, istart'', iend'', elems''), h) ->
            find_slices ((istart'', iend'', elems'')::slices) iend'' h cont'
          in
          find_slices slices iend0 h $. fun ((istart_last, iend_last, elems_last)::slices, h) ->
          let length_last = ctxt#mk_sub iend istart_last in
          let elems_last_notafter = mk_take length_last elems_last in
          let elems_last_after = mk_drop length_last elems_last in
          assume (ctxt#mk_eq elems_last (mk_append elems_last_notafter elems_last_after)) $. fun () ->
          let slices = List.rev ((istart_last, iend, elems_last_notafter)::slices) in
          let rec mk_concat lists =
            match lists with
              [] -> mk_nil()
            | [l] -> l
            | l::ls -> mk_append l (mk_concat ls)
          in
          let target_elems = mk_concat (List.map (fun (istart, iend, elems) -> elems) slices) in
          let target_chunk = mk_chunk istart iend target_elems false in
          let chunks_after = mk_chunk iend iend_last elems_last_after true in
          cont (Some (target_chunk @ chunks_before @ chunks_after @ h))
      in
      let get_slice_deep_rule l h typeid_env [elem_tp; a_tp; v_tp] terms_are_well_typed coef coefpat [arr; istart; iend; p; info] cont = 
        let extract_slice_deep h cond cont' =
          let consume_array_element coef' index elem h =
            (* Close a unit array_slice_deep chunk *)
            (* First check if there is a p(info, elem, ?value) chunk *)
            begin fun cont'' ->
              match
                extract
                  begin function
                    Chunk ((g, is_symb), [], coef'', [arg''; elem''; value''], _) when
                      g == p && definitely_equal coef'' coef' && definitely_equal arg'' info && definitely_equal elem'' elem ->
                      Some value''
                  | _ -> None
                  end
                  h
              with
                Some (v, h) -> cont'' v h
              | None ->
                (* Try to close p(info, elem, ?value) *)
                match try_assq p predinstmap_by_predfamsymb with
                  None -> cont None
                | Some (xs, wbody) ->
                  let tpenv = [] in
                  let ghostenv = [] in
                  let [xinfo, _; xelem, _; xvalue, _] = xs in
                  let env = [xinfo, info; xelem, elem] in
                  let rules = rules_cell in
                  with_context PushSubcontext $. fun () ->
                  with_context (Executing (h, env, asn_loc wbody, "Auto-closing array slice")) $. fun () ->
                  consume_asn rules tpenv h ghostenv env wbody true coef' $. fun _ h ghostenv env size_first ->
                  with_context PopSubcontext $. fun () ->
                  match try_assoc xvalue env with
                    None -> cont None
                  | Some v -> cont'' v h
            end $. fun v h ->
            cont' ((coef', index, ctxt#mk_add index (ctxt#mk_intlit 1), mk_list elem_tp [elem], mk_list v_tp [v]), h)
          in
          match extract
            begin function
              Chunk ((g', is_symb), [elem_tp'; a_tp'; v_tp'], coef', [arr'; istart'; iend'; p'; info'; elems'; vs'], _) as c when
                g' == array_slice_deep_symb && unify elem_tp elem_tp' && unify a_tp a_tp' && unify v_tp v_tp' &&
                definitely_equal arr' arr && definitely_equal p p' && definitely_equal info info' && cond coef' istart' (Some iend') ->
              Some c
            | Chunk ((g', is_symb), [elem_tp'], coef', [arr'; index; elem], _) as c when
                g' == array_element_symb && unify elem_tp elem_tp' && definitely_equal arr' arr && cond coef' index None ->
              Some c
            | Chunk ((g', is_symb), [elem_tp'], coef', [arr'; istart'; iend'; elems'], _) as c when
                g' == array_slice_symb && unify elem_tp elem_tp' && definitely_equal arr' arr && ctxt#query (ctxt#mk_lt istart' iend') &&
                cond coef' istart' (Some (ctxt#mk_add istart' int_unit_term)) || cond coef' (ctxt#mk_sub iend' int_unit_term) (Some iend') ->
              Some c
            | _ -> None
            end
            h
          with
            None -> cont None
          | Some (Chunk ((g', is_symb), [elem_tp'; a_tp'; v_tp'], coef', [arr'; istart'; iend'; p'; info'; elems'; vs'], _), h) when g' == array_slice_deep_symb ->
            cont' ((coef', istart', iend', elems', vs'), h)
          | Some (Chunk ((g', is_symb), [elem_tp'], coef', [arr'; index; elem], _), h) when g' == array_element_symb ->
            consume_array_element coef' index elem h
          | Some (Chunk ((g', is_symb), [elem_tp'], coef', [arr'; istart'; iend'; elems'], _), h) when g' == array_slice_symb ->
            let istart'p1 = ctxt#mk_add istart' int_unit_term in
            if cond coef' istart' (Some istart'p1) then begin
              let head = mk_head elem_tp elems' in
              let tail = mk_tail elems' in
              consume_array_element coef' istart' head (Chunk ((array_slice_symb, true), [elem_tp'], coef', [arr'; istart'p1; iend'; tail], None)::h)
            end else begin
              let iend'm1 = ctxt#mk_sub iend' int_unit_term in
              let index = ctxt#mk_sub iend'm1 istart' in
              let init = mk_take index elems' in
              let last = mk_nth elem_tp index elems' in
              consume_array_element coef' iend'm1 last (Chunk ((array_slice_symb, true), [elem_tp'], coef', [arr'; istart'; iend'm1; init], None)::h)
            end
        in
        if definitely_equal istart iend then (* create empty array by default *)
          cont (Some (Chunk ((array_slice_deep_symb, true), [elem_tp; a_tp; v_tp], real_unit, [arr; istart; iend; p; info; mk_nil(); mk_nil()], None)::h))
        else
          if not (ctxt#query (ctxt#mk_le istart iend)) then
            cont None
          else
          extract_slice_deep h
            begin fun coef' istart' iend' ->
              match iend' with
                None -> definitely_equal istart istart'
              | Some iend' -> ctxt#query (ctxt#mk_and (ctxt#mk_le istart' istart) (ctxt#mk_le istart iend'))
            end $.
          fun ((coef, istart0, iend0, elems0, vs0), h) ->
          let mk_chunk istart iend elems vs =
            Chunk ((array_slice_deep_symb, true), [elem_tp; a_tp; v_tp], coef, [arr; istart; iend; p; info; elems; vs], None)
          in
          let before_length = ctxt#mk_sub istart istart0 in
          let chunk_before = mk_chunk istart0 istart (mk_take before_length elems0) (mk_take before_length vs0) in
          let slices = [(istart, iend0, mk_drop before_length elems0, mk_drop before_length vs0)] in
          let rec find_slices slices curr_end h cont' =
            if ctxt#query (ctxt#mk_le iend curr_end) then
              (* found a list of chunks all the way to the end *)
              cont' (slices, h)
            else
              (* need to consume more chunks *)
            extract_slice_deep h (fun coef'' istart'' end'' -> definitely_equal coef coef'' && definitely_equal istart'' curr_end) $.
            fun ((_, istart'', iend'', elems'', vs''), h) ->
            find_slices ((istart'', iend'', elems'', vs'')::slices) iend'' h cont'
          in
          find_slices slices iend0 h $. fun ((istart_last, iend_last, elems_last, vs_last)::slices, h) ->
          let length_last = ctxt#mk_sub iend istart_last in
          let slices = List.rev ((istart_last, iend, mk_take length_last elems_last, mk_take length_last vs_last)::slices) in
          let rec mk_concat lists =
            match lists with
              [] -> mk_nil()
            | [l] -> l
            | l::ls -> mk_append l (mk_concat ls)
          in
          let target_elems = mk_concat (List.map (fun (istart, iend, elems, vs) -> elems) slices) in
          let target_vs = mk_concat (List.map (fun (istart, iend, elems, vs) -> vs) slices) in
          let target_chunk = mk_chunk istart iend target_elems target_vs in
          let chunk_after = mk_chunk iend iend_last (mk_drop length_last elems_last) (mk_drop length_last vs_last) in
          cont (Some (target_chunk::chunk_before::chunk_after::h))
      in
      begin
      add_rule array_element_symb get_element_rule;
      add_rule array_slice_symb get_slice_upcast_rule;
      add_rule array_slice_symb get_slice_rule;
      add_rule array_slice_deep_symb get_slice_deep_rule
      end
    end;
    rulemap
    (*ref (List.map (fun (predSymb, rules) -> (predSymb, !rules)) !rulemap) *)
  
  let () = rules_cell := ! rules

  let add_rule symb rule = 
    (begin match try_assq symb !rules with
      None -> rules := (symb, ref [rule]) :: !rules
    | Some(rs) -> rs := rule :: !rs end;
    rules_cell := !rules)

  end
  
end
