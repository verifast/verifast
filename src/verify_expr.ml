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
open Assertions

module VerifyExpr(VerifyProgramArgs: VERIFY_PROGRAM_ARGS) = struct
  
  include Assertions(VerifyProgramArgs)
  
  let meths_impl= ref []
  let cons_impl= ref []
  
  module CheckFile_VerifyExpr(CheckFileArgs: CHECK_FILE_ARGS) = struct
  
  include CheckFile_Assertions(CheckFileArgs)
  
  let rec block_assigned_variables ss =
    match ss with
      [] -> []
    | s::ss -> assigned_variables s @ block_assigned_variables ss
  and expr_assigned_variables e =
    match e with
      Operation (l, op, es) | WOperation (l, op, es, _) -> flatmap expr_assigned_variables es
    | TruncatingExpr (l, e) -> expr_assigned_variables e
    | Read (l, e, f) | ActivatingRead (l, e, f) -> expr_assigned_variables e
    | WRead (l, e, fparent, fname, frange, fstatic, fvalue, fghost) -> expr_assigned_variables e
    | ReadArray (l, ea, ei) -> expr_assigned_variables ea @ expr_assigned_variables ei
    | Deref (l, e) -> expr_assigned_variables e
    | WDeref (_, e, _) | WReadUnionMember (_, e, _, _, _, _, _) -> expr_assigned_variables e
    | CallExpr (l, g, _, _, pats, _) -> flatmap (function (LitPat e) -> expr_assigned_variables e | _ -> []) pats
    | ExprCallExpr (l, e, es) -> flatmap expr_assigned_variables (e::es)
    | WPureFunCall (l, g, targs, args) -> flatmap expr_assigned_variables args
    | WPureFunValueCall (l, e, es) -> flatmap expr_assigned_variables (e::es)
    | WMethodCall (l, cn, m, pts, args, mb, tpenv) -> flatmap expr_assigned_variables args
    | NewArray (l, te, e) -> expr_assigned_variables e
    | NewArrayWithInitializer (l, te, es) -> flatmap expr_assigned_variables es
    | IfExpr (l, e1, e2, e3) -> expr_assigned_variables e1 @ expr_assigned_variables e2 @ expr_assigned_variables e3
    | SwitchExpr (l, e, cs, cdef_opt) | WSwitchExpr (l, e, _, _, cs, cdef_opt, _, _) ->
      expr_assigned_variables e @ flatmap (fun (SwitchExprClause (l, ctor, xs, e)) -> expr_assigned_variables e) cs @ (match cdef_opt with None -> [] | Some (l, e) -> expr_assigned_variables e)
    | CastExpr (l, te, e) -> expr_assigned_variables e
    | Upcast (e, fromType, toType) -> expr_assigned_variables e
    | TypedExpr (e, t) -> expr_assigned_variables e
    | WidenedParameterArgument e -> expr_assigned_variables e
    | AddressOf (l, e) -> expr_assigned_variables e
    | AssignExpr (l, (Var (_, x) | WVar (_, x, _)), e) -> [x] @ expr_assigned_variables e
    | AssignExpr (l, e1, e2) -> expr_assigned_variables e1 @ expr_assigned_variables e2
    | AssignOpExpr (l, (Var (_, x) | WVar (_, x, _)), op, e, _) -> [x] @ expr_assigned_variables e
    | AssignOpExpr (l, e1, op, e2, _) -> expr_assigned_variables e1 @ expr_assigned_variables e2
    | InstanceOfExpr(_, e, _) -> expr_assigned_variables e
    | SliceExpr (l, p1, p2) -> flatmap (function Some (LitPat e) -> expr_assigned_variables e | _ -> []) [p1; p2]
    | SuperMethodCall(_, _, args) -> flatmap expr_assigned_variables args
    | WSuperMethodCall(_, _, _, args, _) -> flatmap expr_assigned_variables args
    | _ -> []
  and assigned_variables s =
    match s with
      PureStmt (l, s) -> assigned_variables s
    | NonpureStmt (l, _, s) -> assigned_variables s
    | ExprStmt e -> expr_assigned_variables e
    | DeclStmt (l, xs) -> flatmap (fun (_, _, x, e, _) -> (match e with None -> [] | Some e -> expr_assigned_variables e)) xs
    | IfStmt (l, e, ss1, ss2) -> expr_assigned_variables e @ block_assigned_variables ss1 @ block_assigned_variables ss2
    | ProduceLemmaFunctionPointerChunkStmt (l, e, ftclause, body) ->
      (match e with None -> [] | Some e -> expr_assigned_variables e) @
      begin
        match body with
          None -> []
        | Some s -> assigned_variables s
      end
    | DuplicateLemmaFunctionPointerChunkStmt (l, e) -> expr_assigned_variables e
    | ProduceFunctionPointerChunkStmt (l, ftn, fpe, targs, args, params, openBraceLoc, ss, closeBraceLoc) -> []
    | SwitchStmt (l, e, cs) -> expr_assigned_variables e @ flatmap (fun swtch -> match swtch with (SwitchStmtClause (_, _, ss)) -> block_assigned_variables ss | (SwitchStmtDefaultClause(_, ss)) -> block_assigned_variables ss) cs
    | Assert (l, p) -> []
    | Leak (l, p) -> []
    | Open (l, target, g, targs, ps0, ps1, coef) -> []
    | Close (l, target, g, targs, ps0, ps1, coef) -> []
    | ReturnStmt (l, e) -> (match e with None -> [] | Some e -> expr_assigned_variables e)
    | WhileStmt (l, e, p, d, ss, final_ss) -> expr_assigned_variables e @ block_assigned_variables ss @ block_assigned_variables final_ss
    | Throw (l, e) -> expr_assigned_variables e
    | TryCatch (l, body, catches) -> block_assigned_variables body @ flatmap (fun (l, t, x, body) -> block_assigned_variables body) catches
    | TryFinally (l, body, lf, finally) -> block_assigned_variables body @ block_assigned_variables finally
    | BlockStmt (l, ds, ss, _, _) -> block_assigned_variables ss
    | PerformActionStmt (lcb, nonpure_ctxt, bcn, pre_boxargs, consumed_handle_predicates, lpa, actionname, actionargs, body, closeBraceLoc, post_boxargs, posthandles) ->
      block_assigned_variables body
    | SplitFractionStmt (l, p, targs, pats, coefopt) -> []
    | MergeFractionsStmt (l, a) -> []
    | CreateBoxStmt (l, x, bcn, es, lower_bounds, upper_bounds, handleClauses) -> []
    | CreateHandleStmt (l, x, fresh, hpn, e) -> []
    | DisposeBoxStmt (l, bcn, pats, handleClauses) -> []
    | GotoStmt _ -> []
    | NoopStmt _ -> []
    | LabelStmt _ -> []
    | InvariantStmt _ -> []
    | Break _ -> []
    | SuperConstructorCall(_, es) -> flatmap (fun e -> expr_assigned_variables e) es

  let get_points_to h p predSymb l cont =
    consume_chunk rules h [] [] [] l (predSymb, true) [] real_unit dummypat (Some 1) [TermPat p; dummypat] (fun chunk h coef [_; t] size ghostenv env env' ->
      cont h coef t)
    
  let get_points_to' h p tpx l cont =
    consume_points_to_chunk rules h [] [] [] l tpx real_unit dummypat p dummypat $. fun chunk h coef value ghostenv env env' ->
    cont h coef value

  let current_thread_name = "currentThread"
  let current_thread_type = intType
  
  (* Region: function contracts *)
  
  let functypemap1 =
    let rec iter functypemap ds =
      match ds with
        [] -> List.rev functypemap
      | (ftn, (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, terminates, predfammaps))::ds ->
        let (pre, post) =
          let (wpre, tenv) = check_asn (pn,ilist) tparams (ftxmap @ xmap @ [("this", PtrType Void); (current_thread_name, current_thread_type)]) pre in
          let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
          let (wpost, tenv) = check_asn (pn,ilist) tparams postmap post in
          (wpre, wpost)
        in
        iter ((ftn, (l, gh, tparams, rt, ftxmap, xmap, pre, post, terminates, predfammaps))::functypemap) ds
    in
    iter [] functypedeclmap1
  
  let functypemap = functypemap1 @ functypemap0
  
  let check_breakpoint h env l =
    let ((path, line, col), _) = root_caller_token l in
    match breakpoint with
      None -> ()
    | Some (path0, line0) ->
      if line = line0 && path = path0 then
        assert_false h env l "Breakpoint reached." None

  let check_focus l1 l2 cont =
    match focus with
      None -> cont ()
    | Some (path, line) ->
      let ((path1, line1, _), _) = root_caller_token l1 in
      let ((_, line2, _), _) = root_caller_token l2 in
      if line1 <= line && line <= line2 && path = path1 then
        cont ()

  let is_empty_chunk name targs frac args =
    List.exists
    (fun (symb, fsymbs, conds, ((p, fns), (env, l, predinst_tparams, xs, _, inputParamCount, wbody))) ->
      predname_eq (symb, true) name &&
      let indexCount = List.length fns in
      let Some n = inputParamCount in
      let (inputParams, outputParams) = take_drop n xs in
      let Some tpenv = zip predinst_tparams targs in
      let (indices, real_args) = take_drop indexCount args in
      let (inputArgs, outputArgs) = take_drop n real_args in
      List.for_all2 definitely_equal indices fsymbs &&
      let env = List.map2 (fun (x, tp0) t -> let tp = instantiate_type tpenv tp0 in (x, prover_convert_term t tp tp0)) inputParams inputArgs in
      List.exists (fun conds -> List.for_all (fun cond -> ctxt#query (eval None env cond)) conds) conds
    )
    empty_preds
  
  let check_leaks h env l msg: symexec_result = (* ?check_leaks *)
    match language with
      Java ->
      with_context (Executing (h, env, l, "Leaking remaining chunks")) $. fun () ->
      check_breakpoint h env l;
      major_success ()
    | _ ->
    with_context (Executing (h, env, l, "Cleaning up dummy fraction chunks")) $. fun () ->
    let h = List.filter (fun (Chunk (_, _, coef, _, _)) -> not (is_dummy_frac_term coef)) h in
    with_context (Executing (h, env, l, "Leak check.")) $. fun () ->
    let h = List.filter (function (Chunk(name, targs, frac, args, _)) when is_empty_chunk name targs frac args -> false | _ -> true) h in
    if h <> [] then assert_false h env l msg (Some "leak");
    check_breakpoint [] env l;
    major_success ()
  
  let check_func_header_compat l msg0 msg env00 (k, tparams, rt, xmap, nonghost_callers_only, pre, post, epost, terminates) (k0, tparams0, rt0, xmap0, nonghost_callers_only0, tpenv0, cenv0, pre0, post0, epost0, terminates0) =
    let msg1 = msg in
    let msg = msg ^ ": " in
    if k <> k0 then 
      if (not (is_lemma k)) || (not (is_lemma k0)) then
        static_error l (msg ^ "Not the same kind of function.") None;
    if terminates0 && not terminates then static_error l (msg ^ "Implementation must declare 'terminates' clause.") None;
    let tpenv =
      match zip tparams tparams0 with
        None -> static_error l (msg ^ "Type parameter counts do not match.") None
      | Some bs -> List.map (fun (x, x0) -> (x, GhostTypeParam x0)) bs
    in
    begin
      match (rt, rt0) with
        (None, None) -> ()
      | (Some rt, Some rt0) -> expect_type_core l (msg ^ "Return types: ") None (instantiate_type tpenv rt) rt0
      | _ -> static_error l (msg ^ "Return types do not match.") None
    end;
    begin
      (if (List.length xmap) > (List.length xmap0) then static_error l (msg ^ "Implementation has more parameters than prototype.") None);
      List.iter 
        (fun ((x, t), (x0, t0)) ->
           expect_type_core l (msg ^ "Parameter '" ^ x ^ "': ") None t0 (instantiate_type tpenv t);
        )
        (zip2 xmap xmap0)
    end;
    if nonghost_callers_only <> nonghost_callers_only0 then static_error l (msg ^ "nonghost_callers_only clauses do not match.") None;
    execute_branch begin fun () ->
    with_context (Executing ([], [], l, msg0 ^ ": " ^ msg1)) $. fun () ->
    let env0_0 = List.map (function (p, t) -> (p, get_unique_var_symb p t)) xmap0 in
    let currentThreadEnv = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] in
    let env0 = currentThreadEnv @ env0_0 @ cenv0 in
    produce_asn tpenv0 [] [] env0 pre0 real_unit None None (fun h _ env0 ->
      let bs = zip2 xmap env0_0 in
      let env = currentThreadEnv @ List.map (fun ((p, _), (p0, v)) -> (p, v)) bs @ env00 in
      begin match pre with
        ExprAsn (la, False lf) when la == l ->
        assert_false h env l "Contract required" None
      | _ -> ()
      end;
      consume_asn rules tpenv h [] env pre true real_unit (fun _ h _ env _ ->
        let (env, env0) =
          match rt with
            None -> (env, env0)
          | Some t -> let result = get_unique_var_symb "result" t in (("result", result)::env, ("result", result)::env0)
        in
        execute_branch begin fun () ->
          produce_asn tpenv h [] env post real_unit None None (fun h _ _ ->
            consume_asn rules tpenv0 h [] env0 post0 true real_unit (fun _ h _ env0 _ ->
              check_leaks h env0 l (msg ^ "Implementation leaks heap chunks.")
            )
          )
        end;
        epost |> List.iter begin fun (exceptp, epost) ->
          if not (is_unchecked_exception_type exceptp) then
            execute_branch begin fun () ->
              produce_asn tpenv h [] env epost real_unit None None $. fun h _ _ ->
              let rec handle_exception handlers =
                match handlers with
                | [] -> assert_false h env l ("Potentially unhandled exception " ^ (string_of_type exceptp) ^ ".") None 
                | (handler_tp, epost0) :: handlers ->
                  branch
                    begin fun () ->
                      if (is_subtype_of_ exceptp handler_tp) || (is_subtype_of_ handler_tp exceptp) then
                        consume_asn rules tpenv0 h [] env0 epost0 true real_unit $. fun _ h ghostenv env size_first ->
                        success()
                      else
                        success()
                    end
                    begin fun () ->
                      if not (is_subtype_of_ exceptp handler_tp) then
                        handle_exception handlers
                      else
                        success()
                    end
              in
              handle_exception epost0
            end
        end;
        success()
      )
    )
    end
  
  (** Adds the assumption of the form "is_x(y) == true" to the set
    * of symbolic assumptions, where y is a name of a function that
    * implements a typedef with name x.
    *)
  let assume_is_functype fn ftn =
    let (_, _, _, _, symb) = List.assoc ("is_" ^ ftn) purefuncmap in
    ctxt#assert_term (ctxt#mk_eq (mk_app symb [List.assoc fn funcnameterms]) ctxt#mk_true)
   
  let funcnameterm_of funcmap fn =
    let FuncInfo (env, fterm, l, k, tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, virt, overrides) = List.assoc fn funcmap in fterm
 
  let functypes_implemented = ref []
  
  let check_func_header pn ilist tparams0 tenv0 env0 l k tparams rt fn fterm xs nonghost_callers_only functype_opt contract_opt terminates body =
    if terminates && k <> Regular then static_error l "Terminates clause not allowed here." None;
    check_tparams l tparams0 tparams;
    let tparams1 = tparams0 @ tparams in
    let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) tparams1 Ghost rt) in
    let xmap =
      let rec iter xm xs =
        match xs with
          [] -> List.rev xm
        | (te, x)::xs ->
          if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
          if List.mem_assoc x tenv0 then static_error l ("Parameter '" ^ x ^ "' hides existing variable '" ^ x ^ "'.") None;
          let t = check_pure_type (pn,ilist) tparams1 Ghost te in
          let t =
            match t with
              ArrayType elemType | StaticArrayType (elemType, _) when language = CLang -> PtrType elemType
            | _ -> t
          in
          iter ((x, t)::xm) xs
      in
      iter [] xs
    in
    let tenv = [(current_thread_name, current_thread_type); "#pre", match rt with None -> Void | Some rt -> rt] @ xmap @ tenv0 in
    let (pre, pre_tenv, post) =
      match contract_opt with
        None -> static_error l "Non-fixpoint function must have contract." None
      | Some (pre, post) ->
        let (wpre, pre_tenv) = check_asn (pn,ilist) tparams1 tenv pre in
        let pre_tenv = List.remove_assoc "#pre" pre_tenv in
        let postmap = match rt with None -> pre_tenv | Some rt -> ("result", rt)::pre_tenv in
        let (wpost, tenv) = check_asn (pn,ilist) tparams1 postmap post in
        (wpre, pre_tenv, wpost)
    in
    if nonghost_callers_only then begin
      match k with
        Regular -> static_error l "Only lemma functions can be marked nonghost_callers_only." None
      | Lemma(true, _) -> static_error l "Lemma functions marked nonghost_callers_only cannot be autolemmas." None
      | Lemma(false, _) -> ()
    end;
    let functype_opt =
      match functype_opt with
        None when body <> None && fn = "main" -> Some ("main_full", [], [(l, current_module_name)])
      | _ -> functype_opt
    in
    let functype_opt =
      match functype_opt with
        None -> None
      | Some (ftn, fttargs, ftargs) ->
        if body = None then static_error l "A function prototype cannot implement a function type." None;
        begin
          match resolve Real (pn,ilist) l ftn functypemap with
            None -> static_error l "No such function type." None
          | Some (ftn, (lft, gh, fttparams, rt0, ftxmap0, xmap0, pre0, post0, terminates0, ft_predfammaps)) ->
            let fttargs = List.map (check_pure_type (pn,ilist) [] Ghost) fttargs in
            let fttpenv =
              match zip fttparams fttargs with
                None -> static_error l "Incorrect number of function type type arguments" None
              | Some bs -> bs
            in
            let ftargenv =
              match zip ftxmap0 ftargs with
                None -> static_error l "Incorrect number of function type arguments" None
              | Some bs ->
                List.map
                  begin fun ((x, tp), (larg, arg)) ->
                    let (value, type_) =
                      match try_assoc arg modulemap with
                        None ->
                        begin try
                          List.assoc arg funcnameterms
                        with Not_found ->
                        try
                          funcnameterm_of funcmap0 arg
                        with Not_found ->
                          static_error larg "No such module or function" None
                        end, PtrType Void
                      | Some term -> term, intType
                    in
                    expect_type larg None type_ (instantiate_type fttpenv tp);
                    (x, value)
                  end
                  bs
            in
            let Some fterm = fterm in
            let cenv0 = [("this", fterm)] @ ftargenv in
            let k' = match gh with Real -> Regular | Ghost -> Lemma(true, None) in
            let xmap0 = List.map (fun (x, t) -> (x, instantiate_type fttpenv t)) xmap0 in
            check_func_header_compat l ("Function '" ^ fn ^ "'") "Function type implementation check" env0
              (k, tparams, rt, xmap, nonghost_callers_only, pre, post, [], terminates)
              (k', [], rt0, xmap0, false, fttpenv, cenv0, pre0, post0, [], terminates0);
            if gh = Real then
            begin
              if ftargs = [] && fttargs = [] then
                assume_is_functype fn ftn;
              if not (List.mem_assoc ftn functypemap1) then
                functypes_implemented := (fn, lft, ftn, List.map snd ftargs, unloadable)::!functypes_implemented
            end;
            Some (ftn, ft_predfammaps, fttargs, ftargs)
        end
    in
    (rt, xmap, functype_opt, pre, pre_tenv, post)
  
  let is_transparent_stmt s =
    match s with
    | Assert (_, False _) -> true
    | LabelStmt _ -> true
    | PureStmt _ | NonpureStmt _ | BlockStmt _ -> true
    | _ -> false

  let reportStmts ss = List.iter (stmt_iter (fun s -> if not (is_transparent_stmt s) then reportStmt (stmt_loc s))) ss

  let check_cxx_spec_overrides fenv (meth_name, meth_info) get_meth_info =
    let FuncInfo ([], fterm, l, k, tparams, rt, xmap, ng_callers_only, pre, pre_tenv, post, terminates, _, _, is_virtual, overrides) = meth_info in
    match overrides with
    | [] -> ()
    | _ ->
      let ("this", PtrType (StructType derived)) :: xmap = xmap in
      let this_term = get_unique_var_symb_non_ghost "this" (PtrType (StructType derived)) in
      let env = ("this", this_term) :: fenv in
      let rec check (prev_base_name, prev_base_term) overrides =
        match overrides with
        | [] -> ()
        | override :: overrides ->
          let FuncInfo ([], fterm0, l0, k0, tparams0, rt0, xmap0, ng_callers_only0, pre0, pre_tenv0, post0, terminates0, _, _, is_virtual0, overrides0) = get_meth_info override in
          let ("this", PtrType (StructType base)) :: xmap0 = xmap0 in
          let base_term = direct_base_addr (prev_base_name, prev_base_term) base in
          let () = check_func_header_compat l ("Method '" ^ meth_name ^ "'") ("Checking that it correctly overrides '" ^ override ^ "'") env
            (Regular, [], rt, xmap, false, pre, post, [], terminates)
            (Regular, [], rt0, xmap0, false, [], (("this", base_term) :: fenv), pre0, post0, [], terminates0)
          in
          let () = check (base, base_term) overrides0 in
          check (prev_base_name, prev_base_term) overrides
      in
      check (derived, this_term) overrides
    
  let (funcmap1, prototypes_implemented) =
    let rec iter pn ilist funcmap prototypes_implemented ds =
      match ds with
        [] -> (funcmap, List.rev prototypes_implemented)
      | Func (l, k, tparams, rt, fn, xs, nonghost_callers_only, functype_opt, contract_opt, terminates, body, is_virtual, overrides)::ds when k <> Fixpoint ->
        let fn = full_name pn fn in
        let fterm = List.assoc fn funcnameterms in
        if body <> None then
          ctxt#assert_term (ctxt#mk_eq (ctxt#mk_app func_rank [fterm]) (ctxt#mk_reallit !func_counter));
        if report_skipped_stmts || match contract_opt with Some ((False _ | ExprAsn (_, False _)), _) -> false | _ -> true then begin match body with None -> () | Some (ss, _) -> reportStmts ss end;
        incr func_counter;
        let (rt, xmap, functype_opt, pre, pre_tenv, post) =
          check_func_header pn ilist [] [] [] l k tparams rt fn (Some fterm) xs nonghost_callers_only functype_opt contract_opt terminates body
        in
        let body' = match body with None -> None | Some body -> Some (Some body) in
        let fenv = 
          match xmap, dialect with
          | ("this", PtrType (StructType sn)) :: _, Some Cxx ->
            let _, _, _, _, type_info = List.assoc sn structmap in
            ["thisType", type_info]
          | _ -> []
        in
        begin fun cont ->
          match try_assoc2 fn funcmap funcmap0 with
            None -> cont (fn, FuncInfo ([], fterm, l, k, tparams, rt, xmap, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body', is_virtual, overrides)) prototypes_implemented
          | Some (FuncInfo ([], fterm0, l0, k0, tparams0, rt0, xmap0, nonghost_callers_only0, pre0, pre_tenv0, post0, terminates0, _, Some _, is_virtual0, overrides0)) ->
            if body = None then
              static_error l "Function prototype must precede function implementation." None
            else
              static_error l "Duplicate function implementation." None
          | Some (FuncInfo ([], fterm0, l0, k0, tparams0, rt0, xmap0, nonghost_callers_only0, pre0, pre_tenv0, post0, terminates0, functype_opt0, None, is_virtual, overrides0)) ->
            if body = None then static_error l "Duplicate function prototype." None;
            check_func_header_compat l ("Function '" ^ fn ^ "'") "Function prototype implementation check" fenv 
              (k, tparams, rt, xmap, nonghost_callers_only, pre, post, [], terminates) 
              (k0, tparams0, rt0, xmap0, nonghost_callers_only0, [], fenv, pre0, post0, [], terminates0);
            cont (fn, FuncInfo ([], fterm, l, k, tparams, rt, xmap, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body', is_virtual, overrides)) ((fn, l0)::prototypes_implemented)
        end @@ fun func_info protos_implemented ->
        let () = check_cxx_spec_overrides fenv func_info (fun name -> assoc2 name funcmap funcmap0) in
        iter pn ilist (func_info :: funcmap) protos_implemented ds
      | _::ds -> iter pn ilist funcmap prototypes_implemented ds
    in
    let rec iter' (funcmap,prototypes_implemented) ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest-> iter' (iter pn il funcmap prototypes_implemented ds) rest
      | [] -> (funcmap,prototypes_implemented)
    in
    iter' ([],[]) ps
  
  let funcmap = funcmap1 @ funcmap0

  let cxx_ctor_map1, ctors_implemented =
    let check_init_list pn ilist tenv struct_name body_opt struct_name =
      body_opt |> option_map @@ fun (init_list, b) ->
        let init_list_checked =
          let _, Some (bases, fields, _), _, _, _ = List.assoc struct_name structmap in 
          init_list |> List.map @@ function 
            | ("this", Some (init, is_written)) ->
              let w, tp = check_expr (pn,ilist) [] tenv None init in
              let () = expect_type (expr_loc init) None (StructType struct_name) tp in
              "this", Some (w, is_written)
            | (field_name, init_expr_opt) ->
              (* init_expr_opt is None when the member has a default initializer and no implicit constructor call, otherwise {i Some (init, is_written)} is present *)
              let init_opt =
                init_expr_opt |> option_map @@ fun (init, is_written) ->
                let _, _, field_type, _, _ = List.assoc field_name fields in
                check_expr_t_core functypemap funcmap [] [] (pn, ilist) [] tenv None init field_type, is_written
              in 
              field_name, init_opt
        in
        Some (init_list_checked, b)
    in
    let rec iter pn ilist ctor_map ctors_implemented ds =
      match ds with 
      | [] -> ctor_map, List.rev ctors_implemented
      | CxxCtor (loc, _, _, _, _, _, _, UnionType _) :: _ -> static_error loc "Union constructors are not supported yet." None 
      | CxxCtor (loc, mangled_name, params, contract_opt, terminates, body_opt, implicit, StructType struct_name) :: rest ->
        if report_skipped_stmts || match contract_opt with Some ((False _ | ExprAsn (_, False _)), _) -> false | _ -> true then begin match body_opt with None -> () | Some (_, (ss, _)) -> reportStmts ss end;
        let this_type = PtrType (StructType struct_name) in
        let thisType_type = PtrType (StructType "std::type_info") in
        let None, xmap, None, pre, pre_tenv, post =
          check_func_header pn ilist [] ["this", this_type; "thisType", thisType_type] [] loc Regular [] None struct_name None params false None contract_opt terminates body_opt
        in
        begin
          match try_assoc2 mangled_name ctor_map cxx_ctor_map0 with 
          | None -> 
            iter pn ilist
              ((mangled_name, (loc, xmap, pre, pre_tenv, post, terminates, check_init_list pn ilist pre_tenv struct_name body_opt struct_name)) :: ctor_map)
              ctors_implemented
              rest
          | Some (_, _, _, _, _, _, Some _) ->
            (* We should never reach this because Clang would not allow it, but let's check it to be sure *)
            if body_opt = None then 
              static_error loc "Constructor prototype must precede constructor implementation." None
            else 
              static_error loc "Duplicate constructor implementation." None 
          | Some (loc0, xmap0, pre0, pre_tenv0, post0, terminates0, None) ->
            if body_opt = None then static_error loc "Duplicate constructor prototype." None;
            let this_term = get_unique_var_symb_non_ghost "this" this_type in
            let this_type = 
              let _, _, _, _, type_info = List.assoc struct_name structmap in
              type_info
            in
            let fenv = ["this", this_term; "thisType", this_type] in
            check_func_header_compat loc ("Constructor '" ^ struct_name ^ "'") "Constructor prototype implementation check" fenv
              (Regular, [], None, xmap, false, pre, post, [], terminates) 
              (Regular, [], None, xmap0, false, [], fenv, pre0, post0, [], terminates0);
            iter pn ilist 
              ((mangled_name, (loc, xmap, pre, pre_tenv, post, terminates, check_init_list pn ilist pre_tenv struct_name body_opt struct_name)) :: ctor_map) 
              ((mangled_name, loc0) :: ctors_implemented)
              rest
        end
      | _ :: rest -> iter pn ilist ctor_map ctors_implemented rest
    in
    let rec iter_ps (ctor_map, ctors_implemented) ps =
      match ps with 
      | PackageDecl (loc, pn, ilist, ds) :: rest -> rest |> iter_ps @@ iter pn ilist ctor_map ctors_implemented ds
      | [] -> ctor_map, ctors_implemented
    in
    iter_ps ([], []) ps

  let cxx_ctor_map = cxx_ctor_map1 @ cxx_ctor_map0
  let prototypes_implemented = prototypes_implemented @ ctors_implemented

  let check_cxx_dtor_spec_overrides fenv derived_struct_name dtor_info get_dtor_info =
    let loc, pre, pre_tenv, post, terminates, _, _, overrides = dtor_info in
    match overrides with
    | [] -> ()
    | _ ->
      let this_term = get_unique_var_symb_non_ghost "this" (PtrType (StructType derived_struct_name)) in
      let env = ("this", this_term) :: fenv in
      let derived_dtor_name = cxx_dtor_name derived_struct_name in
      let rec check (prev_base_name, prev_base_term) overrides =
        match overrides with
        | [] -> ()
        | override :: overrides ->
          let loc0, pre0, pre_tenv0, post0, terminates0, _, is_virtual0, overrides0 = get_dtor_info override in
          let base_term = direct_base_addr (prev_base_name, prev_base_term) override in
          let () = check_func_header_compat loc ("Destructor '" ^ derived_dtor_name ^ "'") ("Checking that it correctly overrides '" ^ (cxx_dtor_name override) ^ "'") env
            (Regular, [], None, [], false, pre, post, [], terminates)
            (Regular, [], None, [], false, [], (("this", base_term) :: fenv), pre0, post0, [], terminates0)
          in
          let () = check (override, base_term) overrides0 in
          check (prev_base_name, prev_base_term) overrides
      in
      check (derived_struct_name, this_term) overrides

  let cxx_dtor_map1, dtors_implemented =
    let rec iter pn ilist dtor_map dtors_implemented ds =
      match ds with
      | [] -> dtor_map, List.rev dtors_implemented
      | CxxDtor (loc, _, _, _, _, _, UnionType _, _, _) :: _ -> static_error loc "Union destructors are not supported yet." None 
      | CxxDtor (loc, mangled_name, contract_opt, terminates, body_opt, implicit, StructType struct_name, is_virtual, overrides) :: rest ->
        let dtor_name = cxx_dtor_name struct_name in
        if report_skipped_stmts || match contract_opt with Some ((False _ | ExprAsn (_, False _)), _) -> false | _ -> true then begin match body_opt with None -> () | Some (ss, _) -> reportStmts ss end;
        let this_type = PtrType (StructType struct_name) in
        let thisType_type = PtrType (StructType "std::type_info") in
        let None, [], None, pre, pre_tenv, post =
          check_func_header pn ilist [] ["this", this_type; "thisType", thisType_type] [] loc Regular [] None struct_name None [] false None contract_opt terminates body_opt
        in
        let this_term = get_unique_var_symb_non_ghost "this" this_type in
        let fenv =
          let thisType = 
            let _, _, _, _, type_info = List.assoc struct_name structmap in
            type_info
          in
          ["thisType", thisType] 
        in
        begin fun cont ->
          match try_assoc2 struct_name dtor_map cxx_dtor_map0 with 
          | None ->
            cont (loc, pre, pre_tenv, post, terminates, (body_opt |> option_map @@ fun b -> Some b), is_virtual, overrides) dtors_implemented
          | Some (_, _, _, _, _, Some _, _, _) ->
            (* We should never reach this because Clang would not allow it, but let's check it to be sure *)
            if body_opt = None then 
              static_error loc "Destructor prototype must precede constructor implementation." None
            else 
              static_error loc "Duplicate destructor implementation." None 
          | Some (loc0, pre0, pre_tenv0, post0, terminates0, None, is_virtual, overrides) ->
            if body_opt = None then static_error loc "Duplicate destructor prototype." None;
            let env = ("this", this_term) :: fenv in
            check_func_header_compat loc ("Destructor '" ^ struct_name ^ "'") "Destructor prototype implementation check" env 
              (Regular, [], None, [], false, pre, post, [], terminates) 
              (Regular, [], None, [], false, [], env, pre0, post0, [], terminates0);
            cont (loc, pre, pre_tenv, post, terminates, (body_opt |> option_map @@ fun b -> Some b), is_virtual, overrides) ((dtor_name, loc0) :: dtors_implemented)
        end @@ fun dtor_info dtors_implemented ->
        let () = check_cxx_dtor_spec_overrides fenv struct_name dtor_info (fun name -> assoc2 name cxx_dtor_map0 dtor_map) in
        iter pn ilist ((struct_name, dtor_info) :: dtor_map) dtors_implemented rest
      | _ :: rest -> iter pn ilist dtor_map dtors_implemented rest 
    in 
    let rec iter_ps (dtor_map, dtors_implemented) ps =
      match ps with 
      | PackageDecl (loc, pn, ilist, ds) :: rest -> rest |> iter_ps @@ iter pn ilist dtor_map dtors_implemented ds 
      | [] -> dtor_map, dtors_implemented
    in 
    iter_ps ([], []) ps

  let cxx_dtor_map = cxx_dtor_map1 @ cxx_dtor_map0
  let prototypes_implemented = prototypes_implemented @ dtors_implemented

  let register_prototype_used l g gterm_opt =
    if not (List.mem (g, l) !prototypes_used) then
      prototypes_used := (g, l)::!prototypes_used;
    match gterm_opt with
    | Some gterm -> ctxt#assert_term (ctxt#mk_lt (ctxt#mk_app func_rank [gterm]) int_zero_term)
    | _ -> ()
  
  let interfmap1 =
    List.map
      begin fun (ifn, (l, fieldmap, specs, preds, interfs, pn, ilist, tparams)) ->
        let mmap =
        let rec iter mmap erased_mmap meth_specs =
          match meth_specs with
            [] -> List.rev mmap
          | Meth (lm, gh, rt, n, ps, co, body, binding, _, _, mtparams)::meths ->
            let allTparams =
              if binding = Instance then
                tparams@mtparams
              else
                mtparams
            in
            if body <> None then static_error lm "Interface method cannot have body" None;
            if binding = Static then static_error lm "Interface method cannot be static" None;
            let xmap =
              let rec iter xm xs =
                match xs with
                 [] -> List.rev xm
               | (te, x)::xs ->
                 if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
                 let t = check_pure_type (pn, ilist) allTparams Real te in
                 iter ((x, t)::xm) xs
              in
              iter [] ps
            in
            let sign = (n, List.map snd (List.tl xmap)) in
            if List.mem_assoc sign mmap then static_error lm "Duplicate method" None;
            let erasedXmap = List.map (fun (n,tp) -> (n,erase_type tp)) xmap in
            let erasedSign = (n, List.map snd xmap) in
            if List.mem_assoc erasedSign erased_mmap then static_error lm "Duplicate method after erasure." None;
            let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn, ilist) allTparams Real rt) in
            let (pre, pre_tenv, post, epost, terminates) =
              match co with
                None -> static_error lm ("Non-fixpoint function must have contract: "^n) None
              | Some (pre, post, epost, terminates) ->
                let (pre, tenv) = check_asn (pn,ilist) [] ((current_thread_name, current_thread_type)::erasedXmap) pre in
                let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
                let (post, _) = check_asn (pn,ilist) [] postmap post in
                let epost = List.map (fun (tp, epost) -> 
                  let (epost, _) = check_asn (pn,ilist) [] tenv epost in
                  let tp = check_pure_type (pn, ilist) [] Ghost tp in
                  (tp, epost)
                ) epost in
                (pre, tenv, post, epost, terminates)
            in
            let methodInfo = ItfMethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, terminates, Public, true, mtparams) in
            iter ((sign, methodInfo)::mmap) ((erasedSign, methodInfo)::erased_mmap) meths
        in
        iter [] [] specs
        in
        (ifn, InterfaceInfo (l, fieldmap, mmap, preds, interfs, tparams))
      end
      interfmap1
  
  let string_of_sign (mn, ts) =
    Printf.sprintf "%s(%s)" mn (String.concat ", " (List.map string_of_type ts))
  
  let () = (* Check interfaces in .java files against their specifications in .javaspec files. *)
    interfmap1 |> List.iter begin function (i, InterfaceInfo (l1, fields1, meths1, preds1, interfs1, tparams1)) ->
      match try_assoc i interfmap0 with
      | None -> ()
      | Some (InterfaceInfo (l0,fields0,meths0,preds0,interfs0, tparams0)) ->
        let rec match_fields fields0 fields1 =
          match fields0 with
            [] -> if fields1 <> [] then static_error l1 ".java file does not correct implement .javaspec file: interface declares more fields" None
          | (fn, f0)::fields0 ->
            match try_assoc fn fields1 with
              None -> static_error l1 (".java file does not correctly implement .javaspec file: interface does not declare field " ^ fn) None
            | Some f1 ->
              if f1.ft <> f0.ft then static_error f1.fl ".java file does not correctly implement .javaspec file: field type does not match" None;
              if !(f1.fvalue) <> !(f0.fvalue) then static_error f1.fl ".java file does not correctly implement .javaspec file: field value does not match" None;
              match_fields fields0 (List.remove_assoc fn fields1)
        in
        let rec match_meths meths0 meths1=
          match meths0 with
            [] -> if meths1 <> [] then static_error l1 ".java file does not correctly implement .javaspec file: interface declares more methods" None
          | (sign, ItfMethodInfo (lm0, gh0, rt0, xmap0, pre0, pre_tenv0, post0, epost0, terminates0, v0, abstract0, mtparams0))::meths0 ->
            match try_assoc sign meths1 with
              None-> static_error l1 (".java file does not correctly implement .javaspec file: interface does not declare method " ^ string_of_sign sign) None
            | Some (ItfMethodInfo (lm1, gh1, rt1, xmap1, pre1, pre_tenv1, post1, epost1, terminates1, v1, abstract1, mtparams1)) ->
              let (mn, _) = sign in
              check_func_header_compat lm1 ("Method '" ^ mn ^ "'") "Method specification check" [] (func_kind_of_ghostness gh1,[],rt1, xmap1,false, pre1, post1, epost1, terminates1) (func_kind_of_ghostness gh0, [], rt0, xmap0, false, [], [], pre0, post0, epost0, terminates1);
              match_meths meths0 (List.remove_assoc sign meths1)
        in
        match_fields fields0 fields1;
        match_meths meths0 meths1
    end
  
  let interf_specs_for_sign map1 sign (itf, passedTypes) =
    let InterfaceInfo (_, fields, meths, _, _, tparams) = List.assoc itf map1 in
    let interTparamEnv = match tparams with 
      [] -> [] 
    | tparams -> List.map2 (fun a b -> (a, b)) tparams passedTypes
    in
    let eraseSign = (fun (n, args) -> (n, List.map erase_type args)) in
    let erasedMeths = List.map (fun (sign, info) -> (eraseSign sign, info)) meths (*Erase the signs of the super methods *)
    in
      match try_assoc (eraseSign sign) erasedMeths with
        None -> []
        (* Update specs to properly apply the childs tparams *)
      | Some ItfMethodInfo (lsuper, gh', rt', xmap', pre', pre_tenv', post', epost', terminates', vis', abstract', mtparams') ->
        (*Map type params to the scope of the child class *)
        let rt' = match rt' with 
          Some(t) -> Some(replace_type lsuper interTparamEnv t)
        | None -> None in
        let xmap' = List.map (fun (name, t) -> (name, replace_type lsuper interTparamEnv t)) xmap' in
        let spec = ItfMethodInfo (lsuper, gh', rt', xmap', pre', pre_tenv', post', epost', terminates', vis', abstract', mtparams') in
        [(itf, spec)]

  let interfmap = (* checks overriding methods in interfaces *)
    let rec iter map0 map1 =
      match map0 with
        [] -> map1
      | (i, InterfaceInfo (l, fields, meths, preds, interfs, tparams)) as elem::rest ->
        List.iter (fun (sign, ItfMethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, terminates, v, abstract, mtparams)) ->
          let superspecs = List.flatten (List.map (interf_specs_for_sign map1 sign) interfs) in
          List.iter (fun (tn, ItfMethodInfo (lsuper, gh', rt', xmap', pre', pre_tenv', post', epost', terminates', vis', abstract', mtparams')) ->
            if rt <> rt' then 
              static_error lm ("Return type (" 
              ^ (match rt with None-> "void" | Some(rt) -> string_of_type rt) 
              ^ ") does not match overridden method(" 
              ^ (match rt' with None -> "void" | Some(rt') -> string_of_type rt') 
              ^ ")"
              ) None;
            if gh <> gh' then
                  begin match gh with
                    Ghost -> static_error lm "A lemma method cannot implement or override a non-lemma method." None
                  | Real -> static_error lm "A non-lemma method cannot implement or override a lemma method." None
            end;
            begin
            push();
            let ("this", thisType)::xmap = xmap in
            let ("this", _)::xmap' = xmap' in
            let thisTerm = get_unique_var_symb "this" thisType in
            let (mn, _) = sign in
            check_func_header_compat l ("Method '" ^ mn ^ "'") "Method specification check" [("this", thisTerm)]
              (Regular, [], rt, xmap, false, pre, post, epost, terminates)
              (Regular, [], rt', xmap', false, [], [("this", thisTerm)], pre', post', epost', terminates');
            pop();
            end
          ) superspecs;
        ) meths;
        iter rest (elem :: map1)
    in
    iter interfmap1 interfmap0
  
  let rec dynamic_of asn =
    match asn with
    | WInstPredAsn (l, None, st, cfin, tn, g, index, pats) ->
      WInstPredAsn (l, None, st, cfin, tn, g, get_class_of_this, pats)
    | Sep (l, a1, a2) ->
      let a1' = dynamic_of a1 in
      let a2' = dynamic_of a2 in
      if a1' == a1 && a2' == a2 then asn else Sep (l, a1', a2')
    | IfAsn (l, e, a1, a2) ->
      let a1' = dynamic_of a1 in
      let a2' = dynamic_of a2 in
      if a1' == a1 && a2' == a2 then asn else IfAsn (l, e, a1', a2')
    | WSwitchAsn (l, e, i, cs) ->
      let rec iter cs =
        match cs with
          [] -> cs
        | WSwitchAsnClause (l, ctor, pats, info, body) as c::cs0 ->
          let body' = dynamic_of body in
          let c' = if body' == body then c else WSwitchAsnClause (l, ctor, pats, info, body') in
          let cs0' = iter cs0 in
          if c' == c && cs0' == cs0 then cs else c'::cs0'
      in
      let cs' = iter cs in
      if cs' == cs then asn else WSwitchAsn (l, e, i, cs')
    | CoefAsn (l, coefpat, body) ->
      let body' = dynamic_of body in
      if body' == body then asn else CoefAsn (l, coefpat, body')
    | _ -> asn
  
  let rank_counter = ref 0

  let classmap1 =
    let rec iter classmap1_done classmap1_todo =
      let rec super_specs_for_sign sign (cn, _) itfs =
        class_specs_for_sign sign cn @ flatmap (interf_specs_for_sign interfmap sign) itfs
      and class_specs_for_sign sign cn =
        if cn = "" then [] else
        let (super, interfs, mmap) =
          match try_assoc cn classmap1_done with
            Some (l, abstract, fin, mmap, fds, constr, super, tpenv, interfs, preds, pn, ilist) -> (super, interfs, mmap)
          | None ->
            match try_assoc cn classmap0 with
              Some {csuper; cinterfs; cmeths} -> (csuper, cinterfs, cmeths)
            | None -> assert false
        in
        let specs =
          match try_assoc sign mmap with
          | Some (MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, Instance, v, _, abstract, mtparams)) -> [(cn, ItfMethodInfo (lm, gh, rt, xmap, pre_dyn, pre_tenv, post_dyn, epost_dyn, terminates, v, abstract, mtparams))]
          | _ -> []
        in
        specs @ super_specs_for_sign sign super interfs
      in
      let string_of_rt rt = match rt with Some(t) -> string_of_type t | _ -> "void" in
      let erase_rt rt = match rt with Some(t) -> Some(erase_type t) | None -> None in
      match classmap1_todo with
        [] -> List.rev classmap1_done
      | (cn, (l, abstract, fin, meths, fds, constr, super, tparams, interfs, preds, pn, ilist))::classmap1_todo ->
        let cont cl = iter (cl::classmap1_done) classmap1_todo in
        let rec iter mmap erased_mmap meths =
          match meths with
            [] -> cont (cn, (l, abstract, fin, List.rev mmap, fds, constr, super, tparams, interfs, preds, pn, ilist))
          | Meth (lm, gh, rt, n, ps, co, ss, fb, v,abstract, mtparams)::meths ->
            (* Only combine them for typechecking, names will never overlap and both are in scope here *)
            let allTparams = 
              if fb = Instance then
                tparams @ mtparams 
              else mtparams
            in
            let xmap =
                let rec iter xm xs =
                  match xs with
                   [] -> List.rev xm
                 | (te, x)::xs -> if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
                     let t = check_pure_type (pn,ilist) allTparams Real te in
                     iter ((x, t)::xm) xs
                in
                iter [] ps
            in
            let xmap1 = match fb with Static -> xmap | Instance -> let _::xmap1 = xmap in xmap1 in
            let sign = (n, List.map snd xmap1) in
            if List.mem_assoc sign mmap then static_error lm "Duplicate method." None;
            (* Apply type erasure to sign that is used to check for duplicate methods after erasure*)
            let erasedSign = (n, List.map erase_type (List.map snd xmap1)) in
            if List.mem_assoc erasedSign erased_mmap then static_error lm "Duplicate method after erasure." None;
            let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn, ilist) allTparams Real rt) in
            let co =
              match co with
                None -> None
              | Some (pre, post, epost, terminates) ->
                let (wpre, tenv) = check_asn (pn,ilist) [] ((current_class, ClassOrInterfaceName cn)::(current_thread_name, current_thread_type)::xmap) pre in
                let postmap = match rt with None -> tenv | Some rt -> ("result", rt)::tenv in
                let (wpost, _) = check_asn (pn,ilist) [] postmap post in
                let wepost = List.map (fun (tp, epost) -> 
                  let (wepost, _) = check_asn (pn,ilist) [] ((current_class, ClassOrInterfaceName cn)::(current_thread_name, current_thread_type)::xmap) epost in
                  let tp = check_pure_type (pn,ilist) [] Real tp in
                  (tp, wepost)
                ) epost in
                let (wpre_dyn, wpost_dyn, wepost_dyn) = if fb = Static then (wpre, wpost, wepost) else (dynamic_of wpre, dynamic_of wpost, List.map (fun (tp, wepost) -> (tp, dynamic_of wepost)) wepost) in
                Some (wpre, tenv, wpost, wepost, wpre_dyn, wpost_dyn, wepost_dyn, terminates)
            in
            let super_specs = if fb = Static then [] else super_specs_for_sign sign super interfs in
            if not is_jarspec then
            List.iter
              begin fun (tn, ItfMethodInfo (lsuper, gh', rt', xmap', pre', pre_tenv', post', epost', terminates', vis', abstract', mtparams')) ->
                if gh <> gh' then
                  begin match gh with
                    Ghost -> static_error lm "A lemma method cannot implement or override a non-lemma method." None
                  | Real -> static_error lm "A non-lemma method cannot implement or override a lemma method." None
                  end;
                if (erase_rt rt) <> (erase_rt rt') then static_error lm 
                  (Printf.sprintf "Return type does not match overridden method for class %s. expected: %s actual: %s. " cn (string_of_rt (erase_rt rt)) (string_of_rt (erase_rt rt'))) None;
                match co with
                  None -> ()
                | Some (pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates) ->
                  execute_branch begin fun () ->
                  let ("this", thisType)::xmap = xmap in
                  let ("this", _)::xmap' = xmap' in
                  let thisTerm = get_unique_var_symb "this" thisType in
                  assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [thisTerm]) (List.assoc cn classterms)) (fun _ ->
                    check_func_header_compat l ("Method '" ^ n ^ "'") "Method specification check" [("this", thisTerm)]
                      (Regular, [], rt, xmap, false, pre, post, epost, terminates)
                      (Regular, [], rt', xmap', false, [], [("this", thisTerm)], pre', post', epost', terminates');
                    success()
                  )
                  end
              end
              super_specs;
            let (pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates) =
              match co with
                Some spec -> spec
              | None ->
                match super_specs with
                  (tn, ItfMethodInfo (_, _, _, xmap', pre', pre_tenv', post', epost', terminates', _, _, _))::_ ->
                  if not (List.for_all2 (fun (x, t) (x', t') -> x = x') xmap xmap') then static_error lm (Printf.sprintf "Parameter names do not match overridden method in %s" tn) None;
                  (pre', pre_tenv', post', epost', pre', post', epost', terminates')
                | [] -> static_error lm "Method must have contract" None
            in
            let ss = match ss with None -> None | Some ss -> Some (Some ss) in
            let methodInfo = MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, fb, v, super_specs <> [], abstract, mtparams) in
            iter ((sign, methodInfo)::mmap) ((erasedSign, methodInfo)::erased_mmap) meths
        in
        iter [] [] meths
    in
    iter [] classmap1
  
  let classmap1 =
    List.map
      begin fun (cn, (l, abstract, fin, meths, fds, ctors, super, tparams, interfs, preds, pn, ilist)) ->
        let rec iter cmap ctors =
          match ctors with
            [] -> (cn, {cl=l; cabstract=abstract; cfinal=fin; cmeths=meths; cfds=fds; cctors=List.rev cmap; csuper=super; ctpenv=tparams; cinterfs=interfs; cpreds=preds; cpn=pn; cilist=ilist})
            | Cons (lm, ps, co, ss, v)::ctors ->
              let xmap =
                let rec iter xm xs =
                  match xs with
                   [] -> List.rev xm
                 | (te, x)::xs ->
                   if List.mem_assoc x xm then static_error lm "Duplicate parameter name." None;
                   let t = check_pure_type (pn, ilist) tparams Real te in
                   iter ((x, t)::xm) xs
                in
                iter [] ps
              in
              let sign = List.map snd xmap in
              if List.mem_assoc sign cmap then static_error lm "Duplicate constructor" None;
              let (pre, pre_tenv, post, epost, terminates) =
                match co with
                  None -> static_error lm "Constructor must have contract" None
                | Some (pre, post, epost, terminates) ->
                  let (wpre, tenv) = check_asn (pn,ilist) [] ((current_class, ClassOrInterfaceName cn)::(current_thread_name, current_thread_type)::xmap) pre in
                  let postmap = ("this", ObjType(cn, []))::tenv in
                  let (wpost, _) = check_asn (pn,ilist) [] postmap post in
                  let wepost = List.map (fun (tp, epost) -> 
                    let (wepost, _) = check_asn (pn,ilist) [] tenv epost in
                    let tp = check_pure_type (pn, ilist) [] Ghost tp in
                    (tp, wepost)
                  ) epost in
                  (wpre, tenv, wpost, wepost, terminates)
              in
              let ss' = match ss with None -> None | Some ss -> Some (Some ss) in
               let epost: (type_ * asn) list = epost in
              iter ((sign, CtorInfo (lm, xmap, pre, pre_tenv, post, epost, terminates, ss', v))::cmap) ctors
        in
        iter [] ctors
      end
      classmap1
  
  (* Default constructor insertion *)

  let classmap1 =
    if is_jarspec then classmap1 else
    let rec iter classmap1_done classmap1_todo =
      match classmap1_todo with
        [] -> List.rev classmap1_done
      | (cn, ({cl=l; cfds=fds; cctors=cmap; csuper=(super, targs)} as cls)) as c::classmap1_todo ->
        let c =
          if cmap <> [] then c else
          (* Check if superclass has zero-arg ctor *)
          begin fun cont ->
            let {cctors=cmap'} = assoc2 super classmap1_done classmap0 in
            match try_assoc [] cmap' with
              Some (CtorInfo (l'', xmap, pre, pre_tenv, post, epost, terminates, body, _)) ->
              let epost: (type_ * asn) list = epost in
              cont pre pre_tenv post epost terminates body
            | None -> c
          end $. fun super_pre super_pre_tenv super_post super_epost super_terminates super_body ->
          let _::super_pre_tenv = super_pre_tenv in (* Chop off the current_class entry *)
          let post =
            List.fold_left
              begin fun post (f, {fl; ft; fbinding}) ->
                if fbinding = Static then
                  post
                else
                  let value =
                    match ft with
                      Bool -> LitPat (False fl)
                    | Int (_, _) -> LitPat (WIntLit (fl, zero_big_int))
                    | ObjType _ | ArrayType _ -> LitPat (Null fl)
                    | _ -> DummyPat
                  in
                  Sep (l, post, WPointsTo (fl, WRead (fl, WVar (fl, "this", LocalVar), cn, f, ft, false, ref (Some None), Real), ft, value))
              end
              super_post
              fds
          in
          let rank =
            match super_body with
              Some (Some (_, super_rank)) -> super_rank + 1
            | _ -> 0
          in
          let default_ctor =
            let sign = [] in
            let xmap = [] in
            let ss = Some (Some (([], l), rank)) in
            let vis = Public in
            (sign, CtorInfo (l, xmap, super_pre, (current_class, ClassOrInterfaceName cn)::super_pre_tenv, post, [], super_terminates, ss, vis))
          in
          (cn, {cls with cctors=[default_ctor]})
        in
        iter (c::classmap1_done) classmap1_todo
    in
    iter [] classmap1
  
  (* Merge classmap1 into classmap0; check class implementations against specifications. *)
  let classmap =
    let rec iter map0 map1 =
      match map0 with
        [] -> map1
      | (cn, cls0) as elem::rest ->
        match try_assoc cn map1 with
          None -> iter rest (elem::map1)
        | Some cls1 ->
          if cls1.cfinal <> cls0.cfinal then static_error cls1.cl "Class finality does not match specification." None;
          let match_fds fds0 fds1=
            let rec iter fds0 fds1=
            match fds0 with
              [] -> fds1
            | (f0, {ft=t0; fvis=vis0; fbinding=binding0; ffinal=final0; finit=init0; fvalue=value0}) as elem::rest ->
              match try_assoc f0 fds1 with
                None-> iter rest (elem::fds1)
              | Some {fl=lf1; ft=t1; fvis=vis1; fbinding=binding1; ffinal=final1; finit=init1; fvalue=value1} ->
                let v1 = ! value0 in
                let v2 = ! value1 in
                begin
                  try
                    if t0 <> t1 || vis0 <> vis1 || binding0 <> binding1 || final0 <> final1 || v1 <> v2 then 
                      static_error lf1 "Duplicate field" None
                  with Invalid_argument _ ->
                  begin
                    match (v1, v2) with 
                    | (Some(Some(IntConst b1)), Some(Some(IntConst b2))) -> 
                        if compare_big_int b1 b2 <> 0 then static_error lf1 "Duplicate field" None
                    | _ -> static_error lf1 "Incomparable fields" None
                  end
                end;
                if !value0 = None && init0 <> None then static_error lf1 "Cannot refine a non-constant field with an initializer." None;
                iter rest fds1
            in
            iter fds0 fds1
          in
          let match_meths meths0 meths1=
            let rec iter meths0 meths1=
              match meths0 with
                [] -> meths1
              | (sign0, MethodInfo (lm0,gh0,rt0,xmap0,pre0,pre_tenv0,post0,epost0,pre_dyn0,post_dyn0,epost_dyn0,terminates0,ss0,fb0,v0,_,abstract0, mtparams0)) as elem::rest ->
                let epost0: (type_ * asn) list = epost0 in
                match try_assoc sign0 meths1 with
                  None-> iter rest (elem::meths1)
                | Some (MethodInfo (lm1,gh1,rt1,xmap1,pre1,pre_tenv1,post1,epost1,pre_dyn1,post_dyn1,epost_dyn1,terminates1,ss1,fb1,v1,_,abstract1, mtparams1)) -> 
                  let epost1: (type_ * asn) list = epost1 in
                  let (mn, _) = sign0 in
                  check_func_header_compat lm1 ("Method '" ^ mn ^ "'") "Method implementation check" []
                    (func_kind_of_ghostness gh1,[], rt1, xmap1,false, pre1, post1, epost1, terminates1)
                    (func_kind_of_ghostness gh0, [], rt0, xmap0, false, [], [], pre0, post0, epost0, terminates0);
                  if ss0=None then meths_impl:=(fst sign0,lm0)::!meths_impl;
                  iter rest meths1
            in
            iter meths0 meths1
          in
          let match_constr constr0 constr1=
            let rec iter constr0 constr1=
              match constr0 with
                [] -> constr1
              | (sign0, CtorInfo (lm0,xmap0,pre0,pre_tenv0,post0,epost0,terminates0,ss0,v0)) as elem::rest ->
                let epost0: (type_ * asn) list = epost0 in
                match try_assoc sign0 constr1 with
                  None-> iter rest (elem::constr1)
                | Some (CtorInfo (lm1,xmap1,pre1,pre_tenv1,post1,epost1,terminates1,ss1,v1)) ->
                  let epost1: (type_ * asn) list = epost1 in
                  let rt= None in
                  check_func_header_compat lm1 ("Class '" ^ cn ^ "'") "Constructor implementation check" []
                    (Regular, [], rt, ("this", ObjType (cn, []))::xmap1, false, pre1, post1, epost1, terminates1)
                    (Regular, [], rt, ("this", ObjType (cn, []))::xmap0, false, [], [], pre0, post0, epost0, terminates0);
                  if ss0=None then cons_impl:=(cn,lm0)::!cons_impl;
                  iter rest constr1
            in
            iter constr0 constr1
          in
          if cls0.csuper <> cls1.csuper || cls0.cinterfs <> cls1.cinterfs then static_error cls1.cl "Duplicate class" None
          else 
          let meths'= match_meths cls0.cmeths cls1.cmeths in
          let fds'= match_fds cls0.cfds cls1.cfds in
          let constr'= match_constr cls0.cctors cls1.cctors in
          iter rest ((cn, {cls1 with cmeths=meths'; cfds=fds'; cctors=constr'})::map1)
    in
    iter classmap0 classmap1
  
  (* Region: Type checking of field initializers for instance fields *)

  let classmap =
    List.map
      begin fun (cn, ({cfds=fds; cpn=pn; cilist=ilist} as cls)) ->
        let fds =
          List.map
            begin function
              (f, ({ft; fbinding=Instance; finit=Some e} as fd)) ->
              let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv None e tp in
              let tenv = [(current_class, ClassOrInterfaceName cn); ("this", ObjType (cn, [])); (current_thread_name, current_thread_type)] in
              let w = check_expr_t (pn,ilist) [] tenv e ft in
              (f, {fd with finit=Some w})
            | fd -> fd
            end
            fds
        in
        (cn, {cls with cfds=fds})
      end
      classmap

  (* CXX: check default initializers *)
  let structmap1 = 
    let pn, ilist = "", [] in
    let check_expr_t tenv e tp = check_expr_t_core functypemap funcmap [] [] (pn, ilist) [] tenv None e tp in
    structmap1 |> List.map @@ fun (sn, (sloc, sbody, spad_sym, ssize, sinfo)) ->
      let tenv = ["this", PtrType (StructType sn); current_thread_name, current_thread_type] in 
      let body = sbody |> option_map @@ fun (bases, fields, is_polymorphic) ->
        bases, 
        (fields |> List.map @@ function
          | fname, (floc, fgh, ft, foffset, Some finit) ->
            let init = check_expr_t tenv finit ft in
            fname, (floc, fgh, ft, foffset, Some init)
          | fd -> fd),
        is_polymorphic
      in
      sn, (sloc, body, spad_sym, ssize, sinfo)

  let structmap = structmap1 @ structmap0 
    
  (* Inheritance check *)
  let inheritance_check_processed = ref []
  let inheritance_check cn l =
    if not (List.mem cn !inheritance_check_processed) then
    begin
      inheritance_check_processed := cn::!inheritance_check_processed;
      let {cl; cabstract; cmeths} =
        match try_assoc cn classmap with
        | Some c -> c
        | None -> static_error l "Class not found" None
      in  
      let rec get_overrides cn =
        if cn = "java.lang.Object" then [] else
        let {cmeths; csuper=(csuper, targs)} = List.assoc cn classmap in
        let overrides =
          flatmap
            begin fun (sign, MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, fb, v, is_override, abstract, mtparams)) ->
              if is_override || pre != pre_dyn || post != post_dyn then [(cn, sign)] else []
            end
            cmeths
        in
        overrides @ get_overrides csuper
      in
      if not cabstract then begin
        let overrides = get_overrides cn in
        List.iter
          begin fun (cn, sign) ->
            if not (List.mem_assoc sign cmeths) then
              static_error cl (Printf.sprintf "This class must override method %s declared in class %s or must be declared abstract." (string_of_sign sign) cn) None
          end
          overrides
      end
    end

  let rec interface_methods itf =
    let InterfaceInfo (l, fds, meths, preds, supers, tparams) = List.assoc itf interfmap in
    List.map (fun (sign, _) -> (sign, ("interface", itf))) meths @ flatmap interface_methods (List.map fst supers)
  
  let rec unimplemented_class_methods (cn, targs) trust_cabstract =
    if cn = "" then [] else
    let {cmeths; csuper; cinterfs; cabstract} = List.assoc cn classmap in
    if trust_cabstract && not cabstract then [] else
    let inherited_unimplemented_methods = unimplemented_class_methods csuper true @ flatmap interface_methods (List.map fst cinterfs) in
    let erased_inherited_unimplemented_methods = List.map (fun ((mn,ts),info) -> ((mn, List.map erase_type ts), info)) inherited_unimplemented_methods in
    let abstract_methods = flatmap (function (sign, MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, Instance, v, is_override, true, mtparams)) -> [sign, ("class", cn)] | _ -> []) cmeths in
    let implemented_methods = flatmap (function (sign, MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, Instance, v, is_override, false, mtparams)) -> [sign] | _ -> []) cmeths in
    let erased_implemented_methods = List.map (fun (mn,ts) -> (mn,List.map erase_type ts)) implemented_methods in
    List.filter (fun ((mn,ts), _) -> 
      let erasedSign = (mn, List.map erase_type ts) in
      not (List.mem erasedSign erased_implemented_methods)) erased_inherited_unimplemented_methods @ abstract_methods
  
  let () =
    if not is_jarspec then 
    classmap1 |> List.iter begin function (cn, {cl; cabstract}) ->
      if not cabstract then begin
        match unimplemented_class_methods (cn, []) false with
          [] -> ()
        | (sign, (k, tn))::_ -> static_error cl (Printf.sprintf "This class must implement method %s declared in %s %s or must be declared abstract." (string_of_sign sign) k tn) None
      end
    end
  
  let () =
    if file_type path=Java && filepath = path then begin
    let rec check_spec_lemmas lemmas impl=
      match lemmas with
        [] when List.length impl=0-> ()
      | Func(l,Lemma(auto, trigger),tparams,rt,fn,arglist,nonghost_callers_only,ftype,contract,terminates,None,is_virtual,overrides)::rest ->
          if List.mem (fn,l) impl then
            let impl'= remove (fun (x,l0) -> x=fn && l=l0) impl in
            check_spec_lemmas rest impl'
          else
            static_error l "No implementation found for this lemma." None
    in
    check_spec_lemmas !spec_lemmas prototypes_implemented
    end
  
  let () =
    if file_type path=Java && filepath = path then begin
    let rec check_spec_classes classes meths_impl cons_impl=
      match classes with
        [] -> (match meths_impl with
            []-> ()
          | (n,lm0)::_ -> static_error lm0 ("Method not in specs: "^n) None
          )
      | Class(l, abstract, fin, cn, meths, fds, cons, super, tparams, inames, preds)::rest ->
          inheritance_check cn l;
          let check_meths meths meths_impl=
            let rec iter mlist meths_impl=
              match mlist with
                [] -> meths_impl
              | Meth(lm,gh,rt,n,ps,co,None,fb,v,abstract, mtparams)::rest ->
                if List.mem (n,lm) meths_impl then
                  let meths_impl'= remove (fun (x,l0) -> x=n && lm=l0) meths_impl in
                  iter rest meths_impl'
                else
                static_error lm "No implementation found for this method." None
            in
            iter meths meths_impl
          in
          let check_cons cons cons_impl=
            let rec iter clist cons_impl=
              match clist with
                [] -> cons_impl
              | Cons (lm,ps, co,None,v)::rest ->
                if List.mem (cn,lm) cons_impl then
                  let cons_impl'= remove (fun (x,l0) -> x=cn && lm=l0) cons_impl in
                  iter rest cons_impl'
                else
                static_error lm "No implementation found for this constructor." None
            in
            iter cons cons_impl
          in
          check_spec_classes rest (check_meths meths meths_impl) (check_cons cons cons_impl)
    in
    check_spec_classes !spec_classes !meths_impl !cons_impl
    end
  
  (* Region: symbolic execution helpers *)
  
  let rec mark_if_local locals x =
    match locals with
      [] -> ()
    | (block, head) :: rest -> match try_assoc x head with None -> mark_if_local rest x | Some(addrtaken) -> addrtaken := true; (if(not (List.mem x !block)) then block := x :: (!block))
  
  let rec expr_mark_addr_taken e locals = 
    match e with
      True _ | False _ | Null _ | Var _ | WVar _ | IntLit _ | WIntLit _ | RealLit _ | StringLit(_, _) | ClassLit(_) -> ()
    | Operation(_, _, es) | WOperation (_, _, es, _) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
    | TruncatingExpr (_, e) -> expr_mark_addr_taken e locals
    | AddressOf(_, (Var (_, x) | WVar (_, x, _))) -> mark_if_local locals x
    | Read(_, e, _) | ActivatingRead (_, e, _) -> expr_mark_addr_taken e locals
    | Select(_, e, f) -> expr_mark_addr_taken e locals
    | ArrayLengthExpr(_, e) -> expr_mark_addr_taken e locals
    | WRead(_, e, _, _, _, _, _, _) -> expr_mark_addr_taken e locals
    | WSelect(_, e, _, _, _) -> expr_mark_addr_taken e locals
    | ReadArray(_, e1, e2) -> (expr_mark_addr_taken e1 locals); (expr_mark_addr_taken e2 locals)
    | WReadArray(_, e1, _, e2) -> (expr_mark_addr_taken e1 locals); (expr_mark_addr_taken e2 locals)
    | Deref(_, e) -> expr_mark_addr_taken e locals
    | WDeref(_, e, _) | WReadUnionMember (_, e, _, _, _, _, _) -> expr_mark_addr_taken e locals
    | CallExpr(_, n, _, ps1, ps2, _) -> 
      begin match dialect with 
      | Some Cxx -> 
        let () = ps1 |> List.iter @@ fun pat -> pat_expr_mark_addr_taken pat locals in
        let mark_lvalue_var = function 
        | LitPat (Var (_, x) | WVar (_, x, _)) -> mark_if_local locals x (* otherwise the variable reference would be inside a CxxLValueToRValue expression *)
        | _ -> ()
        in
        if List.mem_assoc n funcmap then 
          ps2 |> List.iter mark_lvalue_var
        else 
          ps2 |>List.iter @@ fun pat -> pat_expr_mark_addr_taken pat locals
      | _ -> 
        List.iter (fun pat -> pat_expr_mark_addr_taken pat locals) (ps1 @ ps2)
      end
    | ExprCallExpr(_, e, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) (e :: es)
    | WFunPtrCall(_, e, ftn, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) (e :: es)
    | WPureFunCall(_, _, _, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
    | WPureFunValueCall(_, e, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) (e :: es)
    | WFunCall(_, _, _, es, _) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
    | WMethodCall _ -> ()
    | NewArray _ -> ()
    | NewObject _ -> ()
    | NewArrayWithInitializer _ -> ()
    | IfExpr(_, e1, e2, e3) -> List.iter (fun e -> expr_mark_addr_taken e locals) [e1;e2;e3]
    | SwitchExpr(_, e, cls, dcl) | WSwitchExpr(_, e, _, _, cls, dcl, _, _) -> List.iter (fun (SwitchExprClause(_, _, _, e)) -> expr_mark_addr_taken e locals) cls; (match dcl with None -> () | Some((_, e)) -> expr_mark_addr_taken e locals)
    | PredNameExpr _ -> ()
    | CastExpr(_, _, e) ->  expr_mark_addr_taken e locals
    | Upcast (e, _, _) -> expr_mark_addr_taken e locals
    | TypedExpr (e, t) -> expr_mark_addr_taken e locals
    | WidenedParameterArgument e -> expr_mark_addr_taken e locals
    | InstanceOfExpr(_, e, _) ->  expr_mark_addr_taken e locals
    | SliceExpr (_, p1, p2) -> List.iter (function Some p -> pat_expr_mark_addr_taken p locals | _ -> ()) [p1; p2]
    | SizeofExpr _ -> ()
    | GenericExpr (l, e, cases, default) ->
      expr_mark_addr_taken e locals;
      List.iter (function (te, e) -> expr_mark_addr_taken e locals) cases;
      begin match default with None -> () | Some e -> expr_mark_addr_taken e locals end
    | AddressOf(_, e) ->  expr_mark_addr_taken e locals
    | ProverTypeConversion(_, _, e) ->  expr_mark_addr_taken e locals
    | ArrayTypeExpr'(_, e) ->  expr_mark_addr_taken e locals
    | AssignExpr(_, e1, e2) ->  expr_mark_addr_taken e1 locals;  expr_mark_addr_taken e2 locals
    | AssignOpExpr(_, e1, _, e2, _) -> expr_mark_addr_taken e1 locals;  expr_mark_addr_taken e2 locals
    | InitializerList(_, es) -> List.iter (fun e -> expr_mark_addr_taken e locals) es
    | CxxNew (_, _, Some e)
    | WCxxNew (_, _, Some e) -> expr_mark_addr_taken e locals
    | CxxNew (_, _, _)
    | WCxxNew (_, _, _) -> ()
    | CxxConstruct (_, _, _, es)
    | WCxxConstruct (_, _, _, es) -> es |> List.iter @@ fun e -> expr_mark_addr_taken e locals
    | CxxDelete (_, e) -> expr_mark_addr_taken e locals
    | CxxLValueToRValue (_, e) -> expr_mark_addr_taken e locals
    | CxxDerivedToBase (_, e, _) -> expr_mark_addr_taken e locals
    | Sep (_, e1, e2) -> expr_mark_addr_taken e1 locals; expr_mark_addr_taken e2 locals
    | TypeExpr _ -> ()
    | Typeid (_, e) -> expr_mark_addr_taken e locals
  and pat_expr_mark_addr_taken pat locals = 
    match pat with
    | LitPat(e) -> expr_mark_addr_taken e locals
    | _ -> ()
  
  let rec ass_mark_addr_taken a locals = 
    match a with
      PointsTo(_, e, pat) -> expr_mark_addr_taken e locals; pat_expr_mark_addr_taken pat locals;
    | WPointsTo(_, e, _, pat) -> expr_mark_addr_taken e locals; pat_expr_mark_addr_taken pat locals;
    | WPredAsn(_, _, _, _, pats1, pats2) -> List.iter (fun p -> pat_expr_mark_addr_taken p locals) (pats1 @ pats2)
    | InstPredAsn(_, e, _, index, pats) -> expr_mark_addr_taken e locals; expr_mark_addr_taken index locals; List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats
    | WInstPredAsn(_, eopt, _, _, _, _, e, pats) -> 
      (match eopt with None -> () | Some(e) -> expr_mark_addr_taken e locals); 
      expr_mark_addr_taken e locals; 
      List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats
    | ExprAsn(_, e) -> expr_mark_addr_taken e locals; 
    | Sep(_, a1, a2) -> ass_mark_addr_taken a1 locals; ass_mark_addr_taken a2 locals
    | IfExpr(_, e, a1, a2)|IfAsn(_, e, a1, a2) -> expr_mark_addr_taken e locals;  ass_mark_addr_taken a1 locals; ass_mark_addr_taken a2 locals
    | SwitchExpr(_, e, cls, None) -> expr_mark_addr_taken e locals;
        List.iter (fun (SwitchExprClause(_, _, _, a)) -> ass_mark_addr_taken a locals) cls;
    | WSwitchAsn(_, e, i, cls) -> expr_mark_addr_taken e locals;
        List.iter (fun (WSwitchAsnClause(_, _, _, _, a)) -> ass_mark_addr_taken a locals) cls;
    | EmpAsn _ -> ()
    | ForallAsn (l, tp, i, e) -> expr_mark_addr_taken e locals; 
    | CoefAsn(_, pat, a) -> pat_expr_mark_addr_taken pat locals; ass_mark_addr_taken a locals
    | MatchAsn (l, e, pat) -> expr_mark_addr_taken e locals; pat_expr_mark_addr_taken pat locals
    | WMatchAsn (l, e, pat, tp) -> expr_mark_addr_taken e locals; pat_expr_mark_addr_taken pat locals
    | e -> expr_mark_addr_taken e locals
  
  let rec stmt_mark_addr_taken s locals pure cont =
    match s with
      DeclStmt(_, ds) ->
      let (block, mylocals)::rest = locals in
      ds |> List.iter begin fun (_, tp, x, e, (_, blockPtr)) ->
        begin match e, tp with 
        | None, _ -> () 
        | Some (Var (l, x) | WVar (l, x, _)), LValueRefTypeExpr _ -> mark_if_local locals x
        | Some(e), _ -> expr_mark_addr_taken e locals 
        end;
        blockPtr := Some block
      end;
      (* filter out lvalue ref decls: don't mark them as 'addr_taken' so we don't try to consume their chunks at the end of their scope/block *)
      let locals_wo_lvalue_refs = ds 
        |> List.filter (fun (_, tx, _, _, _) -> is_lvalue_ref_type_expr tx |> not) 
        |> List.map @@ fun (_, _, x, _, (addr_taken, _)) -> x, addr_taken 
      in
      cont ((block, locals_wo_lvalue_refs @ mylocals) :: rest)
    | BlockStmt(_, _, ss, _, locals_to_free) -> stmts_mark_addr_taken ss ((locals_to_free, []) :: locals) pure (fun _ -> cont locals)
    | ExprStmt(e) -> expr_mark_addr_taken e locals; cont locals
    | PureStmt(_, s) ->  stmt_mark_addr_taken s locals true cont
    | NonpureStmt(_, _, s) -> stmt_mark_addr_taken s locals false cont
    | IfStmt(l, e, ss1, ss2) -> 
        expr_mark_addr_taken e locals; 
        stmts_mark_addr_taken ss1 locals pure (fun locals -> stmts_mark_addr_taken ss2 locals pure (fun _ -> ())); cont locals
    | LabelStmt _ | GotoStmt _ | NoopStmt _ | Break _ | Throw _ | TryFinally _ | TryCatch _ -> cont locals
    | ReturnStmt(_, Some (Var (_, x) | WVar (_, x, _))) when dialect = Some Cxx && not pure -> mark_if_local locals x
    | ReturnStmt(_, Some(e)) ->  expr_mark_addr_taken e locals; cont locals
    | ReturnStmt(_, None) -> cont locals
    | Assert(_, p) -> ass_mark_addr_taken p locals; cont locals
    | Leak(_, p) -> ass_mark_addr_taken p locals; cont locals
    | Open(_, eopt, _, _, pats1, pats2, patopt) | Close(_, eopt, _, _, pats1, pats2, patopt) ->
      (match eopt with None -> () | Some(e) -> expr_mark_addr_taken e locals); 
      List.iter (fun p -> pat_expr_mark_addr_taken p locals) (pats1 @ pats2);
      (match patopt with None -> () | Some(p) -> pat_expr_mark_addr_taken p locals); 
      cont locals
    | SwitchStmt(_, e, cls) -> expr_mark_addr_taken e locals; List.iter (fun cl -> match cl with SwitchStmtClause(_, e, ss) -> (expr_mark_addr_taken e locals); stmts_mark_addr_taken ss locals pure (fun _ -> ()); | SwitchStmtDefaultClause(_, ss) -> stmts_mark_addr_taken ss locals pure (fun _ -> ())) cls; cont locals
    | WhileStmt(_, e1, loopspecopt, e2, ss, final_ss) -> 
        expr_mark_addr_taken e1 locals; 
        (match e2 with None -> () | Some(e2) -> expr_mark_addr_taken e2 locals);
        (match loopspecopt with 
          Some(LoopInv(a)) -> ass_mark_addr_taken a locals;
        | Some(LoopSpec(a1, a2)) -> ass_mark_addr_taken a1 locals; ass_mark_addr_taken a2 locals;
        | None -> ()
        );
        stmts_mark_addr_taken ss locals pure $. fun locals ->
        stmts_mark_addr_taken final_ss locals pure cont
    | SplitFractionStmt(_, _, _, pats, eopt) -> 
        List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats;
        (match eopt with None -> () | Some(e) -> expr_mark_addr_taken e locals); 
        cont locals
    | MergeFractionsStmt(_, a) -> ass_mark_addr_taken a locals;
    | CreateHandleStmt(_, _, _, _, e) -> expr_mark_addr_taken e locals; cont locals
    | DisposeBoxStmt(_, _, pats, clauses) -> 
        List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats;
        List.iter (fun (l, s, pats) -> List.iter (fun p -> pat_expr_mark_addr_taken p locals) pats) clauses;
        cont locals
    | InvariantStmt(_, a) -> ass_mark_addr_taken a locals; cont locals
    | _ -> cont locals
  and
  stmts_mark_addr_taken ss locals pure cont =
    match ss with
      [] -> cont locals
    | s :: ss -> stmt_mark_addr_taken s locals pure (fun locals -> stmts_mark_addr_taken ss locals pure cont)
  
  
  (* locals whose address is taken in e *)
  
  let rec expr_address_taken e =
    let pat_address_taken pat =
      match pat with
        LitPat(e) -> expr_address_taken e
      | _ -> []
    in
    match e with
      True _ | False _ | Null _ | Var _ | WVar _ | IntLit _ | WIntLit _ | RealLit _ | StringLit(_, _) | ClassLit(_) -> []
    | Operation(_, _, es) | WOperation (_, _, es, _) -> List.flatten (List.map (fun e -> expr_address_taken e) es)
    | TruncatingExpr (_, e) -> expr_address_taken e
    | Read(_, e, _) | ActivatingRead (_, e, _) -> expr_address_taken e
    | ArrayLengthExpr(_, e) -> expr_address_taken e
    | WRead(_, e, _, _, _, _, _, _) -> expr_address_taken e
    | WSelect(_, e, _, _, _) -> expr_address_taken e
    | ReadArray(_, e1, e2) -> (expr_address_taken e1) @ (expr_address_taken e2)
    | WReadArray(_, e1, _, e2) -> (expr_address_taken e1) @ (expr_address_taken e2)
    | Deref(_, e) -> (expr_address_taken e)
    | WDeref(_, e, _) | WReadUnionMember (_, e, _, _, _, _, _) -> (expr_address_taken e)
    | CallExpr(_, _, _, ps1, ps2, _) -> List.flatten (List.map (fun pat -> pat_address_taken pat) (ps1 @ ps2))
    | ExprCallExpr(_, e, es) -> List.flatten (List.map (fun e -> expr_address_taken e) (e :: es))
    | WFunPtrCall(_, e, ftn, es) -> List.flatten (List.map (fun e -> expr_address_taken e) (e :: es))
    | WPureFunCall(_, _, _, es) -> List.flatten (List.map (fun e -> expr_address_taken e) es)
    | WPureFunValueCall(_, e, es) -> List.flatten (List.map (fun e -> expr_address_taken e) (e :: es))
    | WFunCall(_, _, _, es, _) -> List.flatten (List.map (fun e -> expr_address_taken e) es)
    | WMethodCall _ -> []
    | NewArray _ -> []
    | NewObject _ -> []
    | NewArrayWithInitializer _ -> []
    | IfExpr(_, e1, e2, e3) -> (expr_address_taken e1) @ (expr_address_taken e2) @ (expr_address_taken e3)
    | SwitchExpr(_, e, cls, dcl) | WSwitchExpr(_, e, _, _, cls, dcl, _, _) -> List.flatten (List.map (fun (SwitchExprClause(_, _, _, e)) -> expr_address_taken e) cls) @ (match dcl with None -> [] | Some((_, e)) -> expr_address_taken e)
    | PredNameExpr _ -> []
    | CastExpr(_, _, e) -> expr_address_taken e
    | Upcast (e, fromType, toType) -> expr_address_taken e
    | TypedExpr (e, t) -> expr_address_taken e
    | WidenedParameterArgument e -> expr_address_taken e
    | InstanceOfExpr(_, e, _) -> expr_address_taken e
    | SliceExpr (_, p1, p2) -> flatmap (function Some p -> pat_address_taken p | _ -> []) [p1; p2]
    | SizeofExpr _ -> []
    | GenericExpr (l, e, cs, d) -> expr_address_taken e @ flatmap (fun (te, e) -> expr_address_taken e) cs @ (match d with None -> [] | Some e -> expr_address_taken e)
    | AddressOf(_, (Var (_, x) | WVar (_, x, _))) -> [x]
    | AddressOf(_, e) -> expr_address_taken e
    | ProverTypeConversion(_, _, e) -> expr_address_taken e
    | ArrayTypeExpr'(_, e) -> expr_address_taken e
    | AssignExpr(_, e1, e2) -> (expr_address_taken e1) @ (expr_address_taken e2)
    | AssignOpExpr(_, e1, _, e2, _) -> (expr_address_taken e1) @ (expr_address_taken e2)
    | InitializerList (_, es) -> flatmap expr_address_taken es
    | _ -> []
  
  let rec stmt_address_taken s =
    (* incomplete: might miss &x expressions *)
    match s with
      PureStmt(_, s) -> stmt_address_taken s
    | NonpureStmt(_, _, s) -> stmt_address_taken s
    | DeclStmt(_, ds) -> List.flatten (List.map (fun (_, _, _, e, _) -> match e with None -> [] | Some(e) -> expr_address_taken e) ds)
    | ExprStmt(e) -> expr_address_taken e
    | IfStmt(_, e, ss1, ss2) -> (expr_address_taken e) @ (List.flatten (List.map (fun s -> stmt_address_taken s) (ss1 @ ss2)))
    | SwitchStmt(_, e, cls) -> (expr_address_taken e) @ (List.flatten (List.map (fun cl -> match cl with SwitchStmtClause(_, e, ss) -> (expr_address_taken e) @ (List.flatten (List.map (fun s -> stmt_address_taken s) ss)) | SwitchStmtDefaultClause(_, ss) -> (List.flatten (List.map (fun s -> stmt_address_taken s) ss))) cls))
    | Assert(_, p) -> []
    | Leak(_, p) -> []
    | Open _ | Close _ -> []
    | ReturnStmt(_, Some(e)) -> expr_address_taken e
    | ReturnStmt(_, None) -> []
    | WhileStmt(_, e1, loopspecopt, e2, ss, final_ss) -> (expr_address_taken e1) @ (match e2 with None -> [] | Some(e2) -> expr_address_taken e2) @ (List.flatten (List.map (fun s -> stmt_address_taken s) ss)) @ flatmap (stmt_address_taken) final_ss
    | BlockStmt(_, decls, ss, _, _) -> (List.flatten (List.map (fun s -> stmt_address_taken s) ss))
    | LabelStmt _ | GotoStmt _ | NoopStmt _ | Break _ | Throw _ | TryFinally _ | TryCatch _ -> []
    | _ -> []
  
  let nonempty_pred_symbs =
    field_pred_map |> flatmap begin function
      (_, ((_, (_, _, _, _, symb, _, _)), None)) -> [symb]
    | (_, ((_, (_, _, _, _, symb, _, _)), Some (_, (_, _, _, _, symb_, _, _)))) -> [symb; symb_]
    end
  
  let eval_non_pure_cps ev is_ghost_expr ((h, env) as state) env e cont =
    let assert_term = if is_ghost_expr then None else Some (fun l t msg url -> assert_term t h env l msg url) in
    let read_field =
      (fun l t f -> read_field h env l t f),
      (fun l f -> read_static_field h env l f),
      (fun l p t -> deref_pointer h env l p t),
      (fun l a i -> read_array h env l a i)
    in
    eval_core_cps ev state assert_term (Some read_field) env e cont
  
  let eval_non_pure is_ghost_expr h env e =
    let assert_term = if is_ghost_expr then None else Some (fun l t msg url -> assert_term t h env l msg url) in
    let read_field =
      (fun l t f -> read_field h env l t f),
      (fun l f -> read_static_field h env l f),
      (fun l p t -> deref_pointer h env l p t),
      (fun l a i -> read_array h env l a i)
    in
    eval_core assert_term (Some read_field) env e
  
  type c_object_value = Unspecified | Default | Expr of expr | Term of termnode

  (** Used to produce malloc'ed, global, local, or nested C variables/objects.
    * If [tp] is a struct type, [producePaddingChunk] says whether the padding chunk for the outermost struct should be produced.
    * (A padding chunk is always produced for nested structs.)
    *)
  let rec produce_c_object l coef addr tp eval_h init allowGhostFields producePaddingChunk h env cont =
    let produce_char_array_chunk h env addr length =
      let pred_symb, elem_type = if init = Default then chars_pred_symb (), charType else chars__pred_symb (), option_type charType in
      let elems = get_unique_var_symb "elems" (list_type elem_type) in
      begin fun cont ->
        if init = Default then
          assume (mk_all_eq charType elems (ctxt#mk_intlit 0)) cont
        else
          cont ()
      end $. fun () ->
      assume_eq (mk_length elems) length $. fun () ->
      cont (Chunk ((pred_symb, true), [], coef, [addr; length; elems], None)::h) env
    in
    match tp with
      StaticArrayType (elemTp, elemCount) ->
      let elemSize = sizeof l elemTp in
      if elemCount > 0 then begin
        let arraySize = ctxt#mk_mul (ctxt#mk_intlit elemCount) elemSize in
        ctxt#assert_term (mk_object_pointer_within_limits addr arraySize)
      end;
      let produce_char_array_chunk h env addr elemCount =
        produce_char_array_chunk h env addr (ctxt#mk_mul (ctxt#mk_intlit elemCount) elemSize)
      in
      let produce_array_chunk h env produceUninitChunk addr elems elemCount =
        match try_pointee_pred_symb0 elemTp with
          Some (_, _, _, arrayPredSymb, _, _, _, _, _, _, _, uninitArrayPredSymb) ->
          let length = ctxt#mk_intlit elemCount in
          assume_eq (mk_length elems) length $. fun () ->
          cont (Chunk (((if produceUninitChunk then uninitArrayPredSymb else arrayPredSymb), true), [], coef, [addr; length; elems], None)::h) env
        | None ->
        match int_rank_and_signedness elemTp with
          Some (k, signedness) ->
          let length = ctxt#mk_intlit elemCount in
          assume_eq (mk_length elems) length $. fun () ->
          cont (Chunk (((if produceUninitChunk then integers___symb () else integers__symb ()), true), [], coef, [addr; rank_size_term k; mk_bool (signedness = Signed); length; elems], None)::h) env
        | None ->
          (* Produce a character array of the correct size *)
          produce_char_array_chunk h env addr elemCount
      in
      begin match elemTp, init with
        Int (Signed, CharRank), Expr (StringLit (_, s)) ->
        produce_array_chunk h env false addr (mk_char_list_of_c_string elemCount s) elemCount
      | (UnionType _ | StructType _ | StaticArrayType (_, _)), Expr (InitializerList (ll, es)) ->
        let rec iter h env i es =
          let addr = mk_ptr_add_ l addr (ctxt#mk_intlit i) elemTp in
          match es with
            [] ->
            produce_char_array_chunk h env addr (elemCount - i)
          | e::es ->
            produce_c_object l coef addr elemTp eval_h (Expr e) false true h env $. fun h env ->
            iter h env (i + 1) es
        in
        iter h env 0 es
      | _, Expr (InitializerList (ll, es)) ->
        let rec iter h env n es cont =
          match es with
            [] -> cont h env (mk_zero_list n)
          | e::es ->
            eval_h h env e $. fun h env elem ->
            iter h env (n - 1) es $. fun h env elems ->
            cont h env (mk_cons elemTp elem elems)
        in
        iter h env elemCount es $. fun h env elems ->
        produce_array_chunk h env false addr elems elemCount
      | _ ->
        let elems = get_unique_var_symb "elems" (list_type (if init = Unspecified then option_type elemTp else elemTp)) in
        begin fun cont ->
          match init, elemTp with
            Default, (Int (_, _)) ->
            assume (mk_all_eq elemTp elems (ctxt#mk_intlit 0)) cont
          | Default, PtrType _ ->
            assume (mk_all_eq elemTp elems (null_pointer_term ())) cont
          | _ ->
            cont ()
        end $. fun () ->
        produce_array_chunk h env (init = Unspecified) addr elems elemCount
      end
    | UnionType un -> begin
      match language, dialect, List.assoc_opt un unionmap with
      CLang, Some Rust, Some (_, Some ([](*fields*), _), _) -> cont h env
      | _ -> produce_char_array_chunk h env addr (sizeof l tp)
      end
    | StructType sn ->
      let (fields, padding_predsymb_opt) =
        match try_assoc sn structmap with
          Some (_, Some (_, fds, _), padding_predsymb_opt, _, _) -> fds, padding_predsymb_opt
        | _ -> static_error l (Printf.sprintf "Cannot produce an object of type 'struct %s' since this struct type has not been defined" sn) None
      in
      let producePaddingChunk = match language, dialect, fields with CLang, Some Rust, [] -> false | _ -> producePaddingChunk in
      let field_values_of_struct_as_value v =
        let (_, _, getters, _) = List.assoc sn struct_accessor_map in
        getters |> List.map (fun (_, getter) -> ctxt#mk_app getter [v])
      in
      begin fun cont ->
        match init with
          Expr (InitializerList (_, es)) -> cont h env (Some (Some (`Exprs es)))
        | Expr e -> eval_h h env e $. fun h env v -> cont h env (Some (Some (`Terms (field_values_of_struct_as_value v))))
        | Term t -> cont h env (Some (Some (`Terms (field_values_of_struct_as_value t))))
        | Default -> cont h env (Some None) (* Initialize to default value (= zero) *)
        | Unspecified -> cont h env None (* Do not initialize; i.e. arbitrary initial value *)
      end $. fun h env inits ->
      begin fun cont ->
        match producePaddingChunk, padding_predsymb_opt with
        | true, Some padding_predsymb ->
          cont (Chunk ((padding_predsymb, true), [], real_unit, [addr], None)::h)
        | _ ->
          cont h
      end $. fun h ->
      let rec iter h env fields inits =
        match fields with
          [] -> cont h env
        | (f, (lf, gh, t, offset, finit))::fields ->
          if gh = Ghost && not allowGhostFields then static_error l "Cannot produce a struct instance with ghost fields in this context." None;
          let init, inits =
            if gh = Ghost then Unspecified, inits else
            match inits with
              Some (Some (`Exprs (e::es))) -> Expr e, Some (Some (`Exprs es))
            | Some (Some (`Terms (t::ts))) -> Term t, Some (Some (`Terms ts))
            | Some (None | Some (`Exprs [] | `Terms [])) -> Default, Some None
            | _ -> Unspecified, None
          in
          match t with
            StaticArrayType (_, _) | StructType _ | UnionType _ ->
            produce_c_object l coef (field_address l addr sn f) t eval_h init allowGhostFields true h env $. fun h env ->
            iter h env fields inits
          | _ ->
            begin fun cont ->
              match init with
                Default ->
                cont h env begin Some
                begin match provertype_of_type t with
                  ProverBool -> ctxt#mk_false
                | ProverInt -> ctxt#mk_intlit 0
                | ProverReal -> real_zero
                | ProverInductive ->
                  match t with
                    PtrType _ -> null_pointer_term ()
                  | _ -> get_unique_var_symb_ "value" t (gh = Ghost)
                end
                end
              | Expr e -> eval_h h env e (fun h env v -> cont h env (Some v))
              | Term t -> cont h env (Some t)
              | Unspecified -> cont h env (match gh with Ghost -> Some (get_unique_var_symb_ "value" t true) | Real -> None)
            end $. fun h env value ->
            assume_field h sn f t gh addr value coef $. fun h ->
            iter h env fields inits
      in
      iter h env fields inits
    | _ ->
      begin fun cont ->
        match init with
          Default -> cont h env (Some (match tp with PtrType _ -> null_pointer_term () | Bool -> false_term | _ -> ctxt#mk_intlit 0))
        | Expr e -> eval_h h env e $. fun h env value -> cont h env (Some value)
        | Unspecified -> cont h env None
        | Term t -> cont h env (Some t)
      end $. fun h env value ->
      produce_points_to_chunk_ l h tp coef addr value $. fun h ->
      cont h env
  
  let rec consume_c_object_core_core l coefpat addr tp h consumePaddingChunk consumeUninitChunk cont =
    let consume_char_array_chunk () =
      let pats = [TermPat addr; TermPat (sizeof l tp); dummypat] in
      consume_chunk rules h [] [] [] l ((if consumeUninitChunk then chars__pred_symb() else chars_pred_symb()), true) [] real_unit coefpat (Some 2) pats $. fun chunk h _ [_; _; cs] _ _ _ _ ->
      cont [chunk] h (Some (get_unique_var_symb "value" tp))
    in
    match tp with
      StaticArrayType (elemTp, elemCount) ->
      begin match try_pointee_pred_symb0 elemTp with
        Some (_, _, _, arrayPredSymb, _, _, _, _, _, _, _, uninitArrayPredSymb) ->
        let pats = [TermPat addr; TermPat (ctxt#mk_intlit elemCount); dummypat] in
        consume_chunk rules h [] [] [] l ((if consumeUninitChunk then uninitArrayPredSymb else arrayPredSymb), true) [] real_unit coefpat (Some 2) pats $. fun chunk h _ [_; _; elems] _ _ _ _ ->
        cont [chunk] h (Some elems)
      | None ->
      match int_rank_and_signedness elemTp with
        Some (k, signedness) ->
        let pats = [TermPat addr; TermPat (rank_size_term k); TermPat (mk_bool (signedness = Signed)); TermPat (ctxt#mk_intlit elemCount); dummypat] in
        consume_chunk rules h [] [] [] l ((if consumeUninitChunk then integers___symb () else integers__symb ()), true) [] real_unit coefpat (Some 4) pats $. fun chunk h _ [_; _; _; _; elems] _ _ _ _ ->
        cont [chunk] h (Some elems)
      | None ->
        consume_char_array_chunk ()
      end
    | UnionType un -> begin
      match language, dialect, List.assoc_opt un unionmap with
      CLang, Some Rust, Some (_, Some ([](*fields*), _), _) -> cont [] h None
      | _ -> consume_char_array_chunk ()
      end
    | StructType sn ->
      let fields, padding_predsymb_opt =
        match try_assoc sn structmap with
          Some (_, Some (_, fds, _), padding_predsymb_opt, _, _) -> fds, padding_predsymb_opt
        | _ -> static_error l (Printf.sprintf "Cannot consume an object of type 'struct %s' since this struct type has not been defined" sn) None
      in
      let consumePaddingChunk = match language, dialect, fields with CLang, Some Rust, [] -> false | _ -> consumePaddingChunk in
      begin fun cont ->
        match consumePaddingChunk, padding_predsymb_opt with
          true, Some padding_predsymb ->
          consume_chunk rules h [] [] [] l (padding_predsymb, true) [] real_unit coefpat (Some 1) [TermPat addr] $. fun chunk h _ _ _ _ _ _ ->
          cont [chunk] h
        | _ ->
          cont [] h
      end $. fun chunks h ->
      let rec iter chunks vs h fields =
        match fields with
          [] ->
          let (_, csym, _, _) = List.assoc sn struct_accessor_map in
          cont chunks h (Some (if consumeUninitChunk then real_unit (* dummy term; should never be used *) else ctxt#mk_app csym (List.rev vs)))
        | (f, (lf, gh, t, offset, finit))::fields ->
          match t with
            StaticArrayType (_, _) | StructType _ | UnionType _ ->
            consume_c_object_core_core l coefpat (field_address l addr sn f) t h true consumeUninitChunk $. fun chunks' h (Some value) ->
            iter (chunks' @ chunks) (value::vs) h fields
          | _ ->
             let (_, (_, _, _, _, f_symb, _, _)), p__opt = List.assoc (sn, f) field_pred_map in
             let f_symb_used =
               match consumeUninitChunk, p__opt with
                 true, Some (_, (_, _, _, _, f_symb_, _, _)) ->
                 f_symb_
               | _ -> f_symb
             in
             consume_chunk rules h [] [] [] l (f_symb_used, true) [] real_unit coefpat (Some 1) [TermPat addr; dummypat] $.
             (fun chunk h coef [_; t] size ghostenv env env' -> iter (chunk::chunks) (t::vs) h fields)
      in
      iter chunks [] h fields
    | _ ->
      consume_points_to_chunk_ rules h [] [] [] l tp real_unit coefpat addr dummypat consumeUninitChunk $. fun chunk h _ value _ _ _ ->
      cont [chunk] h (Some value)
  
  let consume_c_object_core l coefpat addr tp h consumePaddingChunk cont =
    consume_c_object_core_core l coefpat addr tp h consumePaddingChunk false cont

  let consume_c_object l addr tp h consumePaddingChunk cont =
    consume_c_object_core l real_unit_pat addr tp h consumePaddingChunk $. fun _ h _ -> cont h

  let produce_cxx_object l coef addr ty eval_h check_ctor_call init allow_ghost_fields produce_padding_chunk h env cont =
    match ty, init with 
    | UnionType _, _ when dialect = Some Cxx -> static_error l "Union construction is not supported yet." None 
    | StructType struct_name, Expr (WCxxConstruct (lc, mangled_name, _, args)) ->
      let ctor_info = try_assoc mangled_name cxx_ctor_map in
      if ctor_info = None then static_error l ("No matching constructor is defined explicitly for " ^ struct_name ^ ".") None;
      let Some (lc, params, pre, pre_tenv, post, terminates, body_opt) = ctor_info in 
      if body_opt = None then register_prototype_used lc mangled_name None;
      let args = args |> List.map @@ fun e -> SrcPat (LitPat e) in
      check_ctor_call l args params pre post terminates h env struct_name @@ fun h env _ ->
      assume_neq (mk_ptr_address addr) int_zero_term @@ fun () ->
      if produce_padding_chunk then
        let _, _, Some padding_pred_symb, _, _ = List.assoc struct_name structmap in
        produce_chunk h (padding_pred_symb, true) [] coef None [addr] None @@ fun h ->
        cont h env
      else
        cont h env
    | _ ->
      produce_c_object l coef addr ty eval_h init allow_ghost_fields produce_padding_chunk h env cont

  let consume_cxx_object_core l coefpat addr ty check_dtor_call consume_padding_chunk dynamic_dispatch h env cont =
    match ty, dialect with 
    | UnionType _, Some Cxx -> static_error l "Union destruction is not supported yet." None 
    | StructType struct_name, Some Cxx ->
      let dtor_info = try_assoc struct_name cxx_dtor_map in 
      if dtor_info = None then static_error l ("No matching destructor is defined explicitly for " ^ struct_name ^ ".") None;
      let Some (ld, pre, pre_tenv, post, terminates, body_opt, dtor_is_virtual, overrides) = dtor_info in 
      if body_opt = None then register_prototype_used ld (cxx_dtor_name struct_name) None;
      let dispatch_dynamically = 
        match dtor_is_virtual with
        | false -> false
        | true -> dynamic_dispatch
      in
      check_dtor_call l pre post terminates h env dispatch_dynamically struct_name @@ fun h env _ ->
      if consume_padding_chunk then 
        let _, _, Some padding_pred_symb, _, _ = List.assoc struct_name structmap in 
        consume_chunk rules h [] [] [] l (padding_pred_symb, true) [] real_unit coefpat (Some 1) [TermPat addr] @@ fun _ h _ _ _ _ env _ ->
        cont h env
      else 
        cont h env
    | _ ->
      consume_c_object_core_core l coefpat addr ty h consume_padding_chunk true @@ fun _ h _ -> 
      cont h env
  
  let consume_cxx_direct_base_object l coefpat addr ty check_dtor_call consume_padding_chunk h env cont =
    consume_cxx_object_core l coefpat addr ty check_dtor_call consume_padding_chunk false h env cont

  let consume_cxx_object l coefpat addr ty check_dtor_call consume_padding_chunk h env cont =
    consume_cxx_object_core l coefpat addr ty check_dtor_call consume_padding_chunk true h env cont

  let assume_is_of_type l t tp cont =
    match tp with
      Int (_, _) ->
      let (min_term, max_term) = limits_of_type tp in
      assume (ctxt#mk_and (ctxt#mk_le min_term t) (ctxt#mk_le t max_term)) cont
    | PtrType _ ->
      assume (mk_pointer_within_limits t) cont
    | _ -> static_error l (Printf.sprintf "Producing the limits of a variable of type '%s' is not yet supported." (string_of_type tp)) None
  
  let assume_instanceof l t tp cont =
    match tp with
    | ObjType (obj, _) ->
        if not (ctxt#query (ctxt#mk_not (ctxt#mk_eq t (ctxt#mk_intlit 0)))) then
        assert_false [] [] l "Can't produce instanceof for a value that might be null." None;
        assume (ctxt#mk_app instanceof_symbol [t; (prover_type_term l tp)]) cont
    | _ ->
      static_error l (Printf.sprintf "Producing instanceof for a variable of type '%s' is not supported." (string_of_type tp)) None

  (* Region: verification of calls *)
  
  let get_purefuncsymb g = let (_, _, _, _, symb) = List.assoc g purefuncmap in symb
  
  let vararg_int_symb = lazy (get_purefuncsymb "vararg_int")
  let vararg_uint_symb = lazy (get_purefuncsymb "vararg_uint")
  let vararg_pointer_symb = lazy (get_purefuncsymb "vararg_pointer")
  let vararg_double_symb = lazy (get_purefuncsymb "vararg_double")
  
  let mk_vararg_int t = mk_app (Lazy.force vararg_int_symb) [t]
  let mk_vararg_uint t = mk_app (Lazy.force vararg_uint_symb) [t]
  let mk_vararg_pointer t = mk_app (Lazy.force vararg_pointer_symb) [t]
  let mk_vararg_double t = mk_app (Lazy.force vararg_double_symb) [t]
  
  let () =
    if language = CLang then begin
      match try_assoc "func_lt" purefuncmap with
        None -> ()
      | Some (_, _, _, _, (func_lt, _)) ->
        (* forall f, g. func_lt(f, g) = (func_rank(f) < func_rank(g)) *)
        ctxt#begin_formal;
        let f = ctxt#mk_bound 0 ctxt#type_inductive in
        let g = ctxt#mk_bound 1 ctxt#type_inductive in
        let app = ctxt#mk_app func_lt [f; g] in
        let body = ctxt#mk_eq app (ctxt#mk_lt (ctxt#mk_app func_rank [f]) (ctxt#mk_app func_rank [g])) in
        ctxt#end_formal;
        ctxt#assume_forall "func_lt" [app] [ctxt#type_inductive; ctxt#type_inductive] body
    end else begin
      match try_assoc "java.lang.Class_lt" purefuncmap with
        None -> ()
      | Some (_, _, _, _, (class_lt, _)) ->
        (* forall C1, C2. Class_lt(C1, C2) = (class_rank(C1) < class_rank(C2)) *)
        ctxt#begin_formal;
        let c1 = ctxt#mk_bound 0 ctxt#type_int in
        let c2 = ctxt#mk_bound 1 ctxt#type_int in
        let app = ctxt#mk_app class_lt [c1; c2] in
        let body = ctxt#mk_eq app (ctxt#mk_lt (ctxt#mk_app class_rank [c1]) (ctxt#mk_app class_rank [c2])) in
        ctxt#end_formal;
        ctxt#assume_forall "Class_lt" [app] [ctxt#type_int; ctxt#type_int] body
    end
  
  type leminfo =
    RealFuncInfo of
      string list  (* Preceding functions *)
      * string  (* Current function *)
      * bool  (* Current function has 'terminates' clause *)
  | RealMethodInfo of (* Also used for constructors *)
      int option (* rank, or None if not marked as 'terminates' *)
  | LemInfo of
      string list  (* Preceding lemmas *)
      * string  (* Current lemma *)
      * (string * int * (termnode) list) option  (* Inductive parameter name, its index and paramter list*)
      * bool  (* nonghost_callers_only *)
  
  let leminfo_is_lemma leminfo =
    match leminfo with
      RealFuncInfo (_, _, _) -> false
    | RealMethodInfo _ -> false
    | LemInfo (_, _, _, _) -> true
  
  let should_terminate leminfo =
    match leminfo with
      RealFuncInfo (gs, g, terminates) -> terminates
    | RealMethodInfo rank -> rank <> None
    | LemInfo (lems, g, indinfo, nonghost_callers_only) -> true
  
  let consume_class_call_perm l currentThread t h cont =
    let (_, _, _, _, call_perm__symb, _, _) = List.assoc "java.lang.call_perm_" predfammap in
    consume_chunk rules h [] [] [] l (call_perm__symb, true) [] real_unit real_unit_pat (Some 2) [TermPat currentThread; TermPat t] $. fun _ h _ _ _ _ _ _ ->
    cont h

  let verify_call funcmap eval_h l (pn, ilist) xo g targs pats (callee_tparams, tr, ps, funenv, pre, post, epost, terminates, dynamic_dispatch) pure is_upcall target_class leminfo sizemap h tparams tenv ghostenv env cont econt =
    let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (Some pure) e tp in
    let check_expr (pn,ilist) tparams tenv pure e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv pure e in
    let eval_h h env pat cont =
      match pat with
        SrcPat (LitPat e) -> eval_h h env e cont
      | TermPat t -> cont h env t
    in
    let tpenv =
      match zip callee_tparams targs with
        None -> static_error l "Incorrect number of type arguments." None
      | Some tpenv -> tpenv
    in
    let ys: string list = List.map (function (p, t) -> p) ps in
    begin fun cont ->
      let rec iter h env ts pats ps =
        match pats, ps with
          [], [] -> cont h env (List.rev ts)
        | pats, [("varargs", _)] ->
          let rec mk_varargs h env args pats =
            match pats with
              SrcPat (LitPat e) ::pats ->
              let (w, tp) = check_expr (pn,ilist) tparams tenv (Some pure) e in
              eval_h h env (SrcPat (LitPat w)) $. fun h env t ->
              let arg =
                let tp_promoted =
                  match tp with
                    Int (_, _) -> integer_promotion (expr_loc e) tp
                  | _ -> tp
                in
                match tp_promoted with
                  Int (Signed, IntRank) -> mk_vararg_int t
                | Int (Unsigned, IntRank) -> mk_vararg_uint t
                | PtrType _ | StaticArrayType _ -> mk_vararg_pointer t
                | Double -> mk_vararg_double t
                | _ -> static_error (expr_loc e) ("Expressions of type '"^string_of_type tp^"' are not yet supported as arguments for a varargs function.") None
              in
              mk_varargs h env (arg::args) pats
            | [] ->
              let varargs = mk_list (InductiveType ("vararg", [])) (List.rev args) in
              cont h env (List.rev (varargs::ts))
          in
          mk_varargs h env [] pats
        | SrcPat (LitPat e)::pats, (x, tp0)::ps ->
          let e, tp0 = match tp0 with 
          | RefType t -> make_addr_of (expr_loc e) e, PtrType t
          | _ -> e, tp0 
          in
          let tp = instantiate_type tpenv tp0 in
          eval_h h env (SrcPat (LitPat (box (check_expr_t (pn,ilist) tparams tenv e tp) tp tp0))) $. fun h env t ->
          iter h env (t::ts) pats ps
        | TermPat t::pats, _::ps ->
          iter h env (t::ts) pats ps
        | _ -> static_error l "Incorrect number of arguments." None
      in
      iter h env [] pats ps
    end $. fun h env ts ->
    let Some env' = zip ys ts in
    begin fun cont ->
      match dialect, try_assoc "this" ps with
      (*** TODO @Nima: For now, we just ignore this check for Rust. It needs a review later *)
      | _, Some ObjType _ | Some Cxx, Some (PtrType (StructType _)) ->
        let this_term = List.assoc "this" env' in
        if not (ctxt#query (ctxt#mk_not (ctxt#mk_eq this_term (null_pointer_term ())))) then
          assert_false h env l "Target of method call might be null." None;
        cont ()
      | _ -> cont ()
    end @@ fun () ->
    begin fun cont ->
      if dialect <> Some Cxx then cont h env' ghostenv
      else
        let this_info_opt =
          match try_assoc "this" ps, target_class with
          | Some (PtrType (StructType struct_name)), _ ->
            Some (struct_name, List.assoc "this" env')
          | None, Some struct_name ->
            Some (struct_name, List.assoc "this" funenv)
          | _ -> None
        in
        match this_info_opt with
        | Some (struct_name, this_term) ->
          let ghostenv = "thisType" :: ghostenv in
          if dynamic_dispatch then
            let vtype_symb = get_pred_symb_from_map struct_name cxx_vtype_map in
            consume_chunk rules h [] [] [] l (vtype_symb, true) [] real_unit dummypat (Some 1) [TermPat this_term; dummypat] @@ fun _ _ _ [_; vtype] _ _ _ _ ->
            cont h (("thisType", vtype) :: env') ghostenv
          else
            let _, _, _, _, type_info = List.assoc struct_name structmap in
            cont h (("thisType", type_info) :: env') ghostenv
        | None -> cont h env' ghostenv
    end @@ fun h env' ghostenv ->
    let currentThread = List.assoc current_thread_name env in
    let cenv = (current_thread_name, currentThread) :: env' @ funenv in
    with_context (Executing (h, env, l, "Verifying call")) $. fun () ->
    with_context PushSubcontext (fun () ->
      begin fun cont ->
        match leminfo with
          RealMethodInfo (Some _) when not pure && not is_upcall ->
          let target_class_term =
            match target_class with
              Some cn -> List.assoc cn classterms
            | None -> ctxt#mk_app get_class_symbol [List.assoc "this" env']
          in
          consume_class_call_perm l currentThread target_class_term h cont
        | _ -> cont h
      end $. fun h ->
      begin match pre with
        ExprAsn (lg, False ld) when ld == dummy_loc ->
        ignore begin
          with_context (Executing (h, env, lg, "Consuming precondition")) $. fun () ->
          assert_false h env lg "Callee must have contract" None
        end
      | _ -> ()
      end;
      begin fun cont ->
        match leminfo with
          RealFuncInfo (gs, g0, caller_terminates) ->
          if caller_terminates && not pure then begin
            if not terminates then static_error l "Callee should be declared as 'terminates'." None;
            begin match g with
              Some g when not (List.mem g gs) ->
              let (_, _, _, _, call_perm__symb, _, _) = List.assoc "call_perm_" predfammap in
              let fterm = List.assoc g funcnameterms in
              consume_chunk rules h [] [] [] l (call_perm__symb, true) [] real_unit real_unit_pat (Some 2) [TermPat (List.assoc current_thread_name env); TermPat fterm] $. fun _ h _ _ _ _ _ _ ->
              cont h
            | _ -> cont h
            end
          end else
            cont h
        | _ ->
          cont h
      end $. fun h ->
      consume_asn_with_post rules tpenv h ghostenv cenv pre true real_unit (fun _ h ghostenv' env' chunk_size post' ->
        let post =
          match post' with
            None -> post
          | Some post' -> post'
        in
        let _ =
          match leminfo with
            RealFuncInfo (gs, g0, caller_terminates) -> ()
          | RealMethodInfo (Some rank) ->
            if not pure && not terminates then static_error l "Callee should be declared as 'terminates'." None
          | RealMethodInfo None -> ()
          | LemInfo (lems, g0, indinfo, nonghost_callers_only) ->
              if match g with Some g -> List.mem g lems | None -> true then
                ()
              else 
                  if g = Some g0 then
                    let rec nonempty h =
                      match h with
                        [] -> false
                      | Chunk ((p, true), _, coef, ts, _)::_ when List.memq p nonempty_pred_symbs && coef == real_unit -> true
                      | _::h -> nonempty h
                    in
                    if nonempty h then
                      ()
                    else (
                      let recursive_check_fail msg =
                        with_context_force (Executing (h, env', l, "Checking recursion termination")) 
                          (fun _ -> assert_false h env l msg (Some "recursivelemmacall"))
                      in
                      match indinfo with
                        None ->
                          begin
                            match chunk_size with
                              Some (PredicateChunkSize k) when k < 0 -> ()
                            | Some (PredicateChunkSize k) when k > 0 -> 
                                recursive_check_fail "Coinductive proof not supported yet."
                            | _ ->
                                recursive_check_fail "Recursive lemma call does not decrease the heap (no full field chunks left) or the derivation depth of the first chunk and there is no inductive parameter."
                          end
                      | Some (x, i, params) ->
                          let fail () = recursive_check_fail "Recursive lemma call does not decrease the heap (no full field chunks left) or the inductive parameter(s)." in
                          if i != 0 then
                            (* induction on one parameter that is not the first *)
                            begin
                              match try_assq (List.assoc x env') sizemap with
                              | Some(t, k) when k < 0 && t == (List.nth params i) -> ()
                              | _ -> fail ()
                            end
                          else
                            (* lexicographic induction on all parameters *)
                            begin
                              let rec check_nested_induction (params, rec_args) =
                                match (params, rec_args) with
                                | (t1::params, t2::rec_args) ->
                                    begin
                                      match try_assq t2 sizemap with
                                      | Some (t, k) when k < 0 && t1 == t -> true 
                                      | Some (t, k) when k = 0 && t1 == t -> check_nested_induction (params, rec_args)
                                      | _ -> false
                                    end
                                | ([], []) -> false
                              in
                              if not (check_nested_induction (params, ts)) then fail ()
                            end
                    )
                  else
                    static_error l "A lemma can call only preceding lemmas or itself." None
        in
        let r, env'' =
          match tr with
            None -> real_unit, env' (* any term will do *)
          | Some t0 ->
            let symbol_name =
              match xo with
                None -> "result"
              | Some x -> x
            in
            let t = instantiate_type tpenv t0 in
            let r = get_unique_var_symb_ symbol_name t pure in
            let env'' = update env' "result" (prover_convert_term r t t0) in
            r, env''
        in
        execute_branch begin fun () ->
          produce_asn tpenv h ghostenv' env'' post real_unit None None $. fun h _ _ ->
          with_context PopSubcontext $. fun () ->
          cont h env r
        end;
        begin match epost with
          None -> ()
        | Some(epost) ->
          epost |> List.iter begin fun (tp, post) ->
            execute_branch $. fun () ->
            produce_asn tpenv h ghostenv' env' post real_unit None None $. fun h _ _ ->
            with_context PopSubcontext $. fun () ->
            let e = get_unique_var_symb_ "excep" tp false in
            econt l h env tp e
          end
        end;
        success()
      )
    )
  
  let default_value t =
    match t with
     Bool -> ctxt#mk_false
    | Int (_, _)|ObjType _|ArrayType _ -> ctxt#mk_intlit 0
    | _ -> get_unique_var_symb_non_ghost "value" t

  
  module LValues = struct
    type lvalue =
      Var of loc * string * ident_scope
    | Field of
        loc
      * termnode option (* target struct instance or object; None if static *)
      * string (* parent, i.e. name of struct or class *)
      * string (* field name *)
      * type_ (* range, i.e. field type *)
      * constant_value option option ref
      * ghostness
      * termnode (* field symbol *)
      * termnode option (* possibly-uninitialized field symbol *)
    | ValueField of
        loc
      * lvalue
      * symbol (* getter function *)
      * symbol (* setter function *)
    | ArrayElement of
        loc
      * termnode (* array *)
      * type_ (* element type *)
      * termnode (* index *)
    | Deref of (* C dereference operator, e.g. *p *)
        loc
      * termnode
      * type_ (* pointee type *)
  end
  
  (* This function checks whether e is a safe expression.
     An expression is safe if it does not read or write the heap, i.e., it does not require any chunks. *)
  let rec is_safe_expr e =
    match e with 
      WIntLit _ -> true
    | True _ -> true
    | False _ -> true
    | WVar (_, x, scope) -> scope = LocalVar
    | WOperation(_, _, es, _) -> List.for_all is_safe_expr es
    | TruncatingExpr (_, e) -> is_safe_expr e
    | IfExpr(_, e1, e2, e3) -> List.for_all is_safe_expr [e1; e2; e3]
    | SizeofExpr(_, _) -> true
    | AddressOf(_, e) -> is_safe_expr e
    | CastExpr (_, _, e) -> is_safe_expr e
    | Upcast (e, _, _) -> is_safe_expr e
    | WPureFunCall (_, _, _, args) -> List.for_all is_safe_expr args
    | _ -> false
  
  let rec asserts_exclusive_ownership a =
    match a with
      ExprAsn (l, e) -> false
    | Sep (l, a1, a2) -> asserts_exclusive_ownership a1 || asserts_exclusive_ownership a2
    | IfAsn (l, e, a1, a2) -> asserts_exclusive_ownership a1 || asserts_exclusive_ownership a2
    | WSwitchAsn (l, e, i, cs) ->
      List.exists (function WSwitchAsnClause (l, c, xs, _, a) -> asserts_exclusive_ownership a) cs
    | EmpAsn _ -> false
    | ForallAsn (_, _, _, _) -> false
    | CoefAsn (l, DummyPat, a) -> false (* TODO: Support more coefpats *)
    | EnsuresAsn (l, _) -> false
    | WMatchAsn (_, _, _, _) -> false
    | _ -> true

  let rec verify_expr readonly (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e cont econt =
    let (envReadonly, heapReadonly) = readonly in
    let verify_expr readonly h env xo e cont = verify_expr readonly (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e (fun h env v -> cont h env v) econt in
    let check_expr (pn,ilist) tparams tenv e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (Some pure) e in
    let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (Some pure) e tp in
    let l = expr_loc e in
    let has_env_effects () = if not assume_left_to_right_evaluation && envReadonly then static_error l "This potentially side-effecting expression is not supported in this position, because of C's unspecified evaluation order" (Some "illegalsideeffectingexpression") in
    let has_heap_effects () = if not assume_left_to_right_evaluation && heapReadonly then static_error l "This potentially side-effecting expression is not supported in this position, because of C's unspecified evaluation order" (Some "illegalsideeffectingexpression") in
    let eval_h h env e cont = verify_expr (true, true) h env None e cont in
    let eval_h_core ro h env e cont = verify_expr ro h env None e cont in
    let rec evhs h env es cont =
      match es with
        [] -> cont h env []
      | e::es -> eval_h h env e (fun h env v -> evhs h env es (fun h env vs -> cont h env (v::vs))) 
    in 
    let check_assign l x =
      if pure && not (List.mem x ghostenv) then static_error l "Cannot assign to non-ghost variable in pure context." None;
      if not pure && List.mem x ghostenv then static_error l "Cannot assign to ghost variable in non-pure context." None
    in
    let vartp l x = 
      match try_assoc x tenv with
          None -> 
        begin
          match try_assoc' Real (pn, ilist) x globalmap with
            None -> static_error l ("No such variable: "^x) None
          | Some((l, tp, symbol, init)) -> (tp, Some(symbol))
        end 
      | Some tp -> (tp, None) 
    in
    let update_local_or_global h env tpx x symb w cont =
      match symb with
        None -> has_env_effects(); cont h (update env x w)
      | Some(symb) -> 
          has_heap_effects();
          get_points_to' h symb tpx l $. fun h coef _ ->
          if not (definitely_equal coef real_unit) then assert_false h env l "Writing to a global variable requires full permission." None;
          produce_points_to_chunk l h tpx real_unit symb w $. fun h ->
          cont h env
    in
    let check_correct h xo g targs args (lg, callee_tparams, tr, ps, funenv, pre, post, epost, terminates, dynamic_dispatch) is_upcall target_class cont =
      (* check_expr is needed here because args are not typechecked yet. Why does check_expr_t not check the arguments of a WFunCall? *)
      let at_most_one_unsafe args = (List.length (List.filter (fun a -> let (w, t) = check_expr (pn,ilist) tparams tenv a in not (is_safe_expr w)) args)) <= 1 in
      let eval_h = if language == CLang && not heapReadonly &&  (List.length args = 1 || at_most_one_unsafe args) then (fun h env e cont -> eval_h_core (true, false) h env e cont) else eval_h in
      let pre = match pre with ExprAsn (la, False _) when la == lg -> ExprAsn (lg, False dummy_loc) | _ -> pre in
      verify_call funcmap eval_h l (pn, ilist) xo g targs (List.map (fun e -> SrcPat (LitPat e)) args) (callee_tparams, tr, ps, funenv, pre, post, epost, terminates, dynamic_dispatch) pure is_upcall target_class leminfo sizemap h tparams tenv ghostenv env cont econt
    in
    let new_array h env l elem_tp length elems =
      let at = get_unique_var_symb (match xo with None -> "array" | Some x -> x) (ArrayType elem_tp) in
      let (_, _, _, _, array_slice_symb, _, _) = List.assoc "java.lang.array_slice" predfammap in
      assume (ctxt#mk_not (ctxt#mk_eq at (ctxt#mk_intlit 0))) $. fun () ->
      assume (ctxt#mk_eq (ctxt#mk_app arraylength_symbol [at]) length) $. fun () ->
      cont (Chunk ((array_slice_symb, true), [elem_tp], real_unit, [at; ctxt#mk_intlit 0; length; elems], None)::h) env at
    in
    let rec eval_h_core_and_activate_union_members readonly h env w cont =
      match w with
        AddressOf (la, WReadUnionMember (lr, wr, unionName, memberIndex, memberName, memberType, isActivating)) ->
        eval_h_core_and_activate_union_members readonly h env wr $. fun h env target ->
        let vp = mk_union_variant_ptr target unionName memberIndex in
        if isActivating then
          let pats = [TermPat target; TermPat (sizeof l memberType); dummypat] in
          consume_chunk rules h [] [] [] l (chars__pred_symb(), true) [] real_unit real_unit_pat (Some 2) pats $. fun _ h _ [_; _; cs] _ _ _ _ ->
          produce_c_object l real_unit vp memberType eval_h Unspecified false true h env $. fun h env ->
          cont h env vp
        else
          cont h env vp
      | AddressOf (la, WRead (lr, wr, fparent, fname, tp, false, fvalue, fghost)) ->
        eval_h_core_and_activate_union_members readonly h env wr $. fun h env target ->
        cont h env (field_address l target fparent fname)
      | AddressOf (la, WDeref (ld, w, _)) ->
        eval_h_core_and_activate_union_members readonly h env w cont
      | _ ->
        eval_h_core readonly h env w cont
    in
    let rec lhs_to_lvalue h env lhs cont =
      match lhs with
        WVar (l, x, scope) -> cont h env (LValues.Var (l, x, scope))
      | WRead (l, w, fparent, fname, tp, fstatic, fvalue, fghost) ->
        let (_, (_, _, _, _, f_symb, _, _)), p__opt = List.assoc (fparent, fname) field_pred_map in
        begin fun cont ->
          if fstatic then
            cont h env None
          else
            eval_h_core_and_activate_union_members readonly h env w (fun h env target -> cont h env (Some target))
        end $. fun h env target ->
        let f_symb__opt =
          match p__opt with
            Some (_, (_, _, _, _, f_symb_, _, _)) -> Some f_symb_
          | None -> None
        in
        cont h env (LValues.Field (l, target, fparent, fname, tp, fvalue, fghost, f_symb, f_symb__opt))
      | WSelect (l, w, fparent, fname, tp) ->
        let (_, _, getters, setters) = List.assoc fparent struct_accessor_map in
        let getter = List.assoc fname getters in
        let setter = List.assoc fname setters in
        lhs_to_lvalue h env w $. fun h env w ->
        cont h env (LValues.ValueField (l, w, getter, setter))
      | WReadInductiveField (l, w, data_type_name, constructor_name, field_name, targs) ->
        let (_, _, _, getters, setters, _, _, _) = List.assoc data_type_name inductivemap in
        let getter = List.assoc field_name getters in
        let setter = List.assoc field_name setters in
        lhs_to_lvalue h env w $. fun h env w ->
        cont h env (LValues.ValueField (l, w, getter, setter))
      | WReadArray (l, arr, elem_tp, i) ->
        eval_h h env arr $. fun h env arr ->
        eval_h h env i $. fun h env i ->
        cont h env (LValues.ArrayElement (l, arr, elem_tp, i))
      | WDeref (l, w, pointeeType) ->
        eval_h_core_and_activate_union_members readonly h env w $. fun h env target ->
        cont h env (LValues.Deref (l, target, pointeeType))
      | _ -> static_error (expr_loc lhs) "Cannot assign to this expression." None
    in
    let rec read_lvalue h env lvalue cont =
      match lvalue with
        LValues.Var (l, x, scope) ->
        eval_h h env (WVar (l, x, scope)) cont
      | LValues.Field (l, target, fparent, fname, tp, fvalue, fghost, f_symb, _) ->
        begin match target with
          Some target ->
          consume_chunk rules h [] [] [] l (f_symb, true) [] real_unit dummypat (Some 1) [TermPat target; dummypat] $. fun chunk h _ [_; value] _ _ _ _ ->
          cont (chunk::h) env value
        | None ->
          consume_chunk rules h [] [] [] l (f_symb, true) [] real_unit dummypat (Some 0) [dummypat] $. fun chunk h _ [value] _ _ _ _ ->
          cont (chunk::h) env value
        end
      | LValues.ValueField (l, w, getter, setter) ->
        read_lvalue h env w $. fun h env x ->
        cont h env (ctxt#mk_app getter [x])
      | LValues.ArrayElement (l, arr, elem_tp, i) when language = Java ->
        let pats = [TermPat arr; TermPat i; SrcPat DummyPat] in
        consume_chunk rules h [] [] [] l (array_element_symb(), true) [elem_tp] real_unit dummypat (Some 2) pats $. fun chunk h _ [_; _; value] _ _ _ _ ->
        cont (chunk::h) env value
      | LValues.ArrayElement (l, arr, elem_tp, i) when language = CLang ->
        cont h env (read_c_array h env l arr i elem_tp)
      | LValues.Deref (l, target, pointeeType) ->
        consume_c_object_core l dummypat target pointeeType h false $. fun chunks h (Some value) ->
        cont (chunks @ h) env value
    in
    let rec write_lvalue h env lvalue value cont =
      match lvalue with
        LValues.Var (l, x, _) ->
        check_assign l x;
        let (tpx, symb) = vartp l x in
        update_local_or_global h env tpx x symb value cont
      | LValues.Field (l, target, fparent, fname, tp, fvalue, fghost, f_symb, f_symb__opt) ->
        has_heap_effects();
        if pure && fghost = Real then static_error l "Cannot write in a pure context" None;
        let targets =
          match target with
            Some t -> [t]
          | None -> []
        in
        let pats = List.map (fun t -> TermPat t) targets @ [dummypat] in
        let f_symb_used =
          match f_symb__opt with
            Some f_symb_ -> f_symb_
          | None -> f_symb
        in
        consume_chunk rules h [] [] [] l (f_symb_used, true) [] real_unit real_unit_pat (Some 1) pats $. fun _ h _ _ _ _ _ _ ->
        cont (Chunk ((f_symb, true), [], real_unit, targets @ [value], None)::h) env
      | LValues.ValueField (l, w, getter, setter) ->
        read_lvalue h env w $. fun h env x ->
        let x = ctxt#mk_app setter [x; value] in
        write_lvalue h env w x cont
      | LValues.ArrayElement (l, arr, elem_tp, i) when language = Java ->
        has_heap_effects();
        if pure then static_error l "Cannot write in a pure context." None;
        begin match try_update_java_array h env l arr i elem_tp value with
          None -> 
          let pats = [TermPat arr; TermPat i; SrcPat DummyPat] in
          consume_chunk rules h [] [] [] l (array_element_symb(), true) [elem_tp] real_unit real_unit_pat (Some 2) pats $. fun _ h _ _ _ _ _ _ ->
          cont (Chunk ((array_element_symb(), true), [elem_tp], real_unit, [arr; i; value], None)::h) env
        | Some h ->
          cont h env
        end
      | LValues.ArrayElement (l, arr, elem_tp, i) when language = CLang ->
        has_heap_effects();
        if pure then static_error l "Cannot write in a pure context." None;
        let consume_elem () =
          let target = mk_ptr_add_ l arr i elem_tp in
          consume_points_to_chunk_ rules h [] [] [] l elem_tp real_unit real_unit_pat target dummypat true $. fun _ h _ _ _ _ _ ->
          produce_points_to_chunk l h elem_tp real_unit target value $. fun h ->
          cont h env
        in
        let write_integer__array_element () =
          match int_rank_and_signedness elem_tp with
            Some (k, signedness) ->
            let integers__symb = (integers__symb (), true) in
            let size = rank_size_term k in
            let signed = mk_bool (signedness = Signed) in
            let h0 = h in
            begin match h |> extract begin function
              Chunk (g, [], coef, [arr'; size'; signed'; count'; elems'], _) as c
                when
                  predname_eq g integers__symb &&
                  definitely_equal arr' arr &&
                  definitely_equal size' size &&
                  definitely_equal signed' signed &&
                  ctxt#query (ctxt#mk_and (ctxt#mk_le int_zero_term i) (ctxt#mk_lt i count')) ->
                  Some c
            | _ -> None
            end with
            | Some (Chunk (_, _, coef, [arr'; size'; signed'; count'; vs], _), h) ->
              if not (definitely_equal coef real_unit) then assert_false h0 env l "Assignment requires full permission." None;
              let (_, _, _, _, update_symb) = List.assoc "update" purefuncmap in
              let updated = mk_app update_symb [i; apply_conversion (provertype_of_type elem_tp) ProverInductive value; vs] in
              assume (ctxt#mk_eq (mk_length updated) count') $. fun () ->
              cont (Chunk (integers__symb, [], real_unit, [arr'; size'; signed'; count'; updated], None)::h) env
            | None ->
              consume_elem()
            end
          | None -> consume_elem ()
        in
        begin match try_pointee_pred_symb0 elem_tp with
        | None -> write_integer__array_element ()
        | Some (_, _, _, arrayPredSymb, _, _, _, _, _, _, _, uninitArrayPredSymb) ->
        let arrayPredSymb1 = (arrayPredSymb, true) in
        let h0 = h in
        match h |> extract begin function
          Chunk (g, [], coef, [arr'; size'; elems'], _) as c
            when
              predname_eq g arrayPredSymb1 &&
              definitely_equal arr' arr &&
              ctxt#query (ctxt#mk_and (ctxt#mk_le int_zero_term i) (ctxt#mk_lt i size')) ->
              Some c
        | _ -> None
        end with
        | Some (Chunk (_, _, coef, [a; n; vs], _), h) ->
          if not (definitely_equal coef real_unit) then assert_false h0 env l "Assignment requires full permission." None;
          let (_, _, _, _, update_symb) = List.assoc "update" purefuncmap in
          let updated = mk_app update_symb [i; apply_conversion (provertype_of_type elem_tp) ProverInductive value; vs] in
          assume (ctxt#mk_eq (mk_length updated) n) $. fun () ->
          cont (Chunk (arrayPredSymb1, [], real_unit, [a; n; updated], None) :: h) env
        | None ->
        let uninitArrayPredSymb1 = (uninitArrayPredSymb, true) in
        match h |> extract begin function
          Chunk (g, [], coef, [arr'; size'; elems'], _) as c
            when
              predname_eq g uninitArrayPredSymb1 &&
              definitely_equal arr' arr &&
              ctxt#query (ctxt#mk_and (ctxt#mk_le int_zero_term i) (ctxt#mk_lt i size')) ->
              Some c
        | _ -> None
        end with
        | Some (Chunk (_, _, coef, [a; n; vs], _), h) ->
          if not (definitely_equal coef real_unit) then assert_false h0 env l "Assignment requires full permission." None;
          let (_, _, _, _, update_symb) = List.assoc "update" purefuncmap in
          let updated = mk_app update_symb [i; mk_some elem_tp value; vs] in
          assume (ctxt#mk_eq (mk_length updated) n) $. fun () ->
          cont (Chunk (uninitArrayPredSymb1, [], real_unit, [a; n; updated], None) :: h) env
        | None ->
          consume_elem ()
        end
      | LValues.Deref (l, target, pointeeType) ->
        has_heap_effects();
        if pure then static_error l "Cannot write in a pure context." None;
        consume_c_object_core_core l real_unit_pat target pointeeType h true true $. fun _ h _ ->
        produce_c_object l real_unit target pointeeType eval_h (Term value) false true h env $. fun h env ->
        cont h env
    in
    let rec execute_assign_op_expr h env lhs get_values cont =
      lhs_to_lvalue h env lhs $. fun h env lvalue ->
      read_lvalue h env lvalue $. fun h env v1 ->
      get_values h env v1 $. fun h env result_value new_value ->
      write_lvalue h env lvalue new_value $. fun h env ->
      cont h env result_value
    in
    let type_of_expr = function
      TypeExpr te -> check_pure_type (pn,ilist) tparams Real te
    | e ->
      let w, tp = check_expr (pn,ilist) tparams tenv e in
      tp
    in
    match e with
    | Upcast (w, PtrType (StructType derived), PtrType (StructType base)) when dialect = Some Cxx && is_derived_of_base derived base ->
      eval_h_core readonly h env w @@ fun h env v ->
      base_addr l (derived, v) base |> cont h env
    | Upcast (w, _, _) -> eval_h_core readonly h env w cont
    | CastExpr (lc, ManifestTypeExpr (_, tp), (WFunCall (l, "malloc", [], [SizeofExpr (ls, es)], Static) as e)) ->
      let t = type_of_expr es in
      expect_type lc (Some pure) (PtrType t) tp;
      verify_expr readonly h env xo e cont
    | WFunCall (l, ("malloc" as g), [], ([Operation (lmul, Mul, ([e; SizeofExpr (ls, es)] | [SizeofExpr (ls, es); e]))] as args), Static) |
      WFunCall (l as lmul, ("calloc" as g), [], ([e; SizeofExpr (ls, es)] as args), Static) when (match args with [IntLit (_, n, _, _, _); _] when eq_big_int n unit_big_int -> false | _ -> true) ->
      if pure then static_error l "Cannot call a non-pure function from a pure context." None;
      let elemTp = type_of_expr es in
      let w, tp = check_expr (pn,ilist) tparams tenv e in
      begin match tp with
        Int (_, _) -> ()
      | _ -> static_error (expr_loc e) "Expression of integer type expected" None
      end;
      eval_h h env w $. fun h env n ->
      let arraySize = ctxt#mk_mul n (sizeof ls elemTp) in
      if g <> "calloc" then check_overflow lmul int_zero_term arraySize max_uintptr_term (fun l t -> assert_term t h env l);
      let resultType = PtrType elemTp in
      let result = get_unique_var_symb_non_ghost (match xo with None -> "array" | Some x -> x) resultType in
      let cont h = cont h env result in
      branch
        begin fun () ->
          assume_eq result (null_pointer_term ()) $. fun () ->
          cont h
        end
        begin fun () ->
          assume_neq (mk_ptr_address result) int_zero_term $. fun () ->
          let n, elemTp, arrayPredSymb, mallocBlockSymb, extra_args =
            match try_pointee_pred_symb0 elemTp with
              Some (_, _, _, asym, _, mbsym, _, _, _, _, _, uasym) ->
              n, (if g = "calloc" then elemTp else option_type elemTp), (if g = "calloc" then asym else uasym), mbsym, []
            | None ->
            match int_rank_and_signedness elemTp with
              Some (r, s) ->
                n, (if g = "calloc" then intType else option_type intType), (if g = "calloc" then integers__symb () else integers___symb ()), malloc_block_integers__symb (), [rank_size_term r; if s = Signed then true_term else false_term]
            | _ ->
              arraySize, (if g = "calloc" then charType else option_type charType), (if g = "calloc" then chars_pred_symb () else chars__pred_symb ()), malloc_block_chars_pred_symb(), []
          in
          assume (mk_object_pointer_within_limits result arraySize) $. fun () ->
          let values = get_unique_var_symb "values" (list_type elemTp) in
          assume (ctxt#mk_eq (mk_length values) n) $. fun () ->
          begin fun cont ->
            if g = "calloc" then
              assume (mk_all_eq elemTp values (ctxt#mk_intlit 0)) cont
            else
              cont ()
          end $. fun () ->
          let mallocBlockChunk = Chunk ((mallocBlockSymb, true), [], real_unit, result :: extra_args @ [n], None) in
          let arrayChunk = Chunk ((arrayPredSymb, true), [], real_unit, result :: extra_args @ [n; values], None) in
          cont (mallocBlockChunk::arrayChunk::h)
        end
    | WFunCall (l, ("malloc" as g), [], ([SizeofExpr (ls, es)] as args), Static) | WFunCall (l, ("calloc" as g), [], ([IntLit (_, _, _, _, _); SizeofExpr (ls, es)] as args), Static) ->
      assert (match args with [IntLit (_, n, _, _, _); _] -> eq_big_int n unit_big_int | _ -> true); (* Has to be true or the previous case would have matched. *)
      if pure then static_error l "Cannot call a non-pure function from a pure context." None;
      let t = type_of_expr es in
      let resultType = PtrType t in
      let result = get_unique_var_symb_non_ghost (match xo with None -> (match t with StructType tn -> tn | _ -> "address") | Some x -> x) resultType in
      let cont h = cont h env result in
      branch
        begin fun () ->
          assume_eq result (null_pointer_term ()) $. fun () ->
          cont h
        end
        begin fun () ->
          assume_neq (mk_ptr_address result) int_zero_term $. fun () ->
          produce_c_object l real_unit result t eval_h (if g = "calloc" then Default else Unspecified) true false h env $. fun h env ->
          match t with
            StructType sn ->
            let (_, (_, _, _, _, malloc_block_symb, _, _)) = List.assoc sn malloc_block_pred_map in
            cont (Chunk ((malloc_block_symb, true), [], real_unit, [result], None)::h)
          | _ ->
            match try_pointee_pred_symb0 t with
              Some (_, _, _, _, _, arrayMallocBlockSymb, _, _, _, _, _, _) ->
              cont (Chunk ((arrayMallocBlockSymb, true), [], real_unit, [result; ctxt#mk_intlit 1], None)::h)
            | _ ->
              cont (Chunk ((get_pred_symb "malloc_block", true), [], real_unit, [result; sizeof l t], None)::h)
        end
    | WFunPtrCall (l, e, ftn, args) ->
      has_heap_effects ();
      eval_h h env e $. fun h env fterm ->
      let (_, gh, fttparams, rt, ftxmap, xmap, pre, post, terminates, ft_predfammaps) = List.assoc ftn functypemap in
      if pure && gh = Real then static_error l "Cannot call regular function pointer in a pure context." None;
      let check_call targs h args0 cont =
        verify_call funcmap eval_h l (pn, ilist) xo None targs (TermPat fterm::List.map (fun arg -> TermPat arg) args0 @ List.map (fun e -> SrcPat (LitPat e)) args) (fttparams, rt, (("this", PtrType Void)::ftxmap @ xmap), [], pre, post, None, terminates, false) pure true None leminfo sizemap h tparams tenv ghostenv env cont (fun _ _ _ _ -> assert false)
      in
      let consume_call_perm h cont =
        if should_terminate leminfo then begin
          let (_, _, _, _, call_perm__symb, _, _) = List.assoc "call_perm_" predfammap in
          consume_chunk rules h [] [] [] l (call_perm__symb, true) [] real_unit real_unit_pat (Some 2) [TermPat (List.assoc current_thread_name env); TermPat fterm] $. fun _ h _ _ _ _ _ _ ->
          cont h
        end else
          cont h
      in
      begin
        match gh with
          Real when ftxmap = [] && fttparams = [] ->
          let (lg, _, _, _, isfuncsymb) = List.assoc ("is_" ^ ftn) purefuncmap in
          let phi = mk_app isfuncsymb [fterm] in
          assert_term phi h env l ("Could not prove is_" ^ ftn ^ "(" ^ ctxt#pprint fterm ^ ")") None;
          consume_call_perm h $. fun h ->
          check_call [] h [] cont
        | Real ->
          let [(_, (_, _, _, _, predsymb, inputParamCount, _))] = ft_predfammaps in
          let pats = TermPat fterm::List.map (fun _ -> SrcPat DummyPat) ftxmap in
          let targs = List.map (fun _ -> InferredType (object end, ref Unconstrained)) fttparams in
          consume_chunk rules h [] [] [] l (predsymb, true) targs real_unit dummypat inputParamCount pats $. fun (Chunk (_, targs, _, _, _) as c) h coef (_::args) _ _ _ _ ->
          consume_call_perm h $. fun h ->
          check_call targs h args $. fun h env retval ->
          cont (c::h) env retval
        | Ghost ->
          let [(_, (_, _, _, _, predsymb, inputParamCount, _))] = ft_predfammaps in
          let targs = List.map (fun _ -> InferredType (object end, ref Unconstrained)) fttparams in
          let pats = TermPat fterm::List.map (fun _ -> SrcPat DummyPat) ftxmap in
          consume_chunk rules h [] [] [] l (predsymb, true) targs real_unit dummypat inputParamCount pats $. fun chunk h coef (_::args) _ _ _ _ ->
          if leminfo_is_lemma leminfo && not (definitely_equal coef real_unit) then assert_false h env l "Full lemma function pointer chunk required." None;
          let targs = List.map unfold_inferred_type targs in
          check_call targs h args $. fun h env retval ->
          cont (chunk::h) env retval
      end
    | WCxxNew (l, ty, expr_opt) ->
      if pure then static_error l "Cannot call 'new' from a pure context." None ;
      let symb_name = 
        match xo with 
        | None -> (match ty with StructType n -> n | _ -> "address")
        | Some x -> x 
      in 
      let result_type = PtrType ty in 
      let result = get_unique_var_symb_non_ghost symb_name result_type in
      let cont h = cont h env result in
      let init = 
        match expr_opt with 
        | None -> Unspecified
        | Some e -> Expr e 
      in 
      let verify_call loc args params pre post terminates h env target_struct cont = verify_call funcmap eval_h loc (pn, ilist) xo None [] args ([], None, params, ["this", result], pre, post, None, terminates, false) false false (Some target_struct) leminfo sizemap h [] tenv ghostenv env cont @@ fun _ _ _ _ _ -> assert false in
      produce_cxx_object l real_unit result ty eval_h verify_call init false false h env @@ fun h env ->
      begin
        match ty with 
        | StructType struct_name ->
          let new_block_symb = get_pred_symb_from_map struct_name new_block_pred_map in
          let args =
            if is_polymorphic_struct struct_name then
              let _, _, _, _, type_info = List.assoc struct_name structmap in
              [result; type_info]
            else
              [result]
          in
          produce_chunk h (new_block_symb, true) [] real_unit None args None cont
        | _ ->
          begin 
            match try_pointee_pred_symb0 ty with
            | Some (_, _, _, _, _, _, _, array_new_block_symb, _, _, _, _) ->
              produce_chunk h (array_new_block_symb, true) [] real_unit None [result; int_unit_term] None cont
            | _ ->
              produce_chunk h (get_pred_symb "new_block", true) [] real_unit None [result; sizeof l ty] None cont
          end
        end
    | NewObject (l, cn, args, targs) ->
      inheritance_check cn l;
      if pure then static_error l "Object creation is not allowed in a pure context" None;
      let {cctors; ctpenv} = List.assoc cn classmap in
      let args' = List.map (fun e -> check_expr (pn,ilist) tparams tenv e) args in
      let argtps = List.map snd args' in
      let argtps_erased = List.map erase_type argtps in
      let consmap' = 
        let cctors = List.map (fun (sign,info) -> (List.map erase_type sign, info)) cctors in
        List.filter (fun (sign, _) -> is_assignable_to_sign (Some pure) argtps_erased sign) cctors 
      in
      begin match consmap' with
        [] -> static_error l "No matching constructor" None
      | [(sign, CtorInfo (lm, xmap, pre, pre_tenv, post, epost, terminates, ss, v))] ->
        (* Typecheck the type arguments *)
        let targtps = match targs with 
          (* Type check passed type arguments *)
          Some(targs) -> List.map (check_pure_type (pn,ilist) tparams Real) targs
          (* Raw type, make all targs Object *)
          | None -> List.map (fun _ -> javaLangObject) ctpenv 
        in
        let obj = get_unique_var_symb (match xo with None -> "object" | Some x -> x) (ObjType (cn, targtps)) in
        assume_neq obj (ctxt#mk_intlit 0) $. fun () ->
        assume_eq (ctxt#mk_app get_class_symbol [obj]) (List.assoc cn classterms) $. fun () ->
        let is_upcall =
          match ss, leminfo with
            Some (Some (_, rank)), RealMethodInfo (Some rank') -> rank < rank'
          | _ -> true
        in
        let xmap = if targtps = [] then 
            xmap 
          else 
            let Some targEnv = zip ctpenv targtps in
            List.map (fun (name,tp) -> (name, replace_type l targEnv tp)) xmap 
        in
        check_correct h None None [] args (lm, [], None, xmap, ["this", obj], pre, post, Some(epost), terminates, false) is_upcall (Some cn) (fun h env _ -> cont h env obj)
      | _ -> static_error l "Multiple matching overloads" None
      end
    | WMethodCall (l, tn, m, pts, args, fb, tpenv) when m <> "getClass" ->
      let (lm, gh, rt, xmap, pre, post, epost, terminates, is_upcall, target_class, fb', v, mtparams) =
        match try_assoc tn classmap with
        Some {cfinal; cmeths} ->
          let MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, fb, v, is_override, abstract, mtparams) = List.assoc (m, pts) cmeths in
          let can_be_overridden = fb = Instance && cfinal = ExtensibleClass && v <> Private in 
          let is_upcall =
            not can_be_overridden &&
            match ss, leminfo with
              None, _ -> true
            | Some (Some (_, rank)), RealMethodInfo (Some rank') when rank < rank' -> true
            | _ -> false
          in
          let target_class = if can_be_overridden then None else Some tn in
          (lm, gh, rt, xmap, pre_dyn, post_dyn, epost_dyn, terminates, is_upcall, target_class, fb, v, mtparams)
        | _ ->
          let InterfaceInfo (_, _, methods, _, _, _) = List.assoc tn interfmap in
          let ItfMethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, terminates, v, abstract, mtparams) = List.assoc (m, pts) methods in
          (lm, gh, rt, xmap, pre, post, epost, terminates, false, None, Instance, v, mtparams)
      in
      let mtargs = List.map (fun tparam -> List.assoc tparam tpenv) mtparams in
      if gh = Real && pure then static_error l "Method call is not allowed in a pure context" None;
      if gh = Ghost then begin
        if not pure then static_error l "A lemma method call is not allowed in a non-pure context." None;
        if leminfo_is_lemma leminfo then static_error l "Lemma method calls in lemmas are currently not supported (for termination reasons)." None
      end;
      check_correct h xo None mtargs args (lm, mtparams, rt, xmap, [], pre, post, Some epost, terminates, true) is_upcall target_class cont
    | WSuperMethodCall(l, supercn, m, args, (lm, gh, rt, xmap, pre, post, epost, terminates, rank, v)) ->
      if gh = Real && pure then static_error l "Method call is not allowed in a pure context" None;
      if gh = Ghost then begin
        if not pure then static_error l "A lemma method call is not allowed in a non-pure context." None;
        if leminfo_is_lemma leminfo then static_error l "Lemma method calls in lemmas are currently not supported (for termination reasons)." None
      end;
      let is_upcall =
        match rank, leminfo with
          Some rank, RealMethodInfo (Some rank0) -> rank < rank0
        | _ -> true
      in
      check_correct h None None [] args (lm, [], rt, xmap, [], pre, post, Some epost, terminates, false) is_upcall (Some supercn) cont
    | WFunCall (l, g, targs, es, binding) ->
      let FuncInfo (funenv, fterm, lg, k, tparams, tr, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, is_virt, overrides) = List.assoc g funcmap in
      if heapReadonly && not assume_left_to_right_evaluation && not (startswith g "vf__") && asserts_exclusive_ownership pre then has_heap_effects ();
      if body = None then register_prototype_used lg g (Some fterm);
      if pure && k = Regular then static_error l "Cannot call regular functions in a pure context." None;
      if not pure && is_lemma k then static_error l "Cannot call lemma functions in a non-pure context." None;
      if nonghost_callers_only then begin
        match leminfo with
          RealFuncInfo (_, _, _) | LemInfo (_, _, _, true) | RealMethodInfo _ -> ()
        | _ -> static_error l "A lemma function marked nonghost_callers_only cannot be called from a non-nonghost_callers_only lemma function." None
      end;
      check_correct h xo (Some g) targs es (lg, tparams, tr, ps, funenv, pre, post, None, terminates, (binding = Instance && is_virt)) true None cont
    | NewArray(l, tp, e) ->
      let elem_tp = check_pure_type (pn,ilist) tparams Real tp in
      let w = check_expr_t (pn,ilist) tparams tenv e intType in
      eval_h h env w $. fun h env lv ->
      if not (ctxt#query (ctxt#mk_le (ctxt#mk_intlit 0) lv)) then assert_false h env l "array length might be negative" None;
      let elems = get_unique_var_symb "elems" (InductiveType ("list", [elem_tp])) in
      let (_, _, _, _, all_eq_symb) = List.assoc "all_eq" purefuncmap in
      let (_, _, _, _, length_symb) = List.assoc "length" purefuncmap in
      assume_eq (mk_app length_symb [elems]) lv $. fun () ->
        assume (mk_app all_eq_symb [elems; ctxt#mk_boxed_int (ctxt#mk_intlit 0)]) $. fun () ->
          new_array h env l elem_tp lv elems
    | NewArrayWithInitializer(l, tp, es) when language = Java ->
      let elem_tp = check_pure_type (pn,ilist) tparams Real tp in
      let ws = List.map (fun e -> check_expr_t (pn,ilist) tparams tenv e elem_tp) es in
      evhs h env ws $. fun h env vs ->
      let elems = mk_list elem_tp vs in
      let lv = ctxt#mk_intlit (List.length vs) in
      new_array h env l elem_tp lv elems
    | StringLit (l, s)->
      begin match file_type path with
        Java ->
        (* TODO: support UTF-8 *)
        let value = get_unique_var_symb "stringLiteral" (ObjType ("java.lang.String", [])) in
        let (_, _, _, _, chars_of_string_symb) = List.assoc "java.lang.charsOfString" purefuncmap in
        assume_neq value (ctxt#mk_intlit 0) $. fun () ->
        assume_eq (mk_app chars_of_string_symb [value]) (mk_char_list_of_c_string (String.length s) s) $. fun () ->
        cont h env value
      | _ ->
        if unloadable then static_error l "The use of string literals as expressions in unloadable modules is not supported. Put the string literal in a named global array variable instead." None;
        let (_, _, _, _, string_symb, _, _) = List.assoc "string" predfammap in
        let cs = get_unique_var_symb "stringLiteralChars" (InductiveType ("list", [charType])) in
        let value = get_unique_var_symb "stringLiteral" (PtrType charType) in
        let coef = get_dummy_frac_term () in
        assume (ctxt#mk_not (ctxt#mk_eq value (null_pointer_term ()))) $. fun () ->
        assume (ctxt#mk_eq (mk_char_list_of_c_string (String.length s) s) cs) $. fun () ->
        cont (Chunk ((string_symb, true), [], coef, [value; cs], None)::h) env value
      end
    | WOperation (l, Add, [e1; e2], ObjType ("java.lang.String", [])) ->
      eval_h h env e1 $. fun h env v1 ->
      eval_h h env e2 $. fun h env v2 ->
      let value = get_unique_var_symb "string" (ObjType ("java.lang.String", [])) in
      assume_neq value (ctxt#mk_intlit 0) $. fun () ->
      cont h env value
    | WRead (l, e, fparent, fname, frange, false (* is static? *), fvalue, fghost) ->
      eval_h h env e $. fun h env t ->
      begin match frange with
        StaticArrayType (elemTp, elemCount) ->
        cont h env (field_address l t fparent fname)
      | _ ->
      let (_, (_, _, _, _, f_symb, _, _)), _ = List.assoc (fparent, fname) field_pred_map in
      begin match lookup_points_to_chunk_core h f_symb t with
        None -> (* Try the heavyweight approach; this might trigger a rule (i.e. an auto-open or auto-close) and rewrite the heap. *)
        get_points_to h t f_symb l $. fun h coef v ->
        cont (Chunk ((f_symb, true), [], coef, [t; v], None)::h) env v
      | Some v -> cont h env v
      end
      end
    | WRead (l, _, fparent, fname, frange, true (* is static? *), fvalue, fghost) when ! fvalue = None || ! fvalue = Some None->
      let (_, (_, _, _, _, f_symb, _, _)), _ = List.assoc (fparent, fname) field_pred_map in
      consume_chunk rules h [] [] [] l (f_symb, true) [] real_unit dummypat (Some 0) [dummypat] (fun chunk h coef [field_value] size ghostenv _ _ ->
        cont (chunk :: h) env field_value)
    | WReadArray (l, arr, elem_tp, i) when language = Java ->
      eval_h h env arr $. fun h env arr ->
      eval_h h env i $. fun h env i ->
      begin match try_read_java_array h env l arr i elem_tp with
        None -> 
          let pats = [TermPat arr; TermPat i; SrcPat DummyPat] in
          consume_chunk rules h [] [] [] l (array_element_symb(), true) [elem_tp] real_unit (SrcPat DummyPat) (Some 2) pats $. fun _ h coef [_; _; elem] _ _ _ _ ->
          let elem_tp = unfold_inferred_type elem_tp in
          cont (Chunk ((array_element_symb(), true), [elem_tp], coef, [arr; i; elem], None)::h) env elem
      | Some (v) -> 
        if not pure then assume_bounds v elem_tp;
        cont h env v
      end
    | WReadArray (l, arr, elem_tp, i) when language = CLang ->
      eval_h h env arr $. fun h env arr ->
      eval_h h env i $. fun h env i ->
      cont h env (read_c_array h env l arr i elem_tp)
    | WDeref (l, w, pointeeType) as e ->
      lhs_to_lvalue h env e $. fun h env lvalue ->
      read_lvalue h env lvalue cont
    | WOperation (l, Not, [e], t) -> eval_h_core readonly h env e (fun h env v -> cont h env (ctxt#mk_not v))
    | WOperation (l, ((Eq | Neq) as op), [e1; e2], t) ->
      let create_term t1 t2 = match op with Eq -> ctxt#mk_eq t1 t2 | Neq -> ctxt#mk_not (ctxt#mk_eq t1 t2) in
      let e1_safe = is_safe_expr e1 in
      let e2_safe = is_safe_expr e2 in
      eval_h_core (true, heapReadonly || not e2_safe) h env e1 $. fun h env v1 ->
      eval_h_core (true, heapReadonly || not e1_safe) h env e2 $. fun h env v2 ->
      begin match t with
        PtrType tp when not pure && not assume_no_provenance && not (ctxt#query (ctxt#mk_or (ctxt#mk_eq (mk_ptr_address v1) int_zero_term) (ctxt#mk_eq (mk_ptr_address v2) int_zero_term))) ->
        branch
          begin fun () ->
            assume (ctxt#mk_eq (mk_ptr_address v1) (mk_ptr_address v2)) $. fun () ->
            cont h env (if op = Eq then true_term else false_term)
          end
          begin fun () ->
            assume (ctxt#mk_not (ctxt#mk_eq v1 v2)) $. fun () ->
            cont h env (if op = Eq then false_term else true_term)
          end
      | _ ->
        cont h env (create_term v1 v2)
      end
    | WOperation (l, And, [e1; e2], t) ->
      eval_h_core readonly h env e1 $. fun h env v1 ->
      branch
        (fun () -> assume v1 (fun () -> eval_h_core readonly h env e2 cont))
        (fun () -> assume (ctxt#mk_not v1) (fun () -> cont h env ctxt#mk_false))
    | WOperation (l, Or, [e1; e2], t) -> 
      eval_h_core readonly h env e1 $. fun h env v1 ->
      branch
        (fun () -> assume v1 (fun () -> cont h env ctxt#mk_true))
        (fun () -> assume (ctxt#mk_not v1) (fun () -> eval_h_core readonly h env e2 cont))
    | IfExpr (l, con, e1, e2) ->
      eval_h_core readonly h env con $. fun h env v ->
      branch
        (fun () -> assume v (fun () -> eval_h_core readonly h env e1 cont))
        (fun () -> assume (ctxt#mk_not v) (fun () -> eval_h_core readonly h env e2 cont))
    | WAssignOpExpr (l, lhs, x, rhs, postOp) ->
      let get_values h env vlhs cont =
        eval_h h ((x, vlhs)::env) rhs $. fun h env vrhs ->
        assert (List.mem_assoc x env);
        let env = List.remove_assoc x env in
        let r = if postOp then vlhs else vrhs in
        cont h env r vrhs
      in
      execute_assign_op_expr h env lhs get_values cont
    | AssignExpr (l, lhs, rhs) ->
      lhs_to_lvalue h env lhs $. fun h env lvalue ->
      let varName = match lhs with WVar (_, x, _) -> Some x | _ -> None in
      let rhsHeapReadOnly =
        (* 'E = ++E + 1' has undefined behavior. This is true for any lvalue E. *)
        (* We interpret the C standard as saying that 'E = f(++E)' does not have undefined behavior because argument expression evaluation is sequenced before function call. *)
        match (lhs, rhs) with
          (WVar (_, _, _), WFunCall (_, _, _, _, _)) -> false (* Is this OK when the variable is a global? *)
        | (WVar (_, _, LocalVar), _) -> false
        | (WRead (l, WVar (_, _, LocalVar), fparent, fname, tp, false, fvalue, fghost), WFunCall (_, _, _, _, _)) -> false
        | (WDeref (l, WVar (_, _, LocalVar), _), WFunCall (_, _, _, _, _)) -> false
        | _ -> true
      in
      verify_expr (true, rhsHeapReadOnly) h env varName rhs $. fun h env vrhs ->
      write_lvalue h env lvalue vrhs $. fun h env ->
      cont h env vrhs
    | AddressOf (_, WDeref (_, w, _)) ->
      eval_h_core readonly h env w cont
    | e ->
      if not pure then check_ghost_nonrec ghostenv e;
      eval_non_pure_cps (fun (h, env) e cont -> eval_h h env e (fun h env t -> cont (h, env) t)) pure (h, env) env e (fun (h, env) v -> cont h env v)
  
  end

end
