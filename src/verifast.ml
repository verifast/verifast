open Proverapi
open Big_int
open Printf
open Num (* rational numbers *)
open Util
open Stats
open Ast
open Lexer
open Parser
open Verifast0
open Verifast1
open Assertions
open Verify_expr

module VerifyProgram(VerifyProgramArgs: VERIFY_PROGRAM_ARGS) = struct
  
  include VerifyExpr(VerifyProgramArgs)
  
  module CheckFile(CheckFileArgs: CHECK_FILE_ARGS) = struct
  
  include CheckFile_VerifyExpr(CheckFileArgs)
  
  (* Region: verification of statements *)
  
  let verify_expr readonly (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e cont econt =
    verify_expr (readonly, readonly) (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e cont econt
  
  let rec assume_handle_invs bcn hpmap hname hpInvEnv h cont = 
      if hname = bcn ^ "_handle" then
        cont h
      else
      let (_, _, extended, inv, _) = List.assoc hname hpmap in
      match extended with (* tpenv h ghostenv (env: (string * termnode) list) p coef size_first size_all cont *)
        None -> produce_asn [] h [] hpInvEnv inv real_unit None None (fun h _ _ -> cont h)
      | Some(ehname) -> assume_handle_invs bcn hpmap ehname hpInvEnv h (fun h -> produce_asn [] h [] hpInvEnv inv real_unit None None (fun h _ _ -> cont h))

  let rec assert_handle_invs bcn hpmap hname hpInvEnv h cont = 
    if hname = bcn ^ "_handle" then
      cont h
    else
      let (l, _, extended, inv, _) = List.assoc hname hpmap in
      match extended with
        None -> consume_asn rules [] h [] hpInvEnv inv true real_unit (fun _ h _ _ _ -> cont h)
      | Some(ehname) -> assert_handle_invs bcn hpmap ehname hpInvEnv h (fun h ->  consume_asn rules [] h [] hpInvEnv inv true real_unit (fun _ h _ _ _ -> cont h))
  
  let rec verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont econt =
    let l = stmt_loc s in
    let _ =
      match s with
      (* Make sure that nested statements are not counted *)
      | PureStmt _ | NonpureStmt _ | IfStmt _  | SwitchStmt _ | WhileStmt _ | BlockStmt _ -> ()
      | _ -> !stats#stmtExec l;
    in
    let break_label () = if pure then "#ghostBreak" else "#break" in
    let free_locals closeBraceLoc h tenv env locals cont =
      let rec free_locals_core h locals =
        match locals with
          [] -> cont h env
        | x::locals ->
          match try_assoc x env with
            None ->
            free_locals_core h locals
          | Some addr ->
            match List.assoc x tenv with
              StaticArrayType (elemTp, elemCount) as t ->
              consume_c_object closeBraceLoc addr t h true $. fun h ->
              free_locals_core h locals
            | RefType t -> (* free locals of which the address is taken *)
              consume_c_object closeBraceLoc addr t h true $. fun h ->
              free_locals_core h locals
      in
      match locals with
        [] -> cont h env
      | _ -> with_context (Executing (h, env, closeBraceLoc, "Freeing locals.")) (fun _ -> free_locals_core h locals)
    in
    let rec check_block_declarations ss =
      let rec check_after_initial_declarations ss = 
        match ss with
          [] -> ()
        | DeclStmt(l, ds) :: rest -> 
          ds |> List.iter begin fun (_, _, _, _, addresstaken) ->
              if !addresstaken then
                static_error l "A local variable whose address is taken must be declared at the start of a block." None
            end;
          check_after_initial_declarations rest
        | _ :: rest -> check_after_initial_declarations rest
      in
      match ss with
        [] -> ()
      | PureStmt _ :: rest -> check_block_declarations rest
      | DeclStmt _ :: rest -> check_block_declarations rest
      | _ :: rest -> check_after_initial_declarations rest
    in
    if !verbosity >= 1 then printff "%10.6fs: %s: Executing statement\n" (Perf.time ()) (string_of_loc l);
    check_breakpoint h env l;
    let check_expr (pn,ilist) tparams tenv e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (Some pure) e in
    let check_condition (pn,ilist) tparams tenv e = check_condition_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (Some pure) e in
    let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (Some pure) e tp in
    let eval env e = if not pure then check_ghost ghostenv l e; eval_non_pure pure h env e in
    let eval_h_core sideeffectfree pure h env e cont =
      if not pure then check_ghost ghostenv l e;
      verify_expr sideeffectfree (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env None e cont econt
    in
    let eval_h h env e cont =
      eval_h_core true pure h env e cont
    in
    let eval_h_nonpure h env e cont =
      eval_h_core false pure h env e cont
    in
    let eval_h_pure h env e cont =
      eval_h_core true true h env e cont
    in
    let ev e = eval env e in
    let cont = tcont sizemap tenv ghostenv in
    let verify_expr readonly h env xo e cont =
      if not pure then check_ghost ghostenv l e;
      verify_expr readonly (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env xo e cont
    in
    let verify_produce_function_pointer_chunk_stmt stmt_ghostness l fpe ftclause_opt scope_opt =
      if not pure then static_error l "This construct is not allowed in a non-pure context." None;
      let fpe = match fpe with Some e -> e | None -> static_error l "Anonymous produce_lemma_function_pointer_chunk syntax not yet supported" None in
      let (lfn, fn) =
        match fpe with
          Var (lfn, x) -> (lfn, x)
        | _ -> static_error (expr_loc fpe) "Function name expected" None
      in
      match resolve Real (pn,ilist) l fn funcmap with
        None -> static_error l "No such function." None
      | Some (fn, FuncInfo (funenv, fterm, lf, k, f_tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body',fb,v)) ->
        if stmt_ghostness = Ghost && not (is_lemma k) then static_error l "Not a lemma function." None;
        if stmt_ghostness = Real && k <> Regular then static_error l "Regular function expected." None;
        if f_tparams <> [] then static_error l "Taking the address of a function with type parameters is not yet supported." None;
        if body' = None then register_prototype_used lf fn fterm;
        if stmt_ghostness = Ghost then begin
          if nonghost_callers_only then static_error l "Function pointer chunks cannot be produced for nonghost_callers_only lemmas." None;
          match leminfo with
            RealFuncInfo (_, _, _) | RealMethodInfo _ -> ()
          | LemInfo (lems, g0, indinfo, nonghost_callers_only) ->
            if not (List.mem fn lems) then static_error l "Function pointer chunks can only be produced for preceding lemmas." None;
            if scope_opt = None then static_error l "produce_lemma_function_pointer_chunk statement must have a body." None
        end;
        let (ftn, ft_predfammaps, fttargs, ftargs) =
          match ftclause_opt with
            None ->
            begin match functype_opt with
              None -> static_error l "Function does not implement a function type." None
            | Some (ftn, ft_predfammaps, fttargs, ftargs) ->
              if ftargs <> [] then static_error l "Function header must not specify function type arguments." None;
              (ftn, ft_predfammaps, fttargs, [])
            end
          | Some (ftn, fttargs, args, params, openBraceLoc, ss, closeBraceLoc) ->
            let (rt1, xmap1, pre1, post1, terminates1) = (rt, ps, pre, post, terminates) in
            begin match resolve Real (pn,ilist) l ftn functypemap with
              None -> static_error l "No such function type" None
            | Some (ftn, (lft, gh, fttparams, rt, ftxmap, xmap, pre, post, terminates, ft_predfammaps)) ->
              begin match stmt_ghostness with
                Real -> if gh <> Real || (ftxmap = [] && fttparams = []) then static_error l "A produce_function_pointer_chunk statement may be used only for parameterized and type-parameterized function types." None
              | Ghost -> if gh <> Ghost then static_error l "Lemma function pointer type expected." None
              end;
              begin match (rt, rt1) with
                (None, _) -> ()
              | (Some t, Some t1) -> expect_type_core l "Function return type: " (Some (stmt_ghostness = Ghost)) t1 t
              | _ -> static_error l "Return type mismatch: Function does not return a value" None
              end;
              if terminates && not terminates1 then static_error l "Target function should be declared 'terminates'." None;
              let fttargs = List.map (check_pure_type (pn,ilist) tparams) fttargs in
              let tpenv =
                match zip fttparams fttargs with
                  None -> static_error l "Incorrect number of function type type arguments." None
                | Some bs -> bs
              in
              let xmap =
                match zip xmap xmap1 with
                  None -> static_error l "Function type parameter count does not match function parameter count" None
                | Some bs ->
                  List.map
                    begin fun ((x, tp0), (x1, tp1)) ->
                      let tp = instantiate_type tpenv tp0 in
                      expect_type_core l (Printf.sprintf "The types of function parameter '%s' and function type parameter '%s' do not match: " x1 x) (Some (stmt_ghostness = Ghost)) tp tp1;
                      (x, tp, tp0, x1, tp1)
                    end
                  bs
              in
              let ftargenv =
                match zip ftxmap args with
                  None -> static_error l "Incorrect number of function pointer chunk arguments" None
                | Some bs ->
                  List.map
                    begin fun ((x, tp), e) ->
                      let w = check_expr_t (pn,ilist) tparams tenv e (instantiate_type tpenv tp) in
                      (x, ev w)
                    end
                    bs
              in
              let fparams =
                match zip params xmap with
                  None -> static_error l "Incorrect number of parameter names" None
                | Some bs ->
                  List.map
                    begin fun ((lx, x), (x0, tp, tp0, x1, tp1)) ->
                      if List.mem_assoc x tenv then static_error lx "Parameter name hides existing local variable" None;
                      let t = get_unique_var_symb x tp in
                      (x, x0, tp, t, prover_convert_term t tp tp0, x1, tp1)
                    end
                    bs
              in
              let (ss_before, callLoc, resultvar, ss_after) =
                let rec iter ss_before ss_after =
                  match ss_after with
                    [] -> static_error l "'call();' statement expected" None
                  | ExprStmt (CallExpr (lc, "call", [], [], [], Static))::ss_after -> (List.rev ss_before, lc, None, ss_after)
                  | DeclStmt (ld, [lx, tx, x, Some(CallExpr (lc, "call", [], [], [], Static)), _])::ss_after ->
                    if List.mem_assoc x tenv then static_error ld "Variable hides existing variable" None;
                    let t = check_pure_type (pn,ilist) tparams tx in
                    begin match rt1 with
                      None -> static_error ld "Function does not return a value" None
                    | Some rt1 ->
                      expect_type ld (Some true) rt1 t;
                      (List.rev ss_before, lc, Some (x, t), ss_after)
                    end
                  | s::ss_after -> iter (s::ss_before) ss_after
                in
                iter [] ss
              in
              execute_branch begin fun () ->
                let currentThreadEnv = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] in
                let h = [] in
                with_context (Executing (h, [], openBraceLoc, "Producing function type precondition")) $. fun () ->
                with_context PushSubcontext $. fun () ->
                let pre_env = [("this", fterm)] @ currentThreadEnv @ ftargenv @ List.map (fun (x, x0, tp, t, t0, x1, tp1) -> (x0, t0)) fparams in
                produce_asn tpenv h [] pre_env pre real_unit None None $. fun h _ ft_env ->
                with_context PopSubcontext $. fun () ->
                let tenv = List.map (fun (x, x0, tp, t, t0, x1, tp1) -> (x, tp)) fparams @ tenv in
                let ghostenv = List.map (fun (x, x0, tp, t, t0, x1, tp1) -> x) fparams @ ghostenv in
                let env = List.map (fun (x, x0, tp, t, t0, x1, tp1) -> (x, t)) fparams @ env in
                let lblenv = [] in
                let pure = true in
                let return_cont h tenv env t = assert_false h [] l "You cannot return out of a produce_function_pointer_chunk statement" None in
                let econt _ h env texcep excep = assert_false h [] l "You cannot throw an exception from a produce_function_pointer_chunk statement" None in
                begin fun tcont ->
                  let (preceding_lemmas, indinfo) = match leminfo with
                      RealFuncInfo (_, _, _) | RealMethodInfo _ ->
                      let lems =
                        flatmap
                          (function (fn, FuncInfo (funenv, fterm, l, Lemma(_), tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, _, _)) -> [fn] | _ -> [])
                          funcmap
                      in
                      (lems, None)
                    | LemInfo (preceding_lemmas, _, indinfo, _) -> (preceding_lemmas, indinfo)
                  in
                  let leminfo_branch =
                    (* lemma function pointer chunk is never a nonghost_callers_only context. *)
                    LemInfo(preceding_lemmas, "<anonymous lemma>", indinfo, false)
                  in
                  verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure
                    leminfo_branch funcmap predinstmap sizemap tenv ghostenv h
                    env ss_before tcont return_cont econt
                end $. fun sizemap tenv ghostenv h env ->
                with_context (Executing (h, env, callLoc, "Verifying function call")) $. fun () ->
                with_context PushSubcontext $. fun () ->
                let pre1_env = currentThreadEnv @ List.map (fun (x, x0, tp, t, t0, x1, tp1) -> (x1, t)) fparams @ funenv in
                consume_asn rules [] h [] pre1_env pre1 true real_unit $. fun _ h _ f_env _ ->
                let (f_env, ft_env, tenv, ghostenv, env) =
                  match rt1 with
                    None -> (f_env, ft_env, tenv, ghostenv, env)
                  | Some rt1 ->
                    let result = get_unique_var_symb "result" rt1 in
                    let f_env = ("result", result)::f_env in
                    let ft_env =
                      match rt with
                        None -> ft_env
                      | Some rt -> ("result", result)::ft_env
                    in
                    let (tenv, ghostenv, env) =
                      match resultvar with
                        None -> (tenv, ghostenv, env)
                      | Some (x, t) ->
                        ((x, t)::tenv, x::ghostenv, (x, result)::env)
                    in
                    (f_env, ft_env, tenv, ghostenv, env)
                in
                produce_asn [] h [] f_env post1 real_unit None None $. fun h _ _ ->
                with_context PopSubcontext $. fun () ->
                begin fun tcont ->
                  verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss_after tcont return_cont econt
                end $. fun sizemap tenv ghostenv h env ->
                with_context (Executing (h, env, closeBraceLoc, "Consuming function type postcondition")) $. fun () ->
                with_context PushSubcontext $. fun () ->
                consume_asn rules tpenv h [] ft_env post true real_unit $. fun _ h _ _ _ ->
                with_context PopSubcontext $. fun () ->
                check_leaks h [] closeBraceLoc "produce_function_pointer_chunk body leaks heap chunks"
              end;
              (ftn, ft_predfammaps, fttargs, List.map snd ftargenv)
            end
        in
        let [(_, (_, _, _, _, symb, _, _))] = ft_predfammaps in
        let coef = match stmt_ghostness with Real -> get_dummy_frac_term () | Ghost -> real_unit in
        let h = Chunk ((symb, true), fttargs, coef, fterm::ftargs, None)::h in
        match scope_opt with
          None -> cont h env
        | Some s ->
          let consume_chunk h cont =
            with_context (Executing (h, [], l, "Consuming lemma function pointer chunk")) $. fun () ->
            let args = List.map (fun t -> TermPat t) (fterm::ftargs) in
            consume_chunk rules h ghostenv [] [] l (symb, true) fttargs real_unit dummypat (Some 1) args (fun _ h coef ts chunk_size ghostenv env env' ->
              if not (definitely_equal coef real_unit) then assert_false h env l "Full lemma function pointer chunk permission required." None;
              cont h
            )
          in
          let lblenv =
            List.map
              begin fun (lbl, cont) ->
                (lbl,
                 fun blocks_done sizemap tenv ghostenv h env ->
                 consume_chunk h (fun h -> cont blocks_done sizemap tenv ghostenv h env)
                )
              end
              lblenv
          in
          let tcont _ _ _ h env =
            consume_chunk h (fun h ->
              tcont sizemap tenv ghostenv h env
            )
          in
          let return_cont h tenv env retval =
            consume_chunk h (fun h -> return_cont h tenv env retval)
          in
          verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont econt
    in
    match s with
      NonpureStmt (l, allowed, s) ->
      if allowed then
        verify_stmt (pn,ilist) blocks_done lblenv tparams boxes false leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont econt
      else
        static_error l "Non-pure statements are not allowed here." None
    | ExprStmt (CallExpr (l, "produce_limits", [], [], [LitPat (Var (lv, x) as e)], Static)) ->
      if not pure then static_error l "This function may be called only from a pure context." None;
      if List.mem x ghostenv then static_error l "The argument for this call must be a non-ghost variable." None;
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      assume_is_of_type l (ev w) tp (fun () -> cont h env)
    | ExprStmt (CallExpr (l, "produce_instanceof", [], [], [LitPat (Var (lv, x) as e)], Static)) when language = Java ->
      if not pure then static_error l "This function may be called only from a pure context." None;
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      assume_instanceof l (ev w) tp (fun () -> cont h env)
    | ProduceLemmaFunctionPointerChunkStmt (l, e, ftclause_opt, body) ->
      verify_produce_function_pointer_chunk_stmt Ghost l e ftclause_opt body
    | ProduceFunctionPointerChunkStmt (l, ftn, fpe, targs, args, params, openBraceLoc, ss, closeBraceLoc) ->
      verify_produce_function_pointer_chunk_stmt Real l (Some fpe) (Some (ftn, targs, args, params, openBraceLoc, ss, closeBraceLoc)) None
    | DuplicateLemmaFunctionPointerChunkStmt (l, e) ->
      if not pure then static_error l "This construct is not allowed in a non-pure context." None;
      begin
        match leminfo with
          | LemInfo (lems, g0, indinfo, nonghost_callers_only) ->
              if not(nonghost_callers_only) then static_error l "This construct is not allowed in a context that is not nonghost_callers_only." None
          | RealFuncInfo (_, _, _) | RealMethodInfo _ -> ()
      end;
      let (lftn, ftn) =
        match e with
          Var (lftn, x) -> (lftn, x)
        | _ -> static_error (expr_loc e) "Function type expected" None
      in
      begin
        match resolve Real (pn,ilist) l ftn functypemap with
          None -> static_error lftn "No such function type." None
        | Some (ftn, (lft, gh, fttparams, rt, ftxmap, xmap, pre, post, terminates, ft_predfammaps)) ->
          let p_symb = 
            if gh <> Ghost then static_error lftn "Only lemma function types allowed here." None;
            let [(_, (_, _, _, _, p_tn, _, _))] = ft_predfammaps in p_tn
          in
          let targs = List.map (fun _ -> InferredType (object end, ref None)) fttparams in
          let args = List.map (fun _ -> SrcPat DummyPat) ftxmap in
          consume_chunk rules h ghostenv [] [] l (p_symb, true) targs real_unit dummypat (Some (List.length ftxmap + 1)) ((SrcPat DummyPat)::args) $. fun _ h coef ts size _ _ _ ->
          produce_chunk h (p_symb, true) targs coef (Some (List.length ftxmap + 1)) ts size $. fun h ->
          produce_chunk h (p_symb, true) targs real_unit (Some (List.length ftxmap + 1)) ts size $. fun h ->
          cont h env
      end
    | ExprStmt (CallExpr (l, "close_struct", targs, [], args, Static)) when language = CLang ->
      let e = match (targs, args) with ([], [LitPat e]) -> e | _ -> static_error l "close_struct expects no type arguments and one argument." None in
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let sn = match tp with PtrType (StructType sn) -> sn | _ -> static_error l "The argument of close_struct must be of type pointer-to-struct." None in
      eval_h h env w $. fun h env pointerTerm ->
      with_context (Executing (h, env, l, "Consuming character array")) $. fun () ->
      let (_, _, _, _, chars_symb, _, _) = List.assoc ("chars") predfammap in
      consume_chunk rules h ghostenv [] [] l (chars_symb, true) [] real_unit dummypat None [TermPat pointerTerm; TermPat (struct_size sn); SrcPat DummyPat] $. fun _ h coef _ _ _ _ _ ->
      if not (definitely_equal coef real_unit) then assert_false h env l "Closing a struct requires full permission to the character array." None;
      produce_c_object l real_unit pointerTerm (StructType sn) None false true h $. fun h ->
      cont h env
    | ExprStmt (CallExpr (l, "open_struct", targs, [], args, Static)) when language = CLang ->
      let e = match (targs, args) with ([], [LitPat e]) -> e | _ -> static_error l "open_struct expects no type arguments and one argument." None in
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let sn = match tp with PtrType (StructType sn) -> sn | _ -> static_error l "The argument of open_struct must be of type pointer-to-struct." None in
      eval_h h env w $. fun h env pointerTerm ->
      consume_c_object l pointerTerm (StructType sn) h true $. fun h ->
      let (_, _, _, _, chars_symb, _, _) = List.assoc "chars" predfammap in
      let cs = get_unique_var_symb "cs" (InductiveType ("list", [Int (Signed, 1)])) in
      let Some (_, _, _, _, length_symb) = try_assoc' Ghost (pn,ilist) "length" purefuncmap in
      let size = struct_size sn in
      assume (ctxt#mk_eq (mk_app length_symb [cs]) size) $. fun () ->
      cont (Chunk ((chars_symb, true), [], real_unit, [pointerTerm; size; cs], None)::h) env
    | ExprStmt (CallExpr (l, "free", [], [], args,Static) as e) ->
      let args = List.map (function LitPat e -> e | _ -> static_error l "No patterns allowed here" None ) args in
      begin
        match List.map (check_expr (pn,ilist) tparams tenv) args with
          [(arg, PtrType t)] when t <> Void ->
          if pure then static_error l "Cannot call a non-pure function from a pure context." None;
          let arg = ev arg in
          begin match try_pointee_pred_symb0 t with
            Some (_, _, _, arrayPredSymb, _, arrayMallocBlockPredSymb) ->
            consume_chunk rules h [] [] [] l (arrayMallocBlockPredSymb, true) [] real_unit real_unit_pat (Some 1) [TermPat arg; dummypat] $. fun _ h _ [_; n] _ _ _ _ ->
            consume_chunk rules h [] [] [] l (arrayPredSymb, true) [] real_unit real_unit_pat (Some 2) [TermPat arg; TermPat n; dummypat] $. fun _ h _ _ _ _ _ _ ->
            cont h env
          | None ->
          consume_c_object l arg t h false $. fun h ->
          begin match t with
            StructType sn ->
            let (_, (_, _, _, _, malloc_block_symb, _, _)) = List.assoc sn malloc_block_pred_map in
            consume_chunk rules h [] [] [] l (malloc_block_symb, true) [] real_unit real_unit_pat (Some 1) [TermPat arg] $. fun _ h _ _ _ _ _ _ ->
            cont h env
          | _ ->
            consume_chunk rules h [] [] [] l (get_pred_symb "malloc_block", true) [] real_unit real_unit_pat (Some 1) [TermPat arg; TermPat (sizeof l t)] $. fun _ h _ _ _ _ _ _ ->
            cont h env
          end
          end
        | _ ->
          let (w, _) = check_expr (pn,ilist) tparams tenv e in
          verify_expr false h env None w (fun h env _ -> cont h env) econt
      end
    | ExprStmt (CallExpr (l, "set_verifast_verbosity", [], [], [LitPat (IntLit (_, n, _, _, _))], Static)) when pure ->
      let oldv = !verbosity in
      set_verbosity (int_of_big_int n);
      let r = cont h env in
      set_verbosity oldv;
      r
    | ExprStmt (CallExpr (l, "init_class", [], [], args, Static)) when pure ->
      let cn =
        match args with
          [LitPat (ClassLit (l, cn))] ->
          let cn = check_classname (pn, ilist) (l, cn) in
          cn
        | [] ->
          let ClassOrInterfaceName cn = List.assoc current_class tenv in
          cn
        | _ -> static_error l "Syntax error. Syntax: 'init_class(MyClass.class);'." None
      in
      let (_, _, _, _, token_psymb, _, _) = List.assoc "java.lang.class_init_token" predfammap in
      let classterm = List.assoc cn classterms in
      consume_chunk rules h [] [] [] l (token_psymb, true) [] real_unit real_unit_pat (Some 1) [TermPat classterm] $. fun _ h _ _ _ _ _ _ ->
      let {cfds} = List.assoc cn classmap in
      let rec iter h1 fds =
        match fds with
          [] -> cont (h1 @ h) env
        | (fn, {ft;fbinding;finit;fvalue})::fds when fbinding = Static && !fvalue = Some None ->
          begin fun cont ->
            match finit with
              None -> cont h1 [] (default_value ft)
            | Some e -> eval_h h1 [] e cont
          end $. fun h1 [] v ->
          let (_, (_, _, _, _, symb, _, _)) = List.assoc (cn, fn) field_pred_map in
          produce_chunk h1 (symb, true) [] real_unit (Some 0) [v] None $. fun h1 ->
          iter h1 fds
        | _::fds ->
          iter h1 fds
      in
      iter [] cfds
    | ExprStmt (CallExpr (l, "produce_call_below_perm_", [], [], args, Static)) when pure ->
      if args <> [] then static_error l "produce_call_below_perm_ requires no arguments." None;
      if language = Java then begin
        let (_, _, _, _, call_below_perm__symb, _, _) = List.assoc "java.lang.call_below_perm_" predfammap in
        let cn =
          match try_assoc current_class tenv, leminfo with
            Some (ClassOrInterfaceName cn), RealMethodInfo _ -> cn
          | _, _ -> static_error l "This ghost statement must appear inside a class." None
        in
        let classterm = List.assoc cn classterms in
        let callPermChunk = Chunk ((call_below_perm__symb, true), [], real_unit, [classterm], None) in
        cont (callPermChunk::h) env
      end else
      let (_, _, _, _, call_below_perm__symb, _, _) = List.assoc "call_below_perm_" predfammap in
      let g =
        match leminfo with
          RealFuncInfo (gs, g, terminates) -> g
        | LemInfo (lems, g, indinfo, nonghost_callers_only) -> g
      in
      let gterm = List.assoc g funcnameterms in
      let callPermChunk = Chunk ((call_below_perm__symb, true), [], real_unit, [gterm], None) in
      cont (callPermChunk::h) env
    | ExprStmt (CallExpr (l, "open_module", [], [], args, Static)) when pure ->
      if args <> [] then static_error l "open_module requires no arguments." None;
      let (_, _, _, _, module_symb, _, _) = List.assoc "module" predfammap in
      let (_, _, _, _, module_code_symb, _, _) = List.assoc "module_code" predfammap in
      consume_chunk rules h [] [] [] l (module_symb, true) [] real_unit (SrcPat DummyPat) (Some 2) [TermPat current_module_term; TermPat ctxt#mk_true] $. fun _ h coef _ _ _ _ _ ->
      begin fun cont ->
        let rec iter h globals =
          match globals with
            [] -> cont h
          | (x, (_, tp, addr, init))::globals ->
            produce_c_object l coef addr tp (Some !init) true true h $. fun h ->
            iter h globals
        in
        iter h globalmap
      end $. fun h ->
      begin fun cont ->
        let rec iter h importmodules =
          match importmodules with
            | [] -> cont h
            | (x,importmodule_term)::importmodules when importmodule_term != current_module_term -> 
              iter (Chunk((module_symb, true), [], real_unit, [importmodule_term; ctxt#mk_true], None)::h) importmodules
        in
        iter h importmodulemap
      end $. fun h ->
      let codeChunks =
        if unloadable then [Chunk ((module_code_symb, true), [], coef, [current_module_term], None)] else []
      in
      cont (codeChunks @ h) env
    | ExprStmt (CallExpr (l, "close_module", [], [], args, Static)) when pure ->
      if args <> [] then static_error l "close_module requires no arguments." None;
      let (_, _, _, _, module_symb, _, _) = List.assoc "module" predfammap in
      let (_, _, _, _, module_code_symb, _, _) = List.assoc "module_code" predfammap in
      begin fun cont ->
        let rec iter h importmodules =
          match importmodules with
            | [] -> cont h
            | (x,importmodule_term)::importmodules ->
              consume_chunk rules h [] [] [] l (module_symb, true) [] real_unit real_unit_pat (Some 2) [TermPat importmodule_term; SrcPat DummyPat] $. fun _ h coef _ _ _ _ _ -> iter h importmodules
        in
        iter h importmodulemap
      end $. fun h ->
      begin fun cont ->
        let rec iter h globals =
          match globals with
            [] -> cont h
          | (x, (lg, tp, addr, init))::globals ->
            consume_c_object l addr tp h true $. fun h ->
            iter h globals
        in
        iter h globalmap
      end $. fun h ->
      begin fun cont ->
        if unloadable then
          consume_chunk rules h [] [] [] l (module_code_symb, true) [] real_unit real_unit_pat (Some 1) [TermPat current_module_term] $. fun _ h _ _ _ _ _ _ ->
          cont h
        else
          cont h
      end $. fun h ->
      cont (Chunk ((module_symb, true), [], real_unit, [current_module_term; ctxt#mk_false], None)::h) env
    | DeclStmt (ld, xs) ->
      let rec iter h tenv ghostenv env xs =
        match xs with
          [] -> tcont sizemap tenv ghostenv h env
        | (l, te, x, e, address_taken)::xs ->
          let t = check_pure_type (pn,ilist) tparams te in
          if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.") None;
          let ghostenv = if pure then x::ghostenv else List.filter (fun y -> y <> x) ghostenv in
          let produce_object envTp =
            if pure then static_error l "Cannot declare a variable of this type in a ghost context." None;
            let init =
              match e with
                None -> None
              | Some e -> Some (Some (check_c_initializer e t))
            in
            let addr = get_unique_var_symb_non_ghost (x ^ "_addr") (PtrType Void) in
            produce_c_object l real_unit addr t init true true h $. fun h ->
            iter h ((x, envTp)::tenv) ghostenv ((x, addr)::env) xs
          in
          match t with
            StaticArrayType (elemTp, elemCount) ->
            produce_object t
          | StructType sn ->
            produce_object (RefType t)
          | _ ->
            begin fun cont ->
              match e with
                None -> cont h env (get_unique_var_symb_non_ghost x t)
              | Some e ->
                let w = check_expr_t (pn,ilist) tparams tenv e t in
                verify_expr false h env (Some x) w (fun h env v -> cont h env v) econt
            end $. fun h env v ->
            if !address_taken then
              let addr = get_unique_var_symb_non_ghost (x ^ "_addr") (PtrType t) in
              let h = ((Chunk ((pointee_pred_symb l t, true), [], real_unit, [addr; v], None)) :: h) in
              if pure then static_error l "Taking the address of a ghost variable is not allowed." None;
              iter h ((x, RefType(t)) :: tenv) ghostenv ((x, addr)::env) xs
            else
              iter h ((x, t) :: tenv) ghostenv ((x, v)::env) xs
      in
      iter h tenv ghostenv env xs
    | ExprStmt e ->
      let (w, _) = check_expr (pn,ilist) tparams tenv e in
      verify_expr false h env None w (fun h env _ -> cont h env) econt
    | IfStmt (l, e, ss1, ss2) ->
      if not pure then begin
        begin match ss1 with [PureStmt (lp, _)] -> static_error lp "Pure statement not allowed here." None | _ -> () end;
        begin match ss2 with [PureStmt (lp, _)] -> static_error lp "Pure statement not allowed here." None | _ -> () end;
      end;
      let w = check_condition (pn,ilist) tparams tenv e in
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      (eval_h_nonpure h env w ( fun h env w ->
        branch
          (fun _ -> assume w (fun _ -> verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss1 tcont return_cont econt))
          (fun _ -> assume (ctxt#mk_not w) (fun _ -> verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss2 tcont return_cont econt))
      ))
    | SwitchStmt (l, e, cs) ->
      let sizemap = match e with 
        | Var (_, x) ->
          begin match try_assoc x env with 
            | None -> sizemap 
            | Some t -> (match try_assq t sizemap with None -> (t, (t, 0))::sizemap | Some _ -> sizemap)
          end
        | _ -> sizemap
      in
      let lblenv = (break_label (), fun blocks_done sizemap tenv ghostenv h env -> cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env))::lblenv in
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      let verify_expr ro h env opt e cont = verify_expr ro h env opt e cont econt in 
      verify_expr false h env None w $. fun h env v ->
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      begin match unfold_inferred_type tp with
        InductiveType (i, targs) ->
        let (tn, targs, Some (_, itparams, ctormap, _)) = (i, targs, try_assoc' Ghost (pn,ilist) i inductivemap) in
        let (Some tpenv) = zip itparams targs in
        let rec iter ctors cs =
          match cs with
            [] ->
            begin
            match ctors with
              [] -> success()
            | _ -> static_error l ("Missing clauses: " ^ String.concat ", " ctors) None
            end
          | SwitchStmtDefaultClause (l, _) :: cs -> static_error l "default clause not allowed in switch over inductive datatype" None
          | SwitchStmtClause (lc, e, ss)::cs ->
            let (cn, pats) =
              match e with
                CallExpr (lcall, cn, [], [], args, Static) ->
                let pats = List.map (function LitPat (Var (_, x)) -> x | _ -> static_error l "Constructor pattern arguments must be variable names" None) args in
                (cn, pats)
              | Var (_, cn) -> (cn, [])
              | _ -> static_error l "Case expression must be constructor pattern" None
            in
            let pts =
              match try_assoc' Real (pn,ilist) cn ctormap with
                None -> static_error lc ("Not a constructor of type " ^ tn) None
              | Some (_, (l, _, _, pts, _)) -> pts
            in
            let _ = if not (List.mem cn ctors) then static_error lc "Constructor already handled in earlier clause." None in
            let (ptenv, xterms, xenv) =
              let rec iter ptenv xterms xenv pats pts =
                match (pats, pts) with
                  ([], []) -> (List.rev ptenv, List.rev xterms, List.rev xenv)
                | (pat::pats, (name, tp)::pts) ->
                  if List.mem_assoc pat tenv then static_error lc ("Pattern variable '" ^ pat ^ "' hides existing local variable '" ^ pat ^ "'.") None;
                  if List.mem_assoc pat ptenv then static_error lc "Duplicate pattern variable." None;
                  let tp' = instantiate_type tpenv tp in
                  let term = get_unique_var_symb pat tp' in
                  let term' =
                    match unfold_inferred_type tp with
                      TypeParam x -> convert_provertype term (provertype_of_type tp') ProverInductive
                    | _ -> term
                  in
                  iter ((pat, tp')::ptenv) (term'::xterms) ((pat, term)::xenv) pats pts
                | ([], _) -> static_error lc "Too few arguments." None
                | _ -> static_error lc "Too many arguments." None
              in
              iter [] [] [] pats pts
            in
            let Some (_, _, _, _, ctorsym) = try_assoc' Ghost (pn,ilist) cn purefuncmap in
            let sizemap =
              match try_assq v sizemap with
                None -> sizemap
              | Some(t, k) -> List.map (fun (x, tx) -> (tx, (t, k - 1))) xenv @ sizemap
            in
            branch
              (fun _ -> assume_eq v (mk_app ctorsym xterms) (fun _ -> verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap (ptenv @ tenv) (pats @ ghostenv) h (xenv @ env) ss tcont return_cont econt))
              (fun _ -> iter (List.filter (function cn' -> cn' <> cn) ctors) cs)
        in
        iter (List.map (function (cn, _) -> cn) ctormap) cs
      | Int (Signed, 1) | Int (Signed, 2) | Int (Signed, 4) -> 
        let n = List.length (List.filter (function SwitchStmtDefaultClause (l, _) -> true | _ -> false) cs) in
        if n > 1 then static_error l "switch statement can have at most one default clause" None;
        let cs0 = cs in
        let rec fall_through h env cs =
          match cs with
            [] -> cont h env
          | c::cs ->
            let ss =
              match c with
                SwitchStmtDefaultClause (l, ss) -> ss
              | SwitchStmtClause (l, e, ss) -> ss
            in
            let tcont _ _ _ h env = fall_through h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) cs in
            verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont econt
        in
        let rec verify_cases cs =
          match cs with
            [] ->
            if n = 0 then (* implicit default *)
              execute_branch (fun () -> cont h env)
          | c::cs' ->
            begin match c with
              SwitchStmtClause (l, i, ss) ->
              let w2 = check_expr_t (pn,ilist) tparams tenv i intType in
              execute_branch $. fun () ->
              eval_h h env w2 $. fun h env t ->
              assume_eq t v $. fun () ->
              fall_through h env cs
            | SwitchStmtDefaultClause (l, ss) ->
              execute_branch $. fun () ->
              let restr =
                List.fold_left
                  begin fun state clause -> 
                    match clause with
                      SwitchStmtClause (l, i, ss) -> 
                        let w2 = check_expr_t (pn,ilist) tparams tenv i intType in
                        ctxt#mk_and state (ctxt#mk_not (ctxt#mk_eq v (ev w2))) 
                    | _ -> state
                  end
                  ctxt#mk_true cs0
              in
              assume restr $. fun () ->
              fall_through h env cs
            end;
            verify_cases cs'
        in
        verify_cases cs;
        success()
      | _ -> static_error l "Switch statement operand is not an inductive value or integer." None
      end
    | Assert(_, ExprAsn(le, e)) -> 
      let we = check_expr_t (pn,ilist) tparams tenv e boolt in
      let t = eval env we in
      assert_term t h env le ("Assertion might not hold: " ^ (ctxt#pprint t)) None;
      cont h env
    | Assert (l, p) ->
      let (wp, tenv, _) = check_asn_core (pn,ilist) tparams tenv p in
      consume_asn rules [] h ghostenv env wp false real_unit (fun _ _ ghostenv env _ ->
        tcont sizemap tenv ghostenv h env
      )
    | Leak (l, p) ->
      let (wp, tenv, _) = check_asn_core (pn,ilist) tparams tenv p in
      consume_asn rules [] h ghostenv env wp false real_unit (fun chunks h ghostenv env size ->
        let coef = get_dummy_frac_term () in
        let chunks = List.map (fun (Chunk (g, targs, _, args, size)) -> Chunk (g, targs, coef, args, size)) chunks in
        tcont sizemap tenv ghostenv (chunks @ h) env
      )
    | Open (l, target, g, targs, pats0, pats, coefpat) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let open_instance_predicate target target_cn =
        let cn =
          match pats0 with
            [] -> target_cn
          | [LitPat (ClassLit (l, x))] ->
            begin match resolve Real (pn,ilist) l x classmap with
              None -> static_error l "Index: No such class" None
            | Some (cn, _) ->
              if is_subtype_of target_cn cn then
                cn
              else
                static_error l "Target object type must be subtype of index." None
            end
          | _ -> static_error l "Index should be of the form C.class." None
        in
        let (pmap, symb, body) =
          match try_assoc cn classmap with
            Some {cpreds} ->
            begin match try_assoc g cpreds with
              None -> static_error l "No such predicate instance" None
            | Some (lp, pmap, family, symb, body_opt) ->
              match body_opt with
                None -> static_error l "Predicate does not have a body" None
              | Some body -> (pmap, symb, body)
            end
          | None -> static_error l "Target of predicate instance call must be of class type" None
        in
        let index = List.assoc cn classterms in
        let env0 = [("this", target)] in
        ([], [], (symb, true), [TermPat target; TermPat index], 2, List.map (fun (x, t) -> (x, t, t)) pmap, env0, body, Some 2)
      in
      let (targs, tpenv, g_symb, pats0, dropcount, ps, env0, p, inputParamCount) =
        match target with
          Some target ->
          let (target, targetType) = check_expr (pn,ilist) tparams tenv target in
          let target_cn =
            match targetType with
              ObjType cn -> cn
            | _ -> static_error l "Target of predicate instance call must be of class type" None
          in
          let target = ev target in
          open_instance_predicate target target_cn
        | None ->
        let open_pred_inst0 g =
          let fns = match file_type path with
            Java-> check_classnamelist (pn,ilist) (List.map (function LitPat (ClassLit (l, x))-> (l,x) | _ -> static_error l "Predicate family indices must be class names." None) pats0)
          | _ -> List.map (function LitPat (Var (l, x)) -> x | _ -> static_error l "Predicate family indices must be function names." None) pats0
          in
          begin
            let index_term fn =
              match file_type path with
                Java-> List.assoc fn classterms
              | _ -> funcnameterm_of funcmap fn
            in
            match try_assoc (g, fns) predinstmap with
              Some (predenv, _, predinst_tparams, ps, g_symb, inputParamCount, p) ->
              let (targs, tpenv) =
                let targs = if targs = [] then List.map (fun _ -> InferredType (object end, ref None)) predinst_tparams else targs in
                match zip predinst_tparams targs with
                  None -> static_error l (Printf.sprintf "Predicate expects %d type arguments." (List.length predinst_tparams)) None
                | Some bs -> (targs, bs)
              in
              let ps = List.map (fun (x, t) -> (x, t, instantiate_type tpenv t)) ps in
              let inputParamCount = match inputParamCount with None -> None | Some n -> Some (List.length fns + n) in
              Some (targs, tpenv, (g_symb, true), List.map (fun fn -> TermPat (index_term fn)) fns, List.length fns, ps, predenv, p, inputParamCount)
            | None ->
              None
          end
        in
        let open_pred_inst g = 
          match resolve Ghost (pn,ilist) l g predfammap with
            Some (g, _) -> open_pred_inst0 g
          | None ->
          match try_assoc g tenv with
            Some (PredType _) -> open_pred_inst0 g
          | _ -> None
        in
        match open_pred_inst g with
          Some result -> result
        | None ->
          begin
          match try_assoc' Ghost (pn,ilist) g predctormap with
            None ->
            begin match try_assoc "this" tenv with
              None -> static_error l "No such predicate instance." None
            | Some (ObjType target_cn) ->
              let this = List.assoc "this" env in
              open_instance_predicate this target_cn
            end
          | Some (PredCtorInfo (_, ps1, ps2, inputParamCount, body, funcsym)) ->
            if targs <> [] then static_error l "Predicate constructor expects 0 type arguments." None;
            let bs0 =
              match zip pats0 ps1 with
                None -> static_error l "Incorrect number of predicate constructor arguments." None
              | Some bs ->
                List.map (function (LitPat e, (x, t)) -> let w = check_expr_t (pn,ilist) tparams tenv e t in (x, ev w) | _ -> static_error l "Predicate constructor arguments must be expressions." None) bs
            in
            let g_symb = mk_app funcsym (List.map (fun (x, t) -> t) bs0) in
            let ps2 = List.map (fun (x, t) -> (x, t, t)) ps2 in
            ([], [], (g_symb, false), [], 0, ps2, bs0, body, inputParamCount)
          end
      in
      let (coefpat, tenv) =
        match coefpat with
          None -> (DummyPat, tenv)
        | Some coefpat -> check_pat (pn,ilist) tparams tenv RealType coefpat
      in
      let (wpats, tenv') = check_pats (pn,ilist) l tparams tenv (List.map (fun (x, t0, t) -> t) ps) pats in
      let wpats = (List.map (function (LitPat e) -> (TermPat (eval_non_pure true h env e)) | wpat -> SrcPat wpat) wpats) in
      let pats = pats0 @ wpats in
      consume_chunk rules h ghostenv env [] l g_symb targs real_unit (SrcPat coefpat) inputParamCount pats (fun _ h coef ts chunk_size ghostenv env [] ->
        let ts = drop dropcount ts in
        let env' =
          List.map
            begin fun ((p, tp0, tp), t) ->
             (p, prover_convert_term t tp tp0)
            end
            (let Some bs = zip ps ts in bs)
        in
        let env' = env0 @ env' in
        let body_size =
          begin match chunk_size with
          | Some (PredicateChunkSize k) ->
            let inductiveness: inductiveness =
              begin match try_assoc g predfammap with
              | Some (_, _, _, _, _, _, inductiveness) -> inductiveness
              | None ->
                begin match try_assoc g tenv with
                | Some (PredType (_, _, _, inductiveness)) ->  inductiveness
                | _ ->
                  begin match try_assoc' Ghost (pn,ilist) g predctormap with
                  | None ->
                    begin match resolve Ghost (pn,ilist) l g predfammap with
                    | Some (g, (_, _, _, _, _, _, inductiveness)) -> inductiveness
                    | None ->
                      (* The predicate is not in one of the maps supporting
                       * coinductive predicate. It might be an instance
                       * predicate (or another type of predicate where
                       * coinduction is not supported). *)
                      Inductiveness_Inductive
                    end
                  | Some (PredCtorInfo (_, ps1, ps2, inputParamCount, body, funcsym)) ->
                    (* predicate ctors do not support coinductive predicates yet, so they are inductive. *)
                    Inductiveness_Inductive
                  end
                end
              end
            in
            begin match inductiveness with
            | Inductiveness_Inductive -> Some (PredicateChunkSize (k - 1))
            | Inductiveness_CoInductive ->
              if pure then
                static_error l "Coinductive proof by coinduction on first consumed coinductive heap chunk is currently not supported." None
                (* Note that the size can be decreased again by opening chunks in case
                 * copredicates and predicates are nested. *)
              else
                Some (PredicateChunkSize (k + 1))
            end
          | _ -> None
          end
        in
        with_context PushSubcontext (fun () ->
          produce_asn tpenv h ghostenv env' p coef body_size body_size (fun h _ _ ->
            with_context PopSubcontext (fun () -> tcont sizemap tenv' ghostenv h env)
          )
        )
      )
    | SplitFractionStmt (l, p, targs, pats, coefopt) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let (targs, g_symb, pts, inputParamCount) =
        match try_assoc' Ghost (pn,ilist) p predfammap with
          None -> static_error l "No such predicate." None
        | Some (_, predfam_tparams, arity, pts, g_symb, inputParamCount, _) ->
          let targs = if targs = [] then List.map (fun _ -> InferredType (object end, ref None)) predfam_tparams else targs in
          let tpenv =
            match zip predfam_tparams targs with
              None -> static_error l "Incorrect number of type arguments." None
            | Some bs -> bs
          in
          if arity <> 0 then static_error l "Predicate families are not supported in split_fraction statements." None;
          (targs, (g_symb, true), instantiate_types tpenv pts, inputParamCount)
      in
      let splitcoef =
        match coefopt with
          None -> real_half
        | Some e ->
          let w = check_expr_t (pn,ilist) tparams tenv e RealType in
          let coef = ev w in
          assert_term (ctxt#mk_real_lt real_zero coef) h env l "Split coefficient must be positive." None;
          assert_term (ctxt#mk_real_lt coef real_unit) h env l "Split coefficient must be less than one." None;
          coef
      in
      let (wpats, tenv') = check_pats (pn,ilist) l tparams tenv pts pats in
      consume_chunk rules h ghostenv env [] l g_symb targs real_unit dummypat inputParamCount (srcpats wpats) (fun _ h coef ts chunk_size ghostenv env [] ->
        let coef1 = ctxt#mk_real_mul splitcoef coef in
        let coef2 = ctxt#mk_real_mul (ctxt#mk_real_sub real_unit splitcoef) coef in
        let h = Chunk (g_symb, targs, coef1, ts, None)::Chunk (g_symb, targs, coef2, ts, None)::h in
        tcont sizemap tenv' ghostenv h env
      )
    | MergeFractionsStmt (l, a) ->
      let (a, _, _) = check_asn_core (pn,ilist) tparams tenv a in
      let (g_symb, inputParamCount, targs, pats, is_field) =
        match a with
          WPredAsn (_, p, is_global, targs, pats0, pats) ->
          if not is_global then static_error l "Local predicates are not yet supported here." None;
          if pats0 <> [] then static_error l "Predicate families are not yet supported here." None;
          let g_symb =
            match try_assoc p#name predfammap with
              None -> static_error l "No such predicate." None
            | Some (_, predfam_tparams, arity, pts, g_symb, inputParamCount, _) -> g_symb
          in
          let inputParamCount =
            match p#inputParamCount with
              None -> static_error l "Not a precise predicate." None
            | Some n -> n
          in
          ((g_symb, true), inputParamCount, targs, pats, false)
        | WPointsTo (_, WRead (_, e, fparent, fname, frange, fstatic, fvalue, fghost), _, rhs) ->
          let (p, (_, _, _, _, symb, _, _)) = List.assoc (fparent, fname) field_pred_map in
          let pats, inputParamCount =
            if fstatic then
              [rhs], 0
            else
              [LitPat e; rhs], 1
          in
          ((symb, true), inputParamCount, [], pats, true)
        | _ -> static_error l "Only predicate assertions and field-points-to assertions are supported here at this time." None
      in
      let (inpats, outpats) = take_drop inputParamCount pats in
      let inargs = List.map (function (LitPat e) -> ev e | _ -> static_error l "No patterns allowed at input positions." None) inpats in
      List.iter (function DummyPat -> () | _ -> static_error l "Non-dummy patterns not supported here." None) outpats;
      (* Do not use consume_chunk here; it splits dummy fractions, which is exactly what we don't want! *)
      let rec iter totalCoef hdone htodo outargs =
        match htodo with
          [] ->
          begin match outargs with
            None -> assert_false h env l "No matching chunks" None
          | Some outargs ->
            begin fun cont ->
              match totalCoef with
                None -> cont (get_dummy_frac_term ())
              | Some coef ->
                if is_field then
                  assume (ctxt#mk_real_le coef real_unit) $. fun () ->
                  cont coef
                else
                  cont coef
            end $. fun coef ->
            cont (Chunk (g_symb, targs, coef, inargs @ outargs, None)::hdone) env
          end
        | Chunk (g_symb1, targs1, coef1, ts1, _) as c::htodo ->
          if predname_eq g_symb g_symb1 && List.for_all2 unify targs targs1 then
            let (inargs1, outargs1) = take_drop inputParamCount ts1 in
            if List.for_all2 definitely_equal inargs inargs1 then
              match outargs with
                None ->
                let totalCoef = if is_dummy_frac_term coef1 then None else Some coef1 in
                iter totalCoef hdone htodo (Some outargs1)
              | Some outargs as outargs0 ->
                begin fun cont ->
                  let rec iter outargs outargs1 =
                    match outargs, outargs1 with
                      [], [] -> cont ()
                    | outarg::outargs, outarg1::outargs1 ->
                      assume (ctxt#mk_eq outarg outarg1) (fun () -> iter outargs outargs1)
                  in
                  iter outargs outargs1
                end $. fun () ->
                let totalCoef =
                  match totalCoef with
                    None -> None
                  | Some totalCoef ->
                    if is_dummy_frac_term coef1 then None else Some (ctxt#mk_real_add totalCoef coef1)
                in
                iter totalCoef hdone htodo outargs0
            else
              iter totalCoef (c::hdone) htodo outargs
          else
            iter totalCoef (c::hdone) htodo outargs
      in
      iter None [] h None
    | DisposeBoxStmt (l, bcn, pats, handleClauses) ->
      let (_, boxpmap, inv, boxvarmap, amap, hpmap) =
        match try_assoc' Ghost (pn,ilist) bcn boxmap with
          None -> static_error l "No such box class." None
        | Some boxinfo -> boxinfo
      in
      let Some (_, _, _, pts, g_symb, _, _) = try_assoc' Ghost (pn,ilist) bcn predfammap in
      let (pats, tenv) = check_pats (pn,ilist) l tparams tenv pts pats in
      consume_chunk rules h ghostenv env [] l (g_symb, true) [] real_unit dummypat None (srcpats pats) $. fun boxChunk h coef ts _ ghostenv env [] ->
      (*if not (definitely_equal coef real_unit) then static_error l "Disposing a box requires full permission." None;*)
      let boxId::argts = ts in
      let Some boxArgMap = zip boxpmap argts in
      let boxArgMap = List.map (fun ((x, _), t) -> (x, t)) boxArgMap in
      let boxArgMapWithThis = ("this", boxId) :: boxArgMap in
      with_context PushSubcontext $. fun () ->
      produce_asn [] h ghostenv boxArgMapWithThis inv real_unit None None $. fun h _ boxVarMap ->
          let rec dispose_handles tenv ghostenv h env handleClauses cont =
            match handleClauses with
              [] -> cont tenv ghostenv h env
            | (l, hpn, pats)::handleClauses ->
              begin
                match try_assoc hpn hpmap with
                  None -> static_error l "No such handle predicate." None
                | Some (lhp, hpParamMap, hpExtended, hpInv, pbcs) ->
                  let hpParamTypes = List.map (fun (x, t) -> t) hpParamMap in
                  let (wpats, tenv) = check_pats (pn,ilist) l tparams tenv (HandleIdType::hpParamTypes) pats in
                  let wpats = srcpats wpats in
                  let Some (_, _, _, _, hpn_symb, _, _) = try_assoc' Ghost (pn,ilist) hpn predfammap in
                  let handlePat::argPats = wpats in
                  let pats = handlePat::TermPat boxId::argPats in
                  consume_chunk rules h ghostenv env [] l (hpn_symb, true) [] real_unit dummypat None pats $. fun _ h coef ts _ ghostenv env [] ->
                    if not (definitely_equal coef real_unit) then static_error l "Disposing a handle predicate requires full permission." None;
                    let env = List.filter (fun (x, t) -> x <> "#boxId") env in
                    let handleId::_::hpArgs = ts in
                    let Some hpArgMap = zip (List.map (fun (x, t) -> x) hpParamMap) hpArgs in
                    let hpInvEnv = [("predicateHandle", handleId)] @ hpArgMap @ boxVarMap in
                    assume_handle_invs bcn hpmap hpn hpInvEnv h $. fun h ->
                      dispose_handles tenv ghostenv h env handleClauses cont
              end
          in
          dispose_handles tenv ghostenv h env handleClauses $. fun tenv ghostenv h env ->
            produce_chunk h (g_symb, true) [] coef (Some 1) ts None $. fun h ->
            consume_chunk rules h ghostenv env [] l (g_symb, true) [] real_unit (TermPat real_unit) None (srcpats pats) $. fun _ h _ _ _ _ _ _ ->
            with_context PopSubcontext $. fun () ->
              tcont sizemap tenv ghostenv h env
    | Close (l, target, g, targs, pats0, pats, coef) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      let close_instance_predicate target target_cn =
        let cn =
          match pats0 with
            [] -> target_cn
          | [LitPat (ClassLit (l, x))] ->
            begin match resolve Real (pn,ilist) l x classmap with
              None -> static_error l "Index: No such class" None
            | Some (cn, _) ->
              if is_subtype_of target_cn cn then
                cn
              else
                static_error l "Target object type must be subtype of index." None
            end
          | _ -> static_error l "Index should be of the form C.class." None
        in
        let (lpred, pmap, symb, body) =
          match try_assoc cn classmap with
            Some {cpreds} ->
            begin match try_assoc g cpreds with
              None -> static_error l "No such predicate instance" None
            | Some (lp, pmap, family, symb, body_opt) ->
              match body_opt with
                None -> static_error l "Predicate does not have a body" None
              | Some body -> (lp, pmap, symb, body)
            end
          | None -> static_error l "Target of predicate instance call must be of class type" None
        in
        let index = List.assoc cn classterms in
        (lpred, [], [], pmap, [("this", target)], (symb, true), body, [target; index], Some 1)
      in
      let (lpred, targs, tpenv, ps, bs0, g_symb, p, ts0, inputParamCount) =
        match target with
          Some target ->
          let (target, targetType) = check_expr (pn,ilist) tparams tenv target in
          let target_cn =
            match targetType with
              ObjType cn -> cn
            | _ -> static_error l "Target of predicate instance call must be of class type" None
          in
          let target = ev target in
          close_instance_predicate target target_cn
        | None ->
        let close_pred_inst0 g =
          let fns = match file_type path with
            Java-> check_classnamelist (pn,ilist) (List.map (function LitPat (ClassLit (l, x)) -> (l, x) | _ -> static_error l "Predicate family indices must be class names." None) pats0)
          | _ -> List.map (function LitPat (Var (l, x)) -> x | _ -> static_error l "Predicate family indices must be function names." None) pats0
          in
          begin
          match try_assoc (g, fns) predinstmap with
            Some (predenv, lpred, predinst_tparams, ps, g_symb, inputParamCount, body) ->
            let targs = if targs = [] then List.map (fun _ -> InferredType (object end, ref None)) predinst_tparams else targs in
            let tpenv =
              match zip predinst_tparams targs with
                None -> static_error l "Incorrect number of type arguments." None
              | Some bs -> bs
            in
            let ts0 = match file_type path with
              Java -> List.map (fun cn -> List.assoc cn classterms) fns
            | _ -> List.map (fun fn -> funcnameterm_of funcmap fn) fns
            in
            Some (lpred, targs, tpenv, ps, predenv, (g_symb, true), body, ts0, inputParamCount)
          | None -> None
          end
        in
        let close_pred_inst g =
          match resolve Ghost (pn,ilist) l g predfammap with
            Some (g, _) -> close_pred_inst0 g
          | None ->
          match try_assoc g tenv with
            Some (PredType _) -> close_pred_inst0 g
          | _ -> None
        in
        match close_pred_inst g with
          Some result -> result
        | None ->
          begin
            match try_assoc' Ghost (pn,ilist) g predctormap with
              None ->
              begin match try_assoc "this" tenv with
                Some (ObjType cn) ->
                let this = List.assoc "this" env in
                close_instance_predicate this cn
              | _ -> static_error l "No such predicate instance." None
              end
            | Some (PredCtorInfo (lpred, ps1, ps2, inputParamCount, body, funcsym)) ->
              let bs0 =
                match zip pats0 ps1 with
                  None -> static_error l "Incorrect number of predicate constructor arguments." None
                | Some bs ->
                  List.map (function (LitPat e, (x, t)) -> let w = check_expr_t (pn,ilist) tparams tenv e t in (x, ev w) | _ -> static_error l "Predicate constructor arguments must be expressions." None) bs
              in
              let g_symb = mk_app funcsym (List.map (fun (x, t) -> t) bs0) in
              if targs <> [] then static_error l "Incorrect number of type arguments." None;
              (lpred, [], [], ps2, bs0, (g_symb, false), body, [], inputParamCount)
          end
      in
      let ps =
        match zip pats ps with
          None -> static_error l ("Wrong number of arguments: expected " ^ (string_of_int (List.length ps)) ^ " but found " ^ (string_of_int (List.length pats))) None
        | Some bs ->
          List.map
            begin fun (pat, (p, tp0)) ->
              let tp = instantiate_type tpenv tp0 in
              let t =
                match pat with
                  LitPat e -> Some (ev (check_expr_t (pn,ilist) tparams tenv e tp))
                | _ -> None
              in
              (p, pat, tp0, tp, t)
            end
            bs
      in
      let coef =
        match coef with
          None -> real_unit
        | Some (LitPat coef) -> let coef = check_expr_t (pn,ilist) tparams tenv coef RealType in ev coef
        | _ -> static_error l "Coefficient in close statement must be expression." None
      in
      let env' = flatmap (function (p, pat, tp0, tp, Some t) -> [(p, prover_convert_term t tp tp0)] | _ -> []) ps in
      let env' = bs0 @ env' in
      with_context PushSubcontext (fun () ->
        consume_asn rules tpenv h ghostenv env' p true coef (fun _ h p_ghostenv p_env size_first ->
          with_context (Executing (h, p_env, lpred, "Inferring chunk arguments")) $. fun () ->
          let ts =
            List.map
              begin fun (p, pat, tp0, tp, t) ->
                match t with
                  Some t -> ([], t)
                | None ->
                  let t =
                    match try_assoc p p_env with
                      None -> assert_false h p_env l (Printf.sprintf "Predicate body does not bind parameter '%s'; it must be supplied in the close statement." p) None
                    | Some t -> prover_convert_term t tp0 tp
                  in
                  let env =
                    match pat with
                      VarPat (_, x) -> [x, tp, t]
                    | _ -> []
                  in
                  (env, t)
              end
              ps
          in
          with_context PopSubcontext $. fun () ->
          with_context (Executing (h, env, l, "Producing predicate chunk")) $. fun () ->
          let env = List.fold_left (fun env0 (env, t) -> merge_tenvs l (List.map (fun (x, tp, t) -> (x, t)) env) env0) env ts in
          let tenv = List.fold_left (fun tenv0 (env, t) -> merge_tenvs l (List.map (fun (x, tp, t) -> (x, tp)) env) tenv0) tenv ts in
          let ghostenv = List.fold_left (fun ghostenv (env, t) -> List.map (fun (x, tp, t) -> x) env @ ghostenv) ghostenv ts in
          let ts = List.map (fun (env, t) -> t) ts in
          produce_chunk h g_symb targs coef inputParamCount (ts0 @ ts) None $. fun h ->
          tcont sizemap tenv ghostenv h env
        )
      )
    | CreateBoxStmt (l, x, bcn, args, lower_bounds, upper_bounds, handleClauses) ->
      if not pure then static_error l "Box creation statements are allowed only in a pure context." None;
      let (_, boxpmap, inv, boxvarmap, amap, hpmap) =
        match try_assoc' Ghost (pn,ilist) bcn boxmap with
          None -> static_error l "No such box class." None
        | Some boxinfo -> boxinfo
      in
      let (tenv, ghostenv, env) =
        let rec iter tenv ghostenv env handleClauses =
          match handleClauses with
            [] -> (tenv, ghostenv, env)
          | (l, x, fresh, hpn, args)::handleClauses ->
            if List.mem_assoc x tenv then static_error l "Declaration hides existing variable." None;
            iter ((x, HandleIdType)::tenv) (x::ghostenv) ((x, get_unique_var_symb x HandleIdType)::env) handleClauses
        in
        iter tenv ghostenv env handleClauses
      in
      if List.mem_assoc x tenv then static_error l "Declaration hides existing variable." None;
      let boxArgMap =
        match zip args boxpmap with
          None -> static_error l "Incorrect number of arguments." None
        | Some bs ->
          List.map
            begin
              fun (e, (pn, pt)) ->
                let w = check_expr_t (pn,ilist) tparams tenv e pt in
                (pn, eval env w)
            end
            bs
      in
      let boxArgs = List.map (fun (x, t) -> t) boxArgMap in
      let boxIdTerm = get_unique_var_symb x BoxIdType in
      let boxLevelTerm = (mk_app (get_pure_func_symb "box_level") [boxIdTerm]) in
      let boxArgMapWithThis = ("this", boxIdTerm) :: boxArgMap in
      let rec action_permission_chunks amap =
        match amap with
          [] -> []
        | (_, (_, None, _, _, _)) :: rest -> action_permission_chunks rest
        | (_, (_, (Some (action_permission_symb, action_permission_dispenser_symb)), _, _, _)) :: rest ->
          let (pred_symb, parameters) =
            match action_permission_dispenser_symb with
              None -> (action_permission_symb, [boxIdTerm])
            | Some action_permission_dispenser_symb -> (action_permission_dispenser_symb, [boxIdTerm; mk_nil ()])
          in 
          Chunk((pred_symb, true), [], real_unit, parameters, None) :: (action_permission_chunks rest)
      in
      let lower_bound_terms = List.map (fun e -> eval env (check_expr_t  (pn,ilist) tparams tenv e RealType)) lower_bounds in
      let upper_bounds_terms = List.map (fun e -> eval env (check_expr_t  (pn,ilist) tparams tenv e RealType)) upper_bounds in
      List.iter (fun lower_bound -> List.iter (fun upper_bound ->
        if not (ctxt#query (ctxt#mk_lt lower_bound upper_bound)) then 
          static_error l "All lower bounds must be less than all upper bounds" None;
        ) upper_bounds_terms;
      ) lower_bound_terms;
      let rec assume_bounds lower upper cont =
        match lower with
         [] -> begin 
               match upper with 
                 [] -> cont ()
               | first :: rest -> assume (ctxt#mk_lt boxLevelTerm first) (fun () -> assume_bounds [] rest cont)
               end
          | first :: rest -> assume (ctxt#mk_lt first boxLevelTerm) (fun () -> assume_bounds rest upper cont)
      in
      assume_bounds lower_bound_terms upper_bounds_terms $. fun () ->
      let h = (action_permission_chunks amap) @ h in
      with_context PushSubcontext $. fun () ->
      consume_asn rules [] h ghostenv boxArgMapWithThis inv true real_unit $. fun _ h _ boxVarMap _ ->
      begin fun cont ->
        let rec iter handleChunks handleClauses h =
          match handleClauses with
            (l, x, is_fresh, hpn, args)::handleClauses ->
            begin
            match try_assoc hpn hpmap with
              None -> static_error l "No such handle predicate" None
            | Some (lhp, hpParamMap, hpExtended, hpInv, pbcs) ->
              let hpArgMap =
                match zip hpParamMap args with
                  None -> static_error l "Incorrect number of arguments." None
                | Some bs ->
                  List.map
                    begin fun ((x, t), e) ->
                      let w = check_expr_t (pn,ilist) tparams tenv e t in
                      (x, eval env w)
                    end
                    bs
              in
              let handleIdTerm = (List.assoc x env) in
              let hpInvEnv = [("predicateHandle", handleIdTerm)] @ hpArgMap @ boxVarMap in
              with_context (Executing (h, hpInvEnv, asn_loc hpInv, "Checking handle predicate invariant")) $. fun () ->
              assert_handle_invs bcn hpmap hpn hpInvEnv h $. fun h ->
              let (_, _, _, _, hpn_symb, _, _) = match try_assoc' Ghost (pn,ilist) hpn predfammap with 
                None-> static_error l ("No such predicate family: "^hpn) None
              | Some x -> x
              in
              let is_handle_chunks = if not is_fresh then [] else [Chunk ((get_pred_symb "is_handle", true), [], real_unit, [handleIdTerm], None)] in
              iter (Chunk ((hpn_symb, true), [], real_unit, handleIdTerm::boxIdTerm::List.map (fun (x, t) -> t) hpArgMap, None)::(is_handle_chunks @ handleChunks)) handleClauses h
            end
          | [] -> cont (handleChunks, h)
        in
        iter [] handleClauses h
      end $. fun (handleChunks, h) ->
      let (_, _, _, _, bcn_symb, _, _) = match try_assoc' Ghost (pn,ilist) bcn predfammap with
        None -> static_error l ("No such predicate family: "^bcn) None
      | Some x-> x
      in
      with_context PopSubcontext $. fun () ->
      tcont sizemap ((x, BoxIdType)::tenv) (x::ghostenv) (Chunk ((bcn_symb, true), [], real_unit, boxIdTerm::boxArgs, None)::(handleChunks@h)) ((x, boxIdTerm)::env)
    | CreateHandleStmt (l, x, is_fresh, hpn, arg) ->
      if not pure then static_error l "Handle creation statements are allowed only in a pure context." None;
      if List.mem_assoc x tenv then static_error l "Declaration hides existing variable." None;
      begin match chop_suffix hpn "_handle" with
          None -> static_error l "Handle creation statement must mention predicate name that ends in '_handle'." None
        | Some bcn -> match try_assoc' Ghost (pn,ilist) bcn boxmap with
            None-> static_error l "No such box class." None
          | Some bcn -> ()
      end;
      let w = check_expr_t (pn,ilist) tparams tenv arg BoxIdType in
      let boxIdTerm = ev w in
      let handleTerm = get_unique_var_symb x HandleIdType in
      let (_, _, _, _, hpn_symb, _, _) = match try_assoc' Ghost (pn,ilist) hpn predfammap with
        None -> static_error l ("No such predicate family: "^hpn) None
      | Some x-> x
      in
      let is_handle_chunks = if not is_fresh then [] else [Chunk ((get_pred_symb "is_handle", true), [], real_unit, [handleTerm], None)] in
      tcont sizemap ((x, HandleIdType)::tenv) (x::ghostenv) (Chunk ((hpn_symb, true), [], real_unit, [handleTerm; boxIdTerm], None)::is_handle_chunks@h) ((x, handleTerm)::env)
    | ReturnStmt (l, eo) ->
      verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env true l eo [] return_cont econt
    | WhileStmt (l, e, None, dec, ss) ->
      static_error l "Loop invariant required." None
    | WhileStmt (l, e, Some (LoopInv p), dec, ss) ->
      if not pure then begin
        match ss with PureStmt (lp, _)::_ -> static_error lp "Pure statement not allowed here." None | _ -> ()
      end;
      if pure && dec = None then static_error l "Loops without a measure are not supported in a pure context." None;
      let endBodyLoc = match ss with BlockStmt(_, _, _, closeBraceLoc, _) :: _ -> closeBraceLoc | _-> l in
      let break h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      let lblenv = (break_label (), fun blocks_done sizemap tenv ghostenv h env -> break h env)::lblenv in
      let e = check_condition (pn,ilist) tparams tenv e in
      if not pure then check_ghost ghostenv l e;
      let xs = (expr_assigned_variables e) @ (block_assigned_variables ss) in
      let xs = List.filter (fun x -> match try_assoc x tenv with None -> false | Some (RefType _) -> false | _ -> true) xs in
      let (p, tenv') = check_asn (pn,ilist) tparams tenv p in
      let dec = (match dec with None -> None | Some(e) -> Some(check_expr_t (pn,ilist) tparams tenv' e intt)) in
      consume_asn rules [] h ghostenv env p true real_unit $. fun _ h _ _ _ ->
      let lblenv =
        List.map
          begin fun (lbl, cont) ->
            (lbl, fun blocks_done sizemap tenv ghostenv h'' env -> cont blocks_done sizemap tenv ghostenv (h'' @ h) env)
          end
          lblenv
      in
      let return_cont h'' tenv env retval = return_cont (h'' @ h) tenv env retval in
      let bs = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
      let env = bs @ env in
      produce_asn [] [] ghostenv env p real_unit None None $. fun h' ghostenv' env' ->
      begin fun cont ->
        match dec with
          None -> cont None
        | Some dec ->
          eval_h_pure h' env' dec $. fun _ _ t_dec ->
          cont (Some t_dec)
      end $. fun t_dec ->
      with_context (Executing (h', env', l, "Evaluating loop condition")) $. fun () ->
      eval_h_nonpure h' env' e $. fun h' env' v ->
      begin fun cont ->
        branch
          begin fun () ->
            assume v cont
          end
          begin fun () ->
            assume (ctxt#mk_not v) $. fun () ->
            tcont sizemap tenv' ghostenv' (h' @ h) env'
          end
      end $. fun () ->
      begin fun continue ->
        verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv' ghostenv' h' env' ss
          (fun _ _ _ h'' env -> continue h'' env)
          return_cont
          econt
      end $. fun h' env ->
      let env = List.filter (fun (x, _) -> List.mem_assoc x tenv) env in
      consume_asn rules [] h' ghostenv env p true real_unit $. fun _ h''' _ env''' _ ->
      begin fun cont ->
      match (t_dec, dec) with
        (None, None) ->
        let consume_func_call_perm g =
          let gterm = List.assoc g funcnameterms in
          let (_, _, _, _, call_perm__symb, _, _) = List.assoc "call_perm_" predfammap in
          consume_chunk rules h''' [] [] [] l (call_perm__symb, true) [] real_unit dummypat (Some 1) [TermPat gterm] $. fun _ h _ _ _ _ _ _ ->
          cont h
        in
        let consume_class_call_perm () =
          let ClassOrInterfaceName cn = List.assoc current_class tenv in
          let classterm = List.assoc cn classterms in
          consume_class_call_perm l classterm h''' cont
        in
        begin match leminfo with
          RealFuncInfo (gs, g, terminates) -> if terminates then consume_func_call_perm g else cont h'''
        | LemInfo (gs, g, indinfo, nonghost_callers_only) ->
          if language = CLang then consume_func_call_perm g else static_error l "Decreases clause required" None
        | RealMethodInfo rank -> if rank = None then cont h''' else consume_class_call_perm ()
        end
      | (Some t_dec, Some dec) ->
        eval_h_pure h' env''' dec $. fun _ _ t_dec2 ->
        let dec_check1 = ctxt#mk_lt t_dec2 t_dec in
        assert_term dec_check1 h' env''' (expr_loc dec) (sprintf "Cannot prove that loop measure decreases: %s" (ctxt#pprint dec_check1)) None;
        let dec_check2 = ctxt#mk_le (ctxt#mk_intlit 0) t_dec in
        assert_term dec_check2 h' env''' (expr_loc dec) (sprintf "Cannot prove that the loop measure remains non-negative: %s" (ctxt#pprint dec_check2)) None;
        cont h'''
      end $. fun h''' ->
      check_leaks h''' env endBodyLoc "Loop leaks heap chunks."
    | WhileStmt (l, e, Some (LoopSpec (pre, post)), dec, ss) ->
      if not pure then begin
        match ss with PureStmt (lp, _)::_ -> static_error lp "Pure statement not allowed here." None | _ -> ()
      end;
      if pure && (match dec with None -> true | _ -> false) then static_error l "Loops without a measure are not supported in a pure context." None;
      if dec = None && should_terminate leminfo then static_error l "'decreases' clause required." None;
      let endBodyLoc = match ss with BlockStmt(_, _, _, closeBraceLoc, _) :: _ -> closeBraceLoc | _-> l in
      let break h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      let lblenv = (break_label (), fun blocks_done sizemap tenv ghostenv h env -> break h env)::lblenv in
      let e = check_condition (pn,ilist) tparams tenv e in
      if not pure then check_ghost ghostenv l e;
      let (ss, locals_to_free) = (* do we really need to do this? Aren't locals freed automatically at the end of the loop if the body is a block? *)
        match ss with
          BlockStmt(_, _, ss, _, locals_to_free) :: rest -> check_block_declarations ss; (ss @ rest, locals_to_free)
        | _ -> (ss, ref [])
      in
      let xs = (expr_assigned_variables e) @ (block_assigned_variables ss) in
      let xs = List.filter (fun x -> match try_assoc x tenv with None -> false | Some (RefType _) -> false | _ -> true) xs in
      let (pre, tenv') = check_asn (pn,ilist) tparams tenv pre in
      let old_xs_tenv = List.map (fun x -> ("old_" ^ x, List.assoc x tenv)) xs in
      let tenv'' = old_xs_tenv @ tenv' in
      let (post, tenv''') = check_asn (pn,ilist) tparams tenv'' post in
      let dec = match dec with None -> None | Some e -> Some (check_expr_t (pn,ilist) tparams tenv' e intt) in
      let ghostenv' = ghostenv in
      let env' = env in
      consume_asn rules [] h ghostenv env pre true real_unit $. fun _ h ghostenv env _ ->
      let bs = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
      let old_xs_env = List.map (fun (x, t) -> ("old_" ^ x, t)) bs in
      let env' = bs @ env' in
      produce_asn [] [] ghostenv' env' pre real_unit None None $. fun h' ghostenv' env' ->
      begin fun cont ->
        match dec with
          None -> cont None
        | Some dec ->
          eval_h_pure h' env' dec $. fun _ _ t_dec ->
          cont (Some t_dec)
      end $. fun t_dec ->
      let env' = old_xs_env @ env' in
      let ghostenv' = List.map (fun (x, _) -> x) old_xs_env @ ghostenv' in
      let check_post h' env' =
        consume_asn rules [] h' ghostenv' env' post true real_unit $. fun _ h' _ _ _ ->
        check_leaks h' env' endBodyLoc "Loop leaks heap chunks"
      in
      let (ss_before, ss_after) =
        let rec iter ss_before ss =
          match ss with
            [] -> (List.rev ss_before, [])
          | PureStmt (_, ExprStmt (CallExpr (lc, "recursive_call", [], [], [], Static)))::ss_after -> (List.rev ss_before, ss_after)
          | s::ss_after -> iter (s::ss_before) ss_after
        in
        iter [] ss
      in
      let xs_ss_after = block_assigned_variables ss_after in
      let exit_loop h' env' cont =
        execute_branch (fun () -> check_post h' env');
        let env =
          flatmap
            begin fun (x, t) ->
              if List.mem x xs then
                if List.mem x xs_ss_after then
                  [(x, get_unique_var_symb_ x (List.assoc x tenv) true); ("old_" ^ x, t)]
                else
                  [(x, List.assoc x env'); ("old_" ^ x, t)]
              else
                [(x, t)]
            end
            env
        in
        let ghostenv = List.map (fun (x, _) -> x) old_xs_tenv @ ghostenv in
        produce_asn [] h ghostenv env post real_unit None None $. fun h ghostenv env ->
        cont tenv''' ghostenv h env
      in
      let lblenv = List.map (fun (lbl, cont) -> (lbl, fun blocks_done sizemap ttenv _ h' env' -> free_locals endBodyLoc h' ttenv env' !locals_to_free (fun h' _ -> exit_loop h' env' (cont blocks_done sizemap)))) lblenv in
      let return_cont h' tenv env retval = assert_false h' [] l "Returning out of a requires-ensures loop is not yet supported." None in
      with_context (Executing (h', env', l, "Evaluating loop condition")) $. fun () ->
      eval_h_nonpure h' env' e $. fun h' env' v ->
      begin fun cont ->
        branch
          begin fun () ->
            assume v cont
          end
          begin fun () ->
            assume (ctxt#mk_not v) $. fun () -> exit_loop h' env' (tcont sizemap)
          end
      end $. fun () ->
      begin fun continue ->
        verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv'' ghostenv' h' env' ss_before
          (fun _ tenv''' _ h' env' -> free_locals endBodyLoc h' tenv''' env' !locals_to_free (fun h' _ -> continue h' tenv''' env'))
          return_cont
          econt
      end $. fun h' tenv''' env' ->
      let env'' = List.filter (fun (x, _) -> List.mem_assoc x tenv) env' in
      consume_asn rules [] h' ghostenv env'' pre true real_unit $. fun _ h' ghostenv'' env'' _ ->
      execute_branch begin fun () -> match (t_dec, dec) with
        (None, None) -> success()
      | (Some t_dec, Some dec) ->
        eval_h_pure h' env'' dec $. fun _ _ t_dec2 ->
        let dec_check1 = ctxt#mk_lt t_dec2 t_dec in
        assert_term dec_check1 h' env'' (expr_loc dec) (sprintf "Cannot prove that loop measure decreases: %s" (ctxt#pprint dec_check1)) None;
        let dec_check2 = ctxt#mk_le (ctxt#mk_intlit 0) t_dec in
        assert_term dec_check2 h' env'' (expr_loc dec) (sprintf "Cannot prove that the loop measure remains non-negative: %s" (ctxt#pprint dec_check2)) None;
        success()
      end;
      let bs' = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
      let env'' =
        flatmap
          begin fun (x, t) ->
            if List.mem x xs then
              [("old_" ^ x, t); (x, List.assoc x bs')]
            else
              [(x, t)]
          end
          env''
      in
      produce_asn [] h' ghostenv'' env'' post real_unit None None $. fun h' _ _ ->
      let env' = bs' @ env' in
      List.iter (function PureStmt _ -> () | s -> static_error (stmt_loc s) "Only pure statements are allowed after the recursive call." None) ss_after;
      let ss_after_xs = block_assigned_variables ss_after in
      List.iter (fun x -> if List.mem x xs then static_error l "Statements after the recursive call are not allowed to assign to loop variables" None) ss_after_xs;
      verify_cont (pn,ilist) blocks_done [] tparams boxes pure leminfo funcmap predinstmap sizemap tenv''' ghostenv' h' env' ss_after (fun _ tenv _ h' env' ->  check_post h' env') (fun _ _ -> assert false) (fun _ _ _ -> assert false)
    | Throw (l, e) ->
      if pure then static_error l "Throw statements are not allowed in a pure context." None;
      let e' = check_expr_t (pn,ilist) tparams tenv e (ObjType "java.lang.Throwable") in
      check_ghost ghostenv l e';
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      if (is_unchecked_exception_type tp) then
        success()
      else
        verify_expr false h env None w (fun h env v -> (econt l h env tp v)) econt
    | TryCatch (l, body, catches) ->
      if pure then static_error l "Try-catch statements are not allowed in a pure context." None;
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      branch
        begin fun () ->
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont (fun throwl h env2 texcep excep -> 
            let env = List.filter (fun (x, t) -> List.mem_assoc x env) env2 in
            let rec iter catches =
              match catches with
                [] -> econt throwl h env texcep excep
              | (l, te, x, body)::catches ->
                let t = check_pure_type (pn,ilist) tparams te in
                branch
                  begin fun () ->
                    if((is_subtype_of_ texcep t) || (is_subtype_of_ t texcep)) then begin
                      if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.") None;
                      let tenv = (x, t)::tenv in
                      let env = (x, excep)::env in
                      verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont econt
                    end else
                      success()
                  end
                  begin fun () ->
                    if not (is_subtype_of_ texcep t) then
                      iter catches
                    else
                      success()
                  end
              in
              iter catches
          )
        end
        begin fun () ->
          (* Havoc the variables that are assigned by the try block. *)
          let xs = block_assigned_variables body in
          let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
          let bs = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
          let env = bs @ env in
          let h = [] in
          let rec iter catches =
            match catches with
              [] -> success()
            | (l, te, x, body)::catches ->
              branch
                begin fun () ->
                  if List.mem_assoc x tenv then static_error l ("Declaration hides existing local variable '" ^ x ^ "'.") None;
                  let t = check_pure_type (pn,ilist) tparams te in
                  if (is_unchecked_exception_type t) || t = (ObjType "java.lang.Exception") || t = (ObjType "java.lang.Throwable") then begin
                    let xterm = get_unique_var_symb_non_ghost x t in
                    let tenv = (x, t)::tenv in
                    let env = (x, xterm)::env in
                    verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont econt
                  end else
                    success()
                end
                begin fun () ->
                  iter catches
                end
          in
          iter catches
        end
    | TryFinally (l, body, lf, finally) ->
      if pure then static_error l "Try-finally statements are not allowed in a pure context." None;
      let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
      (* Tricky stuff; I hope this is correct... *)
      branch
        begin fun () ->
          let lblenv =
            List.map
              begin fun (lbl, cont) ->
                let cont blocks_done sizemap tenv ghostenv h env =
                  let tcont _ _ _ h env = cont blocks_done sizemap tenv ghostenv h env in
                  verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont econt
                in
                (lbl, cont)
              end
              lblenv
          in
          let tcont _ _ _ h env =
            verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont econt
          in
          let return_cont h tenv env retval =
            let tcont _ _ _ h _ = return_cont h tenv env retval in
            verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env finally tcont return_cont econt
          in
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont econt
        end
        begin fun () ->
          let xs = block_assigned_variables body in
          let xs = List.filter (fun x -> List.mem_assoc x tenv) xs in
          let bs = List.map (fun x -> (x, get_unique_var_symb_ x (List.assoc x tenv) (List.mem x ghostenv))) xs in
          let env = bs @ env in
          let h = [] in
          let tcont _ _ _ _ _ = success() in
          verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont econt
        end
    | PerformActionStmt (lcb, nonpure_ctxt, pre_bcn, pre_bcp_pats, consumed_handle_predicates, lpa, an, aargs, ss, closeBraceLoc, post_bcp_args_opt, produced_handle_predicates) ->
      let (_, boxpmap, inv, boxvarmap, amap, hpmap) =
        match try_assoc' Ghost (pn,ilist) pre_bcn boxmap with
          None -> static_error lcb "No such box class." None
        | Some boxinfo -> boxinfo
      in
      let inv_variables = List.filter (fun (x, t) -> not (List.mem_assoc x boxpmap)) boxvarmap in 
      let pre_bcn=
        match search' Ghost pre_bcn (pn,ilist) boxmap with
          None-> static_error lcb "You cannot perform an action on a box class that has not yet been declared." None
        | Some pre_bcn -> pre_bcn
      in
      if not (List.mem pre_bcn boxes) then static_error lcb "You cannot perform an action on a box class that has not yet been declared." None;
      let (pre_bcp_pats, tenv) = check_pats (pn,ilist) lcb tparams tenv (BoxIdType::List.map (fun (x, t) -> t) boxpmap) pre_bcp_pats in
      let pre_bcp_pats = srcpats pre_bcp_pats in
      let (_, _, _, _, boxpred_symb, _, _) = match try_assoc' Ghost (pn,ilist) pre_bcn predfammap with 
        Some x->x
      | None -> static_error lcb ("Box predicate not found: "^pre_bcn) None
      in
      consume_chunk rules h ghostenv env [] lcb (boxpred_symb, true) [] real_unit dummypat None pre_bcp_pats (fun _ h box_coef ts chunk_size ghostenv env [] ->
        let current_box_level_symb = get_pred_symb "current_box_level" in
        let box_level_symb = get_pure_func_symb "box_level" in
        let (boxId::pre_boxPredArgs) = ts in
        let box_level_term = (mk_app (get_pure_func_symb "box_level") [boxId]) in
        let is_box_coef_real_unit = definitely_equal box_coef real_unit in
        let check_deadlock_freedom h cont =
          if (! nonpure_ctxt) then (* top level call *)
            (* TODO: if toplevel and boxcoef != 1 then C code in body must be a single atomic C operation *) 
            cont ((Chunk ((current_box_level_symb, true), [], real_unit, [mk_app box_level_symb [boxId]], None)) :: h) None
          else begin
            if is_box_coef_real_unit then
              cont h None
            else
              consume_chunk rules h ghostenv env [] lcb (current_box_level_symb, true) [] real_unit dummypat None [dummypat] (fun old_current_box_level_chunk h box_coef ts chunk_size ghostenv env [] ->
                let [current_level] = ts in
                if not (ctxt#query (ctxt#mk_lt current_level box_level_term)) then static_error lcb "Level of inner atomic perform action must be higher than level of outer perform actions" None;
                cont ((Chunk ((current_box_level_symb, true), [], real_unit, [mk_app box_level_symb [boxId]], None)) :: h) (Some old_current_box_level_chunk)
             )
          end
        in
        let Some pre_boxargbs = zip boxpmap pre_boxPredArgs in
        let pre_boxArgMap = List.map (fun ((x, _), t) -> (x, t)) pre_boxargbs in
        let pre_boxArgMapWithThis = ("this", boxId) :: pre_boxArgMap in
        let inv_env = List.map (fun (x, tp) -> (x, get_unique_var_symb_ x tp true)) inv_variables in 
        check_deadlock_freedom h (fun h old_current_box_level_chunk ->
        let rec consume_handle_predicates to_be_consumed already_consumed_handles_info h tenv ghostenv env cont =
          match to_be_consumed with
            [] -> cont h tenv ghostenv env already_consumed_handles_info
          | ConsumingHandlePredicate(lch, pre_hpn, pre_hp_pats) :: rest ->
            let (pre_handlePred_parammap,  pre_handlePred_extended, pre_handlePred_inv) =
              if pre_hpn = pre_bcn ^ "_handle" then
                ([], None, EmpAsn lch)
              else
                match try_assoc' Ghost (pn,ilist) pre_hpn hpmap with
                  None -> static_error lch "No such handle predicate in box class." None
                | Some (l, hppmap, extended, inv, _) ->
                  (hppmap, extended, inv)
            in
            let (_, _, _, _, pre_handlepred_symb, _, _) = match try_assoc' Ghost (pn,ilist) pre_hpn predfammap with 
              Some x->x
            | None -> static_error lcb ("Box predicate not found: "^pre_bcn) None
            in
            let (pre_hp_pats, tenv) = check_pats (pn,ilist) lch tparams tenv (HandleIdType::List.map (fun (x, t) -> t) pre_handlePred_parammap) pre_hp_pats in
            let (pre_handleId_pat::pre_hpargs_pats) = srcpats pre_hp_pats in
            consume_chunk rules h ghostenv (("#boxId", boxId)::env) [] lch (pre_handlepred_symb, true) [] real_unit dummypat None (pre_handleId_pat::TermPat boxId::pre_hpargs_pats)
              (fun _ h coef ts chunk_size ghostenv env [] ->
                 if not (coef == real_unit) then assert_false h env lch "Handle predicate coefficient must be 1." None;
                 let (handleId::_::pre_handlePredArgs) = ts in
                 let assume_handle_inv = (fun h cont ->
                     let Some pre_hpargbs = zip pre_handlePred_parammap pre_handlePredArgs in
                    let pre_hpArgMap = List.map (fun ((x, _), t) -> (x, t)) pre_hpargbs in
                    assume_handle_invs pre_bcn hpmap pre_hpn ([("predicateHandle", handleId)] @ pre_hpArgMap @ pre_boxArgMapWithThis @ inv_env) h cont
                 )
                 in
                 consume_handle_predicates rest (already_consumed_handles_info @ [(handleId, assume_handle_inv)]) h tenv ghostenv env cont
              )
        in
        consume_handle_predicates consumed_handle_predicates [] h tenv ghostenv env (fun h tenv ghostenv env already_consumed_handles_info ->
             let (act_l, action_permission_info, apmap, pre, post) =
               match try_assoc an amap with
                 None -> static_error l "No such action in box class." None
               | Some (act_l, act_pred_symb, apmap, pre, post) -> (act_l, act_pred_symb, apmap, pre, post)
             in
             let aargbs =
               match zip apmap aargs with
                 None -> static_error lpa "Incorrect number of action arguments." None
               | Some bs ->
                 List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
             in
             let consume_action_permission h cont =
               match action_permission_info with
                 None -> cont h []
               | Some (action_permission_pred_symb, action_permission_dispenser_pred_symb) -> 
                 let (parameters, inputParamCount) = match action_permission_dispenser_pred_symb with
                   None -> ([TermPat boxId], Some 1)
                 | Some action_permission_dispenser_pred_symb -> 
                     let [(_, action_parameter)] = aargbs in 
                     ([TermPat boxId; TermPat action_parameter] , Some 2)
                 in
                 consume_chunk rules h ghostenv (("#boxId", boxId)::env) [] act_l (action_permission_pred_symb, true) [] real_unit dummypat inputParamCount parameters (fun consumed h act_perm_coef _ _ _ _ _ -> cont h [consumed])
             in
             let rec assume_all_handle_invs already_consumed_handles_info h cont =
               match already_consumed_handles_info with
                  [] -> cont h
                | (handle_id, assume_func) :: rest -> assume_func h (fun h -> assume_all_handle_invs rest h cont)
             in
               assume_all_handle_invs already_consumed_handles_info h (fun h ->
               consume_action_permission h $. fun h act_perm_chunks ->
               produce_asn [] h ghostenv  (pre_boxArgMapWithThis @ inv_env) inv real_unit None None $. fun h _ pre_boxVarMap ->
               let nonpureStmtCount = ref 0 in
               let ss =
                 List.map
                   begin function
                     NonpureStmt (l, _, s) when !nonpure_ctxt ->
                     nonpureStmtCount := !nonpureStmtCount + 1;
                     NonpureStmt (l, true, s)
                   | s -> s
                   end
                   ss
               in
               let consumed_handle_id_list = List.map (fun (id, _) -> id) already_consumed_handles_info in
               let consumed_handles_ids = List.fold_right (fun (id, _) l -> mk_cons HandleIdType id l) already_consumed_handles_info (mk_nil ()) in
               assume (mk_distinct consumed_handles_ids) (fun _ ->
               verify_cont (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env ->
                 let h = act_perm_chunks @ h in
                 with_context (Executing (h, env, closeBraceLoc, "Closing box")) $. fun () ->
                 (* with_context PushSubcontext $. fun () -> *)
                 let pre_env = [("actionHandles", consumed_handles_ids)] @ pre_boxVarMap @ aargbs in
                 assert_expr pre_env pre h pre_env closeBraceLoc "Action precondition failure." None;
                 let post_boxArgMap =
                   match post_bcp_args_opt with
                     None -> pre_boxArgMap
                   | Some (lpb, post_bcp_args) ->
                     if not (is_box_coef_real_unit) then assert_false h env lpb "Changing the parameters of the box predicate is not allowed unless consumed fraction of box predicate equals 1." None;
                     begin
                       match zip boxpmap post_bcp_args with
                         None -> static_error lpb "Incorrect number of post-state box arguments." None
                       | Some bs ->
                         List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
                     end
                 in
                 let post_boxArgMapWithThis = ("this", boxId) :: post_boxArgMap in 
                 let boxChunk = Chunk ((boxpred_symb, true), [], box_coef, boxId::List.map (fun (x, t) -> t) post_boxArgMap, None) in
                 let h = boxChunk :: h in
                 (* TODO: consume_asn on the next line cannot use spatial auto lemmas that make use of boxChunk (i.e. do a perform_action) as this is box reentry *)
                 consume_asn rules [] h ghostenv post_boxArgMapWithThis inv true real_unit $. fun _ h _ post_boxVarMap _ ->
                 let old_boxVarMap = List.map (fun (x, t) -> ("old_" ^ x, t)) pre_boxVarMap in
                 let post_env = [("actionHandles", consumed_handles_ids)] @ old_boxVarMap @ post_boxVarMap @ aargbs in
                 assert_expr post_env post h post_env closeBraceLoc "Action postcondition failure." None;
                 let reset_current_box_level h cont =
                   if (! nonpure_ctxt) then
                     consume_chunk rules h ghostenv env [] lcb (current_box_level_symb, true) [] real_unit dummypat None [TermPat(box_level_term)] (fun _ h box_coef ts chunk_size ghostenv env [] -> cont h)
                   else begin
                     match old_current_box_level_chunk with
                       None -> cont h
                     | Some chunk -> 
                       consume_chunk rules h ghostenv env [] lcb (current_box_level_symb, true) [] real_unit dummypat None [TermPat(box_level_term)] (fun _ h box_coef ts chunk_size ghostenv env [] -> cont (chunk :: h))
                   end
                 in
                 reset_current_box_level h (fun h ->
                   let produce_post_handle h used_handle_ids fresh lph post_hpn post_hp_args cont =
                     let (post_handlePred_parammap, post_handlePred_extended, post_handlePred_inv) =
                       if post_hpn = pre_bcn ^ "_handle" then
                         ([], None, EmpAsn l)
                       else
                         match try_assoc post_hpn hpmap with
                           None -> static_error lph "Post-state handle predicate: No such handle predicate in box class." None
                         | Some (_, hppmap, extended, inv, _) ->
                           (hppmap, extended, inv)
                     in
                     let (_, _, _, _, post_handlePred_symb, _, _) = match try_assoc' Ghost (pn,ilist) post_hpn predfammap with 
                       None-> static_error lph ("No such predicate family: "^post_hpn) None
                     | Some x-> x
                     in
                     let real_post_hp_args = if fresh then post_hp_args else begin (if (List.length post_hp_args) == 0 then static_error lph "Post-state handle predicate: Incorrect number of arguments." None); List.tl post_hp_args end in
                     let post_hpargs =
                       match zip post_handlePred_parammap real_post_hp_args with
                         None -> static_error lph "Post-state handle predicate: Incorrect number of arguments." None
                       | Some bs ->
                         List.map (fun ((x, t), e) -> let e = check_expr_t (pn,ilist) tparams tenv e t in (x, eval env e)) bs
                     in
                     let handleId = if fresh then get_unique_var_symb "ha" HandleIdType else eval env (check_expr_t (pn,ilist) tparams tenv (List.hd post_hp_args) HandleIdType) in
                     let _ = begin
                     (if not fresh && List.exists (fun id -> (ctxt#query (ctxt#mk_eq handleId id))) used_handle_ids then assert_false h env lph "Handle id already in use." None;);
                     (if not fresh && not (List.exists (fun id -> (ctxt#query (ctxt#mk_eq handleId id))) consumed_handle_id_list) then assert_false h env lph "Handle id must belong to handle that was consumed when entering this box." None;);
                     end
                     in
                     let post_hpinv_env = [("predicateHandle", handleId)] @ post_hpargs @ post_boxVarMap in
                     assert_handle_invs pre_bcn hpmap post_hpn post_hpinv_env h $. fun h ->
                     let hpChunk = Chunk ((post_handlePred_symb, true), [], real_unit, handleId::boxId::List.map (fun (x, t) -> t) post_hpargs, None) in
                     let h = hpChunk :: h  in
                     cont h (handleId :: used_handle_ids)
                   in
                   let tcont _ _ _ h env = tcont sizemap tenv ghostenv h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in
                   let rec produce_handle h used_handle_ids fresh phandles cont =
                     match phandles with
                       ConditionalProducingHandlePredicate(l, condition, name, args, rest) ->
                         let e = check_expr_t (pn,ilist) tparams tenv condition boolt in
                         let condition_term = eval env e in
                         branch
                           (fun _ -> assume condition_term (fun _ -> produce_post_handle h used_handle_ids fresh l name args cont))
                           (fun _ -> assume (ctxt#mk_not condition_term) (fun _ -> produce_handle h used_handle_ids fresh rest cont))
                     | BasicProducingHandlePredicate(l, name, args) -> produce_post_handle h used_handle_ids fresh l name args cont
                   in
                   let rec produce_all_post_handles used_handle_ids posts h cont =
                     match posts with
                       [] -> cont h
                     | (fresh, producing_expr) :: rest ->  produce_handle h used_handle_ids fresh producing_expr (fun h used_handle_ids -> produce_all_post_handles used_handle_ids rest h cont)
                   in
                   produce_all_post_handles [] produced_handle_predicates h (fun h -> tcont sizemap tenv ghostenv h env)
             )
           ) (fun _ _ _ _ -> static_error lcb "Returning from inside perform_action not allowed." None) (fun _ _ _ _ _ -> static_error lcb "Exception from inside perform_action not allowed." None)
          )
        ))
      ))
    | BlockStmt (l, ds, ss, closeBraceLoc, locals_to_free) ->
      let (lems, predinsts, localpreds, localpredinsts) =
        List.fold_left
          begin fun (lems, predinsts, localpreds, localpredinsts) decl ->
            match decl with
            | PredFamilyDecl (l, p, tparams, arity, tes, inputParamCount, inductiveness) ->
              if tparams <> [] then static_error l "Local predicates with type parameters are not yet supported." None;
              if arity <> 0 then static_error l "Local predicate families are not yet supported." None;
              if List.mem_assoc p predfammap then static_error l "Duplicate predicate family name." None;
              if List.mem_assoc p tenv then static_error l "Predicate name conflicts with local variable name." None;
              let ts = List.map (check_pure_type (pn,ilist) tparams) tes in
              let ptype = PredType ([], ts, inputParamCount, inductiveness) in
              let psymb = get_unique_var_symb p ptype in
              (lems, predinsts, (p, (l, ts, inputParamCount, ptype, psymb))::localpreds, localpredinsts)
            | PredFamilyInstanceDecl (l, p, predinst_tparams, is, xs, body) ->
              begin match try_assoc p localpreds with
              | Some (_, ts, inputParamCount, ptype, psymb) ->
                if predinst_tparams <> [] then static_error l "Local predicates with type parameters are not yet supported." None;
                if is <> [] then static_error l "Local predicate families are not yet supported." None;
                if List.mem_assoc p localpredinsts then static_error l "Duplicate predicate family instance." None;
                (lems, predinsts, localpreds, (p, (l, ts, inputParamCount, ptype, psymb, xs, body))::localpredinsts)
              | None ->
                let i = match is with [i] -> i | _ -> static_error l "Local predicate family declarations must declare exactly one index." None in
                if List.mem_assoc (p, i) predinsts then static_error l "Duplicate predicate family instance." None;
                (lems, ((p, i), (l, predinst_tparams, xs, body))::predinsts, localpreds, localpredinsts)
              end
            | Func (l, Lemma(auto, trigger), tparams, rt, fn, xs, nonghost_callers_only, functype_opt, contract_opt, terminates, Some body, Static, Public) ->
              if List.mem_assoc fn funcmap || List.mem_assoc fn lems then static_error l "Duplicate function name." None;
              if List.mem_assoc fn tenv then static_error l "Local lemma name hides existing local variable name." None;
              let fterm = get_unique_var_symb fn (PtrType Void) in
              ((fn, (auto, trigger, fterm, l, tparams, rt, xs, nonghost_callers_only, functype_opt, contract_opt, terminates, body))::lems, predinsts, localpreds, localpredinsts)
            | _ -> static_error l "Local declarations must be lemmas or predicate family instances." None
          end
          ([], [], [], [])
          ds
      in
      let (lems, predinsts, localpreds, localpredinsts) = (List.rev lems, List.rev predinsts, List.rev localpreds, List.rev localpredinsts) in
      let funcnameterms' =
        List.map
          (fun (fn, (autom, trigger, fterm, l, tparams, rt, xs, nonghost_callers_only, functype_opt, contract_opt, terminates, body)) -> (fn, fterm))
        lems
      in
      let env = funcnameterms' @ env in
      let ghostenv = List.map (fun (fn, _) -> fn) funcnameterms' @ ghostenv in
      let tenv = List.map (fun (fn, _) -> (fn, PtrType Void)) funcnameterms' @ tenv in
      let env = List.map (fun (p, (l, ts, inputParamCount, ptype, psymb)) -> (p, psymb)) localpreds @ env in
      let ghostenv = List.map fst localpreds @ ghostenv in
      let tenv = List.map (fun (p, (l, ts, inputParamCount, ptype, psymb)) -> (p, ptype)) localpreds @ tenv in
      let predinstmap' =
        List.map
          begin fun ((p, (li, i)), (l, predinst_tparams, xs, body)) ->
            if not (List.mem_assoc i lems) then static_error li "Index of local predicate family instance must be lemma declared in same block." None;
            check_predinst (pn, ilist) tparams tenv env l p predinst_tparams [i] xs body
          end
          predinsts
      in
      let localpredinsts =
        localpredinsts |> List.map
          begin fun (p, (l, ts, inputParamCount, ptype, psymb, xs, body)) ->
            check_predinst0 [] 0 ts psymb inputParamCount (pn, ilist) tparams tenv env l p [] [] xs body
          end
      in
      let funcmap' =
        List.map
          begin fun (fn, (auto, trigger, fterm, l, tparams', rt, xs, nonghost_callers_only, functype_opt, contract_opt, terminates, body)) ->
            let (rt, xmap, functype_opt, pre, pre_tenv, post) =
              check_func_header pn ilist tparams tenv env l (Lemma(auto, trigger)) tparams' rt fn (Some fterm) xs nonghost_callers_only functype_opt contract_opt terminates (Some body)
            in
            (fn, FuncInfo (env, fterm, l, Lemma(auto, trigger), tparams', rt, xmap, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, Some (Some body), Static, Public))
          end
          lems
      in
      let predinstmap = localpredinsts @ predinstmap' @ predinstmap in
      let funcmap = funcmap' @ funcmap in
      let verify_lems lems0 =
        List.fold_left
          begin fun lems0 (fn, FuncInfo (funenv, fterm, l, k, tparams', rt, xmap, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, Some (Some (ss, closeBraceLoc)), _, _)) ->
            let gs', lems' = verify_func pn ilist [] lems0 boxes predinstmap funcmap tparams funenv l k tparams' rt fn xmap nonghost_callers_only pre pre_tenv post terminates ss closeBraceLoc in
            lems'
          end
          lems0
          funcmap'
      in
      let leminfo =
        match leminfo with
          RealFuncInfo (_, _, _) | RealMethodInfo _ ->
          let lems0 =
            flatmap
              (function (fn, FuncInfo (funenv, fterm, l, Lemma(_), tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, _, _)) -> [fn] | _ -> [])
              funcmap
          in
          ignore $. verify_lems lems0;
          leminfo
        | LemInfo (lems, g, indinfo, nonghost_callers_only) ->
          LemInfo (verify_lems lems, g, indinfo, nonghost_callers_only)
      in
      check_block_declarations ss;
      let cont h env = cont h (List.filter (fun (x, _) -> List.mem_assoc x tenv) env) in      
      let cont h tenv env = free_locals closeBraceLoc h tenv env !locals_to_free cont in
      let return_cont h tenv env retval = free_locals closeBraceLoc h tenv env !locals_to_free (fun h env -> return_cont h tenv env retval) in
      let lblenv = List.map (fun (lbl, lblcont) -> (lbl, (fun blocksdone sizemap tenv ghostenv h env -> free_locals closeBraceLoc h tenv env !locals_to_free (fun h env -> lblcont blocksdone sizemap tenv ghostenv h env)))) lblenv in
      verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (fun sizemap tenv ghostenv h env -> cont h tenv env) return_cont econt
    | PureStmt (l, s) ->
      begin
        match s with
          PerformActionStmt (_, nonpure_ctxt, _, _, _, _, _, _, _, _, _, _) ->
          nonpure_ctxt := not pure
        | _ -> ()
      end;
      verify_stmt (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env s tcont return_cont econt
    | GotoStmt (l, lbl) ->
      if pure then static_error l "goto statements are not allowed in a pure context" None;
      begin
        match try_assoc lbl lblenv with
          None -> static_error l "No such label." None
        | Some cont -> cont blocks_done sizemap tenv ghostenv h env
      end
    | NoopStmt l -> cont h env
    | LabelStmt (l, _) -> static_error l "Label statements cannot appear in this position." None
    | InvariantStmt (l, _) -> static_error l "Invariant statements cannot appear in this position." None
    | Break l ->
      begin match try_assoc (break_label ()) lblenv with
        None -> static_error l "Unexpected break statement" None
      | Some cont -> cont blocks_done sizemap tenv ghostenv h env
      end
    | SuperConstructorCall(l, es) -> static_error l "super must be first statement of constructor." None
  and
    verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont econt =
    match ss with
      [] -> cont sizemap tenv ghostenv h env
    | s::ss ->
      with_context (Executing (h, env, stmt_loc s, "Executing statement")) (fun _ ->
        verify_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env s (fun sizemap tenv ghostenv h env ->
          verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont econt
        ) return_cont econt
      )
  and
  
  (* Region: verification of blocks *)
  
    goto_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont econt block =
    let `Block (inv, ss, cont) = block in
    let l() =
      match (inv, ss) with
        (Some (l, _, _), _) -> l
      | (_, s::_) -> stmt_loc s
      | _ -> assert false (* A block that has no invariant and no body cannot be in a loop *)
    in
    begin
      match (List.memq block blocks_done, inv) with
        (true, _) when pure -> assert_false h env (l()) "Loops are not allowed in a pure context." None
      | (true, None) -> assert_false h env (l()) "Loop invariant required." None
      | (_, Some (l, inv, tenv)) ->
        consume_asn rules [] h ghostenv env inv true real_unit (fun _ h _ _ _ ->
          check_leaks h env l "Loop leaks heap chunks."
        )
      | (false, None) ->
        let blocks_done = block::blocks_done in
        verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (cont blocks_done) return_cont econt
    end
  and verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env explicit l eo epilog return_cont econt =
    with_context (Executing (h, env, l, "Executing return statement")) $. fun () ->
    if explicit then check_breakpoint h env l;
    if pure && not (List.mem "#result" ghostenv) then static_error l "Cannot return from a regular function in a pure context." None;
    begin fun cont ->
      match eo with
        None -> cont h None
      | Some e ->
        if not pure then check_ghost ghostenv l e;
        let tp = match try_assoc "#result" tenv with None -> static_error l "Void function cannot return a value: " None | Some tp -> tp in
        let w = check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (Some pure) e tp in
        verify_expr false (pn,ilist) tparams pure leminfo funcmap sizemap tenv ghostenv h env None w (fun h env v ->
        cont h (Some v)) econt
    end $. fun h retval ->
    begin fun cont ->
      if not pure && unloadable then
        let codeCoef = List.assoc "currentCodeFraction" env in
        let (_, _, _, _, module_code_symb, _, _) = List.assoc "module_code" predfammap in
        produce_chunk h (module_code_symb, true) [] codeCoef (Some 1) [current_module_term] None cont
      else
        cont h
    end $. fun h ->
    begin fun cont ->
      verify_cont (pn,ilist) blocks_done lblenv tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env epilog cont (fun _ _ -> assert false) econt
    end $. fun sizemap tenv ghostenv h env ->
    return_cont h tenv env retval
  and
    verify_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont econt =
    let (decls, ss) =
      let rec iter decls ss =
        match ss with
          (DeclStmt _) as s::ss -> iter (s::decls) ss
        | _ -> (List.rev decls, ss)
      in
      iter [] ss
    in
    begin fun cont ->
      verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env decls cont return_cont econt
    end $. fun sizemap tenv ghostenv h env ->
    let assigned_vars = block_assigned_variables ss in
    let blocks =
      let rec iter blocks ss =
        if ss = [] then
          List.rev blocks
        else
          let (lbls, ss) =
            let rec iter2 lbls ss =
              match ss with
                LabelStmt (l, lbl)::ss ->
                iter2 ((l, lbl)::lbls) ss
              | _ -> (lbls, ss)
            in
            iter2 [] ss
          in
          let (inv, ss) =
            let some_inv l inv ss =
              let (inv, tenv) = check_asn (pn,ilist) tparams tenv inv in
              (Some (l, inv, tenv), ss)
            in
            match ss with
              (PureStmt (_, InvariantStmt (l, inv)))::ss -> some_inv l inv ss
            | InvariantStmt (l, inv)::ss ->
              if not pure then static_error l "Invariant statements must be inside an annotation." None;
              some_inv l inv ss
            | _ -> (None, ss)
          in
          let (body, ss) =
            let rec iter2 body ss =
              match ss with
                [] | LabelStmt _::_ | InvariantStmt _::_ | PureStmt (_, InvariantStmt _)::_ -> (List.rev body, ss)
              | s::ss -> iter2 (s::body) ss
            in
            iter2 [] ss
          in
          iter ((lbls, inv, body)::blocks) ss
      in
      iter [] ss
    in
    let lblenv_ref = ref [] in
    let (lblenv, blocks) =
      let rec iter blocks =
        match blocks with
          [] -> (lblenv, [])
        | (lbls, inv, ss)::blocks ->
          let (lblenv, blocks') = iter blocks in
          let cont blocks_done sizemap tenv ghostenv h env =
            match blocks' with
              [] -> cont sizemap tenv ghostenv h env
            | block'::_ -> goto_block (pn,ilist) blocks_done !lblenv_ref tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont econt block'
          in
          let block' = `Block (inv, ss, cont) in
          let lblenv =
            let cont blocks_done sizemap tenv ghostenv h env =
              goto_block (pn,ilist) blocks_done !lblenv_ref tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont econt block'
            in
            let rec iter lblenv lbls =
              match lbls with
                [] -> lblenv
              | (l, lbl)::lbls ->
                if List.mem_assoc lbl lblenv then static_error l "Duplicate label" None;
                iter ((lbl, cont)::lblenv) lbls
            in
            iter lblenv lbls
          in
          (lblenv, block'::blocks')
      in
      iter blocks
    in
    lblenv_ref := lblenv;
    execute_branch begin fun () ->
      match blocks with
        [] ->
        cont sizemap tenv ghostenv h env
      | block0::_ ->
        goto_block (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env return_cont econt block0
    end;
    begin
      List.iter
        begin fun (`Block (inv, ss, cont) as block) ->
          match inv with
            None -> ()
          | Some (l, inv, tenv) ->
            execute_branch begin fun () ->
            let env =
              flatmap
                begin fun (x, v) ->
                  match try_assoc x tenv with
                    None -> []
                  | Some t ->
                    if List.mem x assigned_vars then
                      [(x, get_unique_var_symb_ x t (List.mem x ghostenv))]
                    else
                      [(x, v)]
                end
                env
            in
            produce_asn [] [] ghostenv env inv real_unit None None (fun h ghostenv env ->
              let blocks_done = block::blocks_done in
              verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss (cont blocks_done) return_cont econt
            )
            end
        end
        blocks
    end;
    success()
  and verify_miniblock (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont econt =
    let (ss, tcont) =
      if not pure && List.exists (function ReturnStmt (_, _) -> true | _ -> false) ss then
        let (ss, lr, eo, epilog) =
          let rec iter ss ss' =
            match ss' with
              ReturnStmt (lr, eo)::epilog -> (List.rev ss, lr, eo, epilog)
            | s::ss' -> iter (s::ss) ss'
          in
          iter [] ss
        in
        let tcont sizemap tenv ghostenv h env =
          let epilog = List.map (function (PureStmt (l, s)) -> s | s -> static_error (stmt_loc s) "An epilog statement must be a pure statement." None) epilog in
          verify_return_stmt (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env true lr eo epilog return_cont econt
        in
        (ss, tcont)
      else
        (ss, tcont)
    in
    verify_cont (pn,ilist) blocks_done lblenv tparams boxes pure leminfo funcmap predinstmap sizemap tenv ghostenv h env ss tcont return_cont econt
  
  (* Region: verification of function bodies *)
  and add_rule_for_lemma lemma_name l pre post ps frac q_ref q_input_args unbound =
    let (_, _, _, _, q_symb, Some q_inputParamCount, _) = List.assoc q_ref#name predfammap in
    let rule l h targs terms_are_well_typed coef coefpat ts cont =
      let rec f input_args ts unbound env =
        if unbound = [] then
          env
        else begin
          match (input_args, ts) with
            ([], []) -> assert false;
          | (LitPat(WVar(_, x, LocalVar)) :: input_args, t :: ts) when List.mem x unbound -> f input_args ts (remove (fun y -> x = y) unbound) ((x, t) :: env)
          | (_ :: input_args, _ :: ts) -> f input_args ts unbound env
        end
      in
      let param_env0 = f q_input_args ts unbound [] in (* env0 maps all parameters not bound by precondition to term *)
      let try_consume_pred h consumed param_env env asn frac p_ref p_args success_cont fail =
        let (_, _, _, _, p_symb, Some p_inputParamCount, _) = List.assoc p_ref#name predfammap in
        let rec find_chunk hdone htodo =
          match htodo with
            [] -> fail ()
          | ((Chunk (actual_name, actual_targs, actual_coef, actual_ts, actual_size)) as chunk) :: hrest when predname_eq actual_name (p_symb ,true) -> 
            let rec match_pats param_env env actuals pats nb_inputs =
              match (actuals, pats) with
                ([], []) ->
                 success_cont (hdone @ hrest) (consumed @ [chunk]) param_env env (fun () -> find_chunk (hdone @ [chunk]) hrest)
              | (t :: actuals, LitPat(WVar(_, x, LocalVar)) :: pats) when List.mem_assoc x ps && not (List.mem_assoc x param_env) -> 
                  match_pats ((x, t) :: param_env) ((x, t) :: env) actuals pats (nb_inputs - 1)
              | (t :: actuals, LitPat(e) :: pats) -> if nb_inputs <= 0 || (definitely_equal t (eval None env e)) then match_pats param_env env actuals pats (nb_inputs - 1) else find_chunk (hdone @ [chunk]) hrest
              | (t :: actuals, DummyPat :: pats) -> match_pats param_env env actuals pats (nb_inputs - 1)
              | (t :: actuals, VarPat(_, x) :: pats) -> match_pats param_env ((x, t) :: env) actuals pats (nb_inputs - 1)
            in
            let check_frac cont = match frac with
              None -> cont env
            | Some(VarPat(_, f)) -> cont ((f, actual_coef) :: env)
            | Some(LitPat(e)) -> if ctxt#query (ctxt#mk_le (eval None env e) actual_coef) then cont env else fail ()
            | Some(DummyPat) -> if is_dummy_frac_term actual_coef then cont env else fail ()
            in
            check_frac (fun env -> match_pats param_env env actual_ts p_args p_inputParamCount) 
          | chunk :: rest -> find_chunk (hdone @ [chunk]) rest
        in
        find_chunk [] h
      in
      let rec try_consume h consumed param_env env asn success_cont fail =
        match asn with
          EmpAsn _ -> success_cont h consumed param_env env fail
        | ExprAsn(_, e) -> if ctxt#query (eval None env e) then success_cont h consumed param_env env fail else fail () 
        | WPredAsn(_, p_ref, true, [], [], p_args) -> try_consume_pred h consumed param_env env asn None p_ref p_args success_cont fail
        | CoefAsn(_, frac,  WPredAsn(_, p_ref, true, [], [], p_args)) -> try_consume_pred h consumed param_env env asn (Some frac) p_ref p_args success_cont fail
        | Sep(_, a1, a2) -> try_consume h consumed param_env env a1 (fun h consumed param_env env fail -> try_consume h consumed param_env env a2 success_cont fail) fail
      in
      try_consume h [] param_env0 param_env0 pre (fun h h_consumed param_env env fail ->
        let dummy_fraction_chunk_generated = match frac with None -> false | Some(f) -> is_dummy_frac_term (eval None env f) in
        if (List.for_all2 (fun wanted e -> definitely_equal wanted (eval None env e)) ts (List.map (function LitPat e -> e) q_input_args)) &&
           (not dummy_fraction_chunk_generated)
        then   
          let tpenv = [] in
          let ghostenv = [] in
          let h = h_consumed @ h in
          with_context (Executing (h, param_env, l, "Auto-applying lemma")) $. fun () ->
            consume_asn rules tpenv h ghostenv param_env pre true real_unit $. fun _ h ghostenv env size ->
             produce_asn tpenv h ghostenv env post real_unit None None $. fun h ghostenv env -> cont (Some h)
        else 
          fail ()
      ) (fun () -> cont None)
    in
    add_lemma_rule q_symb rule

  and create_auto_lemma l (pn,ilist) g trigger pre post ps pre_tenv tparams' =
    match (pre, post) with
    (ExprAsn(_, pre), ExprAsn(_, post)) ->
      List.iter
        begin fun (x, tp) ->
          if not (is_universal_type tp) then
            static_error l
              begin
                Printf.sprintf
                  begin
                    "This auto lemma is not supported because VeriFast currently uses an untyped underlying logic, \
                     and the type of parameter '%s' is not isomorphic to the logic's universe. A type is isomorphic \
                     if it is infinite and its type arguments are isomorphic. \
                     You can work around this limitation by introducing explicit cast functions."
                  end
                  x
              end
              None
        end
        ps;
      ctxt#begin_formal;
      let xs = Array.init (List.length ps) (fun j -> ctxt#mk_bound j (typenode_of_type (snd (List.nth ps j)))) in
      let xs = Array.to_list xs in
      let Some(env) = zip (List.map fst ps) xs in
      let t_pre = eval None env pre in
      let t_post = eval None env post in
      let tps = (List.map (fun (x, t) -> (typenode_of_type t)) ps) in
      let trigger = (
      match trigger with
        None -> []
      | Some(trigger) -> 
          let (trigger, tp) = check_expr (pn,ilist) tparams' pre_tenv (Some true) trigger in
          [eval None env trigger]
      ) in
      let body = ctxt#mk_implies t_pre t_post in
      ctxt#end_formal;
      ctxt#assume_forall g trigger tps body
  | (WPredAsn(p_loc, p_ref, true, p_targs, p_args1, p_args2), Sep(_, WPredAsn(_, q_ref, true, q_targs, q_args1, q_args2), conditions))
    when List.length ps = 0 && List.for_all (fun arg -> match arg with | VarPat(_,_) -> true | _ -> false) (p_args1 @ p_args2) && 
         List.length p_targs = List.length tparams' && (List.for_all (fun (tp, t) -> match (tp, t) with (x, TypeParam(y)) when x = y -> true | _ -> false) (zip2 tparams' p_targs)) &&
         p_ref#name = q_ref#name && List.for_all2 (fun (VarPat(_, x)) arg2 -> match arg2 with LitPat(WVar(_, y, _)) -> x = y | _ -> false) (p_args1 @ p_args2) (q_args1 @ q_args2) &&
         List.for_all2 (fun ta1 ta2 -> ta1 = ta2) p_targs q_targs && is_pure_spatial_assertion conditions -> 
      (Hashtbl.add auto_lemmas (p_ref#name) (None, tparams', List.map (fun (VarPat(_,x)) -> x) p_args1, List.map (fun (VarPat(_,x)) -> x) p_args2, pre, post))
  | (CoefAsn(loc, VarPat(_,f), WPredAsn(p_loc, p_ref, _, p_targs, p_args1, p_args2)), Sep(_, CoefAsn(_, LitPat(WVar(_, g, _)), WPredAsn(_, q_ref, true, q_targs, q_args1, q_args2)), conditions)) 
    when List.length ps = 0 && List.for_all (fun arg -> match arg with | VarPat(_,_) -> true | _ -> false) (p_args1 @ p_args2) && 
         List.length p_targs = List.length tparams' && (List.for_all (fun (tp, t) -> match (tp, t) with (x, TypeParam(y)) when x = y -> true | _ -> false) (zip2 tparams' p_targs)) &&
         p_ref#name = q_ref#name && List.for_all2 (fun (VarPat(_, x)) arg2 -> match arg2 with LitPat(WVar(_, y, _)) -> x = y | _ -> false) (p_args1 @ p_args2) (q_args1 @ q_args2) &&
         List.for_all2 (fun ta1 ta2 -> ta1 = ta2) p_targs q_targs && f = g && is_pure_spatial_assertion conditions->
      (Hashtbl.add auto_lemmas (p_ref#name) (Some(f), tparams', List.map (fun (VarPat(_,x)) -> x) p_args1, List.map (fun (VarPat(_,x)) -> x) p_args2, pre, post))
  | _ ->
    (* todo: determine values of parameters based on postcondition (instead of precondition) to avoid backtracking search *)
    let bound_param_vars_pred p_args vars must = 
     List.fold_left (fun (vars, must) arg ->
        match arg with 
          LitPat(WVar(_, x, _)) -> if List.mem_assoc x ps then (x :: vars, must) else (vars, must)
        | LitPat(e) ->
          let newmust = List.filter (fun x -> (List.mem_assoc x ps) && not (List.mem x vars)) (vars_used e) in
          (vars, must @ newmust)
        | DummyPat -> (vars, must)
        | VarPat(_, _) -> (vars, must)) (vars,must) p_args
    in 
    let rec bound_param_vars asn vars must = match asn with
      EmpAsn _ -> (vars, must)
    | WPredAsn(p_loc, p_ref, true, [], [], p_args) when p_ref#is_precise ->
      bound_param_vars_pred p_args vars must
    | CoefAsn(_, frac, WPredAsn(p_loc, p_ref, true, [], [], p_args)) when p_ref#is_precise ->
      bound_param_vars_pred (frac :: p_args) vars must
    | Sep(_, a1, a2) -> let (vars', must') = bound_param_vars a1 vars must in bound_param_vars a2 vars' must'
    | ExprAsn(_, e) -> 
        let newmust = List.filter (fun x -> (List.mem_assoc x ps) && not (List.mem x vars)) (vars_used e) in
        (vars, must @ newmust)
    | _ -> static_error l (sprintf "precondition of auto lemma %s has wrong form" g) None
    in
    let (bound_ps, must) = bound_param_vars pre [] [] in
    let unbound_ps = List.filter (fun x -> not (List.mem x bound_ps)) (List.map (fun (x, t) -> x) ps) in
    List.iter (fun x -> if not (List.mem x unbound_ps) then static_error l (sprintf "precondition of auto lemma %s has wrong form" g) None) must;
    let rec generate_rules asn = 
      let generate_rules_pred frac q_ref q_args =
        let Some nb_inputs = q_ref#inputParamCount in
        let q_input_args = take nb_inputs q_args in
        let remaining_unbound = List.fold_left (fun unbound a -> match a with
            LitPat(WVar(_, x, _)) when List.mem x unbound -> remove (fun y -> x = y) unbound
          | _ -> unbound
        ) unbound_ps q_input_args 
        in
        if remaining_unbound = [] && List.for_all (function LitPat(e) -> true | _ -> false) q_input_args then
          (add_rule_for_lemma g l pre post ps frac q_ref q_input_args unbound_ps; 1)
        else
          0
      in
      match asn with
      | WPredAsn(q_loc, q_ref, true, [], [], q_args) when q_ref#is_precise -> 
        generate_rules_pred None q_ref q_args
      | CoefAsn(_, LitPat(frac), WPredAsn(q_loc, q_ref, true, [], [], q_args)) when q_ref#is_precise ->
        generate_rules_pred (Some frac) q_ref q_args
      | Sep(_, a1, a2) -> (generate_rules a1) + (generate_rules a2)
      | _ -> 0
    in
    let nb_rules_generated = generate_rules post in
    if nb_rules_generated = 0 then static_error l (sprintf "no suitable predicates found in postcondition to generate rules") None
  and heapify_params h tenv env ps =
    begin match ps with
      [] -> (h, tenv, env)
    | (l, x, t, addr) :: ps -> 
      let xvalue = List.assoc x env in
      let tenv' = update tenv x (RefType (List.assoc x tenv)) in
      let h' = Chunk ((pointee_pred_symb l t, true), [], real_unit, [addr; xvalue], None) :: h in
      let env' = update env x addr in
      heapify_params h' tenv' env' ps
    end
  and cleanup_heapy_locals (pn, ilist) l h env ps cont =
    let rec cleanup_heapy_locals_core (pn, ilist) l h env ps cont= 
    match ps with
      [] -> cont h
    | (_, x, t, addr) :: ps ->
      consume_chunk rules h [] [] [] l (pointee_pred_symb l t, true) [] real_unit (TermPat real_unit) (Some 1) [TermPat addr; dummypat] (fun chunk h coef [_; t] size ghostenv env env' -> cleanup_heapy_locals_core (pn, ilist) l h env ps cont)
    in
    match ps with
      [] -> cont h
    | _ -> with_context (Executing (h, env, l, "Freeing parameters.")) (fun _ -> cleanup_heapy_locals_core (pn, ilist) l h env ps cont)
  and verify_func pn ilist gs lems boxes predinstmap funcmap tparams env l k tparams' rt g ps nonghost_callers_only pre pre_tenv post terminates ss closeBraceLoc =
    if startswith g "vf__" then static_error l "The name of a user-defined function must not start with 'vf__'." None;
    let tparams = tparams' @ tparams in
    let _ = push() in
    let penv = get_unique_var_symbs_ ps (match k with Regular -> false | _ -> true) in (* actual params invullen *)
    let heapy_vars = list_remove_dups (List.flatten (List.map (fun s -> stmt_address_taken s) ss)) in
    let heapy_ps = List.flatten (List.map (fun (x,tp) -> 
      if List.mem x heapy_vars then 
        let addr = get_unique_var_symb_non_ghost (x ^ "_addr") (PtrType tp) in
        [(l, x, tp, addr)] 
      else 
       []
      ) (List.filter (fun (x, tp) -> List.mem_assoc x ps) pre_tenv))
    in
    let (sizemap, indinfo) =
      match ss with
        [SwitchStmt (_, Var (_, x), _)] -> (
        match try_assoc_i x penv with
          None -> ([], None)
        | Some(i, t) -> ([(t, (t, 0))], Some (x, i, List.map (fun (_, t) -> t) penv))
        )
      | _ -> ([], None)
    in
    let tenv =
      match rt with
        None -> pre_tenv
      | Some rt -> ("#result", rt)::pre_tenv
    in
    let (in_pure_context, leminfo, gs', lems', ghostenv) =
      if is_lemma k then 
        (true, LemInfo (lems, g, indinfo, nonghost_callers_only), gs, g::lems, List.map (function (p, t) -> p) ps @ ["#result"])
      else
        (false, RealFuncInfo (gs, g, terminates), g::gs, lems, [])
    in
    let env = [(current_thread_name, get_unique_var_symb current_thread_name current_thread_type)] @ penv @ env in
    let _ =
      check_should_fail () $. fun () ->
      execute_branch $. fun () ->
      with_context (Executing ([], env, l, sprintf "Verifying function '%s'" g)) $. fun () ->
      produce_asn_with_post [] [] ghostenv env pre real_unit (Some (PredicateChunkSize 0)) None (fun h ghostenv env post' ->
        let post =
          match post' with
            None -> post
          | Some post' ->
            post'
        in
        let (prolog, ss) =
          if in_pure_context then
            ([], ss)
          else
            let rec iter prolog ss =
              match ss with
                PureStmt (l, s)::ss -> iter (s::prolog) ss
              | _ -> (List.rev prolog, ss)
            in
            iter [] ss
        in
        begin fun tcont ->
          verify_cont (pn,ilist) [] [] tparams boxes true leminfo funcmap predinstmap sizemap tenv ghostenv h env prolog tcont (fun _ _ -> assert false) (fun _ _ _ -> assert false)
        end $. fun sizemap tenv ghostenv h env ->
        begin fun cont ->
          if unloadable && not in_pure_context then
            let (_, _, _, _, module_code_symb, _, _) = List.assoc "module_code" predfammap in
            with_context (Executing (h, env, l, "Consuming code fraction")) $. fun () ->
            consume_chunk rules h [] [] [] l (module_code_symb, true) [] real_unit (SrcPat DummyPat) (Some 1) [TermPat current_module_term] $. fun _ h coef _ _ _ _ _ ->
            let half = real_mul l real_half coef in
            cont (Chunk ((module_code_symb, true), [], half, [current_module_term], None)::h) (("currentCodeFraction", RealType)::tenv) ("currentCodeFraction"::ghostenv) (("currentCodeFraction", half)::env)
          else
            cont h tenv ghostenv env
        end $. fun h tenv ghostenv env ->
        let do_return h env_post =
          consume_asn rules [] h ghostenv env_post post true real_unit (fun _ h ghostenv env size_first ->
            cleanup_heapy_locals (pn, ilist) closeBraceLoc h env heapy_ps (fun h ->
              check_leaks h env closeBraceLoc "Function leaks heap chunks."
            )
          )
        in
        let return_cont h tenv2 env2 retval =
          match (rt, retval) with
            (None, None) -> do_return h env
          | (Some tp, Some t) -> do_return h (("result", t)::env)
          | (None, Some _) -> assert_false h env l "Void function returns a value." None
          | (Some _, None) -> assert_false h env l "Non-void function does not return a value." None
        in
        begin fun tcont ->
          let (h,tenv,env) = heapify_params h tenv env heapy_ps in
          let outerlocals = ref [] in
          stmts_mark_addr_taken ss [(outerlocals, [])] (fun _ -> ());
          let body = if List.length !outerlocals = 0 then ss else [BlockStmt(l, [], ss, closeBraceLoc, outerlocals)] in
          verify_block (pn,ilist) [] [] tparams boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env body tcont return_cont (fun _ _ _ -> assert false)
        end $. fun sizemap tenv ghostenv h env ->
        verify_return_stmt (pn,ilist) [] [] tparams boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env false closeBraceLoc None [] return_cont (fun _ _ _ -> assert false)
      )
    in
    let _ = pop() in
    let _ = 
      (match k with
        Lemma(true, trigger) -> create_auto_lemma l (pn,ilist) g trigger pre post ps pre_tenv tparams'
      | _ -> ()
    ) in
    gs', lems'
  
  let switch_stmt ss env=
    match ss with
      [SwitchStmt (_, Var (_, x), _)] ->
        (match try_assoc x env with
           None -> ([], None)
         | Some t -> ([(t, (t, 0))], Some x)
        )
    | _ -> ([], None)
  
  let get_fields (pn,ilist) cn lm=
    match try_assoc' Real (pn,ilist) cn classmap with
      Some {cfds} -> cfds
    | None -> static_error lm ("No class was found: "^cn) None
  
  let record_fun_timing l funName body =
    let time0 = Perf.time() in
    let result = body () in
    !stats#recordFunctionTiming (string_of_loc l ^ ": " ^ funName) (Perf.time() -. time0);
    result
  
  let rec verify_exceptional_return (pn,ilist) l h ghostenv env exceptp excep handlers =
    if not (is_unchecked_exception_type exceptp) then
      match handlers with
      | [] -> assert_false h env l ("Potentially unhandled exception " ^ (string_of_type exceptp) ^ ".") None 
      | (handler_tp, epost) :: handlers ->
        branch
          begin fun () ->
            if (is_subtype_of_ exceptp handler_tp) || (is_subtype_of_ handler_tp exceptp) then
              consume_asn rules [] h ghostenv env epost true real_unit $. fun _ h ghostenv env size_first ->
              success()
            else
              success()
          end
          begin fun () ->
            if not (is_subtype_of_ exceptp handler_tp) then
              verify_exceptional_return (pn,ilist) l h ghostenv env exceptp excep handlers
            else
              success()
          end
    else
      success()
  
  let rec verify_cons (pn,ilist) cfin cn supercn superctors boxes lems cons =
    match cons with
      [] -> ()
    | (sign, CtorInfo (lm, xmap, pre, pre_tenv, post, epost, terminates, ss, v))::rest ->
      match ss with
        None ->
        let ((p, _, _), (_, _, _)) = lm in 
        if Filename.check_suffix p ".javaspec" then
          verify_cons (pn,ilist) cfin cn supercn superctors boxes lems rest
        else
          static_error lm "Constructor specification is only allowed in javaspec files!" None
      | Some (Some ((ss, closeBraceLoc), rank)) ->
        record_fun_timing lm (cn ^ ".<ctor>") begin fun () ->
        if !verbosity >= 1 then Printf.printf "%10.6fs: %s: Verifying constructor %s\n" (Perf.time()) (string_of_loc lm) (string_of_sign (cn, sign));
        execute_branch begin fun () ->
        with_context (Executing ([], [], lm, Printf.sprintf "Class '%s': verifying constructor" cn)) $. fun () ->
        let env = get_unique_var_symbs_non_ghost ([(current_thread_name, current_thread_type)] @ xmap) in
        let (sizemap, indinfo) = switch_stmt ss env in
        let (ss, explicitsupercall) = match ss with SuperConstructorCall(l, es) :: body -> (body, Some(SuperConstructorCall(l, es))) | _ -> (ss, None) in
        let (in_pure_context, leminfo, ghostenv) = (false, RealMethodInfo (if terminates then Some rank else None), []) in
        begin
          produce_asn [] [] ghostenv env pre real_unit None None $. fun h ghostenv env ->
          let this = get_unique_var_symb "this" (ObjType cn) in
          begin fun cont ->
            if cfin = FinalClass then assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [this]) (List.assoc cn classterms)) cont else cont ()
          end $. fun () ->
          let do_body h ghostenv env =
            let do_return h env_post =
              consume_asn rules [] h ghostenv env_post post true real_unit $. fun _ h ghostenv env size_first ->
              check_leaks h env closeBraceLoc "Function leaks heap chunks."
            in
            let return_cont h tenv2 env2 retval =
              assert (retval = None);
              do_return h env
            in
            let econt throwl h env2 exceptp excep =
              verify_exceptional_return (pn,ilist) throwl h ghostenv env exceptp excep epost
            in
            let tenv = ("this", ObjType cn):: (current_thread_name, current_thread_type) ::pre_tenv in
            begin fun cont ->
              if cn = "java.lang.Object" then
                cont h
              else
                let (argtypes, args) = match explicitsupercall with
                  None -> ([], [])
                | Some(SuperConstructorCall(l, es)) -> 
                  inheritance_check cn l;
                  ((List.map (fun e -> let (w, tp) = check_expr (pn,ilist) [] tenv (Some true) e in tp) es), es)
                in
                match try_assoc argtypes superctors with
                  None ->
                  static_error lm "There is no superclass constructor that matches the superclass constructor call" None
                | Some (CtorInfo (lc0, xmap0, pre0, pre_tenv0, post0, epost0, terminates0, ss0, v0)) ->
                  with_context (Executing (h, env, lm, "Implicit superclass constructor call")) $. fun () ->
                  if terminates && not terminates0 then static_error lm "Superclass constructor is not declared as 'terminates'" None;
                  let is_upcall =
                    match ss0 with
                      Some (Some (_, rank0)) -> rank0 < rank
                    | _ -> true
                  in
                  let eval_h h env e cont = verify_expr false (pn,ilist) [] false leminfo funcmap sizemap tenv ghostenv h env None e cont econt in
                  let pats = (List.map (fun e -> SrcPat (LitPat e)) args) in
                  verify_call funcmap eval_h lm (pn, ilist) None None [] pats ([], None, xmap0, ["this", this], pre0, post0, Some(epost0), terminates0, v0) false is_upcall (Some supercn) leminfo sizemap h [] tenv ghostenv env (fun h env _ ->
                  cont h) econt
            end $. fun h ->
            let fds = get_fields (pn,ilist) cn lm in
            let rec iter h fds =
              match fds with
                [] -> verify_cont (pn,ilist) [] [] [] boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env ss
                     (fun sizemap tenv ghostenv h env -> return_cont h tenv env None) return_cont econt
              | (f, {ft=t; fbinding=binding; finit=init})::fds ->
                if binding = Instance then begin
                  match init with 
                    None ->
                    assume_field h cn f t Real this (default_value t) real_unit $. fun h ->
                    iter h fds
                  | Some(e) -> 
                    with_context (Executing (h, [], expr_loc e, "Executing field initializer")) $. fun () ->
                    verify_expr false (pn,ilist) [] false leminfo funcmap sizemap [(current_class, ClassOrInterfaceName cn); ("this", ObjType cn); (current_thread_name, current_thread_type)] ghostenv h [("this", this); (current_thread_name, List.assoc current_thread_name env)] None e (fun h _ initial_value ->
                      assume_field h cn f t Real this initial_value real_unit $. fun h ->
                      iter h fds
                    ) (fun throwl h env2 exceptp excep -> assert_false h env2 throwl ("Field initializers throws exception.") None)
                end else
                  iter h fds
            in
            iter h fds
          in
          assume_neq this (ctxt#mk_intlit 0) $. fun() -> do_body h ghostenv (("this", this)::env)
        end
        end
        end;
        verify_cons (pn,ilist) cfin cn supercn superctors boxes lems rest
  
  let rec verify_meths (pn,ilist) cfin cabstract boxes lems meths=
    match meths with
      [] -> ()
    | ((g,sign), MethodInfo (l,gh, rt, ps,pre,pre_tenv,post,epost,pre_dyn,post_dyn,epost_dyn,terminates,sts,fb,v, _,abstract))::meths ->
      if abstract && not cabstract then static_error l "Abstract method can only appear in abstract class." None;
      match sts with
        None -> let ((p,_,_),(_,_,_))=l in 
          if (Filename.check_suffix p ".javaspec") || abstract then verify_meths (pn,ilist) cfin cabstract boxes lems meths
          else static_error l "Method specification is only allowed in javaspec files!" None
      | Some (Some ((ss, closeBraceLoc), rank)) ->
        record_fun_timing l g begin fun () ->
        if !verbosity >= 1 then Printf.printf "%10.6fs: %s: Verifying method %s\n" (Perf.time()) (string_of_loc l) g;
        if abstract then static_error l "Abstract method cannot have implementation." None;
        execute_branch $. fun () ->
        with_context (Executing ([], [], l, Printf.sprintf "Verifying method '%s'" g)) $. fun () ->
        let (in_pure_context, leminfo, ghostenv) =
          match gh with
            Ghost -> (true, LemInfo (lems, "<method>", None, false), List.map (function (p, t) -> p) ps @ ["#result"])
          | Real -> (false, RealMethodInfo (if terminates then Some rank else None), [])
        in
        begin
          let env = get_unique_var_symbs_non_ghost (ps @ [(current_thread_name, current_thread_type)]) in (* actual params invullen *)
          begin fun cont ->
            if fb = Instance then
            begin
              let ("this", thisTerm)::_ = env in
              let ("this", ObjType cn)::_ = ps in
              (* CAVEAT: Remove this assumption once we allow subclassing. *)
              (* assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [thisTerm]) (List.assoc cn classterms)) $. fun () -> *)
              begin fun cont ->
                if cfin = FinalClass then assume (ctxt#mk_eq (ctxt#mk_app get_class_symbol [thisTerm]) (List.assoc cn classterms)) cont else cont ()
              end $. fun () ->
              assume_neq thisTerm (ctxt#mk_intlit 0) (fun _ -> cont (("this", ObjType cn)::pre_tenv))
            end else cont pre_tenv
          end $. fun tenv ->
          let (sizemap, indinfo) = switch_stmt ss env in
          let tenv = match rt with None ->tenv | Some rt -> ("#result", rt)::tenv in
          produce_asn [] [] ghostenv env pre real_unit None None $. fun h ghostenv env ->
          let do_return h env_post =
            consume_asn rules [] h ghostenv env_post post true real_unit $. fun _ h ghostenv env size_first ->
            check_leaks h env closeBraceLoc "Function leaks heap chunks."
          in
          let return_cont h tenv2 env2 retval =
            match (rt, retval) with
              (None, None) -> do_return h env
            | (Some tp, Some t) -> do_return h (("result", t)::env)
            | (None, Some _) -> assert_false h env l "Void function returns a value." None
            | (Some _, None) -> assert_false h env l "Non-void function does not return a value." None
          in
          let econt throwl h env2 exceptp excep =
            verify_exceptional_return (pn,ilist) throwl h ghostenv env exceptp excep epost
          in
          let cont sizemap tenv ghostenv h env = return_cont h tenv env None in
          verify_block (pn,ilist) [] [] [] boxes in_pure_context leminfo funcmap predinstmap sizemap tenv ghostenv h env ss cont return_cont econt
        end
        end;
        verify_meths (pn,ilist) cfin cabstract boxes lems meths
  
  let rec verify_classes boxes lems classm=
    match classm with
      [] -> ()
    | (cn, {cl; cabstract; cfinal; cmeths; cctors; csuper; cpn; cilist})::classm ->
      let (superctors, superfinal) =
        if csuper = "" then ([], ExtensibleClass) else
          let {cctors; cfinal} = List.assoc csuper classmap in
          (cctors, cfinal)
      in
      if superfinal = FinalClass then static_error cl "Cannot extend final class." None;
      verify_cons (cpn, cilist) cfinal cn csuper superctors boxes lems cctors;
      verify_meths (cpn, cilist) cfinal cabstract boxes lems cmeths;
      verify_classes boxes lems classm
  
  let rec verify_funcs (pn,ilist)  boxes gs lems ds =
    match ds with
     [] -> (boxes, gs, lems)
    | Func (l, Lemma(auto, trigger), _, rt, g, ps, _, _, _, _, None, _, _)::ds -> 
      let g = full_name pn g in
      let ((g_file_name, _, _), _) = l in
      if language = Java && not (Filename.check_suffix g_file_name ".javaspec") then
        static_error l "A lemma function outside a .javaspec file must have a body. To assume a lemma, use the body '{ assume(false); }'." None;
      let FuncInfo ([], fterm, _, k, tparams', rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, fb,v) = List.assoc g funcmap in
      if auto && (Filename.check_suffix g_file_name ".c" || is_import_spec || language = CLang && Filename.chop_extension (Filename.basename g_file_name) <> Filename.chop_extension (Filename.basename program_path)) then begin
        register_prototype_used l g fterm;
        create_auto_lemma l (pn,ilist) g trigger pre post ps pre_tenv tparams'
      end;
      let lems =
        if body = None then
          g::lems (* Prototype for lemma defined in preceding module; will generate .requires directive in manifest when called. *)
        else
          lems    (* Prototype for lemma implemented in current file; will not generate .requires directive; calls must be subjected to termination check. *)
      in
      verify_funcs (pn,ilist) boxes gs lems ds
    | Func (l, Regular, _, rt, g, ps, _, _, _, _, None, _, _)::ds ->
      let g = full_name pn g in
      let FuncInfo ([], fterm, _, k, tparams', rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, fb,v) = List.assoc g funcmap in
      let gs =
        if body = None then
          g::gs
        else
          gs
      in
      verify_funcs (pn,ilist) boxes gs lems ds
    | Func (l, k, _, _, g, _, _, functype_opt, _, _, Some _, _, _)::ds when k <> Fixpoint ->
      let g = full_name pn g in
      let gs', lems' =
      record_fun_timing l g begin fun () ->
      if !verbosity >= 1 then Printf.printf "%10.6fs: %s: Verifying function %s\n" (Perf.time()) (string_of_loc l) g;
      let FuncInfo ([], fterm, l, k, tparams', rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, _, Some (Some (ss, closeBraceLoc)),fb,v) = (List.assoc g funcmap)in
      let tparams = [] in
      let env = [] in
      verify_func pn ilist gs lems boxes predinstmap funcmap tparams env l k tparams' rt g ps nonghost_callers_only pre pre_tenv post terminates ss closeBraceLoc
      end in
      verify_funcs (pn, ilist) boxes gs' lems' ds
    | BoxClassDecl (l, bcn, _, _, _, _)::ds -> let bcn=full_name pn bcn in
      let (Some (l, boxpmap, boxinv, boxvarmap, amap, hpmap)) = try_assoc' Ghost (pn,ilist) bcn boxmap in
      let old_boxvarmap = List.map (fun (x, t) -> ("old_" ^ x, t)) boxvarmap in
      let leminfo = LemInfo (lems, "", None, false) in
      List.iter
        (fun (hpn, (l, pmap, extended, inv, pbcs)) ->
           let pbcans =
             List.map
               (fun (PreservedByClause (l, an, xs, ss)) ->
                  begin
                  match try_assoc an amap with
                    None -> static_error l "No such action." None
                  | Some (_, action_permission_info, apmap, pre, post) ->
                    let () =
                      let rec iter ys xs =
                        match xs with
                          [] -> ()
                        | x::xs ->
                          if List.mem_assoc x boxvarmap then static_error l "Action parameter name clashes with box variable." None;
                          if List.mem_assoc x pmap then static_error l "Action parameter name clashes with handle predicate parameter." None;
                          if List.mem x ys then static_error l "Duplicate action parameter." None;
                          if startswith x "old_" then static_error l "Action parameter name cannot start with old_." None;
                          iter (x::ys) xs
                      in
                      iter [] xs
                    in
                    let apbs =
                      match zip xs apmap with
                        None -> static_error l "Incorrect number of action parameters." None
                      | Some bs -> bs
                    in
                    let apmap' = List.map (fun (x, (_, t)) -> (x, t)) apbs in
                    let tenv = boxvarmap @ old_boxvarmap @ pmap @ apmap' in
                    execute_branch begin fun () ->
                    let boxId = get_unique_var_symb "this" BoxIdType in
                    let currentThread = get_unique_var_symb "currentThread" intType in
                    let actionHandles = get_unique_var_symb "actionHandles" (list_type HandleIdType) in
                    let predicateHandle = get_unique_var_symb "predicateHandle" HandleIdType in
                    assume (ctxt#mk_not (mk_mem HandleIdType predicateHandle actionHandles)) begin fun () ->
                      let pre_boxargs = List.map (fun (x, t) -> (x, get_unique_var_symb ("old_" ^ x) t)) boxpmap in
                      let pre_boxargsWithThis = ("this", boxId) :: pre_boxargs in
                      with_context (Executing ([], [], l, "Checking preserved_by clause.")) $. fun () ->
                        with_context PushSubcontext $. fun () ->
                          produce_asn [] [] [] pre_boxargsWithThis boxinv real_unit None None $. fun h_pre _ pre_boxvars ->
                            let aargs = List.map (fun (x, (y, t)) -> (x, y, get_unique_var_symb x t)) apbs in
                            let apre_env = List.map (fun (x, y, t) -> (y, t)) aargs in
                            assume (eval None ([("actionHandles", actionHandles)] @ pre_boxvars @ apre_env) pre) $. fun () ->
                              let produce_action_permission h cont =
                                match action_permission_info with
                                  None -> cont h
                                | Some(action_permission_pred_symb, action_permission_dispenser_pred_symb) -> 
                                  let actionFrac = get_unique_var_symb "#actionFrac" RealType in
                                  assume (ctxt#mk_real_lt real_zero actionFrac) $. fun () -> 
                                    let (parameters, inputParamCount) = match action_permission_dispenser_pred_symb with
                                      None -> ([boxId], Some 1)
                                    | Some action_permission_dispenser_pred_symb -> 
                                      let [(_, action_parameter)] = apre_env in 
                                      ([boxId; action_parameter], Some 2)
                                    in
                                    produce_chunk h (action_permission_pred_symb, true) [] actionFrac inputParamCount parameters None cont
                              in
                              produce_action_permission h_pre $. fun h_pre ->
                              let hpargs = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) pmap in
                              assume_handle_invs bcn hpmap hpn ([("predicateHandle", predicateHandle)] @ pre_boxvars @ hpargs) h_pre $. fun h_pre_hinv ->
                                consume_asn rules [] h_pre_hinv [] pre_boxargsWithThis boxinv true real_unit $. fun _ hinv _ _ _ ->                         
                                  let old_boxvars = List.map (fun (x, t) -> ("old_" ^ x, t)) pre_boxvars in
                                  let post_boxargs = List.map (fun (x, t) -> (x, get_unique_var_symb x t)) boxpmap in
                                  let post_boxargsWithThis = ("this", boxId) :: post_boxargs in
                                  produce_asn [] hinv [] post_boxargsWithThis boxinv real_unit None None $. fun h_post_hinv _ post_boxvars ->
                                    with_context PopSubcontext $. fun () ->
                                    let ghostenv = List.map (fun (x, t) -> x) tenv in
                                      assume (eval None ([("actionHandles", actionHandles)] @ post_boxvars @ old_boxvars @ apre_env) post) $. fun () ->
                                        let aarg_env = List.map (fun (x, y, t) -> (x, t)) aargs in
                                        let env = ["actionHandles", actionHandles; "predicateHandle", predicateHandle; "currentThread", currentThread] @
                                          post_boxvars @ old_boxvars @ aarg_env @ hpargs in
                                        let tenv = ["actionHandles", list_type HandleIdType; "predicateHandle", HandleIdType; "currentThread", intType] @ tenv in
                                        verify_cont (pn,ilist) [] [] [] boxes true leminfo funcmap predinstmap [] tenv ghostenv h_post_hinv env ss begin fun _ _ _ h _ ->
                                          let post_inv_env = [("predicateHandle", predicateHandle)] @ post_boxvars @ hpargs in
                                          (* does not consume extended handles, only suffices if one can only extend pure handles *)
                                          consume_asn rules [] h [] post_inv_env inv true real_unit (fun _ h _ _ _ -> success ())
                                        end begin fun _ _ -> static_error l "Return statements are not allowed in handle predicate preservation proofs." None end
                                        begin fun _ _ _ _ _ -> static_error l "Exceptions are not allowed in handle predicate preservation proofs." None end
                    end
                    end;
                    an
                  end)
               pbcs
           in
           List.iter (fun (an, _) -> if not (List.mem an pbcans) then static_error l ("No preserved_by clause for action '" ^ an ^ "'.") None) amap)
        hpmap;
      verify_funcs (pn,ilist) (bcn::boxes) gs lems ds
    | _::ds -> verify_funcs (pn,ilist)  boxes gs lems ds
  
  let lems1 =
    flatmap
      (function (g, FuncInfo (funenv, fterm, l, Lemma(_), tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, fb, v)) -> [g] | _ -> [])
      funcmap1
  
  let lems0 =
    flatmap
      (function (g, FuncInfo (funenv, fterm, l, Lemma(_), tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, fb, v)) when not (List.mem g lems1) -> [g] | _ -> [])
      funcmap0
  
  let gs1 =
    flatmap
      (function (g, FuncInfo (funenv, fterm, l, Regular, tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, fb, v)) -> [g] | _ -> [])
      funcmap1
  
  let gs0 =
    flatmap
      (function (g, FuncInfo (funenv, fterm, l, Regular, tparams, rt, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, fb, v)) when not (List.mem g gs1) -> [g] | _ -> [])
      funcmap0
  
  let rec verify_funcs' boxes gs lems ps=
    match ps with
      PackageDecl(l,pn,il,ds)::rest-> let (boxes, gs, lems) = verify_funcs (pn,il) boxes gs lems ds in verify_funcs' boxes gs lems rest
    | [] -> verify_classes boxes lems classmap
  
  let () = verify_funcs' [] gs0 lems0 ps
  
  let result = 
    (
      (
        prototypes_implemented, !functypes_implemented, !structures_defined, 
        !nonabstract_predicates, importmodulemap1
      ), 
      (
        structmap1, enummap1, globalmap1, modulemap1, importmodulemap1, 
        inductivemap1, purefuncmap1,predctormap1, malloc_block_pred_map1, 
        field_pred_map1, predfammap1, predinstmap1, typedefmap1, functypemap1, 
        funcmap1, boxmap,classmap1,interfmap1,classterms1,interfaceterms1, 
        pluginmap1
      )
    )
  
  end (* CheckFile *)
  
  let rec check_file filepath is_import_spec include_prelude dir headers ps =
    let module CF = CheckFile(struct
      let filepath = filepath
      let is_import_spec = is_import_spec
      let include_prelude = include_prelude
      let dir = dir
      let headers = headers
      let ps = ps
      let check_file = check_file
    end) in
    CF.result
  
  (* Region: top-level stuff *)
  
  let jardeps = ref []
  let provide_files = ref []
  let (prototypes_implemented, functypes_implemented, structures_defined, 
       nonabstract_predicates, modules_imported) =
    let result = check_should_fail ([], [], [], [], []) $. fun () ->
    let (headers, ds)=
      match file_type path with
        | Java ->
          let l = file_loc path in
          let (headers, javas, provides) =
            if Filename.check_suffix path ".jarsrc" then
              let (jars, javas, provides) = parse_jarsrc_file_core path in
              let specPath = Filename.chop_extension path ^ ".jarspec" in
              let jarspecs = List.map (fun path -> (l, (DoubleQuoteInclude, path ^ "spec",""), [], [])) jars in (* Include the location where the jar is referenced *)
              let pathDir = Filename.dirname path in
              let javas = List.map (concat pathDir) javas in
              if Sys.file_exists specPath then begin
                let (specJars, _) = parse_jarspec_file_core specPath in
                jardeps := specJars @ jars;
                ((l, (DoubleQuoteInclude, Filename.basename specPath,""), [], []) :: jarspecs, javas, provides)
              end else
                (jarspecs, javas, provides)
            else
              ([], [path], [])
          in
          let provides = provides @ options.option_provides in
          let token = (* A string to make the provide files unique *)
            if options.option_keep_provide_files then "" else Printf.sprintf "_%ld" (Stopwatch.getpid ())
          in
          let provide_javas =
            provides |> imap begin fun i provide ->
              let provide_file = Printf.sprintf "%s_provide%d%s.java" (Filename.chop_extension path) i token in
              let cmdLine = Printf.sprintf "%s > %s" provide provide_file in
              let exitCode = Sys.command cmdLine in
              if exitCode <> 0 then
                raise (static_error l (Printf.sprintf "Provide %d: command '%s' failed with exit code %d" i cmdLine exitCode) None);
              provide_file
            end
          in
          provide_files := provide_javas;
          let javas = javas @ provide_javas in
          let context = List.map (fun (((b, _, _), _), (_, p, _), _, _) -> Util.concat (Filename.dirname b) ((Filename.chop_extension p) ^ ".jar")) headers in
          let ds = Java_frontend_bridge.parse_java_files javas context reportRange reportShouldFail options.option_verbose options.option_enforce_annotations options.option_use_java_frontend in
          (headers, ds)
        | CLang ->
          if Filename.check_suffix path ".h" then
            parse_header_file path reportRange reportShouldFail options.option_verbose [] options.option_enforce_annotations
          else
            parse_c_file path reportRange reportShouldFail options.option_verbose options.option_include_paths options.option_enforce_annotations
    in
    emitter_callback ds;
    check_should_fail ([], [], [], [], []) $. fun () ->
    let (linker_info, _) = check_file path false true programDir headers ds in
    linker_info
    in
    begin
      match !shouldFailLocs with
        [] -> ()
      | l::_ -> static_error l "No error found on line." None
    end;
    result
  
  let () =
    if not options.option_keep_provide_files then begin
      !provide_files |> List.iter Sys.remove
    end
  
  let () = !stats#appendProverStats ctxt#stats

  let create_jardeps_file() =
    let jardeps_filename = Filename.chop_extension path ^ ".jardeps" in
    if emit_manifest then
      let file = open_out jardeps_filename in
      do_finally (fun () ->
        List.iter (fun line -> output_string file (line ^ "\n")) !jardeps
      ) (fun () -> close_out file)
    else
      jardeps_map := (jardeps_filename, !jardeps)::!jardeps_map

(*
There are 7 kinds of entries possible in a vfmanifest/dll_vfmanifest file

.provides FILE#NAME:
  The c-files that correspond with this vfmanifest file,
  implement the function NAME that was forward declared in the header FILE.

.provides FILE#F_NAME : FTYPE_NAME(TYPE_ARGS) UNLOADABLE
  The c-files that correspond with this vfmanifest file,
  implement the function F_NAME which is of the function type FTYPE_NAME. The 
  function type FTYPE_NAME was forward declared in the header FILE.
  The type arguments of F_NAME are given by TYPE_ARGS and UNLOADABLE indicates
  if the function F_NAME is an unloadable module.

.requires FILE#NAME:
  The c-files that correspond with this vfmanifest file,
  use the function NAME that was forward declared in the header FILE without
  providing an implementation.

.structure: FILE1@FILE2#NAME:
  The c-files that correspond with this vfmanifest file,
  give the structure NAME a body in the file FILE1 and that structure was 
  forward declared in the header FILE2.
  An empty FILE1 means that the struct can never be given a body, this is used
  to create a vfmanifest or dll_Vfmanifest for a library that was not verified.

.predicate FILE1@FILE2#NAME:
  The c-files that correspond with this vfmanifest file,
  give the predicate NAME a body in the file FILE1 and the predicate family of
  the predicate NAME was declared in the file FILE2.
  A predicate that has no distinct declared predicate family is considered to
  have an implicit predicate family declaration in the same file where de
  predicate is defined (so FILE1 == FILE2 or FILE1 == "").
  When manually creating a vfmanifest or dll_vfmanifest for a library and we 
  have an abstract predicate in the API, we pretend to give that predicate a
  body to prevent the user of that API to give the predicate a body.

.produces name:
  The c-file that corresponds with this vfmanifest file,
  provides the module NAME during linking

.imports NAME:
  The c-file that corresponds with this vfmanifest file,
  requires the module NAME during linking

*)

  let create_manifest_file() =
    let manifest_filename = Filename.chop_extension path ^ ".vfmanifest" in
    let qualified_path path' =
      qualified_path options.option_vroots path (Filename.dirname path', Filename.basename path')
    in
    let sorted_lines symbol protos =
      let lines =
        protos |> List.map begin fun (g, ((path, _, _), _)) ->
          qualified_path path ^ (Char.escaped symbol) ^ g
        end
      in
      List.sort compare lines
    in
    let sorted_module_lines modules =
      let lines =
        modules |> List.map begin fun (name, _) -> name
        end
      in
      List.sort compare lines
    in
    let sorted_delayed_definition_lines defs =
      let lines =
        defs |> List.map begin fun (x, ((declpath, _, _), _), ((defpath, _, _), _)) ->
          Printf.sprintf "%s@%s#%s" (qualified_path defpath) (qualified_path declpath) x
        end
      in
      List.sort compare lines
    in
    let lines =
      List.map (fun line -> ".requires " ^ line) (sorted_lines '#' !prototypes_used)
      @
      List.map (fun line -> ".provides " ^ line) (sorted_lines '#' prototypes_implemented)
      @
      List.map (fun line -> ".structure " ^ line) (sorted_delayed_definition_lines structures_defined)
      @
      List.map (fun line -> ".predicate " ^ line) (sorted_delayed_definition_lines nonabstract_predicates)
      @
      List.sort compare
        begin
          List.map
            begin fun (fn, ((header, _, _), _), ftn, ftargs, unloadable) ->
              Printf.sprintf
                ".provides %s#%s : %s(%s)%s" (qualified_path header) fn ftn (String.concat "," ftargs) (if unloadable then " unloadable" else "")
            end
            functypes_implemented
        end
      @
      List.map (fun line -> ".imports module " ^ line)  (sorted_module_lines modules_imported)
      @
      [".produces module " ^ current_module_name]
    in
    if emit_manifest then
      let file = open_out manifest_filename in
      do_finally (fun () ->
        List.iter (fun line -> output_string file (line ^ "\n")) lines
      ) (fun () -> close_out file)
    else
      manifest_map := (manifest_filename, lines)::!manifest_map
  
  let () =
    if file_type path <> Java then
      create_manifest_file()
    else
      if Filename.check_suffix path ".jarsrc" then
        create_jardeps_file()
  
end

(** Verifies the .c/.jarsrc/.scala file at path [path].
    Uses the SMT solver [ctxt].
    Reports syntax highlighting regions using the callback [reportRange].
    Stops at source line [breakpoint], if not None.
    This function is generic in the types of SMT solver types, symbols, and terms.
    *)
let verify_program_core (* ?verify_program_core *)
    ?(emitter_callback : package list -> unit = fun _ -> ())
    (type typenode') (type symbol') (type termnode')  (* Explicit type parameters; new in OCaml 3.12 *)
    (ctxt: (typenode', symbol', termnode') Proverapi.context)
    (options : options)
    (program_path : string)
    (reportRange : range_kind -> loc -> unit)
    (reportUseSite : decl_kind -> loc -> loc -> unit)
    (reportExecutionForest : node list ref -> unit)
    (breakpoint : (string * int) option)
    (targetPath : int list option) : unit =

  let module VP = VerifyProgram(struct
    let emitter_callback = emitter_callback
    type typenode = typenode'
    type symbol = symbol'
    type termnode = termnode'
    let ctxt = ctxt
    let options = options
    let program_path = program_path
    let reportRange = reportRange
    let reportUseSite = reportUseSite
    let reportExecutionForest = reportExecutionForest
    let breakpoint = breakpoint
    let targetPath = targetPath
  end) in
  ()

(* Region: prover selection *)

class virtual prover_client =
  object
    method virtual run: 'typenode 'symbol 'termnode. ('typenode, 'symbol, 'termnode) Proverapi.context -> Stats.stats
  end

let prover_table: (string * (string * (prover_client -> Stats.stats))) list ref = ref []

let register_prover name banner f =
  prover_table := (name, (banner, f))::!prover_table

let prover_banners () = String.concat "" (List.map (fun (_, (banner, _)) -> banner) !prover_table)

let banner () =
  "VeriFast " ^ Vfversion.version ^ " for C and Java (released " ^ Vfversion.release_date ^ ") <http://www.cs.kuleuven.be/~bartj/verifast/>\n" ^
  "By Bart Jacobs <http://www.cs.kuleuven.be/~bartj/>, Jan Smans <http://www.cs.kuleuven.be/~jans/>, and Frank Piessens, with contributions by Pieter Agten, Cedric Cuypers, Lieven Desmet, Jan Tobias Muehlberg, Willem Penninckx, Pieter Philippaerts, Amin Timany, Thomas Van Eyck, Gijs Vanspauwen, and Frederic Vogels" ^
  prover_banners ()

let lookup_prover prover =
  match prover with
    None ->
    begin
      match !prover_table with
        [] -> assert false
      | (_, (_, f))::_ -> f
    end
  | Some name ->
    begin
      match try_assoc name !prover_table with
        None -> failwith ("No such prover: " ^ name)
      | Some (banner, f) -> f
    end
      
let verify_program (* ?verify_program *)
    ?(emitter_callback : package list -> unit = fun _ -> ())
    (prover : string option)
    (options : options)
    (path : string)
    (reportRange : range_kind -> loc -> unit)
    (reportUseSite : decl_kind -> loc -> loc -> unit)
    (reportExecutionForest : node list ref -> unit)
    (breakpoint : (string * int) option)
    (targetPath : int list option) : Stats.stats =
  lookup_prover prover
    (object
       method run: 'typenode 'symbol 'termnode. ('typenode, 'symbol, 'termnode) Proverapi.context -> Stats.stats =
         fun ctxt -> clear_stats ();
                     verify_program_core ~emitter_callback:emitter_callback ctxt options path reportRange reportUseSite reportExecutionForest breakpoint targetPath;
                     !stats
     end)

(* Region: linker *)

let remove_dups bs =
  let rec iter bs0 bs =
    match bs with
      [] -> List.rev bs0
    | (x, v)::bs ->
      if List.mem_assoc x bs0 then iter bs0 bs else iter ((x, v)::bs0) bs
  in
  iter [] bs

exception LinkError of string

exception FileNotFound

let read_file_lines path =
  if Sys.file_exists path then
    let file = open_in path in
    do_finally (fun () ->
      let rec iter () =
        try
          let line = input_line file in
          let n = String.length line in
          let line = if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line in
          line::iter()
        with
          End_of_file -> []
      in
      iter()
    ) (fun () -> close_in file)
  else raise FileNotFound

let parse_line line =
  let space = String.index line ' ' in
  let command = String.sub line 0 space in
  let symbol = String.sub line (space + 1) (String.length line - space - 1) in
  let symbol = string_map (function '\\' -> '/' | c -> c) symbol in
  (command, symbol)

let link_program vroots library_paths isLibrary allModulepaths dllManifest exports =
  let mainModulePath = match List.rev allModulepaths with [] -> raise (LinkError "DLL must contain at least one module.") | m::_ -> m in
  let mainModuleName = try Filename.chop_extension (Filename.basename mainModulePath) with Invalid_argument _ -> raise (CompilationError "file without extension") in
  let mainModuleManifest =
    match dllManifest with
    | Some (Some n) -> n
    | _ -> Filename.chop_extension mainModulePath ^ ".dll.vfmanifest"
  in
  let rebase_path manifest_path path =
    if path = "" then "" else qualified_path vroots mainModuleManifest (Filename.dirname manifest_path, path)
  in
  let split_manifest_entry symbol entry modulepath =
    let (first, second) = split_around_char entry symbol in
    if second = "" then
      raise (LinkError ("Manifest file '" ^ modulepath ^ "': error parsing line: cannot find symbol '" ^ (Char.escaped symbol) ^ "'."));
    (first, second)
  in
  let consume msg x xs =
    let rec iter xs' xs =
      match xs with
        [] -> raise (LinkError (msg x))
      | (x', modp')::xs -> if x = x' then xs' @ xs else iter ((x', modp')::xs') xs
    in
    iter [] xs
  in
  let get_lines_from_file file =
    let get_lines file =
      (file, List.filter (fun str -> str.[0] <> '#') (read_file_lines file))
    in
    try
      get_lines file
    with FileNotFound ->
      try 
        let file = replace_vroot vroots file in
        get_lines file
      with FileNotFound ->
        try
          let rec search_library_paths library_paths file =
            match library_paths with 
            | path::rest ->
              let search_path = concat path file in
              if Sys.file_exists search_path then
                get_lines search_path
              else
               search_library_paths rest file
            | [] -> raise FileNotFound
          in
          search_library_paths library_paths file
        with FileNotFound ->
          failwith ("VeriFast link phase error: could not find .vfmanifest file '" ^ file ^ 
                    "'. Re-verify the module using the -emit_vfmanifest or -emit_dll_vfmanifest option.")
  in
  let manifest_corruption modulepath msg =
    raise (LinkError ("Manifest file for '" ^ modulepath ^ "' is corrupted: " ^ msg))
  in
  let rec iter (impls, structs, preds) mods modulepaths =
    match modulepaths with
      [] -> ((impls, structs, preds), mods)
    | modulepath::modulepaths ->
      let manifest_path = 
        try Filename.chop_extension modulepath ^ ".vfmanifest" with
          Invalid_argument  _ -> raise (CompilationError "file without extension")
      in
      let is_generated_manifest = List.mem_assoc manifest_path !manifest_map in 
      let (manifest_path, lines) =
        if is_generated_manifest then
          (manifest_path, List.assoc manifest_path !manifest_map)
        else
          get_lines_from_file manifest_path
      in
      let rebase_path path = rebase_path manifest_path path in
      let check_file_name path =
        if path <> "" && (String.get path 0) <> '.' && (String.get path 0) <> '/' && (String.get path 0) <> '\\' then
        begin
          let root::_ = split (fun c -> c = '/' || c = '\\') path in
          match try_assoc0 root vroots with
          | Some _ -> ()
          | None -> manifest_corruption modulepath ("relative path should start with ./ or ../")
        end;
        let absolute_path =
          let path = (replace_vroot vroots (reduce_path path)) in
          let manifest_dir = (replace_vroot vroots (reduce_path (Filename.dirname manifest_path))) in
          if not (Filename.is_relative path) then path else 
          begin
            let path = reduce_path (manifest_dir ^ "/" ^ path) in
            if not (Filename.is_relative path) then path
            else reduce_path (cwd ^ "/" ^ path)
          end
        in
        if (not (Sys.file_exists absolute_path)) then 
          manifest_corruption modulepath ("file does not exist " ^ path ^ " (absolute: " ^ absolute_path ^ ")")
      in
      let rec iter0 (impls', structs', preds') mods' lines =
        match lines with
          [] -> iter (impls', structs', preds') mods' modulepaths
        | line::lines ->
          let (command, symbol) = parse_line line in
          begin
            match command with
            | ".structure"  ->
              begin
                let (def_file, dcl_part) = split_manifest_entry '@' symbol manifest_path in
                if not is_generated_manifest then
                begin
                  let (dcl_file, name) = split_around_char dcl_part '#' in
                  if name = "" then manifest_corruption modulepath ("empty structure entry");
                  if dcl_file = "" then manifest_corruption modulepath ("empty structure declaration file entry");
                  check_file_name def_file;
                  check_file_name dcl_file;
                end;
                let dcl_part = rebase_path dcl_part in
                let def_file = rebase_path def_file in
                let entry = (dcl_part, (def_file, manifest_path)) in
                match try_assoc dcl_part structs with
                | Some (def_file2, _) ->
                  if def_file <> def_file2 then 
                    raise (LinkError ("Module '" ^ modulepath ^ "': Structure " ^ dcl_part ^ " is defined twice."))
                  else 
                    iter0 (impls', structs', preds') mods' lines
                | None -> iter0 (impls', entry::structs', preds') mods' lines
              end
            | ".predicate" -> 
              begin
                let (def_file, dcl_part) = split_manifest_entry '@' symbol manifest_path in
                if not is_generated_manifest then
                begin
                  let (dcl_file, name) = split_around_char dcl_part '#' in
                  if name = "" then manifest_corruption modulepath ("empty predicate entry");
                  if dcl_file = "" then manifest_corruption modulepath ("empty predicate declaration file entry");
                  check_file_name def_file;
                  check_file_name dcl_file;
                end;
                let dcl_part = rebase_path dcl_part in
                let def_file = rebase_path def_file in
                let entry = (dcl_part, (def_file, manifest_path)) in
                match try_assoc dcl_part preds with
                | Some (def_file2, _) ->
                  if def_file <> def_file2 then
                    raise (LinkError ("Module '" ^ modulepath ^ "': Predicates " ^ dcl_part ^ " is given a body twice."))
                  else
                    iter0 (impls', structs', preds') mods' lines
                | None -> iter0 (impls', structs', entry::preds') mods' lines
              end
            | ".provides"   ->
              begin
                if not is_generated_manifest then
                begin
                  let (path, name) = split_around_char symbol '#' in
                  if name = "" then manifest_corruption modulepath ("empty provides entry");
                  if path = "" then manifest_corruption modulepath ("empty provides file entry");
                  check_file_name path;
                end;
                let symbol = rebase_path symbol in
                let entry = (symbol, manifest_path) in
                match try_assoc0 symbol impls' with
                | Some _ -> raise (LinkError ("Module '" ^ modulepath ^ "': Function " ^ symbol ^ " is implemented twice."))
                | None -> iter0 (entry::impls', structs', preds') mods' lines  
              end
            | ".requires"   ->
              begin
                if not is_generated_manifest then
                begin
                  let (path, name) = split_around_char symbol '#' in
                  if name = "" then manifest_corruption modulepath ("empty requires entry");
                  if path = "" then manifest_corruption modulepath ("empty requires file entry");
                  check_file_name path;
                end;
                let symbol = rebase_path symbol in
                match try_assoc0 symbol impls' with
                | Some _ -> iter0 (impls', structs', preds') mods' lines 
                | None -> raise (LinkError ("Module '" ^ modulepath ^ "': unsatisfied requirement '" ^ symbol ^ "'."))
              end
            | ".produces" ->
              iter0 (impls', structs', preds') ((symbol, manifest_path)::mods') lines
            | ".imports" ->
              let mods'' =
                consume (fun x -> "Module '" ^ modulepath ^ "': unsatisfied import '" ^ x ^ "'.") symbol mods'
              in
              iter0 (impls', structs', preds') mods'' lines
            | _ -> manifest_corruption modulepath ("cannot parse line " ^ line)
          end
      in
      iter0 (impls, structs, preds) mods lines
  in
  let ((impls, structs, preds), mods) = iter ([], [], []) [] allModulepaths in
  let mods =
    if not isLibrary then
    begin
      let main = "CRT/prelude.h#main : main()" in 
      let main_full = (Printf.sprintf "CRT/prelude.h#main : main_full(%s)" mainModuleName) in
      match (try_assoc main impls, try_assoc main_full impls) with
      | (None, None) ->
          raise (LinkError ("Program does not implement a function 'main' that implements function type 'main' or 'main_full' declared in prelude.h. Use the '-shared' option to suppress this error."))
      | _ -> consume (fun _ -> "Could not consume the main module") ("module " ^ mainModuleName) mods
    end
    else
      mods
  in
  let (impls, mods) =
    let rec iter (impls, mods) exports =
      match exports with
        [] -> (impls, mods)
      | exportPath::exports ->
        let lines = try read_file_lines exportPath with FileNotFound -> failwith ("Could not find export manifest file '" ^ exportPath ^ "'") in
        let rec iter' (impls, mods) lines =
          match lines with
            [] -> (impls, mods)
          | line::lines ->
            let (command, symbol) = parse_line line in
            match command with
            | ".provides" ->
              begin
                let symbol = rebase_path exportPath symbol in
                match try_assoc0 symbol impls with
                | Some _ -> iter' (impls, mods) lines
                | None ->  raise (LinkError (Printf.sprintf "Unsatisfied requirement '%s' in export manifest '%s'" symbol exportPath))
              end
            | ".produces" ->
              let mods = consume (fun s -> Printf.sprintf "Unsatisfied requirement '%s' in export manifest '%s'" s exportPath) symbol mods in
              iter' (impls, mods) lines
            | _ -> raise (LinkError ("Incorrect export manifest " ^ exportPath))
        in
        let (impls, mods) = iter' (impls, mods) lines in
        iter (impls, mods) exports
    in
    iter (impls, mods) exports
  in
  match dllManifest with None -> () | Some(_) ->
  begin
    try
      let manifestFile = open_out mainModuleManifest in
      let is_dll def = Filename.check_suffix def ".dll.vfmanifest" in
      let print_requires_or_provides (sym, modp) =
        if is_dll modp then
          Printf.fprintf manifestFile ".requires %s\n" sym
        else
          Printf.fprintf manifestFile ".provides %s\n" sym
      in
      let print_if_necesarry label (dcl_file, (def_file, modp)) =
        let entry = Printf.sprintf "%s %s@%s" label def_file dcl_file in
        let (dcl_file, _) = split_around_char dcl_file '#' in
        if not (is_dll modp) || not (Filename.check_suffix dcl_file ".c") then
          Printf.fprintf manifestFile "%s\n" entry
      in
      let print_module (m, mdop) =
        if is_dll mdop then
          Printf.fprintf manifestFile ".imports %s\n" m
        else
          Printf.fprintf manifestFile ".produces %s\n" m
      in
      impls   |> List.iter print_requires_or_provides;
      structs |> List.iter (print_if_necesarry ".structure");
      preds   |> List.iter (print_if_necesarry ".predicate");
      mods    |> List.iter print_module;
      close_out manifestFile
    with
      Sys_error s -> raise (LinkError (Printf.sprintf "Could not create DLL manifest file '%s': %s" mainModuleManifest s))
  end;
  Printf.fprintf stderr "Written %s\n" mainModuleManifest
