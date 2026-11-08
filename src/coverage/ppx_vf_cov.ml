open Ppxlib

let should_instrument loc =
  (not loc.Location.loc_ghost) && loc.Location.loc_start.pos_fname <> ""

let wrap_hit mod_var_name loc idx expr =
  let ghost_loc = { loc with Location.loc_ghost = true } in
  let hit_fn = Ast_builder.Default.evar ~loc:ghost_loc "Vf_cov_runtime.hit" in
  let mod_id_e = Ast_builder.Default.evar ~loc:ghost_loc mod_var_name in
  let idx_e = Ast_builder.Default.eint ~loc:ghost_loc idx in
  let hit_expr = Ast_builder.Default.eapply ~loc:ghost_loc hit_fn [mod_id_e; idx_e] in
  Ast_builder.Default.pexp_sequence ~loc:ghost_loc hit_expr expr

let rec flatten_longident = function
  | Lident s -> [s]
  | Ldot (p, s) -> flatten_longident p @ [s]
  | Lapply (p1, p2) -> flatten_longident p1 @ flatten_longident p2

let last_ident = function
  | Lident s | Ldot (_, s) -> s
  | Lapply _ -> ""

let string_contains needle str =
  let nlen = String.length needle in
  let slen = String.length str in
  let rec loop i =
    if i + nlen > slen then false
    else if String.sub str i nlen = needle then true
    else loop (i + 1)
  in
  loop 0

class ppx_parser_internal_detector = object (self)
  inherit [bool] Ast_traverse.fold as super

  method! expression e acc =
    if acc then true
    else
      match e.pexp_desc with
      | Pexp_ident { txt = id; _ } ->
        let parts = flatten_longident id in
        if List.exists (fun p ->
          p = "Stream" || p = "__strm" || p = "ParseException" || p = "LexerException"
        ) parts then true
        else (
          let last = last_ident id in
          if last = "peek" || last = "junk" || last = "Failure" then true
          else super#expression e acc
        )
      | Pexp_construct ({ txt = id; _ }, _) ->
        let parts = flatten_longident id in
        if List.exists (fun p ->
          p = "Stream" || p = "__strm" || p = "ParseException" || p = "LexerException" || p = "Failure"
        ) parts then true
        else super#expression e acc
      | _ -> super#expression e acc
end

let contains_ppx_parser_internal e =
  let detector = new ppx_parser_internal_detector in
  detector#expression e false

let ident_is_uninstrumented_fn id =
  let needles = [
    "raise"; "raise_notrace"; "failwith"; "invalid_arg"; "exit"; "error";
    "static_error"; "check_error"; "type_error"; "syntax_error"; "parse_error";
    "assert_false"; "not_supported"; "todo"; "unimplemented"; "unreachable";
    "report"; "warn"; "print"; "printf"; "fprintf"; "eprintf"; "sprintf";
    "junk"; "peek"; "abort"; "die"; "crash"; "fatal"; "unsupported";
    "bad_instruction"; "dead_code"; "cannot_prove";
    "trace"; "trace_entering"; "trace_exiting"; "printff"; "debug"; "log"; "dump";
    "cannot_prove"; "fallback"; "refinement_check_failure"; "refinementcheckfailure"
  ] in
  let contains_needle str =
    let lower = String.lowercase_ascii str in
    List.exists (fun needle -> string_contains needle lower) needles
  in
  let parts = flatten_longident id in
  List.exists contains_needle parts

let rec get_root_fn e =
  match e.pexp_desc with
  | Pexp_apply (fn, _) -> get_root_fn fn
  | _ -> e

let rec is_direct_uninstrumented_expr e =
  match e.pexp_desc with
  | Pexp_assert _ -> true
  | Pexp_unreachable -> true
  | Pexp_construct ({ txt = id; _ }, _) ->
    let s = last_ident id in
    s = "Error" || s = "None" || s = "Dummy" || s = "Failure" || s = "RefinementCheckFailure"
  | Pexp_send (_, { txt = m; _ }) ->
    let lower = String.lowercase_ascii m in
    List.exists (fun needle -> string_contains needle lower) [
      "assert_false"; "trace"; "trace_entering"; "trace_exiting";
      "print"; "printf"; "printff"; "debug"; "log"; "dump"
    ]
  | Pexp_apply _ ->
    let root = get_root_fn e in
    (match root.pexp_desc with
     | Pexp_ident { txt = id; _ } -> ident_is_uninstrumented_fn id
     | Pexp_send (_, { txt = m; _ }) ->
       let lower = String.lowercase_ascii m in
       List.exists (fun needle -> string_contains needle lower) [
         "assert_false"; "trace"; "trace_entering"; "trace_exiting";
         "print"; "printf"; "printff"; "debug"; "log"; "dump"
       ]
     | _ -> false)
  | _ -> contains_ppx_parser_internal e

let rec is_uninstrumented_rhs e =
  if is_direct_uninstrumented_expr e then true
  else
    match e.pexp_desc with
    | Pexp_sequence (e1, e2) ->
      is_uninstrumented_rhs e2 || is_direct_uninstrumented_expr e1
    | Pexp_let (_, _, e2)
    | Pexp_letmodule (_, _, e2)
    | Pexp_letexception (_, e2)
    | Pexp_open (_, e2)
    | Pexp_constraint (e2, _)
    | Pexp_coerce (e2, _, _)
    | Pexp_fun (_, _, _, e2) ->
      is_uninstrumented_rhs e2
    | _ -> false

let rec is_wildcard_or_error_pat pat =
  match pat.ppat_desc with
  | Ppat_any -> true
  | Ppat_var _ -> true
  | Ppat_exception _ -> true
  | Ppat_alias (p, _) -> is_wildcard_or_error_pat p
  | Ppat_constraint (p, _) -> is_wildcard_or_error_pat p
  | Ppat_construct ({ txt = id; _ }, _) ->
    let s = last_ident id in
    List.mem s [
      "Error"; "Failure"; "StaticError"; "CompilationError";
      "ParseException"; "LexerException"; "Not_found";
      "End_of_file"; "Invalid_argument"; "Sys_error";
      "RefinementCheckFailure"; "None"
    ]
  | _ -> false

let is_uninstrumented_case c =
  is_uninstrumented_rhs c.pc_rhs ||
  c.pc_guard <> None ||
  is_wildcard_or_error_pat c.pc_lhs

class cov_mapper mod_var_name file_ref points_ref count_ref = object (self)
  inherit Ast_traverse.map as super

  method! attribute attr = attr

  method! value_binding vb =
    if !file_ref = "" && vb.pvb_loc.Location.loc_start.pos_fname <> "" then
      file_ref := vb.pvb_loc.Location.loc_start.pos_fname;
    let rec is_uninstrumented_binding pat =
      match pat.ppat_desc with
      | Ppat_var { txt = name; _ } ->
        let base = Filename.basename !file_ref in
        ((string_contains "refinement_checker" !file_ref || base = "refinement_checker.ml") &&
         (string_contains "string_of_" name || name = "string_of_ty" || name = "string_of_command" ||
          name = "check_rvalue_refines_rvalue" || name = "decode_generic_param")) ||
        (base = "vf_mir_translator.ml" &&
         (string_contains "string_of_" name || name = "string_of_decoded_type")) ||
        (base = "verifast1.ml" &&
         (name = "print_dbg_info" || name = "noop_callbacks" || name = "string_of_typepreddefmap_entry")) ||
        (base = "assertions.ml" &&
         (name = "string_of_chunk_asn" || name = "string_of_asn")) ||
        (base = "redux.ml" &&
         (name = "printff" || name = "indent" || name = "unindent" ||
          name = "trace" || name = "trace_entering" || name = "trace_exiting" ||
          name = "print_expr" || name = "print_symexec_step"))
      | Ppat_constraint (p, _) -> is_uninstrumented_binding p
      | _ -> false
    in
    if is_uninstrumented_binding vb.pvb_pat then
      vb
    else
      super#value_binding vb

  method private record_point loc kind =
    if !file_ref = "" && loc.Location.loc_start.pos_fname <> "" then
      file_ref := loc.Location.loc_start.pos_fname;
    let idx = !count_ref in
    incr count_ref;
    let line = loc.Location.loc_start.pos_lnum in
    let col = loc.Location.loc_start.pos_cnum - loc.Location.loc_start.pos_bol in
    points_ref := (line, col, kind) :: !points_ref;
    idx

  method! case c =
    let pc_lhs = super#pattern c.pc_lhs in
    let pc_guard = c.pc_guard (* Do not instrument inside pattern guards *) in
    let rhs_loc = c.pc_rhs.pexp_loc in
    if is_uninstrumented_case c then
      { pc_lhs; pc_guard; pc_rhs = c.pc_rhs }
    else
      let mapped_rhs = super#expression c.pc_rhs in
      let pc_rhs =
        if should_instrument rhs_loc then
          let idx = self#record_point rhs_loc "case" in
          wrap_hit mod_var_name rhs_loc idx mapped_rhs
        else
          mapped_rhs
      in
      { pc_lhs; pc_guard; pc_rhs }

  method! expression expr =
    if is_direct_uninstrumented_expr expr then
      expr
    else
      match expr.pexp_desc with
      | Pexp_ifthenelse (cond, then_e, else_opt) ->
        let cond' = self#expression cond in
        let then_loc = then_e.pexp_loc in
        let then_e' =
          if is_uninstrumented_rhs then_e then
            then_e
          else
            let mapped_then = self#expression then_e in
            if should_instrument then_loc then
              let idx = self#record_point then_loc "then" in
              wrap_hit mod_var_name then_loc idx mapped_then
            else
              mapped_then
        in
        let else_opt' =
          match else_opt with
          | None -> None
          | Some else_e ->
            let else_loc = else_e.pexp_loc in
            let else_e' =
              if is_uninstrumented_rhs else_e then
                else_e
              else
                let mapped_else = self#expression else_e in
                if should_instrument else_loc then
                  let idx = self#record_point else_loc "else" in
                  wrap_hit mod_var_name else_loc idx mapped_else
                else
                  mapped_else
            in
            Some else_e'
        in
        { expr with pexp_desc = Pexp_ifthenelse (cond', then_e', else_opt') }
    | Pexp_while (cond, body) ->
      let cond' = self#expression cond in
      let body_loc = body.pexp_loc in
      let mapped_body = self#expression body in
      let body' =
        if should_instrument body_loc && not (is_uninstrumented_rhs body) then
          let idx = self#record_point body_loc "while" in
          wrap_hit mod_var_name body_loc idx mapped_body
        else
          mapped_body
      in
      { expr with pexp_desc = Pexp_while (cond', body') }

    | Pexp_for (pat, e1, e2, dir, body) ->
      let pat' = self#pattern pat in
      let e1' = self#expression e1 in
      let e2' = self#expression e2 in
      let body_loc = body.pexp_loc in
      let mapped_body = self#expression body in
      let body' =
        if should_instrument body_loc && not (is_uninstrumented_rhs body) then
          let idx = self#record_point body_loc "for" in
          wrap_hit mod_var_name body_loc idx mapped_body
        else
          mapped_body
      in
      { expr with pexp_desc = Pexp_for (pat', e1', e2', dir, body') }

    | Pexp_fun (lbl, def, pat, body) ->
      let pat' = self#pattern pat in
      let def' = Option.map self#expression def in
      let body' =
        match body.pexp_desc with
        | Pexp_fun _ | Pexp_newtype _ | Pexp_function _ | Pexp_constraint _ | Pexp_coerce _ ->
          self#expression body
        | _ ->
          let body_loc = body.pexp_loc in
          let mapped_body = self#expression body in
          if should_instrument body_loc && not (is_uninstrumented_rhs body) then
            let idx = self#record_point body_loc "fun" in
            wrap_hit mod_var_name body_loc idx mapped_body
          else
            mapped_body
      in
      { expr with pexp_desc = Pexp_fun (lbl, def', pat', body') }

    | Pexp_constraint (inner_e, ty) ->
      let inner_loc = inner_e.pexp_loc in
      let mapped_inner = self#expression inner_e in
      let inner_e' =
        match inner_e.pexp_desc with
        | Pexp_fun _ | Pexp_newtype _ | Pexp_function _ | Pexp_constraint _ | Pexp_coerce _ | Pexp_object _ | Pexp_pack _ ->
          mapped_inner
        | _ ->
          if should_instrument inner_loc && not (is_uninstrumented_rhs inner_e) then
            let idx = self#record_point inner_loc "fun" in
            wrap_hit mod_var_name inner_loc idx mapped_inner
          else
            mapped_inner
      in
      { expr with pexp_desc = Pexp_constraint (inner_e', ty) }

    | _ ->
      super#expression expr
end

let rec find_file_in_structure = function
  | [] -> ""
  | item :: rest ->
    let fname = item.pstr_loc.loc_start.pos_fname in
    if fname <> "" then fname else find_file_in_structure rest

let is_excluded_file file =
  let base = Filename.basename file in
  base = "vf_cov_runtime.ml" || base = "ppx_vf_cov.ml" || base = "vf_cov_report.ml" ||
  base = "vf_mir.ml" || base = "vf_mir_decoder.ml" || base = "stubs_ast.ml" ||
  (let parts = String.split_on_char '/' file in List.mem "java_frontend" parts) ||
  base = "annotation_type_checker.ml" || base = "ast_reader.ml" ||
  base = "communication.ml" || base = "general_ast.ml" ||
  base = "java_frontend.ml" || base = "java_frontend_bridge.ml" ||
  base = "misc.ml" ||
  (base = "ast_translator.ml" && (
    let dir = Filename.dirname file in
    string_contains "java_frontend" dir || dir = "java_frontend"
  )) ||
  base = "rust_fe.ml" ||
  (base = "frontend.ml" && (string_contains "refinement_checker" file || Filename.dirname file = "refinement_checker")) ||
  (base = "main.ml" && (string_contains "refinement_checker" file || Filename.dirname file = "refinement_checker")) ||
  base = "SExpressionEmitter.ml" || base = "ocaml_expr_of_ast.ml" || base = "rocq_of_ast.ml" || base = "stringifier.ml"

let transform_impl st =
  let initial_file = find_file_in_structure st in
  if initial_file = "" || is_excluded_file initial_file then
    st
  else
    let mod_var_name = Printf.sprintf "__vf_cov_mod_id_%08x" (Hashtbl.hash initial_file land 0x3fffffff) in
    let points_ref = ref [] in
    let count_ref = ref 0 in
    let file_ref = ref initial_file in
    let mapper = new cov_mapper mod_var_name file_ref points_ref count_ref in
    let st' = mapper#structure st in
    let points = List.rev !points_ref in
    let file = !file_ref in
    if points = [] || is_excluded_file file then
      st'
    else
      let reg_loc = { Location.none with Location.loc_ghost = true } in
      let fn = Ast_builder.Default.evar ~loc:reg_loc "Vf_cov_runtime.register_module" in
      let file_arg = (Labelled "file", Ast_builder.Default.estring ~loc:reg_loc file) in
      let pts_exprs =
        List.map (fun (l, c, k) ->
          Ast_builder.Default.pexp_tuple ~loc:reg_loc [
            Ast_builder.Default.eint ~loc:reg_loc l;
            Ast_builder.Default.eint ~loc:reg_loc c;
            Ast_builder.Default.estring ~loc:reg_loc k;
          ]
        ) points
      in
      let pts_arr = Ast_builder.Default.pexp_array ~loc:reg_loc pts_exprs in
      let pts_arg = (Labelled "points", pts_arr) in
      let call = Ast_builder.Default.pexp_apply ~loc:reg_loc fn [file_arg; pts_arg] in
      let pat = Ast_builder.Default.ppat_var ~loc:reg_loc { loc = reg_loc; txt = mod_var_name } in
      let vb = Ast_builder.Default.value_binding ~loc:reg_loc ~pat ~expr:call in
      let reg_item = Ast_builder.Default.pstr_value ~loc:reg_loc Nonrecursive [vb] in
      reg_item :: st'

let () =
  Driver.register_transformation "vf_cov" ~impl:transform_impl
