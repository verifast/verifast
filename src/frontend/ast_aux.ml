open Ocaml_aux
open Ast

let list_to_sep_conj asns init =
  let f_aux (loc, asn) asn_opt =
    match asn_opt with
    | None -> Some asn
    | Some asn1 -> Some (Sep (loc, asn, asn1))
  in
  List.fold_right f_aux asns init

let decl_loc_name_and_name_setter (d : decl) =
  match d with
  | Inductive (loc, name, tparams, ctors) ->
      Some (loc, name, fun name -> Inductive (loc, name, tparams, ctors))
  | Struct (loc, name, tparams, definition_opt, attrs) ->
      Some
        ( loc,
          name,
          fun new_name -> Struct (loc, new_name, tparams, definition_opt, attrs)
        )
  | AbstractTypeDecl (l, x) -> Some (l, x, fun x -> AbstractTypeDecl (l, x))
  | TypedefDecl (l, te, x, tparams) ->
      Some (l, x, fun x -> TypedefDecl (l, te, x, tparams))
  | PredFamilyDecl
      (l, g, tparams, nbIndices, pts, inputParamCount, inductiveness) ->
      Some
        ( l,
          g,
          fun g ->
            PredFamilyDecl
              (l, g, tparams, nbIndices, pts, inputParamCount, inductiveness) )
  | PredFamilyInstanceDecl (l, g, tparams, indices, ps, body) ->
      Some
        ( l,
          g,
          fun g -> PredFamilyInstanceDecl (l, g, tparams, indices, ps, body) )
  | PredCtorDecl (l, g, tparams, ctor_ps, ps, inputParamCount, body) ->
      Some
        ( l,
          g,
          fun g ->
            PredCtorDecl (l, g, tparams, ctor_ps, ps, inputParamCount, body) )
  | FuncTypeDecl (l, gh, rt, ftn, tparams, ftxs, xs, contract) ->
      Some
        ( l,
          ftn,
          fun ftn -> FuncTypeDecl (l, gh, rt, ftn, tparams, ftxs, xs, contract)
        )
  | TypePredDef (l, tparams, tp, predName, rhs) -> None
  | Func
      ( l,
        k,
        tparams,
        rt,
        g,
        ps,
        nonghost_callers_only,
        ftclause,
        pre_post,
        terminates,
        body_opt,
        is_virtual,
        overrides ) ->
      Some
        ( l,
          g,
          fun new_name ->
            Func
              ( l,
                k,
                tparams,
                rt,
                new_name,
                ps,
                nonghost_callers_only,
                ftclause,
                pre_post,
                terminates,
                body_opt,
                is_virtual,
                overrides ) )

let decl_map_of (ds : decl list) =
  let rec iter mn ds cont =
    match ds with
    | [] -> cont ()
    | ModuleDecl (l, mn1, ilist, mds) :: ds ->
        iter (if mn = "" then mn1 else mn ^ "::" ^ mn1) mds @@ fun () ->
        iter mn ds cont
    | d :: ds -> (
        match decl_loc_name_and_name_setter d with
        | None -> iter mn ds cont
        | Some (_, dname, _) ->
            ((if mn = "" then dname else mn ^ "::" ^ dname), d)
            :: iter mn ds cont)
  in
  iter "" ds (fun () -> [])

let decl_map_contains_pred_fam_inst_or_pred_ctor_inst map name =
  map
  |> List.exists @@ function
     | ( name',
         ( Ast.PredFamilyInstanceDecl (_, _, _, _, _, _)
         | Ast.PredCtorDecl (_, _, _, _, _, _, _) ) )
       when name' = name ->
         true
     | _ -> false

let decl_name (d : decl) =
  match d with
  | Struct (loc, name, tparams, definition_opt, attrs) -> Some name
  | Func
      ( loc,
        kind,
        ty_params,
        ret_ty_op,
        name,
        params,
        nonghost_callers_only,
        implemented_function_ty_op,
        contract_op,
        terminates,
        body_op,
        is_virtual,
        overrides ) ->
      Some name
  | _ -> failwith "Todo: get Ast.decl name"

let decl_fields (d : decl) =
  match d with
  | Struct (loc, name, tparams, definition_opt, attrs) -> (
      match definition_opt with
      | Some (base_specs, fields, instance_pred_decls, is_polymorphic) ->
          Ok (Some fields)
      | None -> Ok None)
  | _ -> failwith "Todo: get Ast.decl fields"

let decl_loc (d : decl) =
  match d with
  | Struct (loc, name, tparams, definition_opt, attrs) -> loc
  | Func
      ( loc,
        kind,
        ty_params,
        ret_ty_op,
        name,
        params,
        nonghost_callers_only,
        implemented_function_ty_op,
        contract_op,
        terminates,
        body_op,
        is_virtual,
        overrides ) ->
      loc
  | _ -> failwith "Todo: get Ast.decl loc"

let field_name (f : field) =
  match f with
  | Field
      (loc, ghostness, ty, name, method_binding, visibility, is_final, expr_op)
    ->
      name

let field_ty (f : field) =
  match f with
  | Field
      (loc, ghostness, ty, name, method_binding, visibility, is_final, expr_op)
    ->
      ty

let field_loc (f : field) =
  match f with
  | Field
      (loc, ghostness, ty, name, method_binding, visibility, is_final, expr_op)
    ->
      loc

let is_adt_ty (t : type_expr) =
  match t with StructTypeExpr _ -> true | _ -> false

let adt_ty_name (adt : type_expr) =
  match adt with
  | StructTypeExpr (_, Some name, _, _, _) -> Ok name
  | _ -> failwith "adt_ty_name: Not an ADT"

let adt_type_name = function StructType (n, _) | InductiveType (n, _) -> Some n | _ -> None

let is_adt_type_ tp = Option.is_some @@ adt_type_name @@ tp

let sort_decls_lexically ds =
  List.sort
    (fun d d1 ->
      compare
        (Ast.lexed_loc @@ decl_loc @@ snd d)
        (Ast.lexed_loc @@ decl_loc @@ snd d1))
    ds
