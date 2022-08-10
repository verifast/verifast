module TestDataHardCoded = struct
  let c_func_main =
    let dloc = Ast.Lexed Ast.dummy_loc0 in
    let contract = Some (Ast.True dloc, Ast.True dloc) in
    Ast.Func
      ( dloc,
        Ast.Regular,
        [],
        Some (Ast.ManifestTypeExpr (dloc, Ast.Int (Ast.Signed, Ast.IntRank))),
        "main",
        [],
        false,
        None,
        contract,
        true,
        Some
          ( [
              Ast.ReturnStmt
                ( dloc,
                  Some
                    (Ast.IntLit
                       ( dloc,
                         Big_int.zero_big_int,
                         true (* decimal *),
                         false (* U suffix *),
                         Ast.NoLSuffix (* int literal*) )) );
            ],
            dloc ),
        Ast.Static,
        Ast.Package )
end

module Mir = struct
  type mutability = Mut | Not

  type ty_info = { vf_ty : Ast.type_expr }

  type local_decl = { mutability : mutability; id : string; ty : ty_info }

  type basic_block = {
    id : string;
    statements : Ast.stmt list;
    terminator : Ast.stmt;
  }

  type u_int_ty = USize | U8 | U16 | U32 | U64 | U128

  let u_int_ty_bits_len (uit : u_int_ty) =
    match uit with
    | USize ->
        Error
          (`UIntTyBitsLen
            "The number of bits of a usize value is not specified by Rust")
    | U8 -> Ok 8
    | U16 -> Ok 16
    | U32 -> Ok 32
    | U64 -> Ok 64
    | U128 -> Ok 128
end

module TrTyTuple = struct
  let make_tuple_type_name tys =
    if List.length tys != 0 then
      failwith "Todo: Tuple Ty is not implemented yet"
    else "std_tuple_0_"

  let make_tuple_type_decl name tys loc =
    if List.length tys != 0 then
      failwith "Todo: Tuple Ty is not implemented yet"
    else Ast.Struct (loc, name, Some (* field list *) [], (* attr list *) [])
end

module TrTyInt = struct
  let calc_int_rank (bits : int) =
    let n = Float.log2 @@ float_of_int @@ bits in
    let n_is_int = FP_zero == Float.classify_float @@ fst @@ Float.modf @@ n in
    if not (bits > 0 && n_is_int && int_of_float n >= 3) then
      Error
        (`CalcIntRank
          "The number of bits of an integer should be non-negative and equal \
           to 2^n such that n>=3")
    else
      let bytes = bits / 8 in
      let rank = int_of_float @@ Float.log2 @@ float_of_int @@ bytes in
      Ok rank
end

module type VF_MIR_TRANSLATOR_ARGS = sig
  val data_model_opt : Ast.data_model option

  val report_should_fail : string -> Ast.loc0 -> unit

  val report_range : Lexer.range_kind -> Ast.loc0 -> unit
end

module Make (Args : VF_MIR_TRANSLATOR_ARGS) = struct
  open Ocaml_aux
  module VfMirAnnotParser = Vf_mir_annot_parser.Make (Args)
  module VfMirStub = Vf_mir.Make (Capnp.BytesMessage)
  module VfMirRd = VfMirStub.Reader.VfMir

  (* Bodies *)
  module BodyRd = VfMirStub.Reader.Body
  module ContractRd = BodyRd.Contract
  module AnnotationRd = BodyRd.Annotation
  module LocalDeclRd = BodyRd.LocalDecl
  module MutabilityRd = BodyRd.Mutability
  module LocalDeclIdRd = BodyRd.LocalDeclId
  module BasicBlockRd = BodyRd.BasicBlock
  module BasicBlockIdRd = BodyRd.BasicBlockId
  module TerminatorRd = BasicBlockRd.Terminator
  module TerminatorKindRd = TerminatorRd.TerminatorKind
  module FnCallDataRd = TerminatorKindRd.FnCallData
  module OperandRd = BasicBlockRd.Operand
  module ConstantRd = BasicBlockRd.Constant
  module ConstantKindRd = ConstantRd.ConstantKind

  (* Types *)
  module TyRd = VfMirStub.Reader.Ty
  module UIntTyRd = TyRd.UIntTy
  module AdtTyRd = TyRd.AdtTy
  module AdtDefIdRd = TyRd.AdtDefId

  (* Ghost Type Declarations *)
  module GhostTyDecls = Map.Make (String)

  type gh_ty_decls = Ast.decl GhostTyDecls.t

  let translate_contract (contract_cpn : ContractRd.t) =
    let annots_cpn = ContractRd.annotations_get_list contract_cpn in
    let annots = List.map AnnotationRd.raw_get annots_cpn in
    VfMirAnnotParser.parse_func_contract annots
  (* Todo: VeriFast parser throws exceptions. we should catch them and use our own error handling scheme *)

  let translate_mutability (mutability_cpn : MutabilityRd.t) =
    match MutabilityRd.get mutability_cpn with
    | Mut -> Ok Mir.Mut
    | Not -> Ok Mir.Not
    | Undefined _ -> Error (`TrMut "Unknown Mir mutability discriminator")

  let u_size_rank =
    match Args.data_model_opt with
    | None -> Ast.PtrRank
    | Some data_model -> Ast.LitRank data_model.ptr_rank

  let translate_u_int_ty (u_int_ty_cpn : UIntTyRd.t) =
    let dloc = Ast.Lexed Ast.dummy_loc0 in
    let calc_rank ui =
      let* bits = Mir.u_int_ty_bits_len ui in
      let* rank = TrTyInt.calc_int_rank bits in
      Ok (Ast.LitRank rank)
    in
    let* rank =
      match UIntTyRd.get u_int_ty_cpn with
      | USize -> Ok u_size_rank
      | U8 -> calc_rank Mir.U8
      | U16 -> calc_rank Mir.U16
      | U32 -> calc_rank Mir.U32
      | U64 -> calc_rank Mir.U64
      | U128 -> calc_rank Mir.U128
      | Undefined _ -> Error (`TrUIntTy "Unknown Rust unsigned int type")
    in
    let ty_info : Mir.ty_info =
      { vf_ty = Ast.ManifestTypeExpr (dloc, Ast.Int (Ast.Unsigned, rank)) }
    in
    Ok ty_info

  let translate_adt_ty (adt_ty_cpn : AdtTyRd.t) =
    let dloc = Ast.Lexed Ast.dummy_loc0 in
    let open AdtTyRd in
    let id_cpn = id_get adt_ty_cpn in
    let def_path = AdtDefIdRd.name_get id_cpn in
    match def_path with
    | "std::alloc::Layout" ->
        let substs_cpn = substs_get_list adt_ty_cpn in
        if List.length substs_cpn > 0 then
          failwith (def_path ^ " does not have any generic parameter")
        else
          let ty_info : Mir.ty_info =
            {
              vf_ty =
                Ast.ManifestTypeExpr (dloc, Ast.Int (Ast.Unsigned, u_size_rank));
            }
          in
          Ok ty_info
    | _ -> failwith "Todo: Unsupported Adt"

  let translate_ty (ty_cpn : TyRd.t) (gh_ty_decls : gh_ty_decls ref) =
    let open TyRd in
    let dloc = Ast.Lexed Ast.dummy_loc0 in
    let kind_cpn = kind_get ty_cpn in
    match TyRd.TyKind.get kind_cpn with
    | Bool ->
        let ty_info : Mir.ty_info =
          { vf_ty = Ast.ManifestTypeExpr (dloc, Ast.Bool) }
        in
        Ok ty_info
    | Int int_ty_cpn -> failwith "Todo: Int Ty is not implemented yet"
    | UInt u_int_ty_cpn -> translate_u_int_ty u_int_ty_cpn
    | Adt adt_ty_cpn -> translate_adt_ty adt_ty_cpn
    | RawPtr ty1_cpn -> failwith "Todo: Raw Ptr Ty is not implemented yet"
    | Tuple substs_cpn ->
        if Capnp.Array.length substs_cpn != 0 then
          failwith "Todo: Tuple Ty is not implemented yet"
        else
          let name = TrTyTuple.make_tuple_type_name [] in

          (* TODO @Nima: std_tuple_0_ type is declared in prelude_rust_.h.
             We should come up with a better arrangement for these ghost types. *)
          (* (if not @@ GhostTyDecls.exists (fun n _ -> n = name) !gh_ty_decls then
             let decl = TrTyTuple.make_tuple_type_decl name [] Ast.DummyLoc in
             gh_ty_decls := GhostTyDecls.add name decl !gh_ty_decls); *)
          let ty_info : Mir.ty_info =
            { vf_ty = Ast.ManifestTypeExpr (dloc, Ast.StructType name) }
          in
          Ok ty_info
    | Undefined _ -> Error (`TrTy "Unknown Rust type kind")

  let translate_local_decl (local_decl_cpn : LocalDeclRd.t)
      (gh_ty_decls : gh_ty_decls ref) =
    let open LocalDeclRd in
    let mutability_cpn = mutability_get local_decl_cpn in
    let* mutability = translate_mutability mutability_cpn in
    let id_cpn = id_get local_decl_cpn in
    let id = LocalDeclIdRd.name_get id_cpn in
    let ty_cpn = ty_get local_decl_cpn in
    let* ty_info = translate_ty ty_cpn gh_ty_decls in
    let local_decl : Mir.local_decl = { mutability; id; ty = ty_info } in
    Ok local_decl

  let translate_to_vf_local_decl
      ({ mutability = mut; id; ty = ty_info } : Mir.local_decl) =
    let dloc = Ast.Lexed Ast.dummy_loc0 in
    Ast.DeclStmt
      ( dloc,
        [
          ( dloc,
            ty_info.vf_ty,
            id,
            None,
            ( (* indicates whether address is taken *) ref false,
              (* pointer to enclosing block's list of variables whose address is taken *)
              ref None ) );
        ] )

  let translate_fn_call (fn_call_data_cpn : FnCallDataRd.t) =
    let open FnCallDataRd in
    let func_cpn = func_get fn_call_data_cpn in
    let* constant_cpn =
      match OperandRd.get func_cpn with
      | OperandRd.Copy _ | OperandRd.Move _ ->
          Error (`TrFnCall "Invalid Mir Operand kind for function call")
      | OperandRd.Constant constant_cpn -> Ok constant_cpn
      | OperandRd.Undefined _ -> Error (`TrFnCall "Unknown Mir Operand kind")
    in
    let literal_cpn = ConstantRd.literal_get constant_cpn in
    Ok ()

  let translate_terminator_kind (ret_place_id : string)
      (tkind_cpn : TerminatorKindRd.t) =
    let open TerminatorKindRd in
    let dloc = Ast.Lexed Ast.dummy_loc0 in
    match get tkind_cpn with
    | Goto bblock_id_cpn -> failwith "Todo"
    | SwitchInt switch_int_data_cpn ->
        failwith "Todo: Mir SwitchInt terminator is not supported yet"
    | Return -> Ok (Ast.ReturnStmt (dloc, Some (Ast.Var (dloc, ret_place_id))))
    | Call fn_call_data_cpn -> failwith "Todo"
    | Undefined _ -> Error (`TrTerminatorKind "Unknown Mir terminator kind")

  let translate_terminator (ret_place_id : string)
      (terminator_cpn : TerminatorRd.t) =
    let open TerminatorRd in
    let source_info_cpn = source_info_get terminator_cpn in
    (* Todo @Nima: Translate source_info *)
    let terminator_kind_cpn = kind_get terminator_cpn in
    translate_terminator_kind ret_place_id terminator_kind_cpn

  let translate_basic_block (ret_place_id : string)
      (bblock_cpn : BasicBlockRd.t) =
    let open BasicBlockRd in
    let id_cpn = id_get bblock_cpn in
    let id = BasicBlockIdRd.name_get id_cpn in
    let statements_cpn = statements_get_list bblock_cpn in
    if List.length statements_cpn != 0 then
      failwith "Todo: Mir statements are not supported yet";
    let statements = [] in
    let terminator_cpn = terminator_get bblock_cpn in
    let* terminator = translate_terminator ret_place_id terminator_cpn in
    let bblock : Mir.basic_block = { id; statements; terminator } in
    Ok bblock

  let translate_to_vf_basic_block
      ({ id; statements; terminator } : Mir.basic_block) =
    let dloc = Ast.Lexed Ast.dummy_loc0 in
    Ast.LabelStmt (dloc, id) :: (statements @ [ terminator ])

  let translate_body (body_cpn : BodyRd.t) (gh_ty_decls : gh_ty_decls ref) =
    let open BodyRd in
    let def_kind_cpn = def_kind_get body_cpn in
    let def_kind = DefKind.get def_kind_cpn in
    match def_kind with
    | DefKind.Fn ->
        let dloc = Ast.Lexed Ast.dummy_loc0 in
        let def_path = def_path_get body_cpn in
        let contract_cpn = contract_get body_cpn in
        let nonghost_callers_only, fn_type_clause, pre_post, terminates =
          translate_contract contract_cpn
        in
        let arg_count = arg_count_get body_cpn in
        let local_decls_cpn = local_decls_get_list body_cpn in
        let* local_decls =
          ListAux.try_map
            (fun ld_cpn -> translate_local_decl ld_cpn gh_ty_decls)
            local_decls_cpn
        in
        (* There should be always a return place for each function *)
        let (ret_place_decl :: local_decls) = local_decls in
        let { Mir.id = ret_place_id; Mir.ty = ret_ty_info } = ret_place_decl in
        let param_decls, local_decls =
          ListAux.partitioni
            (fun idx _ -> idx < Stdint.Uint32.to_int arg_count)
            local_decls
        in
        let vf_param_decls =
          List.map
            (fun ({ mutability; id; ty = ty_info } : Mir.local_decl) ->
              (ty_info.vf_ty, id))
            param_decls
        in
        let vf_local_decls =
          List.map translate_to_vf_local_decl (ret_place_decl :: local_decls)
        in
        let bblocks_cpn = basic_blocks_get_list body_cpn in
        let* bblocks =
          ListAux.try_map (translate_basic_block ret_place_id) bblocks_cpn
        in
        let vf_bblocks = List.map translate_to_vf_basic_block bblocks in
        let vf_bblocks = List.concat vf_bblocks in
        Ok
          (Ast.Func
             ( dloc,
               Ast.Regular,
               [],
               Some ret_ty_info.Mir.vf_ty,
               def_path,
               vf_param_decls,
               nonghost_callers_only,
               fn_type_clause,
               pre_post,
               terminates,
               Some (vf_local_decls @ vf_bblocks, dloc),
               Ast.Static,
               Ast.Package ))
    | _ -> Error (`TrBody "Unknown MIR Body kind")

  let translate_vf_mir (vf_mir_cpn : VfMirRd.t) =
    let job _ =
      let bodies_cpn = VfMirRd.bodies_get_list vf_mir_cpn in
      let gh_ty_decls = ref GhostTyDecls.empty in
      let* body_decls =
        ListAux.try_map
          (fun body_cpn -> translate_body body_cpn gh_ty_decls)
          bodies_cpn
      in
      let _, gh_ty_decls = GhostTyDecls.bindings !gh_ty_decls |> List.split in
      let decls = gh_ty_decls @ body_decls in
      Ok ([ (*headers*) ], [ Ast.PackageDecl (Ast.dummy_loc, "", [], decls) ])
    in
    match job () with
    | Ok res -> res
    | Error err -> failwith "Todo: translate_vf_mir Error handling"
end
