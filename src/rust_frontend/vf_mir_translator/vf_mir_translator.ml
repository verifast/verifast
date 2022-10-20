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

module IntAux = struct
  module Make (StdintMod : sig
    type t

    val zero : t
    val max_int : t
    val min_int : t
    val ( - ) : t -> t -> t
    val ( + ) : t -> t -> t
    val to_int : t -> int
    val of_int : int -> t
  end) =
  struct
    open StdintMod

    let try_add (a : t) (b : t) =
      if a >= zero then
        if b <= max_int - a then Ok (a + b) else Error (`IntAuxAdd "Overflow")
      else if b >= min_int - a then Ok (a + b)
      else Error (`IntAuxAdd "Underflow")

    let try_to_int (a : t) =
      let i = to_int a in
      if a = of_int i then Ok i else Error `IntAuxToInt
  end

  module Uint64 = Make (Stdint.Uint64)
  module Uint32 = Make (Stdint.Uint32)
end

module Mir = struct
  type mutability = Mut | Not

  type generic_arg = GenArgLifetime | GenArgType of ty_info | GenArgConst

  and ty_info =
    | TyInfoBasic of { vf_ty : Ast.type_expr }
    | TyInfoGeneric of { vf_ty : Ast.type_expr; substs : generic_arg list }

  let basic_type_of (ti : ty_info) =
    match ti with
    | TyInfoBasic ti1 -> ti1.vf_ty
    | TyInfoGeneric _ -> failwith "Todo: Generic types are not supported yet"

  let raw_type_of (ti : ty_info) =
    match ti with
    | TyInfoBasic { vf_ty } -> vf_ty
    | TyInfoGeneric { vf_ty; substs } -> vf_ty

  type annot = { span : Ast.loc; raw : string }

  type local_decl = {
    mutability : mutability;
    id : string;
    ty : ty_info;
    loc : Ast.loc;
  }

  type source_info = { span : Ast.loc; scope : unit }

  type basic_block = {
    id : string;
    statements : Ast.stmt list;
    terminator : Ast.stmt list;
  }

  type fn_call_dst_data = { dst : Ast.expr; dst_bblock_id : string }
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
    else
      Ast.Struct
        ( loc,
          name,
          Some ((* base_spec list *) [], (* field list *) []),
          (* attr list *) [] )
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

module TrTyRawPtr = struct
  type ty_raw_ptr_info = {
    mutability : Mir.mutability;
    pointee_ty_info : Mir.ty_info;
  }
end

module TrName = struct
  let translate_def_path (dp : string) =
    let open Str in
    let r = regexp {|::|} in
    global_replace r "_" dp

  let make_tmp_var_name base_name = "temp_var_" ^ base_name
end

module type DECLS = sig
  type decl

  val add_decl : decl -> unit
  val decls : unit -> decl list
end

module Decls (Args : sig
  type decl
end) : DECLS with type decl = Args.decl = struct
  type decl = Args.decl

  let ds : decl list ref = ref []

  let add_decl (decl : decl) =
    if not @@ List.exists (( = ) decl) !ds then ds := !ds @ [ decl ]

  let decls _ = !ds
end

module type VF_MIR_TRANSLATOR_ARGS = sig
  val data_model_opt : Ast.data_model option
  val report_should_fail : string -> Ast.loc0 -> unit
  val report_range : Lexer.range_kind -> Ast.loc0 -> unit
end

module Make (Args : VF_MIR_TRANSLATOR_ARGS) = struct
  open Ocaml_aux
  module VfMirAnnotParser = Vf_mir_annot_parser.Make (Args)
  module VfMirCapnpAlias = Vf_mir_capnp_alias
  module VfMirRd = VfMirCapnpAlias.VfMirRd
  open VfMirCapnpAlias

  module TyDecls = Decls (struct
    type decl = Ast.decl
  end)

  module Headers = Decls (struct
    type decl = string
  end)

  module HeadersAux = struct
    module type AUX_HEADERS_ARGS = sig
      include VF_MIR_TRANSLATOR_ARGS

      val aux_headers_dir : string
      val verbosity : int
    end

    module Make (Args : AUX_HEADERS_ARGS) = struct
      type t = string list

      let empty : t = []

      let parse_header (header_name : string) =
        let header_path = Filename.concat Args.aux_headers_dir header_name in
        (* Todo @Nima: should we catch the exceptions and return Error here? *)
        let headers, decls =
          Parser.parse_header_file header_path Args.report_range
            Args.report_should_fail Args.verbosity (*include paths*) []
            (*define macros*) [] (*enforce annotation*) true Args.data_model_opt
        in
        let header_names = List.map (fun (_, (_, _, h), _, _) -> h) headers in
        let headers =
          ( Ast.dummy_loc,
            (Lexer.AngleBracketInclude, header_name, Args.aux_headers_dir),
            header_names,
            decls )
          :: headers
        in
        Ok headers
    end
  end

  let translate_path_buf (pbuf_cpn : PathBufRd.t) = PathBufRd.inner_get pbuf_cpn

  let translate_real_file_name (real_fname_cpn : RealFileNameRd.t) =
    let open RealFileNameRd in
    match get real_fname_cpn with
    | LocalPath path_buf_cpn -> Ok (translate_path_buf path_buf_cpn)
    | Remapped -> failwith "Todo: RealFileName Remapped"
    | Undefined _ -> Error (`TrRealFileName "Unknown RealFileName kind")

  let translate_file_name (fname_cpn : FileNameRd.t) =
    let open FileNameRd in
    match get fname_cpn with
    | Real real_fname_cpn -> translate_real_file_name real_fname_cpn
    | QuoteExpansion _ -> failwith "Todo: FileName QuoteExpansion"
    | Undefined _ -> Error (`TrFileName "Unknown FileName kind")

  let translate_source_file (src_file_cpn : SourceFileRd.t) =
    let open SourceFileRd in
    let name_cpn = name_get src_file_cpn in
    translate_file_name name_cpn

  let translate_char_pos (cpos_cpn : CharPosRd.t) =
    let open CharPosRd in
    let cpos = pos_get cpos_cpn in
    (* Make it 1-based *)
    let cpos = IntAux.Uint64.try_add cpos Stdint.Uint64.one in
    cpos

  let translate_loc (loc_cpn : LocRd.t) =
    let open LocRd in
    let file_cpn = file_get loc_cpn in
    let* file = translate_source_file file_cpn in
    let line = line_get loc_cpn in
    let col_cpn = col_get loc_cpn in
    let* col = translate_char_pos col_cpn in
    let* line = IntAux.Uint64.try_to_int line in
    let* col = IntAux.Uint64.try_to_int col in
    let src_pos = (file, line, col) in
    Ok src_pos

  let translate_span_data (span_cpn : SpanDataRd.t) =
    let open SpanDataRd in
    let lo_cpn = lo_get span_cpn in
    let* lo = translate_loc lo_cpn in
    let hi_cpn = hi_get span_cpn in
    let* hi = translate_loc hi_cpn in
    Ok (Ast.Lexed (lo, hi))

  let translate_source_info (src_info_cpn : SourceInfoRd.t) =
    let open SourceInfoRd in
    let span_cpn = span_get src_info_cpn in
    let* span = translate_span_data span_cpn in
    let scope_cpn = scope_get src_info_cpn in
    let src_info : Mir.source_info = { span; scope = () } in
    Ok src_info

  let translate_annotation (annot_cpn : AnnotationRd.t) =
    let open AnnotationRd in
    let raw = raw_get annot_cpn in
    let span_cpn = span_get annot_cpn in
    let* span = translate_span_data span_cpn in
    let annot : Mir.annot = { span; raw } in
    Ok annot

  let translate_contract (contract_cpn : ContractRd.t) =
    let annots_cpn = ContractRd.annotations_get_list contract_cpn in
    let* annots = ListAux.try_map translate_annotation annots_cpn in
    let* annots =
      ListAux.try_map
        (fun { Mir.span; Mir.raw } ->
          match span with
          | Ast.Lexed (b, e) -> Ok (b, raw)
          | DummyLoc | MacroExpansion _ | MacroParamExpansion _ ->
              Error
                (`TrContract "Invalid span translation for function contract"))
        annots
    in
    Ok (VfMirAnnotParser.parse_func_contract annots)
  (* Todo: VeriFast parser throws exceptions. we should catch them and use our own error handling scheme *)

  let translate_mutability (mutability_cpn : MutabilityRd.t) =
    match MutabilityRd.get mutability_cpn with
    | Mut -> Ok Mir.Mut
    | Not -> Ok Mir.Not
    | Undefined _ ->
        Error (`TrMutability "Unknown Mir mutability discriminator")

  let int_size_rank =
    match Args.data_model_opt with
    | None -> Ast.PtrRank
    | Some data_model -> Ast.LitRank data_model.ptr_rank

  let translate_u_int_ty (u_int_ty_cpn : UIntTyRd.t) (loc : Ast.loc) =
    let calc_rank ui =
      let* bits = Mir.u_int_ty_bits_len ui in
      let* rank = TrTyInt.calc_int_rank bits in
      Ok (Ast.LitRank rank)
    in
    let* rank =
      match UIntTyRd.get u_int_ty_cpn with
      | USize -> Ok int_size_rank
      | U8 -> calc_rank Mir.U8
      | U16 -> calc_rank Mir.U16
      | U32 -> calc_rank Mir.U32
      | U64 -> calc_rank Mir.U64
      | U128 -> calc_rank Mir.U128
      | Undefined _ -> Error (`TrUIntTy "Unknown Rust unsigned int type")
    in
    let ty_info =
      Mir.TyInfoBasic
        { vf_ty = Ast.ManifestTypeExpr (loc, Ast.Int (Ast.Unsigned, rank)) }
    in
    Ok ty_info

  let translate_adt_ty (adt_ty_cpn : AdtTyRd.t) (loc : Ast.loc) =
    let open AdtTyRd in
    let id_cpn = id_get adt_ty_cpn in
    let def_path = AdtDefIdRd.name_get id_cpn in
    match def_path with
    | "std::alloc::Layout" ->
        let substs_cpn = substs_get_list adt_ty_cpn in
        if not @@ ListAux.is_empty @@ substs_cpn then
          Error (`TrAdtTy (def_path ^ " does not have any generic parameter"))
        else
          let ty_info =
            Mir.TyInfoBasic
              {
                vf_ty =
                  Ast.ManifestTypeExpr
                    (loc, Ast.Int (Ast.Unsigned, int_size_rank));
              }
          in
          Ok ty_info
    | _ -> failwith "Todo: Unsupported Adt"

  let translate_tuple_ty (substs_cpn : GenArgRd.t list) (loc : Ast.loc) =
    if not @@ ListAux.is_empty @@ substs_cpn then
      failwith "Todo: Tuple Ty is not implemented yet"
    else
      let name = TrTyTuple.make_tuple_type_name [] in

      (* TODO @Nima: std_tuple_0_ type is declared in prelude_rust_.h.
         We should come up with a better arrangement for these ghost types. *)
      let ty_info =
        Mir.TyInfoBasic
          { vf_ty = Ast.ManifestTypeExpr (loc, Ast.StructType name) }
      in
      Ok ty_info

  let rec translate_generic_arg (gen_arg_cpn : GenArgRd.t) (loc : Ast.loc) =
    let open GenArgRd in
    let kind_cpn = kind_get gen_arg_cpn in
    let open GenArgKindRd in
    match get kind_cpn with
    | Lifetime -> failwith "Todo: Generic arg. lifetime is not supported yet"
    | Type ty_cpn ->
        let* ty_info = translate_ty ty_cpn loc in
        Ok (Mir.GenArgType ty_info)
    | Const -> failwith "Todo: Generic arg. constant is not supported yet"
    | Undefined _ -> Error (`TrGenArg "Unknown generic arg. kind")

  and translate_fn_def_ty (fn_def_ty_cpn : FnDefTyRd.t) (loc : Ast.loc) =
    let open FnDefTyRd in
    let id_cpn = id_get fn_def_ty_cpn in
    let id = FnDefIdRd.name_get id_cpn in
    let name = TrName.translate_def_path id in
    let vf_ty = Ast.ManifestTypeExpr (loc, Ast.FuncType name) in
    let substs_cpn = substs_get_list fn_def_ty_cpn in
    if ListAux.is_empty substs_cpn then Ok (Mir.TyInfoBasic { vf_ty })
    else
      let* substs =
        ListAux.try_map
          (fun subst_cpn -> translate_generic_arg subst_cpn loc)
          substs_cpn
      in
      Ok (Mir.TyInfoGeneric { vf_ty; substs })

  and translate_raw_ptr_ty (raw_ptr_ty_cpn : RawPtrTyRd.t) (loc : Ast.loc) =
    let open RawPtrTyRd in
    let mut_cpn = mutability_get raw_ptr_ty_cpn in
    let* mutability = translate_mutability mut_cpn in
    let ty_cpn = ty_get raw_ptr_ty_cpn in
    let* pointee_ty_info = translate_ty ty_cpn loc in
    let (Ast.ManifestTypeExpr ((*loc*) _, pointee_ty)) =
      Mir.basic_type_of pointee_ty_info
    in
    let ty_info =
      Mir.TyInfoBasic
        { vf_ty = Ast.ManifestTypeExpr (loc, Ast.PtrType pointee_ty) }
    in
    Ok ty_info

  and translate_ty (ty_cpn : TyRd.t) (loc : Ast.loc) =
    let open TyRd in
    let kind_cpn = kind_get ty_cpn in
    match TyRd.TyKind.get kind_cpn with
    | Bool ->
        Ok (Mir.TyInfoBasic { vf_ty = Ast.ManifestTypeExpr (loc, Ast.Bool) })
    | Int int_ty_cpn -> failwith "Todo: Int Ty is not implemented yet"
    | UInt u_int_ty_cpn -> translate_u_int_ty u_int_ty_cpn loc
    | Adt adt_ty_cpn -> translate_adt_ty adt_ty_cpn loc
    | RawPtr raw_ptr_ty_cpn -> translate_raw_ptr_ty raw_ptr_ty_cpn loc
    | FnDef fn_def_ty_cpn -> translate_fn_def_ty fn_def_ty_cpn loc
    | Tuple substs_cpn ->
        let substs_cpn = Capnp.Array.to_list substs_cpn in
        translate_tuple_ty substs_cpn loc
    | Undefined _ -> Error (`TrTy "Unknown Rust type kind")

  let translate_local_decl_id (local_decl_id_cpn : LocalDeclIdRd.t) =
    LocalDeclIdRd.name_get local_decl_id_cpn

  let translate_local_decl (local_decl_cpn : LocalDeclRd.t) =
    let open LocalDeclRd in
    let mutability_cpn = mutability_get local_decl_cpn in
    let* mutability = translate_mutability mutability_cpn in
    let id_cpn = id_get local_decl_cpn in
    let id = translate_local_decl_id id_cpn in
    let src_info_cpn = source_info_get local_decl_cpn in
    let* { Mir.span = loc; Mir.scope } = translate_source_info src_info_cpn in
    let ty_cpn = ty_get local_decl_cpn in
    let* ty_info = translate_ty ty_cpn loc in
    let local_decl : Mir.local_decl = { mutability; id; ty = ty_info; loc } in
    Ok local_decl

  let translate_to_vf_local_decl
      ({ mutability = mut; id; ty = ty_info; loc } : Mir.local_decl) =
    let ty = Mir.basic_type_of ty_info in
    Ast.DeclStmt
      ( loc,
        [
          ( loc,
            ty,
            id,
            None,
            ( (* indicates whether address is taken *) ref false,
              (* pointer to enclosing block's list of variables whose address is taken *)
              ref None ) );
        ] )

  let translate_place (place_cpn : PlaceRd.t) (loc : Ast.loc) =
    let open PlaceRd in
    let id_cpn = local_get place_cpn in
    let id = translate_local_decl_id id_cpn in
    let projection_cpn = projection_get_list place_cpn in
    if ListAux.is_empty projection_cpn then Ast.Var (loc, id)
    else failwith "Todo: Place::Projection"

  let translate_typed_constant (ty_const_cpn : TyConstRd.t) (loc : Ast.loc) =
    let open TyConstRd in
    let ty_cpn = ty_get ty_const_cpn in
    let* ty_info = translate_ty ty_cpn loc in

    (* Todo @Nima: Here we might need access to type declarations to create proper constants out of the bytes we get from
       the Rust compiler. It would be more straightforward if we get higher-level info about constant value from Rustc.
    *)
    let ty_expr = Mir.raw_type_of ty_info in
    let ty =
      match ty_expr with
      | Ast.ManifestTypeExpr ((*loc*) _, ty) -> ty
      | _ -> failwith "Todo: Unsupported type_expr"
    in
    match ty with
    | Ast.StructType st_name ->
        if st_name != TrTyTuple.make_tuple_type_name [] then
          failwith
            ("Todo: Constants of type struct " ^ st_name
           ^ " are not supported yet")
        else
          let rvalue_binder_builder tmp_var_name =
            Ast.DeclStmt
              ( loc,
                [
                  ( loc,
                    ty_expr,
                    tmp_var_name,
                    Some (Ast.InitializerList (loc, [])),
                    ( (*indicates whether address is taken*) ref false,
                      (*pointer to enclosing block's list of variables whose address is taken*)
                      ref None ) );
                ] )
          in
          Ok (`TrTypedConstantRvalueBinderBuilder rvalue_binder_builder)
    | Ast.FuncType _ -> Ok (`TrTypedConstantFn ty_info)
    | _ -> failwith "Todo: Constant of unsupported type"

  let translate_constant_kind (constant_kind_cpn : ConstantKindRd.t)
      (loc : Ast.loc) =
    let open ConstantKindRd in
    match get constant_kind_cpn with
    | Ty ty_const_cpn -> translate_typed_constant ty_const_cpn loc
    | Val -> failwith "Todo: ConstantKind::Val"
    | Undefined _ -> Error (`TrConstantKind "Unknown ConstantKind")

  let translate_constant (constant_cpn : ConstantRd.t) =
    let open ConstantRd in
    let span_cpn = span_get constant_cpn in
    let* loc = translate_span_data span_cpn in
    let literal_cpn = literal_get constant_cpn in
    translate_constant_kind literal_cpn loc

  let translate_operand (operand_cpn : OperandRd.t) (loc : Ast.loc) =
    let open OperandRd in
    (* Todo @Nima: Move and Copy are ignored for now. It is checked by the Rust compiler that
       - Only Places of type Copy get used for Operand::Copy
       - Places used by Operand::Move will never get used again (obviously raw pointers are not tracked)
    *)
    match get operand_cpn with
    | Copy place_cpn -> Ok (`TrOperandCopy (translate_place place_cpn loc))
    | Move place_cpn -> Ok (`TrOperandMove (translate_place place_cpn loc))
    | Constant constant_cpn -> translate_constant constant_cpn
    | Undefined _ -> Error (`TrOperand "Unknown Mir Operand kind")

  let translate_fn_call_rexpr (callee_ty_info : Mir.ty_info)
      (args_cpn : OperandRd.t list) (call_loc : Ast.loc) (fn_loc : Ast.loc) =
    match callee_ty_info with
    | Mir.TyInfoBasic
        { vf_ty = Ast.ManifestTypeExpr ((*loc*) _, Ast.FuncType fn_name) } ->
        let tmp_rvalue_binders = ref [] in
        let translate_arg arg_cpn =
          (* Todo @Nima: There should be a way to get separated source spans for args *)
          let* arg = translate_operand arg_cpn fn_loc in
          match arg with
          | `TrOperandCopy operand_expr | `TrOperandMove operand_expr ->
              Ok operand_expr
          | `TrTypedConstantRvalueBinderBuilder rvalue_binder_builder ->
              let tmp_var_cnt = List.length !tmp_rvalue_binders in
              let tmp_var_name =
                TrName.make_tmp_var_name (Int.to_string tmp_var_cnt)
              in
              let rvalue_binder = rvalue_binder_builder tmp_var_name in
              tmp_rvalue_binders := !tmp_rvalue_binders @ [ rvalue_binder ];
              Ok (Ast.Var (fn_loc, tmp_var_name))
          | `TrTypedConstantFn _ ->
              Error (`TrFnCallRExpr "Invalid function call argument")
        in
        let* args = ListAux.try_map translate_arg args_cpn in
        let args = List.map (fun expr -> Ast.LitPat expr) args in
        let call_expr =
          Ast.CallExpr
            ( call_loc,
              fn_name,
              [] (*type arguments*),
              [] (*indices, in case this is really a predicate assertion*),
              args,
              Ast.Static (*method_binding*) )
        in
        Ok (!tmp_rvalue_binders, call_expr)
    | Mir.TyInfoGeneric
        {
          vf_ty = Ast.ManifestTypeExpr ((*loc*) _, Ast.FuncType fn_name);
          substs;
        } -> (
        match fn_name with
        | "std_alloc_Layout_new" -> (
            match substs with
            | [ Mir.GenArgType ty_info ] ->
                let ty_expr = Mir.basic_type_of ty_info in
                Ok
                  ( (*tmp_rvalue_binders*) [],
                    Ast.SizeofExpr (call_loc, Ast.TypeExpr ty_expr) )
            | _ ->
                Error
                  (`TrFnCallRExpr
                    "Invalid generic argument(s) for std::alloc::Layout::new"))
        | _ -> failwith "Todo: Generic functions are not supported yet")
    | _ -> Error (`TrFnCallRExpr "Invalid function definition type translation")

  let translate_basic_block_id (bblock_id_cpn : BasicBlockIdRd.t) =
    BasicBlockIdRd.name_get bblock_id_cpn

  let translate_destination_data (dst_data_cpn : DestinationDataRd.t)
      (loc : Ast.loc) =
    let open DestinationDataRd in
    let place_cpn = place_get dst_data_cpn in
    let dst = translate_place place_cpn loc in
    let dst_bblock_id_cpn = basic_block_id_get dst_data_cpn in
    let dst_bblock_id = translate_basic_block_id dst_bblock_id_cpn in
    let dst_data : Mir.fn_call_dst_data = { dst; dst_bblock_id } in
    dst_data

  let translate_fn_call (fn_call_data_cpn : FnCallDataRd.t) (loc : Ast.loc) =
    let open FnCallDataRd in
    let func_cpn = func_get fn_call_data_cpn in
    let* callee_ty_info = translate_operand func_cpn loc in
    let* callee_ty_info =
      match callee_ty_info with
      | `TrTypedConstantFn ty_info -> Ok ty_info
      | _ -> Error (`TrFnCall "Invalid typed constant for function call")
    in
    let fn_span_cpn = fn_span_get fn_call_data_cpn in
    let* fn_loc = translate_span_data fn_span_cpn in
    let args_cpn = args_get_list fn_call_data_cpn in
    let* fn_call_tmp_rval_ctx, fn_call_rexpr =
      translate_fn_call_rexpr callee_ty_info args_cpn loc fn_loc
    in
    let destination_cpn = destination_get fn_call_data_cpn in
    match OptionRd.get destination_cpn with
    | Nothing -> failwith "Todo: Diverging calls are not supported yet"
    | Something ptr_cpn ->
        let destination_data_cpn = VfMirStub.Reader.of_pointer ptr_cpn in
        let { Mir.dst; Mir.dst_bblock_id } =
          translate_destination_data destination_data_cpn loc
        in
        let full_call_stmt =
          Ast.ExprStmt (Ast.AssignExpr (loc, dst, fn_call_rexpr))
        in
        let full_call_stmt =
          if ListAux.is_empty fn_call_tmp_rval_ctx then full_call_stmt
          else
            Ast.BlockStmt
              ( loc,
                (*decl list*) [],
                fn_call_tmp_rval_ctx @ [ full_call_stmt ],
                loc,
                ref [] )
        in
        let next_bblock_stmt = Ast.GotoStmt (loc, dst_bblock_id) in
        Ok [ full_call_stmt; next_bblock_stmt ]
    | Undefined _ -> Error (`TrFnCall "Unknown Option kind")

  let translate_terminator_kind (ret_place_id : string)
      (tkind_cpn : TerminatorKindRd.t) (loc : Ast.loc) =
    let open TerminatorKindRd in
    match get tkind_cpn with
    | Goto bblock_id_cpn -> failwith "Todo TerminatorKind::Goto"
    | SwitchInt switch_int_data_cpn ->
        failwith "Todo: TerminatorKind::SwitchInt"
    | Resume -> failwith "Todo: Terminatorkind::Resume"
    | Return -> Ok [ Ast.ReturnStmt (loc, Some (Ast.Var (loc, ret_place_id))) ]
    | Call fn_call_data_cpn -> translate_fn_call fn_call_data_cpn loc
    | Undefined _ -> Error (`TrTerminatorKind "Unknown Mir terminator kind")

  let translate_terminator (ret_place_id : string)
      (terminator_cpn : TerminatorRd.t) =
    let open TerminatorRd in
    let src_info_cpn = source_info_get terminator_cpn in
    let* { Mir.span = loc; Mir.scope } = translate_source_info src_info_cpn in
    let terminator_kind_cpn = kind_get terminator_cpn in
    translate_terminator_kind ret_place_id terminator_kind_cpn loc

  let translate_rvalue (rvalue_cpn : RvalueRd.t) (loc : Ast.loc) =
    let open RvalueRd in
    match get rvalue_cpn with
    | Use operand_cpn -> (
        let* operand = translate_operand operand_cpn loc in
        match operand with
        | `TrTypedConstantFn _ ->
            Error (`TrRvalue "Invalid Operand translation for Rvalue")
        | _ -> Ok operand)
    | AddressOf address_of_data_cpn -> failwith "Todo: Rvalue::AddressOf"
    | Undefined _ -> Error (`TrRvalue "Unknown Rvalue kind")

  let translate_statement_kind (statement_kind_cpn : StatementKindRd.t)
      (loc : Ast.loc) =
    let open StatementKindRd in
    match get statement_kind_cpn with
    | Assign assign_data_cpn -> (
        let lhs_place_cpn = AssignData.lhs_place_get assign_data_cpn in
        let lhs_place = translate_place lhs_place_cpn loc in
        let rhs_rvalue_cpn = AssignData.rhs_rvalue_get assign_data_cpn in
        let* rhs_rvalue = translate_rvalue rhs_rvalue_cpn loc in
        match rhs_rvalue with
        | `TrOperandCopy rhs_expr | `TrOperandMove rhs_expr ->
            let assign_stmt =
              Ast.ExprStmt (Ast.AssignExpr (loc, lhs_place, rhs_expr))
            in
            Ok [ assign_stmt ]
        | `TrTypedConstantRvalueBinderBuilder rvalue_binder_builder ->
            (* Todo @Nima: Is this correct to use `loc` for subparts of the block that represents the assignment statement *)
            let tmp_var_name = TrName.make_tmp_var_name "" in
            let rvalue_binder_stmt = rvalue_binder_builder tmp_var_name in
            let assign_stmt =
              Ast.ExprStmt
                (Ast.AssignExpr (loc, lhs_place, Ast.Var (loc, tmp_var_name)))
            in
            let block_stmt =
              Ast.BlockStmt
                ( loc,
                  (*decl list*) [],
                  [ rvalue_binder_stmt; assign_stmt ],
                  loc,
                  ref [] )
            in
            Ok [ block_stmt ])
    | Nop -> Ok []
    | Undefined _ -> Error (`TrStatementKind "Unknown StatementKind")

  let translate_statement (statement_cpn : StatementRd.t) =
    let open StatementRd in
    let src_info_cpn = source_info_get statement_cpn in
    let* { Mir.span = loc; Mir.scope } = translate_source_info src_info_cpn in
    let kind_cpn = kind_get statement_cpn in
    translate_statement_kind kind_cpn loc

  let translate_basic_block (ret_place_id : string)
      (bblock_cpn : BasicBlockRd.t) =
    let open BasicBlockRd in
    let id_cpn = id_get bblock_cpn in
    let id = translate_basic_block_id id_cpn in
    if is_cleanup_get bblock_cpn then
      (* Todo @Nima: For now we are ignoring cleanup basic-blocks *)
      let bblock : Mir.basic_block =
        {
          id;
          statements = [];
          terminator = [ Ast.NoopStmt (Ast.Lexed Ast.dummy_loc0) ];
        }
      in
      Ok bblock
    else
      let statements_cpn = statements_get_list bblock_cpn in
      let* statements = ListAux.try_map translate_statement statements_cpn in
      let statements = List.concat statements in
      let terminator_cpn = terminator_get bblock_cpn in
      let* terminator = translate_terminator ret_place_id terminator_cpn in
      let bblock : Mir.basic_block = { id; statements; terminator } in
      Ok bblock

  let translate_to_vf_basic_block
      ({ id; statements; terminator } : Mir.basic_block) =
    if ListAux.is_empty terminator then
      Error (`TrToVfBBlock "Basic block without any terminator")
    else
      let statements = statements @ terminator in
      let loc = Ast.stmt_loc @@ List.hd @@ statements in
      Ok (Ast.LabelStmt (loc, id) :: statements)

  let translate_body (body_cpn : BodyRd.t) =
    let open BodyRd in
    let def_kind_cpn = def_kind_get body_cpn in
    let def_kind = DefKind.get def_kind_cpn in
    match def_kind with
    | DefKind.Fn ->
        let def_path = def_path_get body_cpn in
        let name = TrName.translate_def_path def_path in
        let contract_cpn = contract_get body_cpn in
        let* nonghost_callers_only, fn_type_clause, pre_post, terminates =
          translate_contract contract_cpn
        in
        let arg_count = arg_count_get body_cpn in
        let* arg_count = IntAux.Uint32.try_to_int arg_count in
        let local_decls_cpn = local_decls_get_list body_cpn in
        let* local_decls =
          ListAux.try_map translate_local_decl local_decls_cpn
        in
        (* There should always be a return place for each function *)
        let (ret_place_decl :: local_decls) = local_decls in
        let ({
               mutability = ret_mut;
               id = ret_place_id;
               ty = ret_ty_info;
               loc = ret_place_loc;
             }
              : Mir.local_decl) =
          ret_place_decl
        in
        let ret_ty = Mir.basic_type_of ret_ty_info in
        let param_decls, local_decls =
          ListAux.partitioni (fun idx _ -> idx < arg_count) local_decls
        in
        let vf_param_decls =
          List.map
            (fun ({ mutability; id; ty = ty_info; loc } : Mir.local_decl) ->
              let ty = Mir.basic_type_of ty_info in
              (ty, id))
            param_decls
        in
        let vf_local_decls =
          List.map translate_to_vf_local_decl (ret_place_decl :: local_decls)
        in
        let bblocks_cpn = basic_blocks_get_list body_cpn in
        let* bblocks =
          ListAux.try_map
            (fun bblock_cpn -> translate_basic_block ret_place_id bblock_cpn)
            bblocks_cpn
        in
        let* vf_bblocks = ListAux.try_map translate_to_vf_basic_block bblocks in
        let vf_bblocks = List.concat vf_bblocks in
        let span_cpn = span_get body_cpn in
        let* loc = translate_span_data span_cpn in
        let imp_span_cpn = imp_span_get body_cpn in
        let* imp_loc = translate_span_data imp_span_cpn in
        Ok
          (Ast.Func
             ( loc,
               Ast.Regular,
               [],
               Some ret_ty,
               name,
               vf_param_decls,
               nonghost_callers_only,
               fn_type_clause,
               pre_post,
               terminates,
               Some (vf_local_decls @ vf_bblocks, imp_loc),
               Ast.Static,
               Ast.Package ))
    | DefKind.AssocFn -> failwith "Todo: MIR Body kind AssocFn"
    | _ -> Error (`TrBody "Unknown MIR Body kind")

  let translate_vf_mir (vf_mir_cpn : VfMirRd.t) =
    let job _ =
      let module HeadersAux = HeadersAux.Make (struct
        include Args

        let aux_headers_dir = Filename.dirname Sys.executable_name
        let verbosity = 0
      end) in
      let bodies_cpn = VfMirRd.bodies_get_list vf_mir_cpn in
      let* body_decls = ListAux.try_map translate_body bodies_cpn in
      let ty_decls = TyDecls.decls () in
      let decls = ty_decls @ body_decls in
      (* Todo @Nima: we should add necessary inclusions from Rust side *)
      let _ = Headers.add_decl "rust/std/alloc.h" in
      let header_names = Headers.decls () in
      let* headers = ListAux.try_map HeadersAux.parse_header header_names in
      let headers = List.concat headers in
      Ok (headers, [ Ast.PackageDecl (Ast.dummy_loc, "", [], decls) ])
    in
    match job () with
    | Ok res -> res
    | Error err -> failwith "Todo: translate_vf_mir Error handling"
end
(* Todo @Nima: terminator kind goto *)
