module RustBelt = Rustbelt
module LocAux = Src_loc_aux

module IntAux = struct
  module Make (StdintMod : sig
    type t

    val zero : t
    val max_int : t
    val min_int : t
    val ( - ) : t -> t -> t
    val ( + ) : t -> t -> t
    val div : t -> t -> t
    val rem : t -> t -> t
    val to_int : t -> int
    val of_int : int -> t
    val to_string : t -> string
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

    let rec to_big_int (a : t) = Big_int.big_int_of_string (to_string a)
  end

  module Int8 = Make (Stdint.Int8)
  module Int16 = Make (Stdint.Int16)
  module Int32 = Make (Stdint.Int32)
  module Int64 = Make (Stdint.Int64)
  module Int128 = Make (Stdint.Int128)
  module Uint8 = Make (Stdint.Uint8)
  module Uint16 = Make (Stdint.Uint16)
  module Uint32 = Make (Stdint.Uint32)
  module Uint64 = Make (Stdint.Uint64)
  module Uint128 = Make (Stdint.Uint128)
end

module AstAux = struct
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
        (loc, name, fun name -> Inductive (loc, name, tparams, ctors))
    | Struct (loc, name, tparams, definition_opt, attrs) ->
        ( loc,
          name,
          fun new_name -> Struct (loc, new_name, tparams, definition_opt, attrs)
        )
    | AbstractTypeDecl (l, x) -> (l, x, fun x -> AbstractTypeDecl (l, x))
    | TypedefDecl (l, te, x, tparams) ->
        (l, x, fun x -> TypedefDecl (l, te, x, tparams))
    | PredFamilyDecl
        (l, g, tparams, nbIndices, pts, inputParamCount, inductiveness) ->
        ( l,
          g,
          fun g ->
            PredFamilyDecl
              (l, g, tparams, nbIndices, pts, inputParamCount, inductiveness) )
    | PredFamilyInstanceDecl (l, g, tparams, indices, ps, body) ->
        ( l,
          g,
          fun g -> PredFamilyInstanceDecl (l, g, tparams, indices, ps, body) )
    | PredCtorDecl (l, g, tparams, ctor_ps, ps, inputParamCount, body) ->
        ( l,
          g,
          fun g ->
            PredCtorDecl (l, g, tparams, ctor_ps, ps, inputParamCount, body) )
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

  let sort_decls_lexically ds =
    List.sort
      (fun d d1 ->
        compare
          (Ast.lexed_loc @@ decl_loc @@ d)
          (Ast.lexed_loc @@ decl_loc @@ d1))
      ds
end

module SizeAux : sig
  (* These types have the invariant of holding a meaningful number of bits, bytes, etc. *)
  type sz_bits
  type sz_bytes

  val sz_bits_of_int :
    int -> (sz_bits, [> `SizeAuxSzBitsOfInt of string ]) result

  val sz_bytes_of_int :
    int -> (sz_bytes, [> `SizeAuxSzBytesOfInt of string ]) result

  val sz_bytes_of_sz_bits : sz_bits -> sz_bytes
  val int_of_sz_bytes : sz_bytes -> int
end = struct
  type sz_bits = int
  type sz_bytes = int

  let sz_bits_of_int bits =
    if bits = 0 then Ok bits
    else
      let n = Float.log2 @@ float_of_int @@ bits in
      let n_is_int_and_bits_gt_zero =
        FP_zero == Float.classify_float @@ fst @@ Float.modf @@ n
      in
      if not (n_is_int_and_bits_gt_zero && int_of_float n >= 3) then
        Error
          (`SizeAuxSzBitsOfInt
            "The number of bits should be 0 or 2^n such that n is an integer \
             and n>=3")
      else Ok bits

  let sz_bytes_of_int bytes =
    if bytes < 0 then
      Error
        (`SizeAuxSzBytesOfInt
          "The number of bytes should be a non-negative integer")
    else Ok bytes

  let sz_bytes_of_sz_bits n = n / 8
  let int_of_sz_bytes sb = sb
end

module Hir = struct
  type generic_param = GenParamLifetime | GenParamType | GenParamConst
end

module Mir = struct
  type mutability = Mut | Not

  type generic_arg = GenArgLifetime | GenArgType of ty_info | GenArgConst

  and ty_info =
    | TyInfoBasic of { vf_ty : Ast.type_expr; interp : RustBelt.ty_interp }
    | TyInfoGeneric of {
        vf_ty : Ast.type_expr;
        substs : generic_arg list;
        vf_ty_mono : Ast.type_expr;
        interp : RustBelt.ty_interp;
      }

  let basic_type_of (ti : ty_info) =
    match ti with
    | TyInfoBasic { vf_ty } -> vf_ty
    | TyInfoGeneric { vf_ty_mono } -> vf_ty_mono

  let interp_of (ti : ty_info) =
    match ti with TyInfoBasic { interp } | TyInfoGeneric { interp } -> interp

  let raw_type_of (ti : ty_info) =
    match ti with TyInfoBasic { vf_ty } | TyInfoGeneric { vf_ty } -> vf_ty

  type annot = { span : Ast.loc; raw : string }

  type local_decl = {
    mutability : mutability;
    id : string;
    ty : ty_info;
    loc : Ast.loc;
  }

  type source_info = { span : Ast.loc; scope : unit }

  type bb_walk_state = NotSeen | Walking of int * basic_block list | Exhausted

  and basic_block = {
    id : string;
    statements : Ast.stmt list;
    terminator : Ast.stmt list;
    successors : string list;
    mutable walk_state : bb_walk_state;
    mutable is_block_head : bool;
    mutable parent : basic_block option;
        (* If this BB is inside a block (i.e. not the head), points to the innermost containing block's block head *)
    mutable children : basic_block list;
  }

  type fn_call_dst_data = { dst : Ast.expr; dst_bblock_id : string }
  type int_ty = ISize | I8 | I16 | I32 | I64 | I128

  let int_ty_to_string (it : int_ty) =
    match it with
    | ISize -> "isize"
    | I8 -> "i8"
    | I16 -> "i16"
    | I32 -> "i32"
    | I64 -> "i64"
    | I128 -> "i128"

  let int_ty_bits_len (it : int_ty) =
    match it with
    | ISize ->
        Error
          (`UIntTyBitsLen
            "The number of bits of a isize value is not specified by Rust")
    | I8 -> Ok 8
    | I16 -> Ok 16
    | I32 -> Ok 32
    | I64 -> Ok 64
    | I128 -> Ok 128

  type u_int_ty = USize | U8 | U16 | U32 | U64 | U128

  let u_int_ty_to_string (uit : u_int_ty) =
    match uit with
    | USize -> "usize"
    | U8 -> "u8"
    | U16 -> "u16"
    | U32 -> "u32"
    | U64 -> "u64"
    | U128 -> "u128"

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

  type var_debug_info_internal = VdiiPlace of { id : string } | VdiiConstant

  type var_debug_info = {
    internal : var_debug_info_internal;
    surf_name : string;
  }

  type debug_info = { id : Ast.loc; info : var_debug_info list }
  type visibility = Public | Restricted | Invisible
  type adt_kind = Struct | Enum | Union

  let decl_mir_adt_kind (d : Ast.decl) =
    match d with
    | Ast.Struct _ -> Ok Struct
    | Ast.Inductive _ -> Ok Enum
    | Ast.Union _ -> failwith "Todo: Unsupported ADT"
    | _ -> failwith "decl_mir_adt_kind: Not an ADT"

  type aggregate_kind =
    | AggKindAdt of {
        adt_kind : adt_kind;
        adt_name : string;
        variant_name : string;
        def : Ast.decl;
      }

  type field_def_tr = {
    name : string;
    ty : ty_info;
    vis : visibility;
    loc : Ast.loc;
  }

  type variant_def_tr = {
    loc : Ast.loc;
    name : string;
    fields : field_def_tr list;
  }

  type adt_def_tr = {
    loc : Ast.loc;
    name : string;
    tparams : string list;
    fds : field_def_tr list;
    def : Ast.decl;
    aux_decls : Ast.decl list;
    full_bor_content : Ast.decl option;
    proof_obligs : Ast.decl list;
  }
end

module TrTyTuple = struct
  let tuple0_name = "std_tuple_0_"

  let make_tuple_type_name tys =
    if List.length tys != 0 then
      failwith "Todo: Tuple Ty is not implemented yet"
    else tuple0_name

  let make_tuple_type_decl name tys loc =
    if List.length tys != 0 then
      failwith "Todo: Tuple Ty is not implemented yet"
    else
      Ast.Struct
        ( loc,
          name,
          [],
          Some
            ( (*base_spec list*) [],
              (*field list*) [],
              (*instance_pred_decl list*) [],
              (*is polymorphic*) false ),
          (*struct_attr list*) [] )
end

module TrTyInt = struct
  let calc_rank (bytes : SizeAux.sz_bytes) =
    let open SizeAux in
    int_of_float @@ Float.log2 @@ float_of_int @@ int_of_sz_bytes @@ bytes
end

module TrTyRawPtr = struct
  type ty_raw_ptr_info = {
    mutability : Mir.mutability;
    pointee_ty_info : Mir.ty_info;
  }
end

module TrName = struct
  let tag_internal (n : string) = "$" ^ n

  let translate_def_path (dp : string) =
    (*
    let open Str in
    let r = regexp {|::|} in
    global_replace r "_" dp
    *)
    dp

  let make_tmp_var_name base_name = tag_internal "temp_var_" ^ base_name

  let rec lft_name_without_apostrophe n =
    let open String in
    let len = length n in
    if len > 0 then
      if get n 0 = '\'' then lft_name_without_apostrophe (sub n 1 (len - 1))
      else Ok n
    else Error (`LftNameWithoutApostrophe "Empty string for name")

  let is_from_std_lib path = String.starts_with ~prefix:"std::" path
end

module type VF_MIR_TRANSLATOR_ARGS = sig
  val data_model_opt : Ast.data_model option
  val report_should_fail : string -> Ast.loc0 -> unit
  val report_range : Lexer.range_kind -> Ast.loc0 -> unit
  val report_macro_call : Ast.loc0 -> Ast.loc0 -> unit
end

module Make (Args : VF_MIR_TRANSLATOR_ARGS) = struct
  open Ocaml_aux
  module VfMirAnnotParser = Vf_mir_annot_parser.Make (Args)
  module VfMirCapnpAlias = Vf_mir_capnp_alias
  module VfMirRd = VfMirCapnpAlias.VfMirRd
  open VfMirCapnpAlias

  module CapnpAux = struct
    open Stdint

    let int128_get (i_cpn : Int128Rd.t) : Int128.t =
      let open Int128Rd in
      let open Int128 in
      let h = h_get i_cpn in
      let l = l_get i_cpn in
      let r = of_int64 h in
      let r = shift_left r 64 in
      let r = add r (of_uint64 l) in
      r

    let uint128_get (ui_cpn : UInt128Rd.t) : Uint128.t =
      let open UInt128Rd in
      let open Uint128 in
      let h = h_get ui_cpn in
      let l = l_get ui_cpn in
      let r = of_uint64 h in
      let r = shift_left r 64 in
      let r = add r (of_uint64 l) in
      r

    let rec ind_list_get_list (il_cpn : IndListRd.t) =
      let open IndListRd in
      match get il_cpn with
      | Nil -> Ok []
      | Cons cons_cpn ->
          let open Cons in
          let h_cpn = VfMirStub.Reader.of_pointer (h_get cons_cpn) in
          let t_cpn = t_get cons_cpn in
          let* t_cpn = ind_list_get_list t_cpn in
          Ok (h_cpn :: t_cpn)
      | Undefined _ ->
          Error (`CapnpIndListGetList "Unknown inductive list constructor")
  end

  let parse_header (crateName : string) (header_path : string) =
    let header_name = Filename.basename header_path in
    let decls =
      if not (Filename.check_suffix header_name ".rsspec") then
        failwith
          (Printf.sprintf "Bad header name '%s': should end with .rsspec"
             header_name);
      let ds = VfMirAnnotParser.parse_rsspec_file header_path in
      let pos = (header_path, 1, 1) in
      let loc = Ast.Lexed (pos, pos) in
      Rust_parser.flatten_module_decls loc
        [ Ast.ModuleDecl (loc, crateName, [], ds) ]
    in
    let header =
      ( Ast.dummy_loc,
        (Lexer.AngleBracketInclude, header_name, header_path),
        [],
        decls )
    in
    [ header ]

  module VF0 = Verifast0

  let translate_real_file_name (real_fname_cpn : RealFileNameRd.t) =
    let open RealFileNameRd in
    match get real_fname_cpn with
    | LocalPath path -> Ok path
    | Remapped remapped_data_cpn -> (
        let open RemappedData in
        let local_path_opt_cpn = local_path_get remapped_data_cpn in
        let virtual_name = virtual_name_get remapped_data_cpn in
        match OptionRd.get local_path_opt_cpn with
        | Nothing -> Ok virtual_name
        | Something ptr_cpn ->
            let text_wrapper_cpn = VfMirStub.Reader.of_pointer ptr_cpn in
            Ok (TextWrapperRd.text_get text_wrapper_cpn)
        | Undefined _ ->
            Error (`TrRealFileName "Unknown RealFileName::Remapped"))
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
    let (Ast.Lexed ((sf_name, sl, sc), (ef_name, el, ec))) = span in
    let* sl = IntAux.Uint64.try_to_int (start_line_get annot_cpn) in
    let* sc = IntAux.Uint64.try_to_int (start_col_get annot_cpn) in
    let* el = IntAux.Uint64.try_to_int (end_line_get annot_cpn) in
    let* ec = IntAux.Uint64.try_to_int (end_col_get annot_cpn) in
    let span = Ast.Lexed ((sf_name, sl, sc), (ef_name, el, ec)) in
    let annot : Mir.annot = { span; raw } in
    Ok annot

  let translate_annot_to_vf_parser_inp ({ span; raw } : Mir.annot) =
    let spos, epos = Ast.lexed_loc span in
    (spos, raw)

  let translate_contract (contract_cpn : ContractRd.t) =
    let open ContractRd in
    let span_cpn = span_get contract_cpn in
    let* loc = translate_span_data span_cpn in
    let* contract_opt =
      let annots_cpn = annotations_get_list contract_cpn in
      if ListAux.is_empty annots_cpn then Ok None
      else
        let* annots = ListAux.try_map translate_annotation annots_cpn in
        let annots = List.map translate_annot_to_vf_parser_inp annots in
        Ok (Some (VfMirAnnotParser.parse_func_contract annots))
    in
    Ok (loc, contract_opt)

  let translate_ghost_stmt (gs_cpn : AnnotationRd.t) =
    let open AnnotationRd in
    let* gs = translate_annotation gs_cpn in
    let gs = translate_annot_to_vf_parser_inp gs in
    Ok (VfMirAnnotParser.parse_ghost_stmt gs)

  let translate_ghost_decl_batch (gh_decl_batch_cpn : AnnotationRd.t) =
    let* gh_decl_b = translate_annotation gh_decl_batch_cpn in
    let gh_decl_b = translate_annot_to_vf_parser_inp gh_decl_b in
    Ok (VfMirAnnotParser.parse_ghost_decl_batch gh_decl_b)

  let translate_ghost_decl_block (gdb_cpn : BodyRd.GhostDeclBlock.t) =
    let open BodyRd.GhostDeclBlock in
    let open AnnotationRd in
    let* gh_decl_b = translate_annotation (start_get gdb_cpn) in
    let gh_decl_b_parser_input = translate_annot_to_vf_parser_inp gh_decl_b in
    let ghost_decls =
      VfMirAnnotParser.parse_ghost_decl_batch gh_decl_b_parser_input
    in
    let* closeBraceSpan = translate_span_data (close_brace_span_get gdb_cpn) in
    let ghost_decl_block =
      Ast.BlockStmt (gh_decl_b.span, ghost_decls, [], closeBraceSpan, ref [])
    in
    Ok ghost_decl_block

  let translate_mutability (mutability_cpn : MutabilityRd.t) =
    match MutabilityRd.get mutability_cpn with
    | Mut -> Ok Mir.Mut
    | Not -> Ok Mir.Not
    | Undefined _ ->
        Error (`TrMutability "Unknown Mir mutability discriminator")

  let translate_symbol (sym_cpn : SymbolRd.t) = SymbolRd.name_get sym_cpn

  let translate_ident (i_cpn : IdentRd.t) =
    let open IdentRd in
    let name_cpn = name_get i_cpn in
    let name = translate_symbol name_cpn in
    let span_cpn = span_get i_cpn in
    let* loc = translate_span_data span_cpn in
    Ok (name, loc)

  let translate_region (reg_cpn : RegionRd.t) = RegionRd.id_get reg_cpn
  let int_size_rank = Ast.PtrRank

  let simple_shr loc fbc_name lft tid l =
    Ok
      (Ast.CoefAsn
         ( loc,
           DummyPat,
           CallExpr
             ( loc,
               "frac_borrow",
               [],
               [],
               [
                 LitPat lft;
                 LitPat
                   (CallExpr
                      (loc, fbc_name, [], [], [ LitPat tid; LitPat l ], Static));
               ],
               Static ) ))

  let simple_shr_pred loc fbc_name =
    Ok
      (Ast.CallExpr
         (loc, "simple_share", [], [], [ LitPat (Var (loc, fbc_name)) ], Static))

  let translate_int_ty (int_ty_cpn : IntTyRd.t) (loc : Ast.loc) =
    let open Ast in
    let sz_rank_name i =
      let open SizeAux in
      let* bits = Mir.int_ty_bits_len i in
      let* sz_bits = sz_bits_of_int bits in
      let sz_bytes = sz_bytes_of_sz_bits sz_bits in
      let sz_expr =
        IntLit
          ( loc,
            Big_int.big_int_of_int @@ int_of_sz_bytes @@ sz_bytes,
            (*decimal*) true,
            (*U suffix*) true,
            NoLSuffix )
      in
      let rank = FixedWidthRank (TrTyInt.calc_rank sz_bytes) in
      Ok (sz_expr, rank, Mir.int_ty_to_string i)
    in
    let* sz_expr, rank, ty_name =
      match IntTyRd.get int_ty_cpn with
      | ISize ->
          (* isize is pointer-sized *)
          let ptr_sz_expr =
            SizeofExpr (loc, TypeExpr (ManifestTypeExpr (loc, PtrType Void)))
          in
          Ok (ptr_sz_expr, int_size_rank, Mir.int_ty_to_string Mir.ISize)
      | I8 -> sz_rank_name Mir.I8
      | I16 -> sz_rank_name Mir.I16
      | I32 -> sz_rank_name Mir.I32
      | I64 -> sz_rank_name Mir.I64
      | I128 -> sz_rank_name Mir.I128
      | Undefined _ -> Error (`TrIntTy "Unknown Rust int type")
    in
    let own tid vs = Ok (True loc) in
    let own_pred = Ok (Var (loc, ty_name ^ "_own")) in
    let fbc_name = ty_name ^ "_full_borrow_content" in
    let full_bor_content = Ok (Var (loc, fbc_name)) in
    let points_to tid l vid_op =
      (* Todo: The size and bounds of the integer that this assertion is specifying will depend on the pointer `l` type
         which is error-prone. It is helpful if we add a sanity-check or use elevated `integer_(...)` predicates with bound infos *)
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, pat))
    in
    let ty_info =
      Mir.TyInfoBasic
        {
          vf_ty = ManifestTypeExpr (loc, Int (Signed, rank));
          interp =
            RustBelt.
              {
                size = sz_expr;
                own;
                own_pred;
                shr = simple_shr loc fbc_name;
                shr_pred = simple_shr_pred loc fbc_name;
                full_bor_content;
                points_to;
              };
        }
    in
    Ok ty_info

  let translate_u_int_ty (u_int_ty_cpn : UIntTyRd.t) (loc : Ast.loc) =
    let open Ast in
    let sz_rank_name ui =
      let open SizeAux in
      let* bits = Mir.u_int_ty_bits_len ui in
      let* sz_bits = sz_bits_of_int bits in
      let sz_bytes = sz_bytes_of_sz_bits sz_bits in
      let sz_expr =
        IntLit
          ( loc,
            Big_int.big_int_of_int @@ int_of_sz_bytes @@ sz_bytes,
            (*decimal*) true,
            (*U suffix*) true,
            NoLSuffix )
      in
      let rank = FixedWidthRank (TrTyInt.calc_rank sz_bytes) in
      Ok (sz_expr, rank, Mir.u_int_ty_to_string ui)
    in
    let* sz_expr, rank, ty_name =
      match UIntTyRd.get u_int_ty_cpn with
      | USize ->
          (* usize is pointer-sized *)
          let ptr_sz_expr =
            SizeofExpr (loc, TypeExpr (ManifestTypeExpr (loc, PtrType Void)))
          in
          Ok (ptr_sz_expr, int_size_rank, Mir.u_int_ty_to_string Mir.USize)
      | U8 -> sz_rank_name Mir.U8
      | U16 -> sz_rank_name Mir.U16
      | U32 -> sz_rank_name Mir.U32
      | U64 -> sz_rank_name Mir.U64
      | U128 -> sz_rank_name Mir.U128
      | Undefined _ -> Error (`TrUIntTy "Unknown Rust unsigned int type")
    in
    let own tid vs = Ok (True loc) in
    let own_pred = Ok (Var (loc, ty_name ^ "_own")) in
    let fbc_name = ty_name ^ "_full_borrow_content" in
    let full_bor_content = Ok (Var (loc, fbc_name)) in
    let points_to tid l vid_op =
      (* Todo: The size and bounds of the integer that this assertion is specifying will depend on the pointer `l` type
         which is error-prone. It is helpful if we add a sanity-check or use elevated `integer_(...)` predicates with bound infos *)
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, pat))
    in
    let ty_info =
      Mir.TyInfoBasic
        {
          vf_ty = ManifestTypeExpr (loc, Int (Unsigned, rank));
          interp =
            RustBelt.
              {
                size = sz_expr;
                own;
                own_pred;
                shr = simple_shr loc fbc_name;
                shr_pred = simple_shr_pred loc fbc_name;
                full_bor_content;
                points_to;
              };
        }
    in
    Ok ty_info

  let translate_adt_def_id (adt_def_id_cpn : AdtDefIdRd.t) =
    AdtDefIdRd.name_get adt_def_id_cpn

  let rec translate_adt_ty (adt_ty_cpn : AdtTyRd.t) (loc : Ast.loc) =
    let open AdtTyRd in
    let open Ast in
    let def_path = translate_adt_def_id @@ id_get @@ adt_ty_cpn in
    let name = TrName.translate_def_path def_path in
    let kind = AdtKindRd.get @@ kind_get @@ adt_ty_cpn in
    let substs_cpn = substs_get_list adt_ty_cpn in
    match kind with
    | StructKind -> (
        match def_path with
        | "std::alloc::Layout" ->
            (* Todo: To handle the ADTs from std lib we should use the original definition and search for their external-specs in VeriFast headers
               e.g. `external struct std::alloc::Layout; //@ ordinary_type` *)
            if not @@ ListAux.is_empty @@ substs_cpn then
              Error
                (`TrAdtTy (def_path ^ " should not have any generic parameter"))
            else
              let open TyBd.UIntTy in
              let usz_ty_cpn = init_root () in
              u_size_set usz_ty_cpn;
              translate_u_int_ty (to_reader usz_ty_cpn) loc
        | "std::cell::UnsafeCell" | "std::mem::ManuallyDrop" ->
            let [ arg_cpn ] = substs_cpn in
            let* (Mir.GenArgType arg_ty) = translate_generic_arg arg_cpn loc in
            Ok arg_ty
        | _ ->
            let* targs =
              ListAux.try_map
                (fun targ_cpn -> translate_generic_arg targ_cpn loc)
                substs_cpn
            in
            let targs =
              targs
              |> List.map @@ function
                 | Mir.GenArgLifetime ->
                     raise
                       (Ast.StaticError
                          ( loc,
                            "Lifetime arguments are not yet supported here",
                            None ))
                 | Mir.GenArgType arg_ty -> Mir.basic_type_of arg_ty
                 | Mir.GenArgConst ->
                     raise
                       (Ast.StaticError
                          ( loc,
                            "Const arguments are not yet supported here",
                            None ))
            in
            let vf_ty = StructTypeExpr (loc, Some name, None, [], targs) in
            let sz_expr = SizeofExpr (loc, TypeExpr vf_ty) in
            let own tid vs =
              let args = List.map (fun x -> LitPat x) (tid :: vs) in
              Ok
                (CallExpr
                   ( loc,
                     name ^ "_own",
                     (*type arguments*) [],
                     (*indices*) [],
                     args,
                     Static ))
            in
            let own_pred = Ok (Var (loc, name ^ "_own_")) in
            let shr lft tid l =
              Ok
                (CoefAsn
                   ( loc,
                     DummyPat,
                     CallExpr
                       ( loc,
                         name ^ "_share",
                         (*type arguments*) [],
                         (*indices*) [],
                         (*arguments*)
                         [ LitPat lft; LitPat tid; LitPat l ],
                         Static ) ))
            in
            let shr_pred = Ok (Var (loc, name ^ "_share")) in
            let full_bor_content =
              Ok (Var (loc, name ^ "_full_borrow_content"))
            in
            (* Todo: Nested structs *)
            let points_to tid l vid_op = Ok (True loc) in
            let interp =
              RustBelt.
                {
                  size = sz_expr;
                  own;
                  own_pred;
                  shr;
                  shr_pred;
                  full_bor_content;
                  points_to;
                }
            in
            let ty_info = Mir.TyInfoBasic { vf_ty; interp } in
            Ok ty_info)
    | EnumKind ->
        let* targs =
          ListAux.try_map
            (fun targ_cpn -> translate_generic_arg targ_cpn loc)
            substs_cpn
        in
        let targs =
          targs
          |> List.map @@ function
             | Mir.GenArgLifetime ->
                 raise
                   (Ast.StaticError
                      ( loc,
                        "Lifetime arguments are not yet supported here",
                        None ))
             | Mir.GenArgType arg_ty -> Mir.basic_type_of arg_ty
             | Mir.GenArgConst ->
                 raise
                   (Ast.StaticError
                      (loc, "Const arguments are not yet supported here", None))
        in
        let vf_ty = ConstructedTypeExpr (loc, name, targs) in
        let sz_expr = SizeofExpr (loc, TypeExpr vf_ty) in
        let own tid vs =
          Error "Expressing ownership of an enum value is not yet supported"
        in
        let own_pred =
          Error
            "Expressing the ownership predicate of an enum value is not yet \
             supported"
        in
        let shr lft tid l =
          Error
            "Expressing shared ownership of an enum value is not yet supported"
        in
        let shr_pred =
          Error
            "Expressing the shared ownership predicate of an enum value is not \
             yet supported"
        in
        let full_bor_content =
          Error
            "Expressing the full borrow content of an enum value is not yet \
             supported"
        in
        (* Todo: Nested structs *)
        let points_to tid l vid_op =
          Error
            "Expressing a points-to assertion for an enum pointer is not yet \
             supported"
        in
        let interp =
          RustBelt.
            {
              size = sz_expr;
              own;
              own_pred;
              shr;
              shr_pred;
              full_bor_content;
              points_to;
            }
        in
        let ty_info = Mir.TyInfoBasic { vf_ty; interp } in
        Ok ty_info
    | UnionKind -> failwith "Todo: AdtTy::Union"
    | Undefined _ -> Error (`TrAdtTy "Unknown ADT kind")

  and translate_tuple_ty (substs_cpn : GenArgRd.t list) (loc : Ast.loc) =
    if not @@ ListAux.is_empty @@ substs_cpn then
      failwith "Todo: Tuple Ty is not implemented yet"
    else
      let name = TrTyTuple.make_tuple_type_name [] in
      (* TODO @Nima: std_tuple_0_ type is declared in prelude_rust_.h.
         We should come up with a better arrangement for these auxiliary types. *)
      let ty_info =
        Mir.TyInfoBasic
          {
            vf_ty = Ast.ManifestTypeExpr (loc, Ast.StructType (name, []));
            interp = RustBelt.emp_ty_interp loc;
          }
      in
      Ok ty_info

  and bool_ty_info loc =
    let open Ast in
    let vf_ty = ManifestTypeExpr (loc, Bool) in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own _ _ = Ok (True loc) in
    let own_pred = Ok (Var (loc, "bool_own")) in
    let fbc_name = "bool_full_borrow_content" in
    let full_bor_content = Ok (Var (loc, fbc_name)) in
    let points_to tid l vid_op =
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, pat))
    in
    Mir.TyInfoBasic
      {
        vf_ty;
        interp =
          RustBelt.
            {
              size;
              own;
              own_pred;
              shr = simple_shr loc fbc_name;
              shr_pred = simple_shr_pred loc fbc_name;
              full_bor_content;
              points_to;
            };
      }

  and char_ty_info loc =
    let open Ast in
    let vf_ty =
      ManifestTypeExpr (loc, Int (Unsigned, FixedWidthRank 2))
      (* https://doc.rust-lang.org/reference/types/textual.html *)
    in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own tid vs =
      match vs with
      | [ c ] ->
          Ok
            (CallExpr
               ( loc,
                 "char_own",
                 (*type arguments*) [],
                 (*indices*) [],
                 [ LitPat tid; LitPat c ],
                 Static ))
          (* Todo: According to https://doc.rust-lang.org/reference/types/textual.html,
             "It is immediate Undefined Behavior to create a char that falls outside this (0 <= v && v <= 0xD7FF || 0xE000 <= v && v <= 0x10FFFF) range".
             So it is not enough to check char ranges in function boundaries. Miri warns about UB when reading an out-of-range character.
             A proposal is to translate char-ptr/ref dereferences to calls to a function with a contract that checks for the range. *)
      | _ -> Error "[[char]].own(tid, vs) should have `vs == [c]`"
    in
    let own_pred = Ok (Var (loc, "char_own")) in
    let shr = Ok (Var (loc, "char_share")) in
    let fbc_name = "char_full_borrow_content" in
    let full_bor_content = Ok (Var (loc, fbc_name)) in
    let points_to tid l vid_op =
      match vid_op with
      | Some vid when vid != "" ->
          let var_pat = VarPat (loc, vid) in
          let var_expr = Var (loc, vid) in
          let* own = own tid [ var_expr ] in
          Ok (Sep (loc, PointsTo (loc, l, var_pat), own))
      | _ -> Error "char points_to needs a value id"
    in
    Mir.TyInfoBasic
      {
        vf_ty;
        interp =
          RustBelt.
            {
              size;
              own;
              own_pred;
              shr = simple_shr loc fbc_name;
              shr_pred = simple_shr_pred loc fbc_name;
              full_bor_content;
              points_to;
            };
      }

  and never_ty_info loc =
    let open Ast in
    let vf_ty = ManifestTypeExpr (loc, UnionType "std_empty_") in
    let size =
      IntLit
        ( loc,
          Big_int.zero_big_int,
          (*decimal*) false,
          (*U suffix*) true,
          NoLSuffix )
    in
    let own _ _ = Ok (False loc) in
    let own_pred =
      Error
        "Calling a function with `!` as a generic type argument is not yet \
         supported"
    in
    let shr lft tid l =
      Error
        "Expressing the shared ownership of the never type is not yet supported"
    in
    let shr_pred =
      Error
        "Expressing the shared ownership of the never type is not yet supported"
    in
    let full_bor_content =
      Error
        "Expressing the full borrow content of the never type is not yet \
         supported"
    in
    let points_to _ _ _ = Ok (False loc) in
    Mir.TyInfoBasic
      {
        vf_ty;
        interp =
          RustBelt.
            { size; own; own_pred; shr; shr_pred; full_bor_content; points_to };
      }

  and str_ref_ty_info loc =
    let open Ast in
    let vf_ty = ManifestTypeExpr (loc, StructType ("str_ref", [])) in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own tid vs =
      Error "Expressing ownership of &str values is not yet supported"
    in
    let own_pred =
      Error
        "Passing type &str as a type argument to a generic function is not yet \
         supported"
    in
    let shr lft tid l =
      Error "Expressing shared ownership of &str values is not yet supported"
    in
    let shr_pred =
      Error "Expressing shared ownership of &str values is not yet supported"
    in
    let full_bor_content =
      Error
        "Expressing the full borrow content of &str values is not yet supported"
    in
    let points_to tid l vid_op =
      Error
        "Expressing a points-to assertion for a &str object is not yet \
         supported"
    in
    Mir.TyInfoBasic
      {
        vf_ty;
        interp =
          RustBelt.
            { size; own; own_pred; shr; shr_pred; full_bor_content; points_to };
      }

  and slice_ref_ty_info loc elem_ty_info =
    let open Ast in
    let vf_ty =
      StructTypeExpr
        (loc, Some "slice_ref", None, [], [ Mir.basic_type_of elem_ty_info ])
    in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own tid vs =
      Error "Expressing ownership of &[_] values is not yet supported"
    in
    let own_pred =
      Error
        "Passing type &[_] as a type argument to a generic function is not yet \
         supported"
    in
    let shr lft tid l =
      Error "Expressing shared ownership of &[_] values is not yet supported"
    in
    let shr_pred =
      Error "Expressing shared ownership of &[_] values is not yet supported"
    in
    let full_bor_content =
      Error
        "Expressing the full borrow content of &[_] values is not yet supported"
    in
    let points_to tid l vid_op =
      Error
        "Expressing a points-to assertion for a &[_] object is not yet \
         supported"
    in
    Mir.TyInfoBasic
      {
        vf_ty;
        interp =
          RustBelt.
            { size; own; own_pred; shr; shr_pred; full_bor_content; points_to };
      }

  and translate_generic_arg (gen_arg_cpn : GenArgRd.t) (loc : Ast.loc) =
    let open GenArgRd in
    let kind_cpn = kind_get gen_arg_cpn in
    let open GenArgKindRd in
    match get kind_cpn with
    | Lifetime -> failwith "Todo: Generic arg. lifetime is not supported yet"
    | Type ty_cpn ->
        let* ty_info = translate_ty ty_cpn loc in
        Ok (Mir.GenArgType ty_info)
    | Const _ -> Ok Mir.GenArgConst
    | Undefined _ -> Error (`TrGenArg "Unknown generic arg. kind")

  and decode_generic_arg (gen_arg_cpn : GenArgRd.t) =
    let open GenArgRd in
    let kind_cpn = kind_get gen_arg_cpn in
    let open GenArgKindRd in
    match get kind_cpn with
    | Lifetime -> failwith "Todo: Generic arg. lifetime is not supported yet"
    | Type ty_cpn -> `Type (decode_ty ty_cpn)
    | Const _ -> `Const
    | Undefined _ -> `Undefined

  and translate_fn_name (name : string) (substs_cpn : GenArgRd.t list) =
    match (name, lazy (List.map decode_generic_arg substs_cpn)) with
    | ( "std::ops::Deref::deref",
        (lazy [ `Type (`Adt ("std::mem::ManuallyDrop", _, _)) ]) ) ->
        "std::mem::ManuallyDrop::deref"
    | ( "std::ops::DerefMut::deref_mut",
        (lazy [ `Type (`Adt ("std::mem::ManuallyDrop", _, _)) ]) ) ->
        "std::mem::ManuallyDrop::deref_mut"
    | _ -> name

  and translate_fn_def_ty (fn_def_ty_cpn : FnDefTyRd.t) (loc : Ast.loc) =
    let open FnDefTyRd in
    let id_cpn = id_get fn_def_ty_cpn in
    let id = FnDefIdRd.name_get id_cpn in
    let name = TrName.translate_def_path id in
    let substs_cpn = substs_get_list fn_def_ty_cpn in
    let vf_ty =
      Ast.ManifestTypeExpr
        (loc, Ast.FuncType (translate_fn_name name substs_cpn))
    in
    let id_mono_cpn = id_mono_get fn_def_ty_cpn in
    match OptionRd.get id_mono_cpn with
    | Nothing ->
        if not (ListAux.is_empty substs_cpn) then
          Error (`TrFnDefTy "Simple function type with generic arg(s)")
        else Ok (Mir.TyInfoBasic { vf_ty; interp = RustBelt.emp_ty_interp loc })
    | Something ptr_cpn ->
        if ListAux.is_empty substs_cpn then
          Error (`TrFnDefTy "Generic function type without generic arg(s)")
        else
          let id_mono_cpn = VfMirStub.Reader.of_pointer ptr_cpn in
          let id_mono = FnDefIdRd.name_get id_mono_cpn in
          let name_mono = TrName.translate_def_path id_mono in
          let vf_ty_mono = Ast.ManifestTypeExpr (loc, Ast.FuncType name_mono) in
          let* substs =
            ListAux.try_map
              (fun subst_cpn -> translate_generic_arg subst_cpn loc)
              substs_cpn
          in
          Ok
            (Mir.TyInfoGeneric
               {
                 vf_ty;
                 substs;
                 vf_ty_mono;
                 interp = RustBelt.emp_ty_interp loc;
               })

  and translate_fn_ptr_ty (fn_ptr_ty_cpn : FnPtrTyRd.t) (loc : Ast.loc) =
    let open FnPtrTyRd in
    let output_cpn = output_get fn_ptr_ty_cpn in
    let* (TyInfoBasic { vf_ty = output_ty }) = translate_ty output_cpn loc in
    Ok
      (Mir.TyInfoBasic
         {
           vf_ty = FuncTypeExpr (loc, output_ty, []);
           (* Only the return type matters *)
           interp = RustBelt.emp_ty_interp loc;
         })

  and translate_raw_ptr_ty (raw_ptr_ty_cpn : RawPtrTyRd.t) (loc : Ast.loc) =
    let open RawPtrTyRd in
    let open Ast in
    let mut_cpn = mutability_get raw_ptr_ty_cpn in
    let* mutability = translate_mutability mut_cpn in
    let ty_cpn = ty_get raw_ptr_ty_cpn in
    let* pointee_ty_info = translate_ty ty_cpn loc in
    let pointee_ty = Mir.basic_type_of pointee_ty_info in
    let vf_ty = PtrTypeExpr (loc, pointee_ty) in
    let size_expr = SizeofExpr (loc, TypeExpr vf_ty) in
    let own tid vs = Ok (True loc) in
    let own_pred = Ok (Var (loc, "raw_ptr_own")) in
    let fbc_name = "raw_ptr_full_borrow_content" in
    let full_bor_content = Ok (Var (loc, fbc_name)) in
    let points_to tid l vid_op =
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, pat))
    in
    let ty_info =
      Mir.TyInfoBasic
        {
          vf_ty;
          interp =
            RustBelt.
              {
                size = size_expr;
                own;
                own_pred;
                shr = simple_shr loc fbc_name;
                shr_pred = simple_shr_pred loc fbc_name;
                full_bor_content;
                points_to;
              };
        }
    in
    Ok ty_info

  and translate_ref_ty (ref_ty_cpn : RefTyRd.t) (loc : Ast.loc) =
    let open RefTyRd in
    let open Ast in
    let region_cpn = region_get ref_ty_cpn in
    let region = translate_region region_cpn in
    let lft = Var (loc, region) in
    let mut_cpn = mutability_get ref_ty_cpn in
    let* mut = translate_mutability mut_cpn in
    let ty_cpn = ty_get ref_ty_cpn in
    match TyRd.TyKind.get @@ TyRd.kind_get ty_cpn with
    | Str -> Ok (str_ref_ty_info loc)
    | Slice elem_ty_cpn ->
        let* elem_ty_info = translate_ty elem_ty_cpn loc in
        Ok (slice_ref_ty_info loc elem_ty_info)
    | _ ->
        let* pointee_ty_info = translate_ty ty_cpn loc in
        let pointee_ty = Mir.basic_type_of pointee_ty_info in
        let vf_ty = PtrTypeExpr (loc, pointee_ty) in
        let sz_expr = SizeofExpr (loc, TypeExpr vf_ty) in
        let RustBelt.
              {
                size = ptee_sz;
                own = ptee_own;
                shr = ptee_shr;
                full_bor_content = ptee_fbc;
                points_to = ptee_points_to;
              } =
          Mir.interp_of pointee_ty_info
        in
        let* own, own_pred, shr, shr_pred, full_bor_content, points_to =
          match mut with
          | Mir.Mut ->
              let own tid vs =
                match vs with
                | [ l ] ->
                    let* ptee_fbc = ptee_fbc in
                    let ptee_fbc = ExprCallExpr (loc, ptee_fbc, [ tid; l ]) in
                    Ok
                      (CallExpr
                         ( loc,
                           "full_borrow",
                           (*type arguments*) [],
                           (*indices*) [],
                           (*arguments*)
                           [ LitPat lft; LitPat ptee_fbc ],
                           Static ))
                | _ -> Error "[[&mut T]].own(tid, vs) needs to vs == [l]"
              in
              let own_pred =
                Error
                  "Calling a function with a mutable reference type as a \
                   generic type argument is not yet supported"
              in
              let shr lft tid l =
                Error
                  "Calling a function with a mutable reference type as a \
                   generic type argument is not yet supported"
              in
              let shr_pred =
                Error
                  "Calling a function with a mutable reference type as a \
                   generic type argument is not yet supported"
              in
              let full_bor_content =
                (* This will need to add a definition for each mut reference type in the program because the body of the predicate will need to mention
                   [[&mut T]].own which depends on T. Another solution is to make VeriFast support Higher order predicates with non-predicate arguments *)
                Error
                  "Expressing the full borrow content of a mutable reference \
                   type is not yet supported"
                (* CallExpr
                   ( loc,
                     "mut_ref_full_borrow_content",
                     (*type arguments*) [],
                     (*indices*) [],
                     (*arguments*)
                     [ LitPat tid; LitPat l ],
                     Static ) *)
              in
              let points_to tid l vid_op =
                match vid_op with
                | Some vid when vid != "" ->
                    let var_pat = VarPat (loc, vid) in
                    let var_expr = Var (loc, vid) in
                    let* own = own tid [ var_expr ] in
                    Ok (Sep (loc, PointsTo (loc, l, var_pat), own))
                | _ -> Error "mut reference points_to needs a value id"
              in
              Ok (own, own_pred, shr, shr_pred, full_bor_content, points_to)
          | Mir.Not ->
              let own tid vs =
                match vs with
                | [ l ] -> ptee_shr lft tid l
                | _ -> Error "[[&T]].own(tid, vs) needs to vs == [l]"
              in
              let own_pred =
                Error
                  "Calling a function with a shared reference type as a \
                   generic type argument is not yet supported"
              in
              let shr lft tid l =
                Error
                  "Calling a function with a shared reference type as a \
                   generic type argument is not yet supported"
              in
              let shr_pred =
                Error
                  "Calling a function with a shared reference type as a \
                   generic type argument is not yet supported"
              in
              let full_bor_content =
                Error
                  "Expressing the full borrow content of a shared reference \
                   type is not yet supported"
              in
              let points_to tid l vid_op =
                match vid_op with
                | Some vid when vid != "" ->
                    let var_pat = VarPat (loc, vid) in
                    let var_expr = Var (loc, vid) in
                    let* own = own tid [ var_expr ] in
                    Ok (Sep (loc, PointsTo (loc, l, var_pat), own))
                | _ -> Error "shared reference points_to needs a value id"
              in
              Ok (own, own_pred, shr, shr_pred, full_bor_content, points_to)
        in
        let ty_info =
          Mir.TyInfoBasic
            {
              vf_ty;
              interp =
                RustBelt.
                  {
                    size = sz_expr;
                    own;
                    own_pred;
                    shr;
                    shr_pred;
                    full_bor_content;
                    points_to;
                  };
            }
        in
        Ok ty_info

  and decode_adt_ty (adt_ty_cpn : AdtTyRd.t) =
    let open AdtTyRd in
    let def_path = AdtDefIdRd.name_get @@ id_get @@ adt_ty_cpn in
    let kind = AdtKindRd.get @@ kind_get @@ adt_ty_cpn in
    let substs_cpn = substs_get_list adt_ty_cpn in
    (def_path, kind, List.map decode_generic_arg substs_cpn)

  and decode_ty (ty_cpn : TyRd.t) =
    let open TyRd in
    let kind_cpn = kind_get ty_cpn in
    match TyRd.TyKind.get kind_cpn with
    | Bool -> `Bool
    | Int int_ty_cpn -> `Int
    | UInt u_int_ty_cpn -> `Uint
    | Char -> `Char
    | Adt adt_ty_cpn -> `Adt (decode_adt_ty adt_ty_cpn)
    | RawPtr raw_ptr_ty_cpn -> `RawPtr
    | Ref ref_ty_cpn -> `Ref
    | FnDef fn_def_ty_cpn -> `FnDef
    | FnPtr fn_ptr_ty_cpn -> `FnPtr
    | Never -> `Never
    | Tuple substs_cpn -> `Tuple
    | Param name -> `Param
    | Undefined _ -> `Undefined

  and translate_ty (ty_cpn : TyRd.t) (loc : Ast.loc) =
    let open Ast in
    let open TyRd in
    let kind_cpn = kind_get ty_cpn in
    match TyRd.TyKind.get kind_cpn with
    | Bool -> Ok (bool_ty_info loc)
    | Int int_ty_cpn -> translate_int_ty int_ty_cpn loc
    | UInt u_int_ty_cpn -> translate_u_int_ty u_int_ty_cpn loc
    | Char -> Ok (char_ty_info loc)
    | Adt adt_ty_cpn -> translate_adt_ty adt_ty_cpn loc
    | RawPtr raw_ptr_ty_cpn -> translate_raw_ptr_ty raw_ptr_ty_cpn loc
    | Ref ref_ty_cpn -> translate_ref_ty ref_ty_cpn loc
    | FnDef fn_def_ty_cpn -> translate_fn_def_ty fn_def_ty_cpn loc
    | FnPtr fn_ptr_ty_cpn -> translate_fn_ptr_ty fn_ptr_ty_cpn loc
    | Never -> Ok (never_ty_info loc)
    | Tuple substs_cpn ->
        let substs_cpn = Capnp.Array.to_list substs_cpn in
        translate_tuple_ty substs_cpn loc
    | Param name ->
        let vf_ty = ManifestTypeExpr (loc, GhostTypeParam name) in
        let interp : RustBelt.ty_interp =
          {
            size = SizeofExpr (loc, TypeExpr vf_ty);
            own =
              (fun t vs ->
                Ok
                  (Ast.ExprCallExpr
                     ( loc,
                       TypePredExpr (loc, IdentTypeExpr (loc, None, name), "own"),
                       t :: vs )));
            own_pred =
              Ok (TypePredExpr (loc, IdentTypeExpr (loc, None, name), "own"));
            shr =
              (fun k t l ->
                Ok
                  (CoefAsn
                     ( loc,
                       DummyPat,
                       ExprCallExpr
                         ( loc,
                           TypePredExpr
                             (loc, IdentTypeExpr (loc, None, name), "share"),
                           [ k; t; l ] ) )));
            shr_pred =
              Ok (TypePredExpr (loc, IdentTypeExpr (loc, None, name), "share"));
            full_bor_content =
              Ok
                (TypePredExpr
                   (loc, IdentTypeExpr (loc, None, name), "full_borrow_content"));
            points_to =
              (fun t l vid ->
                let rhs =
                  match vid with
                  | None -> DummyPat
                  | Some vid -> VarPat (loc, vid)
                in
                Ok (Ast.PointsTo (loc, l, rhs)));
          }
        in
        Ok (Mir.TyInfoBasic { vf_ty; interp })
    | Undefined _ -> Error (`TrTy "Unknown Rust type kind")

  type body_tr_defs_ctx = { adt_defs : Mir.adt_def_tr list }
  type var_id_trs_entry = { id : string; internal_name : string }
  type var_id_trs_map = var_id_trs_entry list

  module TrBody (Args : sig
    val var_id_trs_map_ref : var_id_trs_map ref
    val ghost_stmts : Ast.stmt list
    val body_imp_loc : Ast.loc
    val body_tr_defs_ctx : body_tr_defs_ctx
  end) =
  struct
    module State = struct
      let var_id_trs_map_ref = Args.var_id_trs_map_ref
      let ghost_stmts = ref Args.ghost_stmts
      let body_imp_loc = Args.body_imp_loc
      let body_tr_defs_ctx = Args.body_tr_defs_ctx

      let fetch_ghost_stmts_before (l : Ast.loc0) =
        let* gs_before, gs_rem =
          ListAux.try_partition
            (fun g ->
              let lg = Ast.lexed_loc (Ast.stmt_loc g) in
              let* cmp = LocAux.try_compare_loc lg l in
              Ok (cmp < 0))
            !ghost_stmts
        in
        ghost_stmts := gs_rem;
        Ok gs_before

      let get_adt_def adt_name =
        Ok
          (List.find_opt
             (fun ({ name } : Mir.adt_def_tr) -> name = adt_name)
             body_tr_defs_ctx.adt_defs)
    end

    let translate_local_decl_id (local_decl_id_cpn : LocalDeclIdRd.t) =
      let id = TrName.tag_internal (LocalDeclIdRd.name_get local_decl_id_cpn) in
      match
        List.find_opt
          (fun ({ id = id1; _ } : var_id_trs_entry) -> id = id1)
          !State.var_id_trs_map_ref
      with
      | None -> id
      | Some { id; internal_name } -> internal_name

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
              Some ty,
              id,
              None,
              ( (* indicates whether address is taken *) ref false,
                (* pointer to enclosing block's list of variables whose address is taken *)
                ref None ) );
          ] )

    type place_element =
      | Deref
      | Field of string option * int
      | Downcast of int

    let decode_place_element (place_elm : PlaceElementRd.t) : place_element =
      let open PlaceElementRd in
      match get place_elm with
      | Deref -> Deref
      | Field field_data_cpn ->
          let open FieldData in
          let index = index_get field_data_cpn in
          let name_cpn = name_get field_data_cpn in
          let name =
            match OptionRd.get name_cpn with
            | Nothing -> None
            | Something name_cpn ->
                Some (SymbolRd.name_get (VfMirStub.Reader.of_pointer name_cpn))
          in
          Field (name, Stdint.Uint32.to_int index)
      | Downcast variant_index -> Downcast (Stdint.Uint32.to_int variant_index)

    let translate_projection (loc : Ast.loc) (elems : place_element list)
        (e : Ast.expr) =
      let rec iter elems =
        match elems with
        | [] -> e
        | Deref :: elems -> Ast.Deref (loc, iter elems)
        | Field (_, field_idx) :: Downcast variant_idx :: elems ->
            Ast.CallExpr
              ( loc,
                "#inductive_projection",
                [],
                [],
                [
                  LitPat (iter elems);
                  LitPat (WIntLit (loc, Big_int.big_int_of_int variant_idx));
                  LitPat (WIntLit (loc, Big_int.big_int_of_int field_idx));
                ],
                Static )
        | Field (Some name, _) :: elems -> Ast.Select (loc, iter elems, name)
        | Field (None, _) :: _ ->
            failwith "Not yet supported: Field(None, _)::_"
        | Downcast _ :: _ -> failwith "Not yet supported: Downcast _::_"
      in
      iter elems

    let translate_place (place_cpn : PlaceRd.t) (loc : Ast.loc) =
      let open PlaceRd in
      let id_cpn = local_get place_cpn in
      let id = translate_local_decl_id id_cpn in
      let projection_cpn = projection_get_list place_cpn in
      let place_elems = List.map decode_place_element projection_cpn in
      Ok (translate_projection loc (List.rev place_elems) (Ast.Var (loc, id)))

    let translate_scalar_int (si_cpn : ScalarRd.Int.t) (ty : Ast.type_expr)
        (loc : Ast.loc) =
      let mk_const v =
        let open Ast in
        let lit =
          IntLit (loc, v, (*decimal*) true, (*U suffix*) false, LLSuffix)
        in
        Ok (CastExpr (loc, ty, lit))
      in
      let open ScalarRd.Int in
      let open IntAux in
      match get si_cpn with
      | Isize v_cpn | I128 v_cpn ->
          let vi128 = Int128.to_big_int (CapnpAux.int128_get v_cpn) in
          mk_const vi128
      | I8 v | I16 v -> mk_const (Big_int.big_int_of_int v)
      | I32 vi32 -> mk_const (Int32.to_big_int vi32)
      | I64 vi64 -> mk_const (Int64.to_big_int vi64)
      | Undefined _ -> Error (`TrScalarInt "Unknown Int type")

    let translate_scalar_u_int (sui_cpn : ScalarRd.UInt.t) (ty : Ast.type_expr)
        (loc : Ast.loc) =
      let mk_const v =
        let open Ast in
        let lit =
          IntLit (loc, v, (*decimal*) true, (*U suffix*) true, LLSuffix)
        in
        Ok (CastExpr (loc, ty, lit))
      in
      let open ScalarRd.UInt in
      let open IntAux in
      match get sui_cpn with
      | Usize v_cpn | U128 v_cpn ->
          let vui128 = Uint128.to_big_int (CapnpAux.uint128_get v_cpn) in
          mk_const vui128
      | U8 v | U16 v -> mk_const (Big_int.big_int_of_int v)
      | U32 vu32 -> mk_const (Uint32.to_big_int vu32)
      | U64 vu64 -> mk_const (Uint64.to_big_int vu64)
      | Undefined _ -> Error (`TrScalarUint "Unknown Uint type")

    let translate_scalar (s_cpn : ScalarRd.t) (ty : Ast.type_expr)
        (loc : Ast.loc) =
      let open ScalarRd in
      match get s_cpn with
      | Bool b -> Ok (if b then Ast.True loc else Ast.False loc)
      | Char code ->
          let open Ast in
          Ok
            (CastExpr
               ( loc,
                 ManifestTypeExpr (loc, Int (Unsigned, FixedWidthRank 2)),
                 IntLit
                   (loc, IntAux.Uint32.to_big_int code, true, true, LLSuffix) ))
      | Int int_cpn -> translate_scalar_int int_cpn ty loc
      | Uint u_int_cpn -> translate_scalar_u_int u_int_cpn ty loc
      | Float float_cpn -> failwith "Todo: Scalar::Float"
      | FnDef -> failwith "Todo: Scalar::FnDef"
      | Undefined _ -> Error (`TrScalar "Unknown Scalar kind")

    let mk_unit_expr loc =
      Ast.CastExpr
        ( loc,
          StructTypeExpr (loc, Some TrTyTuple.tuple0_name, None, [], []),
          InitializerList (loc, []) )

    let translate_unit_constant (loc : Ast.loc) =
      let rvalue_binder_builder tmp_var_name =
        Ast.DeclStmt
          ( loc,
            [
              ( loc,
                Some
                  (Ast.ManifestTypeExpr
                     (loc, Ast.StructType (TrTyTuple.tuple0_name, []))),
                tmp_var_name,
                Some (Ast.InitializerList (loc, [])),
                ( (*indicates whether address is taken*) ref false,
                  (*pointer to enclosing block's list of variables whose address is taken*)
                  ref None ) );
            ] )
      in
      Ok (`TrTypedConstantRvalueBinderBuilder rvalue_binder_builder)

    let translate_const_value (cv_cpn : ConstValueRd.t) (ty : Ast.type_expr)
        (loc : Ast.loc) =
      let open ConstValueRd in
      match get cv_cpn with
      | Scalar scalar_cpn ->
          let* expr = translate_scalar scalar_cpn ty loc in
          Ok (`TrTypedConstantScalar expr)
      | ZeroSized -> (
          match ty with
          | Ast.ManifestTypeExpr (_, Ast.StructType (sn, _))
            when sn = TrTyTuple.tuple0_name ->
              translate_unit_constant loc
          | _ -> failwith "Todo: ConstValue::ZeroSized")
      | Slice _ -> failwith "Todo: ConstValue::Slice"
      | Undefined _ -> Error (`TrConstValue "Unknown ConstValue")

    let translate_ty_const_kind (ck_cpn : TyConstKindRd.t) (ty : Ast.type_expr)
        (loc : Ast.loc) =
      let open TyConstKindRd in
      match get ck_cpn with
      | Param -> failwith "Todo: ConstKind::Param"
      | Value v_cpn -> translate_const_value v_cpn ty loc
      | Undefined _ -> Error (`TrTyConstKind "Unknown ConstKind")

    let translate_typed_constant (ty_const_cpn : TyConstRd.t) (loc : Ast.loc) =
      let open TyConstRd in
      let ty_cpn = ty_get ty_const_cpn in
      let* ty_info = translate_ty ty_cpn loc in
      let ty_expr = Mir.raw_type_of ty_info in
      let ty =
        match ty_expr with
        | Ast.ManifestTypeExpr ((*loc*) _, ty) -> ty
        | _ -> failwith "Todo: Unsupported type_expr"
      in
      match ty with
      | Ast.StructType (st_name, _) ->
          if st_name != TrTyTuple.make_tuple_type_name [] then
            failwith
              ("Todo: Constants of type struct " ^ st_name
             ^ " are not supported yet")
          else translate_unit_constant loc
      | Ast.FuncType _ -> Ok (`TrTypedConstantFn ty_info)
      | Ast.Int (_, _) | Ast.Bool ->
          let kind_cpn = kind_get ty_const_cpn in
          translate_ty_const_kind kind_cpn ty_expr loc
      | _ -> failwith "Todo: Constant of unsupported type"

    let translate_const (constant_kind_cpn : ConstRd.t) (loc : Ast.loc) =
      let open ConstRd in
      match get constant_kind_cpn with
      | Ty ty_const_cpn -> translate_typed_constant ty_const_cpn loc
      | Val val_cpn -> (
          let open ConstRd.Val in
          let* ty_info = translate_ty (ty_get val_cpn) loc in
          let ty_expr = Mir.raw_type_of ty_info in
          let ty =
            match ty_expr with
            | Ast.ManifestTypeExpr ((*loc*) _, ty) -> ty
            | _ -> failwith "Todo: Unsupported type_expr"
          in
          match ty with
          | Ast.FuncType _ -> Ok (`TrTypedConstantFn ty_info)
          | StructType ("str_ref", []) -> (
              match ConstValueRd.get @@ const_value_get val_cpn with
              | Slice bytes ->
                  Ok
                    (`TrTypedConstantScalar
                      (Ast.CastExpr
                         ( loc,
                           StructTypeExpr (loc, Some "str_ref", None, [], []),
                           InitializerList
                             ( loc,
                               [
                                 (None, StringLit (loc, bytes));
                                 ( None,
                                   IntLit
                                     ( loc,
                                       Big_int.big_int_of_int
                                         (String.length bytes),
                                       true,
                                       false,
                                       NoLSuffix ) );
                               ] ) )))
              | _ -> failwith "TODO")
          | _ -> translate_const_value (const_value_get val_cpn) ty_expr loc)
      | Undefined _ -> Error (`TrConstantKind "Unknown ConstantKind")

    let translate_const_operand (constant_cpn : ConstOperandRd.t) =
      let open ConstOperandRd in
      let span_cpn = span_get constant_cpn in
      let* loc = translate_span_data span_cpn in
      let const_cpn = const_get constant_cpn in
      translate_const const_cpn loc

    let translate_operand (operand_cpn : OperandRd.t) (loc : Ast.loc) =
      let open OperandRd in
      (* Todo @Nima: Move and Copy are ignored for now. It is checked by the Rust compiler that
         - Only Places of type Copy get used for Operand::Copy
         - Places used by Operand::Move will never get used again (obviously raw pointers are not tracked)
      *)
      match get operand_cpn with
      | Copy place_cpn ->
          let* place = translate_place place_cpn loc in
          Ok (`TrOperandCopy place)
      | Move place_cpn ->
          let* place = translate_place place_cpn loc in
          Ok (`TrOperandMove place)
      | Constant constant_cpn -> translate_const_operand constant_cpn
      | Undefined _ -> Error (`TrOperand "Unknown Mir Operand kind")

    let translate_operands (oprs : (OperandRd.t * Ast.loc) list) =
      (* We want to preserve Rust's left to right argument evaluation *)
      let tmp_rvalue_binders = ref [] in
      let translate_opr ((opr_cpn, loc) : OperandRd.t * Ast.loc) =
        let* opr = translate_operand opr_cpn loc in
        match opr with
        | `TrOperandCopy operand_expr | `TrOperandMove operand_expr ->
            Ok operand_expr
        | `TrTypedConstantRvalueBinderBuilder rvalue_binder_builder ->
            let tmp_var_cnt = List.length !tmp_rvalue_binders in
            let tmp_var_name =
              TrName.make_tmp_var_name (Int.to_string tmp_var_cnt)
            in
            let rvalue_binder = rvalue_binder_builder tmp_var_name in
            tmp_rvalue_binders := !tmp_rvalue_binders @ [ rvalue_binder ];
            Ok (Ast.Var (loc, tmp_var_name))
        | `TrTypedConstantFn _ ->
            failwith
              "Todo: Functions as operand in rvalues are not supported yet"
        | `TrTypedConstantScalar expr -> Ok expr
      in
      let* oprs = ListAux.try_map translate_opr oprs in
      Ok (!tmp_rvalue_binders, oprs)

    let translate_fn_call_rexpr (callee_cpn : OperandRd.t)
        (args_cpn : OperandRd.t list) (call_loc : Ast.loc) (fn_loc : Ast.loc) =
      let translate_regular_fn_call substs fn_name =
        (* Todo @Nima: There should be a way to get separated source spans for args *)
        let args = List.map (fun arg_cpn -> (arg_cpn, fn_loc)) args_cpn in
        let* tmp_rvalue_binders, args = translate_operands args in
        let targs =
          Util.flatmap (function Mir.GenArgType ty -> [ ty ] | _ -> []) substs
        in
        let targs = List.map Mir.raw_type_of targs in
        let args = List.map (fun expr -> Ast.LitPat expr) args in
        let call_expr =
          Ast.CallExpr
            ( call_loc,
              fn_name,
              targs (*type arguments*),
              [] (*indices, in case this is really a predicate assertion*),
              args,
              Ast.Static (*method_binding*) )
        in
        Ok (tmp_rvalue_binders, call_expr)
      in
      let* callee = translate_operand callee_cpn call_loc in
      match callee with
      | `TrOperandMove (Var (_, fn_name)) ->
          translate_regular_fn_call [] fn_name
      | `TrTypedConstantFn ty_info -> (
          match ty_info with
          | Mir.TyInfoBasic
              { vf_ty = Ast.ManifestTypeExpr ((*loc*) _, Ast.FuncType fn_name) }
            ->
              translate_regular_fn_call [] fn_name
          | Mir.TyInfoGeneric
              {
                vf_ty = Ast.ManifestTypeExpr ((*loc*) _, Ast.FuncType fn_name);
                substs;
                vf_ty_mono =
                  Ast.ManifestTypeExpr ((*loc*) _, Ast.FuncType fn_name_mono);
              } -> (
              match fn_name with
              (* Todo @Nima: For cases where we inline an expression instead of a function call,
                 there is a problem with extending the implementation for clean-up paths *)
              | "std::alloc::Layout::new" -> (
                  if not (ListAux.is_empty args_cpn) then
                    Error
                      (`TrFnCallRExpr
                        "Invalid number of arguments for \
                         std::alloc::Layout::new")
                  else
                    match substs with
                    | [ Mir.GenArgType ty_info; Mir.GenArgConst ] ->
                        let ty_expr = Mir.basic_type_of ty_info in
                        Ok
                          ( (*tmp_rvalue_binders*) [],
                            Ast.SizeofExpr (call_loc, Ast.TypeExpr ty_expr) )
                    | _ ->
                        Error
                          (`TrFnCallRExpr
                            "Invalid generic argument(s) for \
                             std::alloc::Layout::new"))
              | "std::ptr::mut_ptr::<impl *mut T>::is_null" -> (
                  match (substs, args_cpn) with
                  | ( [ Mir.GenArgType gen_arg_ty_info; Mir.GenArgConst ],
                      [ arg_cpn ] ) ->
                      let* tmp_rvalue_binders, [ arg ] =
                        translate_operands [ (arg_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          Ast.Operation
                            ( fn_loc,
                              Ast.Eq,
                              [
                                arg;
                                IntLit
                                  ( fn_loc,
                                    Big_int.zero_big_int,
                                    (*decimal*) true,
                                    (*U suffix*) false,
                                    (*int literal*) Ast.NoLSuffix );
                              ] ) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          "Invalid (generic) arg(s) for \
                           std::ptr::mut_ptr::<impl *mut T>::is_null"))
              | "std::ptr::const_ptr::<impl *const T>::offset"
              | "std::ptr::mut_ptr::<impl *mut T>::offset" -> (
                  match (substs, args_cpn) with
                  | ( [ Mir.GenArgType gen_arg_ty_info; Mir.GenArgConst ],
                      [ arg1_cpn; arg2_cpn ] ) ->
                      let* tmp_rvalue_binders, [ arg1; arg2 ] =
                        translate_operands
                          [ (arg1_cpn, fn_loc); (arg2_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          Ast.Operation (fn_loc, Ast.Add, [ arg1; arg2 ]) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          (Printf.sprintf "Invalid (generic) arg(s) for %s"
                             fn_name)))
              | "std::ptr::const_ptr::<impl *const T>::add"
              | "std::ptr::mut_ptr::<impl *mut T>::add" -> (
                  match (substs, args_cpn) with
                  | ( [ Mir.GenArgType gen_arg_ty_info; Mir.GenArgConst ],
                      [ arg1_cpn; arg2_cpn ] ) ->
                      let* tmp_rvalue_binders, [ arg1; arg2 ] =
                        translate_operands
                          [ (arg1_cpn, fn_loc); (arg2_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          Ast.Operation
                            ( fn_loc,
                              Ast.Add,
                              [
                                arg1;
                                CastExpr
                                  ( fn_loc,
                                    ManifestTypeExpr
                                      (fn_loc, Int (Signed, PtrRank)),
                                    arg2 );
                              ] ) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          (Printf.sprintf "Invalid (generic) arg(s) for %s"
                             fn_name)))
              | "std::ptr::const_ptr::<impl *const T>::sub"
              | "std::ptr::mut_ptr::<impl *mut T>::sub" -> (
                  match (substs, args_cpn) with
                  | ( [ Mir.GenArgType gen_arg_ty_info; Mir.GenArgConst ],
                      [ arg1_cpn; arg2_cpn ] ) ->
                      let* tmp_rvalue_binders, [ arg1; arg2 ] =
                        translate_operands
                          [ (arg1_cpn, fn_loc); (arg2_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          Ast.Operation
                            ( fn_loc,
                              Ast.Sub,
                              [
                                arg1;
                                CastExpr
                                  ( fn_loc,
                                    ManifestTypeExpr
                                      (fn_loc, Int (Signed, PtrRank)),
                                    arg2 );
                              ] ) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          (Printf.sprintf "Invalid (generic) arg(s) for %s"
                             fn_name)))
              | "std::ptr::null_mut" ->
                  Ok
                    ( [],
                      IntLit
                        ( fn_loc,
                          Big_int.zero_big_int,
                          (*decimal*) true,
                          (*U suffix*) false,
                          (*int literal*) Ast.NoLSuffix ) )
              | "std::ptr::read" ->
                  let [ src_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ src ] =
                    translate_operands [ (src_cpn, fn_loc) ]
                  in
                  Ok (tmp_rvalue_binders, Ast.Deref (fn_loc, src))
              | "std::ptr::write" ->
                  let [ dst_cpn; src_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ dst; src ] =
                    translate_operands [ (dst_cpn, fn_loc); (src_cpn, fn_loc) ]
                  in
                  Ok
                    ( tmp_rvalue_binders
                      @ [
                          Ast.ExprStmt
                            (AssignExpr (fn_loc, Deref (fn_loc, dst), src));
                        ],
                      mk_unit_expr fn_loc )
              | "std::cell::UnsafeCell::<T>::new"
              | "std::cell::UnsafeCell::<T>::get"
              | "std::mem::ManuallyDrop::<T>::new"
              | "std::mem::ManuallyDrop::deref"
              | "std::mem::ManuallyDrop::deref_mut" ->
                  let [ arg_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  Ok (tmp_rvalue_binders, arg)
              | "core::str::<impl str>::as_ptr"
              | "core::slice::<impl [T]>::as_ptr" ->
                  let [ arg_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  Ok (tmp_rvalue_binders, Ast.Select (fn_loc, arg, "ptr"))
              | "core::str::<impl str>::len" | "core::slice::<impl [T]>::len" ->
                  let [ arg_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  Ok (tmp_rvalue_binders, Ast.Select (fn_loc, arg, "len"))
              | "core::str::<impl str>::as_bytes" ->
                  let [ arg_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  let slice_u8_ref_ty =
                    Ast.StructTypeExpr
                      ( fn_loc,
                        Some "slice_ref",
                        None,
                        [],
                        [
                          ManifestTypeExpr
                            (fn_loc, Int (Unsigned, FixedWidthRank 0));
                        ] )
                  in
                  Ok
                    ( tmp_rvalue_binders,
                      Ast.CastExpr
                        ( fn_loc,
                          slice_u8_ref_ty,
                          InitializerList
                            ( fn_loc,
                              [
                                (None, Select (fn_loc, arg, "ptr"));
                                (None, Select (fn_loc, arg, "len"));
                              ] ) ) )
              | _ -> translate_regular_fn_call substs fn_name)
          | _ ->
              Error
                (`TrFnCallRExpr "Invalid function definition type translation"))
      | _ -> Error (`TrFnCall "Invalid callee operand for function call")

    let translate_basic_block_id (bblock_id_cpn : BasicBlockIdRd.t) =
      BasicBlockIdRd.name_get bblock_id_cpn

    let translate_destination_data (dst_data_cpn : DestinationDataRd.t)
        (loc : Ast.loc) =
      let open DestinationDataRd in
      let place_cpn = place_get dst_data_cpn in
      let* dst = translate_place place_cpn loc in
      let dst_bblock_id_cpn = basic_block_id_get dst_data_cpn in
      let dst_bblock_id = translate_basic_block_id dst_bblock_id_cpn in
      let dst_data : Mir.fn_call_dst_data = { dst; dst_bblock_id } in
      Ok dst_data

    let translate_fn_call (fn_call_data_cpn : FnCallDataRd.t) (loc : Ast.loc) =
      let open FnCallDataRd in
      let func_cpn = func_get fn_call_data_cpn in
      let fn_span_cpn = fn_span_get fn_call_data_cpn in
      let* fn_loc = translate_span_data fn_span_cpn in
      let args_cpn = args_get_list fn_call_data_cpn in
      let* fn_call_tmp_rval_ctx, fn_call_rexpr =
        translate_fn_call_rexpr func_cpn args_cpn loc fn_loc
      in
      let destination_cpn = destination_get fn_call_data_cpn in
      let* call_stmt, next_bblock_stmt_op, targets =
        match OptionRd.get destination_cpn with
        | Nothing -> (*Diverging call*) Ok (Ast.ExprStmt fn_call_rexpr, None, [])
        | Something ptr_cpn ->
            let destination_data_cpn = VfMirStub.Reader.of_pointer ptr_cpn in
            let* { Mir.dst; Mir.dst_bblock_id } =
              translate_destination_data destination_data_cpn loc
            in
            Ok
              ( Ast.ExprStmt (Ast.AssignExpr (loc, dst, fn_call_rexpr)),
                Some (Ast.GotoStmt (loc, dst_bblock_id)),
                [ dst_bblock_id ] )
        | Undefined _ -> Error (`TrFnCall "Unknown Option kind")
      in
      let full_call_stmt =
        match fn_call_rexpr with
        | Ast.CallExpr
            ( call_loc,
              "VeriFast_ghost_command",
              [] (*type arguments*),
              [] (*indices, in case this is really a predicate assertion*),
              [],
              Ast.Static (*method_binding*) ) ->
            let get_start_loc loc =
              let (_, ln, col), _ = loc in
              (ln, col)
            in
            let phl = get_start_loc (Ast.lexed_loc call_loc) in
            let ghost_stmt =
              List.find
                (fun gs ->
                  let gsl = get_start_loc Ast.(gs |> stmt_loc |> lexed_loc) in
                  let (gsl_l, gsl_c), (phl_l, phl_c) = (gsl, phl) in
                  gsl_l = phl_l)
                !State.ghost_stmts
            in
            ghost_stmt
        | _ ->
            if ListAux.is_empty fn_call_tmp_rval_ctx then call_stmt
            else
              Ast.BlockStmt
                ( loc,
                  (*decl list*) [],
                  fn_call_tmp_rval_ctx @ [ call_stmt ],
                  loc,
                  ref [] )
      in
      match next_bblock_stmt_op with
      | None -> Ok ([ full_call_stmt ], targets)
      | Some next_bblock_stmt ->
          Ok ([ full_call_stmt; next_bblock_stmt ], targets)

    let translate_sw_targets_branch (br_cpn : SwitchTargetsBranchRd.t) =
      let open SwitchTargetsBranchRd in
      let v_cpn = val_get br_cpn in
      let v = CapnpAux.uint128_get v_cpn in
      let target_cpn = target_get br_cpn in
      let target = translate_basic_block_id target_cpn in
      (v, target)

    let translate_sw_int (sw_int_data_cpn : SwitchIntDataRd.t) (loc : Ast.loc) =
      let open SwitchIntDataRd in
      let discr_cpn = discr_get sw_int_data_cpn in
      let* tmp_rvalue_binders, [ discr ] =
        translate_operands [ (discr_cpn, loc) ]
      in
      let discr_ty_cpn = discr_ty_get sw_int_data_cpn in
      let* discr_ty = translate_ty discr_ty_cpn loc in
      let targets_cpn = targets_get sw_int_data_cpn in
      let open SwitchTargetsRd in
      let branches_cpn = branches_get_list targets_cpn in
      let branches = List.map translate_sw_targets_branch branches_cpn in
      let otherwise_cpn = otherwise_get targets_cpn in
      let otherwise_op =
        match OptionRd.get otherwise_cpn with
        | Nothing -> None
        | Something ptr_cpn ->
            let otherwise_cpn = VfMirStub.Reader.of_pointer ptr_cpn in
            let otherwise = translate_basic_block_id otherwise_cpn in
            Some otherwise
      in
      let* main_stmt, targets =
        match Mir.basic_type_of discr_ty with
        | Ast.ManifestTypeExpr ((*loc*) _, Ast.Bool) -> (
            match (branches, otherwise_op) with
            | [ (v, false_tgt) ], Some true_tgt when Stdint.Uint128.(zero = v)
              ->
                Ok
                  ( Ast.IfStmt
                      ( loc,
                        discr,
                        [ Ast.GotoStmt (loc, true_tgt) ],
                        [ Ast.GotoStmt (loc, false_tgt) ] ),
                    [ true_tgt; false_tgt ] )
            | _ ->
                Error
                  (`TrSwInt "Invalid SwitchTargets for a boolean discriminant"))
        | Ast.ManifestTypeExpr (_, Int (_, _)) ->
            let clauses =
              branches
              |> List.map @@ fun (value, target) ->
                 Ast.SwitchStmtClause
                   ( loc,
                     IntLit
                       ( loc,
                         Big_int.big_int_of_string
                           (Stdint.Uint128.to_string value),
                         true,
                         false,
                         NoLSuffix ),
                     [ Ast.GotoStmt (loc, target) ] )
            in
            let default_clause =
              match otherwise_op with
              | None -> []
              | Some tgt ->
                  [
                    Ast.SwitchStmtDefaultClause
                      (loc, [ Ast.GotoStmt (loc, tgt) ]);
                  ]
            in
            let targets =
              List.map snd branches
              @ match otherwise_op with None -> [] | Some tgt -> [ tgt ]
            in
            Ok (Ast.SwitchStmt (loc, discr, clauses @ default_clause), targets)
        | Ast.ManifestTypeExpr (_, tp) ->
            failwith
              (Printf.sprintf
                 "Todo: SwitchInt TerminatorKind for discriminant type %s"
                 (Verifast0.string_of_type tp))
      in
      if ListAux.is_empty tmp_rvalue_binders then Ok (main_stmt, targets)
      else
        Ok
          ( Ast.BlockStmt
              ( loc,
                (*decl list*) [],
                tmp_rvalue_binders @ [ main_stmt ],
                loc,
                ref [] ),
            targets )

    let translate_terminator_kind (ret_place_id : string)
        (tkind_cpn : TerminatorKindRd.t) (loc : Ast.loc) =
      let open TerminatorKindRd in
      match get tkind_cpn with
      | Goto bblock_id_cpn ->
          let bb_id = translate_basic_block_id bblock_id_cpn in
          Ok ([ Ast.GotoStmt (loc, bb_id) ], [ bb_id ])
      | SwitchInt sw_int_data_cpn ->
          let* sw_stmt, targets = translate_sw_int sw_int_data_cpn loc in
          Ok ([ sw_stmt ], targets)
      | Resume -> failwith "Todo: Terminatorkind::Resume"
      | Return ->
          Ok ([ Ast.ReturnStmt (loc, Some (Ast.Var (loc, ret_place_id))) ], [])
      | Unreachable -> Ok ([ Ast.Assert (loc, False loc) ], [])
      | Call fn_call_data_cpn -> translate_fn_call fn_call_data_cpn loc
      | Drop ->
          raise
            (Ast.StaticError (loc, "Implicit drops are not yet supported", None))
      | Undefined _ -> Error (`TrTerminatorKind "Unknown Mir terminator kind")

    let translate_terminator (ret_place_id : string)
        (terminator_cpn : TerminatorRd.t) =
      let open TerminatorRd in
      let src_info_cpn = source_info_get terminator_cpn in
      let* { Mir.span = loc; Mir.scope } = translate_source_info src_info_cpn in
      let terminator_kind_cpn = kind_get terminator_cpn in
      translate_terminator_kind ret_place_id terminator_kind_cpn loc

    let translate_bin_op (bin_op_cpn : BinOpRd.t) =
      let open BinOpRd in
      match get bin_op_cpn with
      | Add -> Ok Ast.Add
      | Sub -> Ok Ast.Sub
      | Mul -> Ok Ast.Mul
      | Div -> Ok Ast.Div
      | Rem -> Ok Ast.Mod
      | BitXor -> Ok Ast.BitXor
      | BitAnd -> Ok Ast.BitAnd
      | BitOr -> Ok Ast.BitOr
      | Shl -> failwith "Todo: BinOp::Shl"
      | Shr -> failwith "Todo: BinOp::Shr"
      | Eq -> Ok Ast.Eq
      | Lt -> Ok Ast.Lt
      | Le -> Ok Ast.Le
      | Ne -> Ok Ast.Neq
      | Ge -> Ok Ast.Ge
      | Gt -> Ok Ast.Gt
      | Offset -> failwith "Todo: BinOp::Offset"
      | Undefined _ -> Error (`TrBinOp "Unknown binary operator")

    let translate_un_op (un_op_cpn : UnOpRd.t) =
      let open UnOpRd in
      match get un_op_cpn with
      | Not -> Ok Ast.Not
      | Neg -> Ok Ast.Sub
      | Undefined _ -> Error (`TrUnOp "Unknown unary operator")

    let translate_binary_operation (bin_op_data_cpn : BinaryOpDataRd.t)
        (loc : Ast.loc) =
      let open BinaryOpDataRd in
      let operator_cpn = operator_get bin_op_data_cpn in
      let* operator = translate_bin_op operator_cpn in
      let operandl_cpn = operandl_get bin_op_data_cpn in
      let* operandl = translate_operand operandl_cpn loc in
      let operandr_cpn = operandr_get bin_op_data_cpn in
      let* operandr = translate_operand operandr_cpn loc in
      Ok (operator, operandl, operandr)

    let translate_unary_operation (un_op_data_cpn : UnaryOpDataRd.t)
        (loc : Ast.loc) =
      let open UnaryOpDataRd in
      let operator_cpn = operator_get un_op_data_cpn in
      let* operator = translate_un_op operator_cpn in
      let operand_cpn = operand_get un_op_data_cpn in
      let* operand = translate_operand operand_cpn loc in
      Ok (operator, operand)

    let translate_aggregate_kind (agg_kind_cpn : AggregateKindRd.t) =
      let open AggregateKindRd in
      match get agg_kind_cpn with
      | Array es_ty_cpn -> failwith "Todo: AggregateKind::Array"
      | Tuple -> failwith "Todo: AggregateKind::Tuple"
      | Adt adt_data_cpn ->
          let open AdtData in
          let adt_id_cpn = adt_id_get adt_data_cpn in
          let adt_def_path = translate_adt_def_id adt_id_cpn in
          let adt_name = TrName.translate_def_path adt_def_path in
          let* adt_def_opt = State.get_adt_def adt_name in
          let* adt_def =
            Option.to_result
              ~none:(`TrAggregateKind ("No decl found for " ^ adt_name))
              adt_def_opt
          in
          (*check it is an adt*)
          let* adt_kind = Mir.decl_mir_adt_kind adt_def.def in
          let variant_idx_cpn = variant_idx_get adt_data_cpn in
          let variant_name = variant_id_get adt_data_cpn in
          let substs_cpn = substs_get_list adt_data_cpn in
          Ok
            Mir.(
              AggKindAdt { adt_kind; adt_name; variant_name; def = adt_def.def })
      | Closure -> failwith "Todo: AggregateKind::Closure"
      | Generator -> failwith "Todo: AggregateKind::Generator"
      | Undefined _ -> Error (`TrAggregateKind "Unknown AggregateKind")

    let translate_aggregate (agg_data_cpn : AggregateDataRd.t) (loc : Ast.loc) =
      let open AggregateDataRd in
      let operands_cpn = operands_get_list agg_data_cpn in
      let operands_cpn = List.map (fun op -> (op, loc)) operands_cpn in
      let* tmp_rvalue_binders, operand_exprs =
        translate_operands operands_cpn
      in
      let agg_kind_cpn = aggregate_kind_get agg_data_cpn in
      let* agg_kind = translate_aggregate_kind agg_kind_cpn in
      match agg_kind with
      | AggKindAdt { adt_kind; adt_name; variant_name; def = adt_def } -> (
          match adt_kind with
          | Enum ->
              let init_stmts_builder lhs_place =
                let arg_pats = List.map (fun e -> Ast.LitPat e) operand_exprs in
                let assignment =
                  Ast.ExprStmt
                    (AssignExpr
                       ( loc,
                         lhs_place,
                         CallExpr (loc, variant_name, [], [], arg_pats, Static)
                       ))
                in
                tmp_rvalue_binders @ [ assignment ]
              in
              Ok (`TrRvalueAggregate init_stmts_builder)
          | Union -> failwith "Todo: Unsupported Adt kind for aggregate"
          | Struct ->
              let* fields_opt = AstAux.decl_fields adt_def in
              let* fields =
                Option.to_result
                  ~none:(`TrAggregate "Struct without fields definition")
                  fields_opt
              in
              if List.length operands_cpn <> List.length fields then
                Error
                  (`TrAggregate
                    "The number of struct fields and initializing operands are \
                     different")
              else
                let field_names = List.map AstAux.field_name fields in
                let init_stmts_builder lhs_place =
                  let field_init_stmts =
                    List.map
                      (fun (field_name, init_expr) ->
                        let open Ast in
                        ExprStmt
                          (AssignExpr
                             ( loc,
                               Select (loc, lhs_place, field_name),
                               init_expr )))
                      (List.combine field_names operand_exprs)
                  in
                  tmp_rvalue_binders @ field_init_stmts
                in
                Ok (`TrRvalueAggregate init_stmts_builder))

    let translate_rvalue (rvalue_cpn : RvalueRd.t) (loc : Ast.loc) =
      let open RvalueRd in
      let tr_operand operand =
        match operand with
        | `TrOperandCopy expr
        | `TrOperandMove expr
        | `TrTypedConstantScalar expr ->
            Ok (`TrRvalueExpr expr)
        | `TrTypedConstantRvalueBinderBuilder rvalue_binder_builder ->
            Ok (`TrRvalueRvalueBinderBuilder rvalue_binder_builder)
        | `TrTypedConstantFn _ ->
            Error (`TrRvalue "Invalid operand translation for Rvalue")
      in
      match get rvalue_cpn with
      | Use operand_cpn ->
          let* operand = translate_operand operand_cpn loc in
          tr_operand operand
      | Ref ref_data_cpn ->
          let open RefData in
          let region_cpn = region_get ref_data_cpn in
          let bor_kind_cpn = bor_kind_get ref_data_cpn in
          let place_cpn = place_get ref_data_cpn in
          let* place_expr = translate_place place_cpn loc in
          let expr = Ast.AddressOf (loc, place_expr) in
          Ok (`TrRvalueExpr expr)
          (*Todo @Nima: We might need to assert the chunk when we make a reference to it*)
      | AddressOf address_of_data_cpn ->
          let open AddressOfData in
          let mut_cpn = mutability_get address_of_data_cpn in
          let place_cpn = place_get address_of_data_cpn in
          let* place_expr = translate_place place_cpn loc in
          let expr = Ast.AddressOf (loc, place_expr) in
          Ok (`TrRvalueExpr expr)
      | Cast cast_data_cpn -> (
          let open CastData in
          let operand_cpn = operand_get cast_data_cpn in
          let* operand = translate_operand operand_cpn loc in
          let ty_cpn = ty_get cast_data_cpn in
          let* ty_info = translate_ty ty_cpn loc in
          let ty = Mir.basic_type_of ty_info in
          match operand with
          | `TrOperandCopy expr
          | `TrOperandMove expr
          | `TrTypedConstantScalar expr ->
              Ok (`TrRvalueExpr (Ast.CastExpr (loc, ty, expr)))
          | `TrTypedConstantRvalueBinderBuilder rvalue_binder_builder ->
              failwith "Todo: Rvalue::Cast"
              (*Todo @Nima: We need a better design (refactor) for passing different results of operand translation*)
          | `TrTypedConstantFn ty_info -> (
              match ty_info with
              | Mir.TyInfoBasic
                  {
                    vf_ty =
                      Ast.ManifestTypeExpr ((*loc*) _, Ast.FuncType fn_name);
                  } ->
                  Ok
                    (`TrRvalueExpr (Ast.CastExpr (loc, ty, Var (loc, fn_name))))
              | _ ->
                  Error
                    (`TrRvalue "Invalid operand translation for Rvalue::Cast")))
      | BinaryOp bin_op_data_cpn ->
          let* operator, operandl, operandr =
            translate_binary_operation bin_op_data_cpn loc
          in
          let* operandl = tr_operand operandl in
          let* operandr = tr_operand operandr in
          Ok (`TrRvalueBinaryOp (operator, operandl, operandr))
      | UnaryOp un_op_data_cpn ->
          let* operator, operand =
            translate_unary_operation un_op_data_cpn loc
          in
          let* operand = tr_operand operand in
          Ok (`TrRvalueUnaryOp (operator, operand))
      | Aggregate agg_data_cpn -> translate_aggregate agg_data_cpn loc
      | Discriminant place_cpn ->
          let* place_expr = translate_place place_cpn loc in
          Ok
            (`TrRvalueExpr
              (Ast.CallExpr
                 ( loc,
                   "#inductive_ctor_index",
                   [],
                   [],
                   [ LitPat place_expr ],
                   Static )))
      | Undefined _ -> Error (`TrRvalue "Unknown Rvalue kind")

    let translate_statement_kind (statement_kind_cpn : StatementKindRd.t)
        (loc : Ast.loc) =
      let open StatementKindRd in
      match get statement_kind_cpn with
      | Assign assign_data_cpn -> (
          let lhs_place_cpn = AssignData.lhs_place_get assign_data_cpn in
          let* lhs_place = translate_place lhs_place_cpn loc in
          let rhs_rvalue_cpn = AssignData.rhs_rvalue_get assign_data_cpn in
          let* rhs_rvalue = translate_rvalue rhs_rvalue_cpn loc in
          match rhs_rvalue with
          | `TrRvalueExpr rhs_expr ->
              let assign_stmt =
                Ast.ExprStmt (Ast.AssignExpr (loc, lhs_place, rhs_expr))
              in
              Ok [ assign_stmt ]
          | `TrRvalueRvalueBinderBuilder rvalue_binder_builder ->
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
              Ok [ block_stmt ]
          | `TrRvalueUnaryOp (operator, operand) -> (
              let rvalue_binder_stmts, expr =
                match operand with
                | `TrRvalueExpr expr -> ([], expr)
                | `TrRvalueRvalueBinderBuilder rvalue_binder_builder ->
                    let tmp_var_name = TrName.make_tmp_var_name "operand" in
                    let rvalue_binder_stmt =
                      rvalue_binder_builder tmp_var_name
                    in
                    ([ rvalue_binder_stmt ], Ast.Var (loc, tmp_var_name))
              in
              let assign_stmt =
                Ast.ExprStmt
                  (Ast.AssignExpr
                     ( loc,
                       lhs_place,
                       Ast.Operation
                         ( loc,
                           operator,
                           match operator with
                           | Sub ->
                               [
                                 IntLit
                                   ( loc,
                                     Big_int.zero_big_int,
                                     true,
                                     false,
                                     NoLSuffix );
                                 expr;
                               ]
                           | _ -> [ expr ] ) ))
              in
              match rvalue_binder_stmts with
              | [] -> Ok [ assign_stmt ]
              | _ ->
                  let block_stmt =
                    Ast.BlockStmt
                      ( loc,
                        (*decl list*) [],
                        rvalue_binder_stmts @ [ assign_stmt ],
                        loc,
                        ref [] )
                  in
                  Ok [ block_stmt ])
          | `TrRvalueBinaryOp (operator, operandl, operandr) -> (
              let rvalue_binder_stmts, exprl, exprr =
                match (operandl, operandr) with
                | `TrRvalueExpr exprl, `TrRvalueExpr exprr -> ([], exprl, exprr)
                | ( `TrRvalueExpr exprl,
                    `TrRvalueRvalueBinderBuilder rvalue_binder_builderr ) ->
                    let tmp_var_name = TrName.make_tmp_var_name "right" in
                    let rvalue_binder_stmt =
                      rvalue_binder_builderr tmp_var_name
                    in
                    ([ rvalue_binder_stmt ], exprl, Ast.Var (loc, tmp_var_name))
                | ( `TrRvalueRvalueBinderBuilder rvalue_binder_builderl,
                    `TrRvalueExpr exprr ) ->
                    let tmp_var_name = TrName.make_tmp_var_name "left" in
                    let rvalue_binder_stmt =
                      rvalue_binder_builderl tmp_var_name
                    in
                    ([ rvalue_binder_stmt ], Ast.Var (loc, tmp_var_name), exprr)
                | ( `TrRvalueRvalueBinderBuilder rvalue_binder_builderl,
                    `TrRvalueRvalueBinderBuilder rvalue_binder_builderr ) ->
                    let tmp_vl, tmp_vr =
                      ( TrName.make_tmp_var_name "left",
                        TrName.make_tmp_var_name "right" )
                    in
                    let rvbl, rvbr =
                      ( rvalue_binder_builderl tmp_vl,
                        rvalue_binder_builderr tmp_vr )
                    in
                    ( [ rvbl; rvbr ],
                      Ast.Var (loc, tmp_vl),
                      Ast.Var (loc, tmp_vr) )
              in
              let assign_stmt =
                Ast.ExprStmt
                  (Ast.AssignExpr
                     ( loc,
                       lhs_place,
                       Ast.Operation (loc, operator, [ exprl; exprr ]) ))
              in
              match rvalue_binder_stmts with
              | [] -> Ok [ assign_stmt ]
              | _ ->
                  let block_stmt =
                    Ast.BlockStmt
                      ( loc,
                        (*decl list*) [],
                        rvalue_binder_stmts @ [ assign_stmt ],
                        loc,
                        ref [] )
                  in
                  Ok [ block_stmt ])
          | `TrRvalueAggregate init_stmts_builder ->
              Ok (init_stmts_builder lhs_place))
      | Nop -> Ok []
      | Undefined _ -> Error (`TrStatementKind "Unknown StatementKind")

    let translate_statement (statement_cpn : StatementRd.t) =
      let open StatementRd in
      let src_info_cpn = source_info_get statement_cpn in
      let* { Mir.span = loc; Mir.scope } = translate_source_info src_info_cpn in
      (* Todo @Nima: The following `loc` substitution is due to deal with statements with their location equal to the whole body of the function.
         They prevent us from embedding ghost statements into the MIR statements. The ghost embedding approach should be changed.
         After that this `loc` changing and the `body_imp_loc` in the State are not necessary anymore. *)
      let loc =
        if loc = State.body_imp_loc then
          let spos, _ = Ast.lexed_loc State.body_imp_loc in
          Ast.Lexed (spos, spos)
        else loc
      in
      let kind_cpn = kind_get statement_cpn in
      translate_statement_kind kind_cpn loc

    let translate_basic_block (ret_place_id : string)
        (bblock_cpn : BasicBlockRd.t) =
      let open BasicBlockRd in
      let id_cpn = id_get bblock_cpn in
      let id = translate_basic_block_id id_cpn in
      if is_cleanup_get bblock_cpn then
        (* Todo @Nima: For now we are ignoring cleanup basic-blocks *)
        Ok None
      else
        let statements_cpn = statements_get_list bblock_cpn in
        let* statements = ListAux.try_map translate_statement statements_cpn in
        let statements = List.concat statements in
        let terminator_cpn = terminator_get bblock_cpn in
        let* terminator, successors =
          translate_terminator ret_place_id terminator_cpn
        in
        let bblock : Mir.basic_block =
          {
            id;
            statements;
            terminator;
            successors;
            walk_state = NotSeen;
            is_block_head = false;
            parent = None;
            children = [];
          }
        in
        Ok (Some bblock)

    let find_blocks (bblocks : Mir.basic_block list) =
      let open Mir in
      let explicit_block_heads_table = Hashtbl.create 10 in
      let bblocks_table = Hashtbl.create 100 in
      let explicit_block_ends = ref [] in
      bblocks
      |> List.iter (fun (bb : Mir.basic_block) ->
             match bb.terminator with
             | [
              Ast.BlockStmt
                ( l,
                  decls,
                  [
                    ExprStmt
                      (CallExpr
                        (_, "#ghost_decl_block_start", [], [], [], Static));
                  ],
                  closeBraceLoc,
                  _ );
              Ast.GotoStmt (lg, target);
             ] ->
                 let id =
                   Printf.sprintf "bh%d"
                     (Hashtbl.length explicit_block_heads_table)
                 in
                 let fixed_bb =
                   {
                     bb with
                     terminator = [ Ast.GotoStmt (l, id) ];
                     successors = [ id ];
                   }
                 in
                 let bh =
                   { bb with id; is_block_head = true; statements = [] }
                 in
                 Hashtbl.add bblocks_table bb.id fixed_bb;
                 Hashtbl.add bblocks_table id bh;
                 Hashtbl.add explicit_block_heads_table closeBraceLoc bh
             | [
              Ast.ExprStmt
                (CallExpr
                  (closeBraceLoc, "#ghost_decl_block_end", [], [], [], Static));
              (Ast.GotoStmt (lg, target) as gotoStmt);
             ] ->
                 explicit_block_ends :=
                   (closeBraceLoc, gotoStmt, bb) :: !explicit_block_ends
             | _ -> Hashtbl.add bblocks_table bb.id bb);
      !explicit_block_ends
      |> List.iter (fun (closeBraceLoc, gotoStmt, (bb : Mir.basic_block)) ->
             let head_bb =
               Hashtbl.find explicit_block_heads_table closeBraceLoc
             in
             Hashtbl.add bblocks_table bb.id
               {
                 bb with
                 terminator = [ gotoStmt ];
                 successors = head_bb.id :: bb.successors;
               });
      let entry_id = (List.hd bblocks).id in
      let toplevel_blocks = ref [] in
      let rec set_parent (bb : basic_block) k k' path =
        if k' = k then ()
        else
          let (bb' :: path) = path in
          match bb'.parent with
          | None ->
              (*Printf.printf "Setting %s.parent <- Some %s\n" bb'.id bb.id;*)
              bb'.parent <- Some bb;
              set_parent bb k (k' - 1) path
          | Some bb'' ->
              let (Walking (k'', path')) = bb''.walk_state in
              if k'' < k then (
                (*Printf.printf "Setting %s.parent <- Some %s\n" bb'.id bb.id;*)
                bb'.parent <- Some bb;
                set_parent bb k (k' - 1) path)
              else if k'' = k then ()
              else set_parent bb k k'' path'
      in
      let rec iter path k bb_id =
        let bb = Hashtbl.find bblocks_table bb_id in
        match bb.walk_state with
        | NotSeen -> (
            let path = bb :: path in
            bb.walk_state <- Walking (k, path);
            bb.successors
            |> List.iter (fun succ_id -> iter path (k + 1) succ_id);
            bb.walk_state <- Exhausted;
            match bb.parent with
            | None -> toplevel_blocks := bb :: !toplevel_blocks
            | Some bb' -> bb'.children <- bb :: bb'.children)
        | Walking (k', _) ->
            (*Printf.printf "Found a loop with head at rank %d: %s\n" k' (String.concat " -> " (List.map (fun (bb: basic_block) -> bb.id) (List.rev (bb::path))));*)
            bb.is_block_head <- true;
            set_parent bb k' (k - 1) path
        | Exhausted -> (
            match bb.parent with
            | None -> ()
            | Some bb' -> (
                match bb'.walk_state with
                | Walking (k', _) -> set_parent bb' k' (k - 1) path
                | Exhausted ->
                    failwith
                      (Printf.sprintf
                         "Error: found a loop with head %s and children %s and \
                          a secondary entry point with path %s"
                         bb'.id
                         (String.concat ", "
                            (List.map
                               (fun (bb : basic_block) -> bb.id)
                               bb'.children))
                         (String.concat " -> "
                            (List.rev
                               (List.map
                                  (fun (bb : basic_block) -> bb.id)
                                  (bb :: path)))))))
      in
      iter [] 0 entry_id;
      !toplevel_blocks

    let rec translate_to_vf_basic_block
        ({
           id;
           statements = stmts0;
           terminator = trm;
           successors;
           is_block_head;
           children;
         } :
          Mir.basic_block) =
      let stmts = stmts0 @ trm in
      (* let* stmts = ListAux.try_fold_left embed_ghost_stmts [] stmts in *)
      let loc = stmts |> List.hd |> Ast.stmt_loc in
      let stmts =
        if is_block_head then
          let children_stmts =
            Util.flatmap translate_to_vf_basic_block children
          in
          match trm with
          | [
           Ast.BlockStmt
             ( l,
               decls,
               [
                 ExprStmt
                   (CallExpr (_, "#ghost_decl_block_start", [], [], [], Static));
               ],
               closeBraceLoc,
               _ );
           (Ast.GotoStmt (lg, target) as gotoStmt);
          ] ->
              [
                Ast.BlockStmt
                  ( loc,
                    decls,
                    Ast.LabelStmt (loc, id)
                    :: (stmts0 @ [ gotoStmt ] @ children_stmts),
                    closeBraceLoc,
                    ref [] );
              ]
          | _ ->
              [
                (match stmts with
                | Ast.PureStmt (lp, InvariantStmt (linv, inv)) :: stmts ->
                    Ast.WhileStmt
                      ( loc,
                        True loc,
                        Some (LoopInv inv),
                        None,
                        stmts @ children_stmts @ [ Ast.LabelStmt (loc, id) ],
                        [] )
                | _ ->
                    Ast.BlockStmt
                      ( loc,
                        [],
                        Ast.LabelStmt (loc, id) :: (stmts @ children_stmts),
                        loc,
                        ref [] ));
              ]
        else stmts
      in
      Ast.LabelStmt (loc, id) :: stmts

    let translate_var_debug_info_contents (vdic_cpn : VarDebugInfoContentsRd.t)
        (loc : Ast.loc) =
      let open VarDebugInfoContentsRd in
      match get vdic_cpn with
      | Place place_cpn -> (
          let* place = translate_place place_cpn loc in
          match place with
          | Ast.Var ((*loc*) _, id) -> Ok (Mir.VdiiPlace { id })
          | _ -> failwith "Todo VarDebugInfoContents Place")
      | Const constant_cpn -> Ok Mir.VdiiConstant
      | Undefined _ ->
          Error (`TrVarDebugInfoContents "Unknown variable debug info kind")

    let translate_var_debug_info (vdi_cpn : VarDebugInfoRd.t) =
      let open VarDebugInfoRd in
      let name_cpn = name_get vdi_cpn in
      let name = translate_symbol name_cpn in
      let src_info_cpn = source_info_get vdi_cpn in
      let* src_info = translate_source_info src_info_cpn in
      let value_cpn = value_get vdi_cpn in
      let* value = translate_var_debug_info_contents value_cpn src_info.span in
      Ok ({ internal = value; surf_name = name } : Mir.var_debug_info)
  end
  (* TrBody *)

  let gen_contract (adt_defs : Mir.adt_def_tr list) (contract_loc : Ast.loc)
      (lft_vars : string list) (params : Mir.local_decl list)
      (ret : Mir.local_decl) =
    let open Ast in
    let bind_pat_b n = VarPat (contract_loc, n) in
    let lit_pat_b n = LitPat (Var (contract_loc, n)) in
    (* Todo @Nima: Move RustBelt token, etc. constructors like the following to the RustBelt module so
       The hard-coded names will be in the same place and the code will be reusable *)
    let nonatomic_token_b pat =
      CallExpr
        ( contract_loc,
          "thread_token",
          [] (*type arguments*),
          [] (*indices*),
          [ pat ] (*arguments*),
          Static )
    in
    let thread_id_name = "_t" in
    let pre_na_token = nonatomic_token_b (bind_pat_b thread_id_name) in
    let post_na_token = nonatomic_token_b (lit_pat_b thread_id_name) in
    let lft_token_b pat_b n =
      let coef_n = "_q_" ^ n in
      CoefAsn
        ( contract_loc,
          pat_b coef_n,
          CallExpr
            ( contract_loc,
              "lifetime_token",
              [] (*type arguments*),
              [] (*indices*),
              [ pat_b n ] (*arguments*),
              Static ) )
    in
    let pre_lft_tks =
      List.map (fun lft_var -> lft_token_b bind_pat_b lft_var) lft_vars
    in
    let post_lft_tks =
      List.map (fun lft_var -> lft_token_b lit_pat_b lft_var) lft_vars
    in
    let gen_local_ty_asn (local : Mir.local_decl) =
      let Mir.{ mutability; id; ty = ty_info; loc } = local in
      let raw_ty = Mir.raw_type_of ty_info in
      let* vs =
        if not (AstAux.is_adt_ty raw_ty) then Ok [ Ast.Var (loc, id) ]
        else
          let* adt_name = AstAux.adt_ty_name raw_ty in
          match adt_name with
          (*Todo: We need to have these built-in types defined during translation and not through headers*)
          | "std_tuple_0_" | "std_empty_" -> Ok [ Ast.Var (loc, id) ]
          | _ -> (
              let adt_def =
                List.find
                  (fun ({ name } : Mir.adt_def_tr) -> name = adt_name)
                  adt_defs
              in
              let* adt_kind = Mir.decl_mir_adt_kind adt_def.def in
              match adt_kind with
              | Mir.Enum | Mir.Union ->
                  failwith "Todo: Generate owner assertion for local ADT"
              | Mir.Struct ->
                  let* fields_opt = AstAux.decl_fields adt_def.def in
                  let* fields =
                    Option.to_result
                      ~none:(`GenLocalTyAsn "ADT without fields definition")
                      fields_opt
                  in
                  let vs =
                    List.map
                      (fun field ->
                        Ast.Select
                          (loc, Ast.Var (loc, id), AstAux.field_name field))
                      fields
                  in
                  Ok vs)
      in
      let RustBelt.{ size; own; shr } = Mir.interp_of ty_info in
      match own (Ast.Var (loc, thread_id_name)) vs with
      | Ok asn -> Ok asn
      | Error estr ->
          Error (`GenLocalTyAsn ("Owner assertion function error: " ^ estr))
    in
    let* params_ty_asns = ListAux.try_map gen_local_ty_asn params in
    let params_ty_asns =
      List.filter
        (fun asn -> match asn with True _ -> false | _ -> true)
        params_ty_asns
    in
    let params_ty_asns =
      AstAux.list_to_sep_conj
        (List.map (fun asn -> (contract_loc, asn)) params_ty_asns)
        None
    in
    let pre_asn =
      AstAux.list_to_sep_conj
        (List.map (fun asn -> (contract_loc, asn)) pre_lft_tks)
        params_ty_asns
    in
    let pre_asn =
      match pre_asn with
      | None -> pre_na_token
      | Some pre_asn -> Sep (contract_loc, pre_na_token, pre_asn)
    in
    let* ret_ty_asn =
      gen_local_ty_asn
        {
          mutability = ret.mutability;
          id = "result";
          ty = ret.ty;
          loc = ret.loc;
        }
    in
    let (Some post_asn) =
      AstAux.list_to_sep_conj
        (List.map (fun asn -> (contract_loc, asn)) post_lft_tks)
        (Some ret_ty_asn)
      (*might be just True*)
    in
    let post_asn = Sep (contract_loc, post_na_token, post_asn) in
    Ok (pre_asn, post_asn)

  let gen_drop_contract adt_defs self_ty self_ty_targs limpl =
    let { loc = ls; tparams; fds } : Mir.adt_def_tr =
      List.find
        (function ({ name } : Mir.adt_def_tr) -> name = self_ty)
        adt_defs
    in
    let pre =
      Ast.Sep
        ( ls,
          Ast.CallExpr
            (ls, "thread_token", [], [], [ VarPat (ls, "_t") ], Static),
          Ast.CallExpr
            ( ls,
              self_ty ^ "_full_borrow_content",
              self_ty_targs,
              [ LitPat (Var (ls, "_t")); LitPat (Var (ls, "self")) ],
              [],
              Static ) )
    in
    List.iter2
      (fun targ tparam ->
        match targ with
        | Ast.IdentTypeExpr (_, None, x) when x = tparam -> ()
        | Ast.ManifestTypeExpr (_, GhostTypeParam x) when x = tparam -> ()
        | _ ->
            raise
              (Ast.StaticError
                 ( limpl,
                   "A drop function for a struct type whose type arguments are \
                    not identical to its type parameters is not yet supported",
                   None )))
      self_ty_targs tparams;
    let post =
      Ast.Sep
        ( ls,
          Ast.CallExpr
            (ls, "thread_token", [], [], [ LitPat (Var (ls, "_t")) ], Static),
          List.fold_right
            (fun ({ name; ty; loc } : Mir.field_def_tr) asn ->
              match (Mir.interp_of ty).full_bor_content with
              | Error msg ->
                  raise
                    (Ast.StaticError
                       ( limpl,
                         "Cannot express the content of a full borrow of the \
                          type of field " ^ name,
                         None ))
              | Ok fbc ->
                  let fbc_args =
                    [
                      Ast.Var (loc, "_t");
                      AddressOf (loc, Read (loc, Var (loc, "self"), name));
                    ]
                  in
                  let fbc_call fbc_name =
                    Ast.CallExpr
                      ( loc,
                        fbc_name,
                        [],
                        List.map (fun e -> Ast.LitPat e) fbc_args,
                        [],
                        Static )
                  in
                  Ast.Sep
                    ( loc,
                      (match fbc with
                      | Var (_, fbc) -> fbc_call fbc
                      | _ -> Ast.ExprCallExpr (loc, fbc, fbc_args)),
                      asn ))
            fds
            (Ast.CallExpr
               ( limpl,
                 "struct_" ^ self_ty ^ "_padding",
                 self_ty_targs,
                 [],
                 [ LitPat (Var (limpl, "self")) ],
                 Static )) )
    in
    Ok (pre, post)

  (** makes the mappings used for substituting the MIR level local declaration ids with names closer to variables surface name *)
  let make_var_id_name_maps (vdis : Mir.var_debug_info list) =
    let make_var_id_name_entries surf_names_set id surf_name =
      match List.find_opt (fun (n, _) -> n = surf_name) surf_names_set with
      | None ->
          let surf_names_set = (surf_name, ref 0) :: surf_names_set in
          let env_entry_opt : VF0.var_debug_info option = None in
          let trs_entry : var_id_trs_entry =
            (*We will directly substitute the id with the surface name*)
            { id; internal_name = surf_name }
          in
          (env_entry_opt, trs_entry, surf_names_set)
      | Some (_, counter) ->
          (* This name is shadowed or is in a nested scope *)
          (* Todo @Nima: Ghost statements will refer to surface variable names.
             Since VeriFast does not support shadowing, shadowed variables either need to have different internal names or
             be in nested scopes. The current code is based on the former approach but it lacks substituting ghost statements variable names
             with their corresponding internal names. The alternative solution to the whole problem of shadowed variable names and scoped variable names
             is to use nested scopes which means adding nested scopes to the surface code scopes to handle shadowed names. *)
          (* Note @Nima: To support shadowing for ghost variables will be confusing for the user. example:
             ``
             let x = 42;
             //@ ghost x = 43;
             let y = x + 2;
             ``
             The third `x` refers to the first x but the code might be confusing for the user *)
          failwith "Todo: Shadowed variable names"
      (*
          let internal_name =
            TrName.tag_internal surf_name ^ string_of_int !counter
          in
          if !counter = Int.max_int then
            failwith "Shadowed var name counter ovf"
          else
            let _ = counter := succ !counter in
            let env_entry_opt : VF0.var_debug_info option =
              Some { internal_name; surf_name }
            in
            let trs_entry : var_id_trs_entry = { id; internal_name } in
            (env_entry_opt, trs_entry, surf_names_set)
          *)
    in
    let f_aux (env_map, trs_map, surf_names_set)
        ({ internal; surf_name } : Mir.var_debug_info) =
      match internal with
      | Mir.VdiiConstant ->
          (* Todo @Nima: We do not want to un-substitute the constant. We might just want to show the constant name and value in the Store in the future *)
          (env_map, trs_map, surf_names_set)
      | Mir.VdiiPlace { id } ->
          let env_entry_opt, trs_entry, surf_names_set =
            make_var_id_name_entries surf_names_set id surf_name
          in
          let env_map =
            match env_entry_opt with
            | None -> env_map
            | Some env_entry -> env_entry :: env_map
          in
          (env_map, trs_entry :: trs_map, surf_names_set)
    in
    let env_map, trs_map, surf_names_set =
      List.fold_left f_aux ([], [], []) vdis
    in
    ( env_map (* This will be used during the pprinting of execution states *),
      trs_map (* This will be used during the translation of variable names *)
    )

  let translate_unsafety (unsafety_cpn : UnsafetyRd.t) =
    let open UnsafetyRd in
    match get unsafety_cpn with
    | Safe -> Ok false
    | Unsafe -> Ok true
    | Undefined _ -> Error (`TrUnsafety "Unknown unsafety kind")

  let translate_hir_generic_param_name loc (is_type_param_name : bool)
      (n_cpn : HirGenericParamNameRd.t) =
    let open HirGenericParamNameRd in
    match get n_cpn with
    | Plain ident_cpn ->
        let* name, loc = translate_ident ident_cpn in
        if is_type_param_name && not (Verifast0.tparam_is_uppercase name) then
          raise
            (Ast.StaticError
               (loc, "Type parameters must start with an uppercase letter", None));
        Ok (name, loc)
    | Fresh id_cpn ->
        failwith
          (Printf.sprintf "Todo: ParamName::Fresh (at %s)"
             (Ast.string_of_loc loc))
    | Undefined _ -> Error (`TrHirGenericParamName "Unknown ParamName kind")

  let translate_hir_generic_param_kind (kind_cpn : HirGenericParamKindRd.t) =
    let open HirGenericParamKindRd in
    match get kind_cpn with
    | Lifetime -> Ok Hir.GenParamLifetime
    | Type -> Ok Hir.GenParamType
    | Const -> Ok Hir.GenParamConst
    | Undefined _ -> Error (`TrHirGenericParamKind "Unknown GenericParamKind")

  let translate_hir_generic_param (p_cpn : HirGenericParamRd.t) =
    let open HirGenericParamRd in
    let span_cpn = span_get p_cpn in
    let* loc = translate_span_data span_cpn in
    let kind_cpn = kind_get p_cpn in
    let* kind = translate_hir_generic_param_kind kind_cpn in
    let name_cpn = name_get p_cpn in
    let* name, name_loc =
      translate_hir_generic_param_name loc (kind = Hir.GenParamType) name_cpn
    in
    let pure_wrt_drop = pure_wrt_drop_get p_cpn in
    Ok (name, kind, loc)

  let translate_hir_generics (gens_cpn : HirGenericsRd.t) =
    let open HirGenericsRd in
    let params_cpn = params_get_list gens_cpn in
    let* params = ListAux.try_map translate_hir_generic_param params_cpn in
    let span_cpn = span_get gens_cpn in
    let* loc = translate_span_data span_cpn in
    Ok (params, loc)

  let translate_trait_required_fn (adt_defs : Mir.adt_def_tr list)
      (trait_name : string) (required_fn_cpn : TraitRd.RequiredFn.t) =
    let open TraitRd.RequiredFn in
    let name = name_get required_fn_cpn in
    let* loc = translate_span_data (name_span_get required_fn_cpn) in
    let* input_infos =
      inputs_get_list required_fn_cpn
      |> ListAux.try_map (fun ty_cpn -> translate_ty ty_cpn loc)
    in
    let inputs = input_infos |> List.map Mir.basic_type_of in
    let* output = translate_ty (output_get required_fn_cpn) loc in
    let ret_ty = Mir.basic_type_of output in
    let arg_names = arg_names_get_list required_fn_cpn in
    let (Some vf_param_decls) = Util.zip inputs arg_names in
    let* unsafe = translate_unsafety (unsafety_get required_fn_cpn) in
    let contract = contract_get_list required_fn_cpn in
    let* annots = ListAux.try_map translate_annotation contract in
    let annots = List.map translate_annot_to_vf_parser_inp annots in
    let* ( (nonghost_callers_only : bool),
           (fn_type_clause : _ option),
           (pre_post : _ option),
           (terminates : bool) ) =
      if unsafe then Ok (VfMirAnnotParser.parse_func_contract annots)
      else (
        if contract <> [] then
          raise
            (Ast.StaticError
               ( loc,
                 "An explicit spec on a safe trait required function is not \
                  yet supported",
                 None ));
        let params : Mir.local_decl list =
          List.combine arg_names input_infos
          |> List.map (fun (arg_name, ty_info) : Mir.local_decl ->
                 { id = arg_name; ty = ty_info; loc; mutability = Not })
        in
        let result : Mir.local_decl =
          { id = "result"; ty = output; loc; mutability = Not }
        in
        let* pre, post =
          gen_contract adt_defs loc
            (lifetime_params_get_list required_fn_cpn)
            params result
        in
        Ok (false, None, Some (pre, post), false))
    in
    let decl =
      Ast.Func
        ( loc,
          Ast.Regular,
          (*type params*) [ "Self" ],
          Some ret_ty,
          Printf.sprintf "%s::%s" trait_name name,
          vf_param_decls,
          nonghost_callers_only,
          fn_type_clause,
          pre_post,
          terminates,
          None,
          (*virtual*) false,
          (*overrides*) [] )
    in
    Ok decl

  let translate_trait (adt_defs : Mir.adt_def_tr list) (trait_cpn : TraitRd.t) =
    let name = TraitRd.name_get trait_cpn in
    let* required_fns =
      CapnpAux.ind_list_get_list (TraitRd.required_fns_get trait_cpn)
    in
    ListAux.try_map (translate_trait_required_fn adt_defs name) required_fns

  let translate_body (body_tr_defs_ctx : body_tr_defs_ctx) (body_cpn : BodyRd.t)
      =
    let open BodyRd in
    let var_id_trs_map_ref = ref [] in
    let ghost_stmts_cpn = ghost_stmts_get_list body_cpn in
    let* ghost_stmts = ListAux.try_map translate_ghost_stmt ghost_stmts_cpn in
    let* ghost_stmts =
      ListAux.try_sort LocAux.compare_err_desc
        (fun s1 s2 ->
          let f s = s |> Ast.stmt_loc |> Ast.lexed_loc in
          let l1, l2 = (f s1, f s2) in
          LocAux.try_compare_loc l1 l2)
        ghost_stmts
    in
    let* ghost_decl_blocks =
      ListAux.try_map translate_ghost_decl_block
        (ghost_decl_blocks_get_list body_cpn)
    in
    let ghost_decl_block_start_stmts =
      ghost_decl_blocks
      |> List.map @@ fun (Ast.BlockStmt (l, decls, [], closeBraceLoc, _)) ->
         Ast.BlockStmt
           ( l,
             decls,
             [
               ExprStmt
                 (CallExpr (l, "#ghost_decl_block_start", [], [], [], Static));
             ],
             closeBraceLoc,
             ref [] )
    in
    let ghost_decl_block_end_stmts =
      ghost_decl_blocks
      |> List.map @@ fun (Ast.BlockStmt (l, decls, [], closeBraceLoc, _)) ->
         Ast.ExprStmt
           (CallExpr (closeBraceLoc, "#ghost_decl_block_end", [], [], [], Static))
    in
    let ghost_stmts =
      ghost_decl_block_start_stmts @ ghost_decl_block_end_stmts @ ghost_stmts
    in
    let imp_span_cpn = imp_span_get body_cpn in
    let* imp_loc = translate_span_data imp_span_cpn in
    let open TrBody (struct
      let var_id_trs_map_ref = var_id_trs_map_ref
      let ghost_stmts = ghost_stmts
      let body_imp_loc = imp_loc
      let body_tr_defs_ctx = body_tr_defs_ctx
    end) in
    let vdis_cpn = var_debug_info_get_list body_cpn in
    (* Since var id translation map is empty var debug info contains the plain Mir ids *)
    let* vdis = ListAux.try_map translate_var_debug_info vdis_cpn in
    let env_map, trs_map = make_var_id_name_maps vdis in
    let _ = var_id_trs_map_ref := trs_map in
    let def_kind_cpn = def_kind_get body_cpn in
    let def_kind = DefKind.get def_kind_cpn in
    match def_kind with
    | DefKind.Fn ->
        let def_path = def_path_get body_cpn in
        let name = TrName.translate_def_path def_path in
        (*Printf.printf "Translating body %s...\n" name;*)
        let* tparams =
          match impl_block_hir_generics_get body_cpn |> OptionRd.get with
          | Nothing -> Ok []
          | Something hir_gens_cpn_ptr ->
              let hir_gens_cpn = VfMirStub.Reader.of_pointer hir_gens_cpn_ptr in
              let* gens, gens_loc = translate_hir_generics hir_gens_cpn in
              Ok
                (Util.flatmap
                   (function
                     | name, Hir.GenParamType, loc -> [ name ] | _ -> [])
                   gens)
        in
        let hir_gens_cpn = hir_generics_get body_cpn in
        let* gens, gens_loc = translate_hir_generics hir_gens_cpn in
        let* lft_param_names =
          ListAux.try_filter_map
            (fun (name, kind, loc) ->
              if kind = Hir.GenParamLifetime then
                let* name = TrName.lft_name_without_apostrophe name in
                Ok (Some name)
              else Ok None)
            gens
        in
        let tparams =
          tparams
          @ Util.flatmap
              (function name, Hir.GenParamType, loc -> [ name ] | _ -> [])
              gens
        in
        let tparams =
          if is_trait_fn_get body_cpn then "Self" :: tparams else tparams
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
        let contract_cpn = contract_get body_cpn in
        let* contract_loc, contract_opt = translate_contract contract_cpn in
        let* is_unsafe = translate_unsafety @@ unsafety_get @@ body_cpn in
        let* contract_template_opt, contract =
          if is_unsafe then
            let* contract =
              Option.to_result
                ~none:
                  (`TrBodyFailed
                    ( contract_loc,
                      "User should provide contract for unsafe functions" ))
                contract_opt
            in
            Ok (None, contract)
          else
            (*safe function*)
            let* pre_post_template =
              if is_drop_fn_get body_cpn then
                let ({ ty = self_ty } :: _) = param_decls in
                let (PtrTypeExpr
                      (_, StructTypeExpr (_, Some self_ty, _, _, self_ty_targs)))
                    =
                  Mir.basic_type_of self_ty
                in
                gen_drop_contract body_tr_defs_ctx.adt_defs self_ty
                  self_ty_targs contract_loc
              else
                gen_contract body_tr_defs_ctx.adt_defs contract_loc
                  lft_param_names param_decls ret_place_decl
            in
            let contract_template =
              (false, None, Some pre_post_template, false)
            in
            match contract_opt with
            | None -> Ok (None, contract_template)
            | Some contract -> Ok (Some contract_template, contract)
        in
        let bblocks_cpn = basic_blocks_get_list body_cpn in
        let* bblocks =
          ListAux.try_filter_map
            (fun bblock_cpn -> translate_basic_block ret_place_id bblock_cpn)
            bblocks_cpn
        in
        let toplevel_blocks = find_blocks bblocks in
        let vf_bblocks =
          Util.flatmap translate_to_vf_basic_block toplevel_blocks
        in
        let span_cpn = span_get body_cpn in
        let* loc = translate_span_data span_cpn in
        let* closing_cbrace_loc = LocAux.get_last_col_loc loc in
        let mk_fn_decl contract body =
          let ( (nonghost_callers_only : bool),
                (fn_type_clause : _ option),
                (pre_post : _ option),
                (terminates : bool) ) =
            contract
          in
          Ast.Func
            ( loc,
              Ast.Regular,
              (*type params*) tparams,
              Some ret_ty,
              name,
              vf_param_decls,
              nonghost_callers_only,
              fn_type_clause,
              pre_post,
              terminates,
              body,
              (*virtual*) false,
              (*overrides*) [] )
        in
        let body =
          mk_fn_decl contract
            (Some (vf_local_decls @ vf_bblocks, closing_cbrace_loc))
        in
        let body_sig_opt =
          match contract_template_opt with
          | None -> None
          | Some contract_template ->
              let body_sig = mk_fn_decl contract_template None in
              Some body_sig
        in
        Ok
          ( body_sig_opt,
            body,
            ({ id = loc; info = env_map } : VF0.debug_info_rust_fe) )
    | DefKind.AssocFn -> failwith "Todo: MIR Body kind AssocFn"
    | _ -> Error (`TrBodyFatal "Unknown MIR Body kind")

  let translate_visibility (vis_cpn : VisibilityRd.t) =
    let open VisibilityRd in
    match get vis_cpn with
    | Public -> Ok Mir.Public
    | Restricted -> Ok Mir.Restricted
    | Invisible -> Ok Mir.Invisible
    | Undefined _ -> Error (`TrVisibility "Unknown visibility kind")

  let translate_field_def (fdef_cpn : FieldDefRd.t) =
    let open FieldDefRd in
    let name_cpn = name_get fdef_cpn in
    let name = translate_symbol name_cpn in
    let span_cpn = span_get fdef_cpn in
    let* loc = translate_span_data span_cpn in
    (* Todo @Nima: We are using the whole field definition span as the type span which should be corrected *)
    let ty_cpn = ty_get fdef_cpn in
    let* ty_info = translate_ty ty_cpn loc in
    let vis_cpn = vis_get fdef_cpn in
    let* vis = translate_visibility vis_cpn in
    Ok Mir.{ name; ty = ty_info; vis; loc }

  let translate_to_vf_field_def
      (Mir.{ name; ty = ty_info; vis; loc } : Mir.field_def_tr) =
    Ast.Field
      ( loc,
        Ast.Real (*ghostness*),
        Mir.basic_type_of ty_info,
        name,
        Ast.Instance (*method_binding*),
        Ast.Public (*visibility*),
        true (*final*),
        None (*expr option*) )

  let translate_variant_def (vdef_cpn : VariantDefRd.t) =
    let open VariantDefRd in
    let* loc = translate_span_data (span_get vdef_cpn) in
    let name = name_get vdef_cpn in
    let fields_cpn = fields_get_list vdef_cpn in
    let* fields = ListAux.try_map translate_field_def fields_cpn in
    Ok Mir.{ loc; name; fields }

  let gen_adt_full_borrow_content adt_kind name tparams
      (variants : Mir.variant_def_tr list) adt_def_loc =
    let open Ast in
    match adt_kind with
    | Mir.Enum | Mir.Union ->
        failwith "Todo: Gen ADT full borrow content for Enum or Union"
    | Mir.Struct ->
        let fbor_content_name = name ^ "_full_borrow_content" in
        let tid_param_name = "tid" in
        let ptr_param_name = "l" in
        let fbor_content_params =
          [
            ( IdentTypeExpr (adt_def_loc, None (*package name*), "thread_id_t"),
              tid_param_name );
            ( ManifestTypeExpr
                ( adt_def_loc,
                  PtrType
                    (StructType
                       (name, List.map (fun x -> GhostTypeParam x) tparams)) ),
              ptr_param_name );
          ]
        in
        let* fields =
          match variants with
          | [ variant_def ] -> Ok variant_def.fields
          | _ ->
              Error
                (`GenAdtFullBorContent "Struct ADT def should have one variant")
        in
        let field_chunk (f : Mir.field_def_tr) =
          let* fc =
            (Mir.interp_of f.ty).points_to
              (Var (f.loc, tid_param_name))
              (Read (f.loc, Var (f.loc, ptr_param_name), f.name))
              (Some f.name)
          in
          Ok (f.loc, fc)
        in
        let* field_chunks =
          match ListAux.try_map field_chunk fields with
          | Ok field_chunks -> Ok field_chunks
          | Error msg -> Error (`GenAdtFullBorContent msg)
        in
        let own_args =
          LitPat (Var (adt_def_loc, tid_param_name))
          :: List.map
               (fun (f : Mir.field_def_tr) -> LitPat (Var (f.loc, f.name)))
               fields
        in
        let own_pred =
          CallExpr
            ( adt_def_loc,
              name ^ "_own",
              (*type arguments*)
              List.map (fun x -> IdentTypeExpr (adt_def_loc, None, x)) tparams,
              (*indices*) [],
              (*arguments*)
              own_args,
              Static )
        in
        let padding_pred =
          CallExpr
            ( adt_def_loc,
              Printf.sprintf "struct_%s_padding" name,
              List.map (fun x -> IdentTypeExpr (adt_def_loc, None, x)) tparams,
              [],
              [ LitPat (Var (adt_def_loc, ptr_param_name)) ],
              Static )
        in
        let (Some body_asn) =
          AstAux.list_to_sep_conj field_chunks
            (Some (Ast.Sep (adt_def_loc, padding_pred, own_pred)))
        in
        let fbor_content_pred_ctor =
          PredCtorDecl
            ( adt_def_loc,
              fbor_content_name,
              tparams (* type parameters*),
              fbor_content_params,
              [],
              None
              (* (Some n) means the predicate is precise and the first n parameters are input parameters *),
              body_asn )
        in
        Ok fbor_content_pred_ctor

  let gen_adt_proof_obligs adt_def tparams =
    let open Ast in
    let* adt_kind = Mir.decl_mir_adt_kind adt_def in
    match adt_kind with
    | Mir.Enum | Mir.Union ->
        failwith "Todo: Gen proof obligs for Enum or Union"
    | Mir.Struct ->
        let adt_def_loc = AstAux.decl_loc adt_def in
        let tparams_targs =
          List.map (fun x -> IdentTypeExpr (adt_def_loc, None, x)) tparams
        in
        let* name =
          Option.to_result ~none:(`GenAdtProofObligs "Failed to get ADT name")
            (AstAux.decl_name adt_def)
        in
        let lft_param n =
          (IdentTypeExpr (adt_def_loc, None (*package name*), "lifetime_t"), n)
        in
        let thread_id_param n =
          (IdentTypeExpr (adt_def_loc, None (*package name*), "thread_id_t"), n)
        in
        let void_ptr_param n =
          (ManifestTypeExpr (adt_def_loc, PtrType Void), n)
        in
        let lpat_var n = LitPat (Var (adt_def_loc, n)) in
        let add_type_interp_asn asn =
          List.fold_right
            (fun x asn ->
              Sep
                ( adt_def_loc,
                  CallExpr
                    ( adt_def_loc,
                      "type_interp",
                      [ IdentTypeExpr (adt_def_loc, None, x) ],
                      [],
                      [],
                      Static ),
                  asn ))
            tparams asn
        in
        (*TY-SHR-MONO*)
        let params =
          [
            lft_param "k";
            lft_param "k1";
            thread_id_param "t";
            void_ptr_param "l";
          ]
        in
        let lft_inc_asn =
          Operation
            ( adt_def_loc,
              Eq,
              [
                CallExpr
                  ( adt_def_loc,
                    "lifetime_inclusion",
                    (*type arguments*) [],
                    (*indices*) [],
                    (*arguments*)
                    List.map lpat_var [ "k1"; "k" ],
                    Static );
                True adt_def_loc;
              ] )
        in
        let shr_asn lft_n =
          CoefAsn
            ( adt_def_loc,
              DummyPat,
              CallExpr
                ( adt_def_loc,
                  name ^ "_share",
                  (*type arguments*) tparams_targs,
                  (*indices*) [],
                  (*arguments*)
                  List.map lpat_var [ lft_n; "t"; "l" ],
                  Static ) )
        in
        let pre =
          add_type_interp_asn (Sep (adt_def_loc, lft_inc_asn, shr_asn "k"))
        in
        let post = add_type_interp_asn (shr_asn "k1") in
        let share_mono_po =
          Func
            ( adt_def_loc,
              Lemma
                ( false
                  (*indicates whether an axiom should be generated for this lemma*),
                  None (*trigger*) ),
              tparams (*type parameters*),
              None (*return type*),
              name ^ "_share_mono",
              params,
              false (*nonghost_callers_only*),
              None
              (*implemented function type, with function type type arguments and function type arguments*),
              Some (pre, post) (*contract*),
              false (*terminates*),
              None (*body*),
              false (*virtual*),
              [] (*overrides*) )
        in
        (*TY-SHR*)
        let params =
          [ lft_param "k"; thread_id_param "t"; void_ptr_param "l" ]
        in
        let atomic_mask_token =
          CallExpr
            ( adt_def_loc,
              "atomic_mask",
              (*type arguments*) [],
              (*indices*) [],
              (*arguments*)
              [ lpat_var "Nlft" ],
              Static )
        in
        let fbor_pred =
          CallExpr
            ( adt_def_loc,
              "full_borrow",
              (*type arguments*) [],
              (*indices*) [],
              (*arguments*)
              [
                lpat_var "k";
                LitPat
                  (CallExpr
                     ( adt_def_loc,
                       name ^ "_full_borrow_content",
                       (*type arguments*) tparams_targs,
                       (*indices*) [],
                       (*arguments*)
                       List.map lpat_var [ "t"; "l" ],
                       Static ));
              ],
              Static )
        in
        let lft_token coef_pat =
          CoefAsn
            ( adt_def_loc,
              coef_pat,
              CallExpr
                ( adt_def_loc,
                  "lifetime_token",
                  (*type arguments*) [],
                  (*indices*) [],
                  (*arguments*)
                  [ lpat_var "k" ],
                  Static ) )
        in
        let (Some pre) =
          AstAux.list_to_sep_conj
            (List.map
               (fun asn -> (adt_def_loc, asn))
               [
                 atomic_mask_token;
                 fbor_pred;
                 lft_token (VarPat (adt_def_loc, "q"));
               ])
            None
        in
        let pre = add_type_interp_asn pre in
        let share_pred =
          CoefAsn
            ( adt_def_loc,
              DummyPat,
              CallExpr
                ( adt_def_loc,
                  name ^ "_share",
                  (*type arguments*) tparams_targs,
                  (*indices*) [],
                  (*arguments*) List.map lpat_var [ "k"; "t"; "l" ],
                  Static ) )
        in
        let (Some post) =
          AstAux.list_to_sep_conj
            (List.map
               (fun asn -> (adt_def_loc, asn))
               [ atomic_mask_token; share_pred; lft_token (lpat_var "q") ])
            None
        in
        let post = add_type_interp_asn post in
        let share_po =
          Func
            ( adt_def_loc,
              Lemma
                ( false
                  (*indicates whether an axiom should be generated for this lemma*),
                  None (*trigger*) ),
              tparams (*type parameters*),
              None (*return type*),
              name ^ "_share_full",
              params,
              false (*nonghost_callers_only*),
              None
              (*implemented function type, with function type type arguments and function type arguments*),
              Some (pre, post) (*contract*),
              false (*terminates*),
              None (*body*),
              false (*virtual*),
              [] (*overrides*) )
        in
        Ok [ share_mono_po; share_po ]

  let translate_adt_def (adt_def_cpn : AdtDefRd.t) =
    let open AdtDefRd in
    let id_cpn = id_get adt_def_cpn in
    let def_path = translate_adt_def_id id_cpn in
    if TrName.is_from_std_lib def_path then Ok None
    else
      let name = TrName.translate_def_path def_path in
      let* tparams =
        hir_generics_get adt_def_cpn
        |> HirGenericsRd.params_get_list
        |> ListAux.try_map @@ fun param_cpn ->
           let* l =
             translate_span_data (HirGenericParamRd.span_get param_cpn)
           in
           (match
              HirGenericParamRd.kind_get param_cpn |> HirGenericParamKindRd.get
            with
           | Lifetime ->
               raise
                 (Ast.StaticError
                    ( l,
                      "Structs with lifetime parameters are not yet supported",
                      None ))
           | Type -> ()
           | Const ->
               raise
                 (Ast.StaticError
                    ( l,
                      "Structs with const parameters are not yet supported",
                      None )));
           match
             HirGenericParamRd.name_get param_cpn |> HirGenericParamNameRd.get
           with
           | Plain ident -> Ok (IdentRd.name_get ident |> SymbolRd.name_get)
           | Fresh _ ->
               raise
                 (Ast.StaticError
                    ( l,
                      "Structs with inferred type parameters are not yet \
                       supported",
                      None ))
      in
      let variants_cpn = variants_get_list adt_def_cpn in
      let* variants = ListAux.try_map translate_variant_def variants_cpn in
      let span_cpn = span_get adt_def_cpn in
      let* def_loc = translate_span_data span_cpn in
      let tparams_targs =
        List.map (fun x -> Ast.IdentTypeExpr (def_loc, None, x)) tparams
      in
      let vis_cpn = vis_get adt_def_cpn in
      let* vis = translate_visibility vis_cpn in
      let is_local = is_local_get adt_def_cpn in
      let kind_cpn = kind_get adt_def_cpn in
      let* kind, fds, def, aux_decls =
        match AdtKindRd.get kind_cpn with
        | StructKind ->
            let* fds =
              match variants with
              | [ variant_def ] -> Ok variant_def.fields
              | _ -> Error (`TrAdtDef "Struct ADT kind should have one variant")
            in
            let field_defs = List.map translate_to_vf_field_def fds in
            let struct_decl =
              Ast.Struct
                ( def_loc,
                  name,
                  tparams,
                  Some
                    ( (*base_spec list*) [],
                      (*field list*) field_defs,
                      (*instance_pred_decl list*) [],
                      (*is polymorphic*) false ),
                  (*struct_attr list*) [] )
            in
            let struct_typedef_aux =
              Ast.TypedefDecl
                ( def_loc,
                  StructTypeExpr (def_loc, Some name, None, [], tparams_targs),
                  name,
                  tparams )
            in
            Ok (Mir.Struct, fds, struct_decl, [ struct_typedef_aux ])
        | EnumKind ->
            let ctors =
              variants
              |> List.map @@ fun Mir.{ loc; name; fields } ->
                 let ps =
                   fields
                   |> List.map @@ fun Mir.{ name; ty } ->
                      (name, Mir.basic_type_of ty)
                 in
                 Ast.Ctor (loc, name, ps)
            in
            let decl = Ast.Inductive (def_loc, name, tparams, ctors) in
            Ok (Mir.Enum, [], decl, [])
        | UnionKind -> failwith "Todo: AdtDef::Union"
        | Undefined _ -> Error (`TrAdtDef "Unknown ADT kind")
      in
      (* Todo: Should we have full_borrow_content for private structs? In particular a private function can have a mutable reference to a private struct. *)
      let* full_bor_content, proof_obligs, aux_decls' =
        match (is_local, vis) with
        | false, _ | true, Mir.Restricted -> Ok (None, [], [])
        | true, Mir.Invisible ->
            Error
              (`TrAdtDef
                ("The " ^ def_path
               ^ " ADT definition is local and locally invisible"))
        | true, Mir.Public ->
            let* full_bor_content =
              gen_adt_full_borrow_content kind name tparams variants def_loc
            in
            let* proof_obligs = gen_adt_proof_obligs def tparams in
            let own__pred_decls =
              let own_args =
                fds
                |> List.map @@ fun (fd : Mir.field_def_tr) ->
                   Ast.LitPat (Select (def_loc, Var (def_loc, "v"), fd.name))
              in
              [
                Ast.PredFamilyDecl
                  ( def_loc,
                    name ^ "_own_",
                    tparams,
                    0,
                    [
                      IdentTypeExpr (def_loc, None, "thread_id_t");
                      StructTypeExpr
                        (def_loc, Some name, None, [], tparams_targs);
                    ],
                    None,
                    Ast.Inductiveness_Inductive );
                Ast.PredFamilyInstanceDecl
                  ( def_loc,
                    name ^ "_own_",
                    tparams,
                    [],
                    [
                      (IdentTypeExpr (def_loc, None, "thread_id_t"), "t");
                      ( StructTypeExpr
                          (def_loc, Some name, None, [], tparams_targs),
                        "v" );
                    ],
                    CallExpr
                      ( def_loc,
                        name ^ "_own",
                        tparams_targs,
                        [],
                        LitPat (Var (def_loc, "t")) :: own_args,
                        Static ) );
              ]
            in
            Ok (Some full_bor_content, proof_obligs, own__pred_decls)
      in
      Ok
        (Some
           Mir.
             {
               loc = def_loc;
               name;
               tparams;
               fds;
               def;
               aux_decls = aux_decls @ aux_decls';
               full_bor_content;
               proof_obligs;
             })

  (** Checks for the existence of a lemma for proof obligation in ghost code.
      The consistency of the lemma with proof obligation will be checked by VeriFast later *)
  let check_proof_obligation gh_decls po =
    let loc = AstAux.decl_loc po in
    let* po_name =
      Option.to_result
        ~none:(`ChekProofObligationFatal "Proof obligation without a name")
        (AstAux.decl_name po)
    in
    let check decl =
      match decl with
      | Ast.Func (_, _, _, _, name, _, _, _, _, _, Some body, _, _)
        when po_name = name ->
          true
      | _ -> false
    in
    if List.exists check gh_decls then
      Ok () (*in case of duplicates VeriFast complains later*)
    else
      Error
        (`ChekProofObligationFailed
          (loc, "Lemma " ^ po_name ^ " Should be proven"))

  type trait_impl = {
    loc : Ast.loc;
    of_trait : string;
    self_ty : string;
    items : string list;
  }

  let translate_trait_impls (trait_impls_cpn : TraitImplRd.t list) =
    trait_impls_cpn
    |> ListAux.try_map (fun trait_impl_cpn ->
           let open TraitImplRd in
           let* loc = translate_span_data (span_get trait_impl_cpn) in
           let of_trait = of_trait_get trait_impl_cpn in
           let self_ty = self_ty_get trait_impl_cpn in
           let items = items_get_list trait_impl_cpn in
           Ok ({ loc; of_trait; self_ty; items } : trait_impl))

  let compute_trait_impl_prototypes (adt_defs : Mir.adt_def_tr list)
      traits_and_body_decls trait_impls =
    trait_impls
    |> Util.flatmap (fun { loc = limpl; of_trait; self_ty; items } ->
           if of_trait = "std::ops::Drop" then (
             assert (items = [ "drop" ]);
             [] (* drop is safe *))
           else
             items
             |> List.map (fun item ->
                    let trait_fn_name = Printf.sprintf "%s::%s" of_trait item in
                    let impl_fn_name =
                      Printf.sprintf "<%s as %s>::%s" self_ty of_trait item
                    in
                    let (Some prototype) =
                      traits_and_body_decls
                      |> Util.head_flatmap_option (function
                           | Ast.Func
                               ( lf,
                                 Regular,
                                 "Self" :: tparams,
                                 rt,
                                 name,
                                 ps,
                                 false,
                                 None,
                                 Some (pre, post),
                                 terminates,
                                 body,
                                 false,
                                 [] )
                             when name = trait_fn_name ->
                               let self_ty_typeid =
                                 Ast.Typeid
                                   ( lf,
                                     Ast.TypeExpr
                                       (Ast.ManifestTypeExpr
                                          (lf, Ast.StructType (self_ty, []))) )
                               in
                               let pre =
                                 Ast.LetTypeAsn
                                   ( lf,
                                     "Self",
                                     Ast.StructType (self_ty, []),
                                     Ast.Sep
                                       ( lf,
                                         MatchAsn
                                           ( lf,
                                             self_ty_typeid,
                                             VarPat (lf, "Self_typeid") ),
                                         Ast.Sep
                                           (lf, pre, Ast.EnsuresAsn (lf, post))
                                       ) )
                               in
                               let post = Ast.EmpAsn lf in
                               Some
                                 (Ast.Func
                                    ( lf,
                                      Regular,
                                      tparams,
                                      rt,
                                      impl_fn_name,
                                      ps,
                                      false,
                                      None,
                                      Some (pre, post),
                                      terminates,
                                      None,
                                      false,
                                      [] ))
                           | _ -> None)
                    in
                    prototype))

  let rec translate_module (module_cpn : VfMirStub.Reader.Module.t) :
      (Ast.decl, _) result =
    let open VfMirStub.Reader.Module in
    let name = name_get module_cpn in
    let* loc = translate_span_data (header_span_get module_cpn) in
    let* submodules =
      submodules_get_list module_cpn |> ListAux.try_map translate_module
    in
    let* ghost_decl_batches =
      ListAux.try_map translate_ghost_decl_batch
        (ghost_decl_batches_get_list module_cpn)
    in
    Ok
      (Ast.ModuleDecl
         (loc, name, [], submodules @ List.flatten ghost_decl_batches))

  let modularize_decl (d : Ast.decl) : Ast.decl =
    let l, name, name_setter = AstAux.decl_loc_name_and_name_setter d in
    if String.contains name ':' then
      let segments = String.split_on_char ':' name in
      let rec iter = function
        | segment :: "" :: segments ->
            Ast.ModuleDecl (l, segment, [], [ iter segments ])
        | [ segment ] -> name_setter segment
      in
      iter segments
    else d

  let translate_vf_mir (extern_specs : string list) (vf_mir_cpn : VfMirRd.t)
      (report_should_fail : string -> Ast.loc0 -> unit) =
    let job _ =
      let directives_cpn = VfMirRd.directives_get_list vf_mir_cpn in
      let* directives = ListAux.try_map translate_annotation directives_cpn in
      directives
      |> List.iter (fun ({ span; raw } : Mir.annot) ->
             report_should_fail raw (Ast.lexed_loc span));
      let adt_defs_cpn = VfMirRd.adt_defs_get vf_mir_cpn in
      let* adt_defs_cpn = CapnpAux.ind_list_get_list adt_defs_cpn in
      let* adt_defs = ListAux.try_map translate_adt_def adt_defs_cpn in
      let adt_defs = List.filter_map Fun.id adt_defs in
      (* Todo @Nima: External definitions and their corresponding ghost headers inclusion should be handled in a better way *)
      (* Todo @Nima: The MIR exporter encodes `ADT`s and adds the `ADT` declarations used in them later in the same array.
         For a Tree hierarchy of types just reversing the array works but obviously
         for more complicated scenarios we need to add all of the declarations without definitions first
         and then add all of the complete declarations
         Note that the following `fold_left` also reverses the list
      *)
      let adt_decls, aux_decls, adts_full_bor_content_preds, adts_proof_obligs =
        List.fold_left
          (fun (defs, ads, fbors, pos)
               Mir.{ def; aux_decls; full_bor_content; proof_obligs } ->
            ( def :: defs,
              aux_decls @ ads,
              full_bor_content :: fbors,
              proof_obligs @ pos ))
          ([], [], [], []) adt_defs
      in
      let adts_full_bor_content_preds =
        List.filter_map Fun.id adts_full_bor_content_preds
      in
      let* module_decls =
        ListAux.try_map translate_module (VfMirRd.modules_get_list vf_mir_cpn)
      in
      let ghost_decl_batches_cpn =
        VfMirRd.ghost_decl_batches_get_list vf_mir_cpn
      in
      let* ghost_decl_batches =
        ListAux.try_map translate_ghost_decl_batch ghost_decl_batches_cpn
      in
      let ghost_decls = module_decls @ List.flatten ghost_decl_batches in
      let* _ =
        ListAux.try_map
          (fun po -> check_proof_obligation ghost_decls po)
          adts_proof_obligs
      in
      let* traits_cpn =
        CapnpAux.ind_list_get_list (VfMirRd.traits_get vf_mir_cpn)
      in
      let* traits_decls =
        ListAux.try_map (translate_trait adt_defs) traits_cpn
      in
      let traits_decls = List.flatten traits_decls in
      let bodies_cpn = VfMirRd.bodies_get_list vf_mir_cpn in
      let body_tr_defs_ctx = { adt_defs } in
      let* bodies_tr_res =
        ListAux.try_map (translate_body body_tr_defs_ctx) bodies_cpn
      in
      let body_sig_opts, body_decls, debug_infos =
        ListAux.split3 bodies_tr_res
      in
      let body_sigs = List.filter_map Fun.id body_sig_opts in
      (* `vfide` relies on the similarity of the order of function declarations
         over several calls to `verifast` hence we are sorting them since `rustc` does not keep that order the same.
      *)
      let body_sigs = AstAux.sort_decls_lexically body_sigs in
      let body_decls = AstAux.sort_decls_lexically body_decls in
      let traits_and_body_decls = traits_decls @ body_decls in
      let* trait_impls =
        translate_trait_impls (VfMirRd.trait_impls_get_list vf_mir_cpn)
      in
      let debug_infos = VF0.DbgInfoRustFe debug_infos in
      let trait_impl_prototypes =
        compute_trait_impl_prototypes adt_defs traits_and_body_decls trait_impls
      in
      (* Hack: for structs, functions, and other item-likes inside modules we
         currently generate toplevel VF declarations with paths as names. However, to properly resolve names inside those declarations,
         they need to be inside appropriate `ModuleDecl`s. `modularize_decl` does this. TODO: Generate the declarations inside the right
         module declarations from the start. This will become necessary once we want to take real `use` items into account inside annotations.*)
      let decls =
        List.map modularize_decl
          (traits_decls @ trait_impl_prototypes @ adt_decls @ aux_decls
         @ adts_full_bor_content_preds @ adts_proof_obligs)
        @ ghost_decls
        @ List.map modularize_decl (body_sigs @ body_decls)
      in
      (* Todo @Nima: we should add necessary inclusions during translation *)
      let extern_header_names =
        extern_specs
        |> List.map @@ fun extern_spec ->
           match String.split_on_char '=' extern_spec with
           | [ crateName; header_path ] -> (crateName, header_path)
           | _ ->
               failwith
                 (Printf.sprintf
                    "-extern_spec argument '%s' should be of the form \
                     `crateName=path/to/spec_file.rsspec`"
                    extern_spec)
      in
      let header_names =
        [
          ( "std",
            Filename.concat
              (Filename.dirname Sys.executable_name)
              "rust/std/lib.rsspec" );
        ]
        @ extern_header_names
      in
      let headers =
        Util.flatmap
          (fun (crateName, header_path) -> parse_header crateName header_path)
          header_names
      in
      Ok
        ( headers,
          Rust_parser.flatten_module_decls Ast.dummy_loc decls,
          Some debug_infos )
    in
    match job () with
    | Ok res -> res
    | Error err -> (
        match err with
        | `AdtTyName str
        | `CapnpIndListGetList str
        | `ChekProofObligationFatal str
        | `DeclMirAdtKind str
        | `GenAdtFullBorContent str
        | `GenAdtProofObligs str
        | `GenLocalTyAsn str
        | `GetAdtDef str
        | `GetLastColLoc str
        | `IntAuxAdd str
        | `IsWellFormedLoc0 str
        | `IsWellFormedSrcPos str
        | `LftNameWithoutApostrophe str
        | `SizeAuxSzBitsOfInt str
        | `Sort str
        | `TrAdtDef str
        | `TrAdtTy str
        | `TrAggregate str
        | `TrAggregateKind str
        | `TrBinOp str
        | `TrBodyFatal str
        | `TrConstValue str
        | `TrConstantKind str
        | `TrContract str
        | `TrFileName str
        | `TrFnCall str
        | `TrFnCallRExpr str
        | `TrFnDefTy str
        | `TrGenArg str
        | `TrHirGenericParamKind str
        | `TrHirGenericParamName str
        | `TrMutability str
        | `TrOperand str
        | `TrPlaceElement str
        | `TrRealFileName str
        | `TrRvalue str
        | `TrScalar str
        | `TrScalarUint str
        | `TrStatementKind str
        | `TrSwInt str
        | `TrTerminatorKind str
        | `TrToVfBBlock str
        | `TrTy str
        | `TrTyConstKind str
        | `TrUIntTy str
        | `TrUnsafety str
        | `TrVarDebugInfoContents str
        | `TrVisibility str
        | `TryCompareLoc str
        | `TryCompareSrcPos str
        | `UIntTyBitsLen str ->
            print_endline ("MIR Translator Failed: " ^ str);
            raise (Parser.CompilationError "Rust Translator Error")
        | `IntAuxToInt ->
            raise
              (Parser.CompilationError "Rust Translator Error: to int failed")
        | `ChekProofObligationFailed (loc, str) | `TrBodyFailed (loc, str) ->
            raise (Ast.StaticError (loc, str, None)))

  (* Todo @Nima: We should add error handling parts at the end of `translate_*` functions *)
end
(* Todo @Nima: There would be naming conflicts if the user writes a function in Rust with a name like `std_alloc_alloc`.
   A possible solution might be adding `crate` in front of local declarations. Another problem with names is that two paths
   like `a::mut_ptr::b` and `a::mut_ptr::b` both convert to `a_mut_ptr_b` *)

(* Todo @Nima: Unit type gets translated to an empty struct and Never (empty) type to an empty union.
   The latter is not true because an empty union type has a value. For now, we are preventing the production and consumption
   of padding chunks and chars predicates for empty structs and empty unions respectively when verifying Rust programs in
   the `produce_c_object` and `consume_c_object` functions in `verify_expr.ml`.
   For the Never type, we should add a specific type to VeriFast instead and extend the function `prover_type_of_type` to support it.
   Moreover, check for the correct behaviour of production and consumption of chars predicate for empty Rust unions. *)
