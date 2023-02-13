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
    val div : t -> t -> t
    val rem : t -> t -> t
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

    let rec to_big_int (a : t) =
      let a_maybe_truncated = to_int a in
      let a_reconst = of_int a_maybe_truncated in
      if a = a_reconst then
        let a_int = a_maybe_truncated in
        Big_int.(big_int_of_int a_int)
      else
        let m = div a a_reconst in
        let r = rem a a_reconst in
        let open Big_int in
        let bi = big_int_of_int a_maybe_truncated in
        let bi = mult_big_int (to_big_int m) bi in
        add_int_big_int (to_int r) bi
  end

  module Uint8 = Make (Stdint.Uint8)
  module Uint16 = Make (Stdint.Uint16)
  module Uint32 = Make (Stdint.Uint32)
  module Uint64 = Make (Stdint.Uint64)
  module Uint128 = Make (Stdint.Uint128)
end

module LocAux = struct
  open Ocaml_aux
  open Ast

  let is_well_formed_src_pos (path, ln, col) =
    if ln < 1 then
      Error (`IsWellFormedSrcPos ("Invalid line number: " ^ Int.to_string ln))
    else if col < 1 then
      Error
        (`IsWellFormedSrcPos ("Invalid column number: " ^ Int.to_string col))
    else Ok ()

  let is_well_formed_loc0
      ((((spath, sln, scol) as spos), ((epath, eln, ecol) as epos)) : loc0) =
    let* _ = is_well_formed_src_pos spos in
    let* _ = is_well_formed_src_pos epos in
    if spath <> epath then
      Error
        (`IsWellFormedLoc0
          "The start and end positions are not in the same file")
    else if not (sln < eln || (sln = eln && scol <= ecol)) then
      Error (`IsWellFormedLoc0 "The start and end positions are not in order")
    else Ok ()

  let get_last_col_loc (loc : loc) =
    let loc0 = lexed_loc loc in
    let* _ = is_well_formed_loc0 loc0 in
    let _, ((path, ln, col) as epos) = loc0 in
    if col > 1 (*1 based*) then Ok (Lexed ((path, ln, col - 1), epos))
    else Error (`GetLastColLoc "There is no column before end position column")

  let try_compare_src_pos ((path1, ln1, col1) as pos1)
      ((path2, ln2, col2) as pos2) =
    let* _ = is_well_formed_src_pos pos1 in
    let* _ = is_well_formed_src_pos pos2 in
    if path1 <> path2 then
      Error
        (`TryCompareSrcPos "Cannot compare source positions in different files")
    else if ln1 > ln2 then Ok 1
    else if ln1 < ln2 then Ok (-1)
    else if col1 > col2 then Ok 1
    else if col1 < col2 then Ok (-1)
    else Ok 0

  type inc_kind = LeftInRight | RightInLeft

  type overlapping_kind =
    | Partial of { intersection : loc0; union : loc0 }
    | Inclusion of { kind : inc_kind }
    | Eq

  type rel =
    | None
    | Disjoint of { compare : int }
    | Overlapping of { kind : overlapping_kind }

  let rel l1 l2 =
    let* _ = is_well_formed_loc0 l1 in
    let* _ = is_well_formed_loc0 l2 in
    let (((spath1, _, _) as spos1), epos1), (((spath2, _, _) as spos2), epos2) =
      (l1, l2)
    in
    if spath1 <> spath2 then Ok None
    else
      let* cmp_s2_s1 = try_compare_src_pos spos2 spos1 in
      let s2_gt_s1 = cmp_s2_s1 > 0 in
      let* cmp_s2_e1 = try_compare_src_pos spos2 epos1 in
      let s2_lt_e1 = cmp_s2_e1 < 0 in
      let* cmp_e2_s1 = try_compare_src_pos epos2 spos1 in
      let e2_gt_s1 = cmp_e2_s1 > 0 in
      let* cmp_e2_e1 = try_compare_src_pos epos2 epos1 in
      let e2_lt_e1 = cmp_e2_e1 < 0 in
      let s2_eq_s1 = cmp_s2_s1 = 0 in
      let e2_eq_e1 = cmp_e2_e1 = 0 in
      match (s2_gt_s1, s2_lt_e1, e2_gt_s1, e2_lt_e1) with
      | true (*s2>s1*), true (*s2<e1*), true (*e2>s1*), true (*e2<e1*) ->
          Ok (Overlapping { kind = Inclusion { kind = RightInLeft } })
      | true (*s2>s1*), true (*s2<e1*), true (*e2>s1*), false (*e2>=e1*) ->
          Ok
            (Overlapping
               {
                 kind =
                   Partial
                     { intersection = (spos2, epos1); union = (spos1, epos2) };
               })
      | true (*s2>s1*), true (*s2<e1*), false (*e2<=s1*), true (*e2<e1*) ->
          failwith "bug!" (*e2<s2*)
      | true (*s2>s1*), true (*s2<e1*), false (*e2<=s1*), false (*e2>=e1*) ->
          failwith "bug!" (*e2<s2*)
      | true (*s2>s1*), false (*s2>=e1*), true (*e2>s1*), true (*e2<e1*) ->
          failwith "bug!" (*e2<s2*)
      | true (*s2>s1*), false (*s2>=e1*), true (*e2>s1*), false (*e2>=e1*) ->
          Ok (Disjoint { compare = -1 })
      | true (*s2>s1*), false (*s2>=e1*), false (*e2<=s1*), true (*e2<e1*) ->
          failwith "bug!" (*e2<s2*)
      | true (*s2>s1*), false (*s2>=e1*), false (*e2<=s1*), false (*e2>=e1*) ->
          failwith "bug!" (*e2<s2*)
      | false (*s2<=s1*), true (*s2<e1*), true (*e2>s1*), true (*e2<e1*) ->
          Ok
            (Overlapping
               {
                 kind =
                   Partial
                     { intersection = (spos1, epos2); union = (spos2, epos1) };
               })
      | false (*s2<=s1*), true (*s2<e1*), true (*e2>s1*), false (*e2>=e1*) ->
          if s2_eq_s1 && e2_eq_e1 then Ok (Overlapping { kind = Eq })
          else Ok (Overlapping { kind = Inclusion { kind = LeftInRight } })
      | false (*s2<=s1*), true (*s2<e1*), false (*e2<=s1*), true (*e2<e1*) ->
          Ok (Disjoint { compare = 1 })
      | false (*s2<=s1*), true (*s2<e1*), false (*e2<=s1*), false (*e2>=e1*) ->
          Ok (Disjoint { compare = 1 }) (*s1=e1=e2*)
      | false (*s2<=s1*), false (*s2>=e1*), true (*e2>s1*), true (*e2<e1*) ->
          failwith "bug!" (*s1=e1=s2 => no e2*)
      | false (*s2<=s1*), false (*s2>=e1*), true (*e2>s1*), false (*e2>=e1*) ->
          Ok (Disjoint { compare = -1 }) (*s1=e1=s2*)
      | false (*s2<=s1*), false (*s2>=e1*), false (*e2<=s1*), true (*e2<e1*) ->
          failwith "bug!" (*s1=e1=s2 => e2<s2*)
      | false (*s2<=s1*), false (*s2>=e1*), false (*e2<=s1*), false (*e2>=e1*)
        ->
          Ok (Overlapping { kind = Eq })
  (*s1=e1=s2=e2*)

  let try_compare_loc l1 l2 =
    let* rel = rel l1 l2 in
    match rel with
    | Disjoint { compare } -> Ok compare
    | None ->
        Error (`TryCompareLoc "Cannot compare source spans in different files")
    | Overlapping { kind = _ } ->
        Error (`TryCompareLoc "Not strictly ordered locations")

  let compare_err_desc ei =
    match ei with
    | `IsWellFormedLoc0 msg -> "Malformed source span: " ^ msg
    | `IsWellFormedSrcPos msg -> "Malformed source position: " ^ msg
    | `TryCompareLoc msg -> "Failed to compare source spans: " ^ msg
    | `TryCompareSrcPos msg -> "Failed to compare source positions: " ^ msg

  let disjoint_batches get_loc elms =
    let f_aux disj_batches elm =
      let loc_elm = Ast.lexed_loc (get_loc elm) in
      match disj_batches with
      | [] -> Ok [ ([ elm ], loc_elm) ]
      | (batch_elms, loc_batch) :: t_disj_batches -> (
          let* rel = rel loc_elm loc_batch in
          match rel with
          | None -> Error (`DisjointBatches "Elements with unrelated locations")
          | Disjoint _ -> Ok (([ elm ], loc_elm) :: disj_batches)
          | Overlapping { kind } ->
              let loc_batch =
                match kind with
                | Partial d -> d.union
                | Inclusion { kind } -> (
                    match kind with
                    | RightInLeft -> loc_elm
                    | LeftInRight -> loc_batch)
                | Eq -> loc_elm
              in
              Ok ((elm :: batch_elms, loc_batch) :: t_disj_batches))
    in
    let* dbs = ListAux.try_fold_left f_aux [] elms in
    let dbs = List.map (fun (es, l) -> (List.rev es, l)) dbs in
    Ok (List.rev dbs)
end

module Mir = struct
  type mutability = Mut | Not

  type generic_arg = GenArgLifetime | GenArgType of ty_info | GenArgConst

  and ty_info =
    | TyInfoBasic of { vf_ty : Ast.type_expr }
    | TyInfoGeneric of {
        vf_ty : Ast.type_expr;
        substs : generic_arg list;
        vf_ty_mono : Ast.type_expr;
      }

  let basic_type_of (ti : ty_info) =
    match ti with
    | TyInfoBasic { vf_ty } -> vf_ty
    | TyInfoGeneric { vf_ty; substs; vf_ty_mono } -> vf_ty_mono

  let raw_type_of (ti : ty_info) =
    match ti with TyInfoBasic { vf_ty } | TyInfoGeneric { vf_ty; _ } -> vf_ty

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

  type var_debug_info_internal = VdiiPlace of { id : string } | VdiiConstant

  type var_debug_info = {
    internal : var_debug_info_internal;
    surf_name : string;
  }

  type debug_info = { id : Ast.loc; info : var_debug_info list }
  type visibility = Public | Restricted | Invisible
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
          Some
            ((*base_spec list*) [], (*field list*) [], (*is polymorphic*) false),
          (*attr list*) [] )
end

module TrTyInt = struct
  let calc_int_width (bits : int) =
    let n = Float.log2 @@ float_of_int @@ bits in
    let n_is_int = FP_zero == Float.classify_float @@ fst @@ Float.modf @@ n in
    if not (bits > 0 && n_is_int && int_of_float n >= 3) then
      Error
        (`CalcIntWidth
          "The number of bits of an integer should be non-negative and equal \
           to 2^n such that n>=3")
    else
      let bytes = bits / 8 in
      let width = int_of_float @@ Float.log2 @@ float_of_int @@ bytes in
      Ok width
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
    let open Str in
    let r = regexp {|::|} in
    global_replace r "_" dp

  let make_tmp_var_name base_name = tag_internal "temp_var_" ^ base_name
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

    let uint128_get (ui_cpn : UInt128Rd.t) : Uint128.t =
      let open UInt128Rd in
      let open Uint128 in
      let h = h_get ui_cpn in
      let l = l_get ui_cpn in
      let r = of_uint64 h in
      let r = shift_left r 8 in
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

  module AstDecls = Decls (struct
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
          Parser.parse_header_file Args.report_macro_call header_path
            Args.report_range Args.report_should_fail Args.verbosity
            (*include paths*) [] (*define macros*) []
            (*enforce annotation*) true Args.data_model_opt
        in
        let header_names = List.map (fun (_, (_, _, h), _, _) -> h) headers in
        let headers =
          ( Ast.dummy_loc,
            (Lexer.AngleBracketInclude, header_name, header_path),
            header_names,
            decls )
          :: headers
        in
        Ok headers
    end
  end

  module VF0 = Verifast0

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

  let translate_annot_to_vf_parser_inp ({ span; raw } : Mir.annot) =
    let spos, epos = Ast.lexed_loc span in
    (spos, raw)

  let translate_contract (contract_cpn : ContractRd.t) =
    let annots_cpn = ContractRd.annotations_get_list contract_cpn in
    let* annots = ListAux.try_map translate_annotation annots_cpn in
    let annots = List.map translate_annot_to_vf_parser_inp annots in
    Ok (VfMirAnnotParser.parse_func_contract annots)
  (* Todo: VeriFast parser throws exceptions. we should catch them and use our own error handling scheme *)

  let translate_ghost_stmt (gs_cpn : AnnotationRd.t) =
    let open AnnotationRd in
    let* gs = translate_annotation gs_cpn in
    let gs = translate_annot_to_vf_parser_inp gs in
    Ok (VfMirAnnotParser.parse_ghost_stmt gs)

  let translate_ghost_decl_batch (gh_decl_batch_cpn : AnnotationRd.t) =
    let* gh_decl_b = translate_annotation gh_decl_batch_cpn in
    let gh_decl_b = translate_annot_to_vf_parser_inp gh_decl_b in
    Ok (VfMirAnnotParser.parse_ghost_decl_batch gh_decl_b)

  let translate_mutability (mutability_cpn : MutabilityRd.t) =
    match MutabilityRd.get mutability_cpn with
    | Mut -> Ok Mir.Mut
    | Not -> Ok Mir.Not
    | Undefined _ ->
        Error (`TrMutability "Unknown Mir mutability discriminator")

  let translate_symbol (sym_cpn : SymbolRd.t) = SymbolRd.name_get sym_cpn
  let int_size_rank = Ast.PtrRank

  let translate_u_int_ty (u_int_ty_cpn : UIntTyRd.t) (loc : Ast.loc) =
    let calc_rank ui =
      let* bits = Mir.u_int_ty_bits_len ui in
      let* width = TrTyInt.calc_int_width bits in
      Ok (Ast.FixedWidthRank width)
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

  let translate_adt_def_id (adt_def_id_cpn : AdtDefIdRd.t) =
    AdtDefIdRd.name_get adt_def_id_cpn

  let translate_adt_ty (adt_ty_cpn : AdtTyRd.t) (loc : Ast.loc) =
    let open AdtTyRd in
    let id_cpn = id_get adt_ty_cpn in
    let def_path = translate_adt_def_id id_cpn in
    let name = TrName.translate_def_path def_path in
    let kind_cpn = kind_get adt_ty_cpn in
    let kind = AdtKindRd.get kind_cpn in
    let substs_cpn = substs_get_list adt_ty_cpn in
    match kind with
    | StructKind -> (
        match def_path with
        | "std::alloc::Layout" ->
            if not @@ ListAux.is_empty @@ substs_cpn then
              Error
                (`TrAdtTy (def_path ^ " does not have any generic parameter"))
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
        | _ ->
            let ty_info =
              Mir.TyInfoBasic
                { vf_ty = Ast.ManifestTypeExpr (loc, Ast.StructType name) }
            in
            Ok ty_info)
    | EnumKind -> failwith "Todo: AdtTy::Enum"
    | UnionKind -> failwith "Todo: AdtTy::Union"
    | Undefined _ -> Error (`TrAdtTy "Unknown ADT kind")

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
    let id_mono_cpn = id_mono_get fn_def_ty_cpn in
    match OptionRd.get id_mono_cpn with
    | Nothing ->
        if not (ListAux.is_empty substs_cpn) then
          Error (`TrFnDefTy "Simple function type with generic arg(s)")
        else Ok (Mir.TyInfoBasic { vf_ty })
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
          Ok (Mir.TyInfoGeneric { vf_ty; substs; vf_ty_mono })

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

  and translate_ref_ty (ref_ty_cpn : RefTyRd.t) (loc : Ast.loc) =
    let open RefTyRd in
    let region_cpn = region_get ref_ty_cpn in
    let mut_cpn = mutability_get ref_ty_cpn in
    let ty_cpn = ty_get ref_ty_cpn in
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
    | Ref ref_ty_cpn -> translate_ref_ty ref_ty_cpn loc
    | FnDef fn_def_ty_cpn -> translate_fn_def_ty fn_def_ty_cpn loc
    | Never ->
        Ok
          (Mir.TyInfoBasic
             { vf_ty = Ast.ManifestTypeExpr (loc, Ast.UnionType "std_empty_") })
    | Tuple substs_cpn ->
        let substs_cpn = Capnp.Array.to_list substs_cpn in
        translate_tuple_ty substs_cpn loc
    | Undefined _ -> Error (`TrTy "Unknown Rust type kind")

  type var_id_trs_entry = { id : string; internal_name : string }
  type var_id_trs_map = var_id_trs_entry list

  module TrBody (Args : sig
    val var_id_trs_map_ref : var_id_trs_map ref
    val ghost_stmts : Ast.stmt list
    val body_imp_loc : Ast.loc
  end) =
  struct
    module State = struct
      let var_id_trs_map_ref = Args.var_id_trs_map_ref
      let ghost_stmts = ref Args.ghost_stmts
      let body_imp_loc = Args.body_imp_loc

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
              ty,
              id,
              None,
              ( (* indicates whether address is taken *) ref false,
                (* pointer to enclosing block's list of variables whose address is taken *)
                ref None ) );
          ] )

    let translate_place_element (loc : Ast.loc) (e : Ast.expr)
        (place_elm : PlaceElementRd.t) =
      let open PlaceElementRd in
      match get place_elm with
      | Deref -> Ok (Ast.Deref (loc, e))
      | Field field_data_cpn ->
          let open FieldData in
          let name_cpn = name_get field_data_cpn in
          let name = translate_symbol name_cpn in
          Ok (Ast.Select (loc, e, name))
      | Undefined _ ->
          Error (`TrPlaceElement "Unknown place element projection")

    let translate_place (place_cpn : PlaceRd.t) (loc : Ast.loc) =
      let open PlaceRd in
      let id_cpn = local_get place_cpn in
      let id = translate_local_decl_id id_cpn in
      let projection_cpn = projection_get_list place_cpn in
      ListAux.try_fold_left
        (translate_place_element loc)
        (Ast.Var (loc, id))
        projection_cpn

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
      | Bool b -> failwith "Todo: Scalar::Bool"
      | Char str -> failwith "Todo: Scalar::Char"
      | Int int_cpn -> failwith "Todo: Scalar::Int"
      | Uint u_int_cpn -> translate_scalar_u_int u_int_cpn ty loc
      | Float float_cpn -> failwith "Todo: Scalar::Float"
      | FnDef -> failwith "Todo: Scalar::FnDef"
      | Undefined _ -> Error (`TrScalar "Unknown Scalar kind")

    let translate_const_value (cv_cpn : ConstValueRd.t) (ty : Ast.type_expr)
        (loc : Ast.loc) =
      let open ConstValueRd in
      match get cv_cpn with
      | Scalar scalar_cpn -> translate_scalar scalar_cpn ty loc
      | Slice -> failwith "Todo: ConstValue::Slice"
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
      | Ast.Int (Ast.Unsigned, _) ->
          let val_cpn = val_get ty_const_cpn in
          let* const_expr = translate_ty_const_kind val_cpn ty_expr loc in
          Ok (`TrTypedConstantScalar const_expr)
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
      | Copy place_cpn ->
          let* place = translate_place place_cpn loc in
          Ok (`TrOperandCopy place)
      | Move place_cpn ->
          let* place = translate_place place_cpn loc in
          Ok (`TrOperandMove place)
      | Constant constant_cpn -> translate_constant constant_cpn
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

    let translate_fn_call_rexpr (callee_ty_info : Mir.ty_info)
        (args_cpn : OperandRd.t list) (call_loc : Ast.loc) (fn_loc : Ast.loc) =
      match callee_ty_info with
      | Mir.TyInfoBasic
          { vf_ty = Ast.ManifestTypeExpr ((*loc*) _, Ast.FuncType fn_name) } ->
          (* Todo @Nima: There should be a way to get separated source spans for args *)
          let args = List.map (fun arg_cpn -> (arg_cpn, fn_loc)) args_cpn in
          let* tmp_rvalue_binders, args = translate_operands args in
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
          Ok (tmp_rvalue_binders, call_expr)
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
          | "std_alloc_Layout_new" -> (
              if not (ListAux.is_empty args_cpn) then
                Error
                  (`TrFnCallRExpr
                    "Invalid number of arguments for std::alloc::Layout::new")
              else
                match substs with
                | [ Mir.GenArgType ty_info ] ->
                    let ty_expr = Mir.basic_type_of ty_info in
                    Ok
                      ( (*tmp_rvalue_binders*) [],
                        Ast.SizeofExpr (call_loc, Ast.TypeExpr ty_expr) )
                | _ ->
                    Error
                      (`TrFnCallRExpr
                        "Invalid generic argument(s) for \
                         std::alloc::Layout::new"))
          | "std_ptr_mut_ptr_<impl *mut T>_is_null" -> (
              match (substs, args_cpn) with
              | [ Mir.GenArgType gen_arg_ty_info ], [ arg_cpn ] ->
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
                      "Invalid (generic) arg(s) for std::ptr::mut_ptr::<impl \
                       *mut T>::is_null"))
          | _ ->
              failwith
                ("Todo: Generic functions are not supported yet. Function: "
               ^ fn_name))
      | _ ->
          Error (`TrFnCallRExpr "Invalid function definition type translation")

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
      let* call_stmt, next_bblock_stmt_op =
        match OptionRd.get destination_cpn with
        | Nothing -> (*Diverging call*) Ok (Ast.ExprStmt fn_call_rexpr, None)
        | Something ptr_cpn ->
            let destination_data_cpn = VfMirStub.Reader.of_pointer ptr_cpn in
            let* { Mir.dst; Mir.dst_bblock_id } =
              translate_destination_data destination_data_cpn loc
            in
            Ok
              ( Ast.ExprStmt (Ast.AssignExpr (loc, dst, fn_call_rexpr)),
                Some (Ast.GotoStmt (loc, dst_bblock_id)) )
        | Undefined _ -> Error (`TrFnCall "Unknown Option kind")
      in
      let full_call_stmt =
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
      | None -> Ok [ full_call_stmt ]
      | Some next_bblock_stmt -> Ok [ full_call_stmt; next_bblock_stmt ]

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
      let* main_stmt =
        match Mir.basic_type_of discr_ty with
        | Ast.ManifestTypeExpr ((*loc*) _, Ast.Bool) -> (
            match (branches, otherwise_op) with
            | [ (v, false_tgt) ], Some true_tgt when Stdint.Uint128.(zero = v)
              ->
                Ok
                  (Ast.IfStmt
                     ( loc,
                       discr,
                       [ Ast.GotoStmt (loc, true_tgt) ],
                       [ Ast.GotoStmt (loc, false_tgt) ] ))
            | _ ->
                Error
                  (`TrSwInt "Invalid SwitchTargets for a boolean discriminant"))
        | _ -> failwith "Todo: SwitchInt TerminatorKind"
      in
      if ListAux.is_empty tmp_rvalue_binders then Ok main_stmt
      else
        Ok
          (Ast.BlockStmt
             ( loc,
               (*decl list*) [],
               tmp_rvalue_binders @ [ main_stmt ],
               loc,
               ref [] ))

    let translate_terminator_kind (ret_place_id : string)
        (tkind_cpn : TerminatorKindRd.t) (loc : Ast.loc) =
      let open TerminatorKindRd in
      match get tkind_cpn with
      | Goto bblock_id_cpn ->
          let bb_id = translate_basic_block_id bblock_id_cpn in
          Ok [ Ast.GotoStmt (loc, bb_id) ]
      | SwitchInt sw_int_data_cpn ->
          let* sw_stmt = translate_sw_int sw_int_data_cpn loc in
          Ok [ sw_stmt ]
      | Resume -> failwith "Todo: Terminatorkind::Resume"
      | Return ->
          Ok [ Ast.ReturnStmt (loc, Some (Ast.Var (loc, ret_place_id))) ]
      | Call fn_call_data_cpn -> translate_fn_call fn_call_data_cpn loc
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
          let cast_kind_cpn = cast_kind_get cast_data_cpn in
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
          | `TrTypedConstantFn _ ->
              Error (`TrRvalue "Invalid operand translation for Rvalue::Cast"))
      | BinaryOp bin_op_data_cpn ->
          let* operator, operandl, operandr =
            translate_binary_operation bin_op_data_cpn loc
          in
          let* operandl = tr_operand operandl in
          let* operandr = tr_operand operandr in
          Ok (`TrRvalueBinaryOp (operator, operandl, operandr))
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
                  Ok [ block_stmt ]))
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
        ({ id; statements = stmts; terminator = trm } : Mir.basic_block) =
      if ListAux.is_empty trm then
        Error (`TrToVfBBlock "Basic block without any terminator")
      else
        let embed_ghost_stmts all_stmts stmt =
          let loc_stmt = stmt |> Ast.stmt_loc |> Ast.lexed_loc in
          let* ghost_stmts = State.fetch_ghost_stmts_before loc_stmt in
          Ok (all_stmts @ ghost_stmts @ [ stmt ])
        in
        let stmts = stmts @ trm in
        let* stmts = ListAux.try_fold_left embed_ghost_stmts [] stmts in
        let loc = stmts |> List.hd |> Ast.stmt_loc in
        Ok (Ast.LabelStmt (loc, id) :: stmts)

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

  (** makes the mappings used for substituting the MIR level local declaration ids with names closer to variables surface name *)
  let make_var_id_name_maps (vdis : Mir.var_debug_info list) =
    let make_var_id_name_entries surf_names_set id surf_name =
      match List.find_opt (fun (n, _) -> n = surf_name) surf_names_set with
      | None ->
          let surf_names_set = (surf_name, ref 0) :: surf_names_set in
          let env_entry_opt : VF0.var_debug_info option = None in
          let trs_entry : var_id_trs_entry =
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
          failwith "Todo: Shadowed variable names";
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
    ( List.rev
        env_map (* This will be used during the pprinting of execution states *),
      List.rev
        trs_map (* This will be used during the translation of variable names *)
    )

  let translate_body (body_cpn : BodyRd.t) =
    let open BodyRd in
    let var_id_trs_map_ref = ref [] in
    let ghost_stmts_cpn = ghost_stmts_get_list body_cpn in
    let* ghost_stmts = ListAux.try_map translate_ghost_stmt ghost_stmts_cpn in
    let* ghost_stmts =
      ListAux.try_sort LocAux.compare_err_desc
        (fun s1 s2 ->
          let l1, l2 =
            (fun f -> (f s1, f s2)) @@ fun s ->
            s |> Ast.stmt_loc |> Ast.lexed_loc
          in
          LocAux.try_compare_loc l1 l2)
        ghost_stmts
    in
    let imp_span_cpn = imp_span_get body_cpn in
    let* imp_loc = translate_span_data imp_span_cpn in
    let open TrBody (struct
      let var_id_trs_map_ref = var_id_trs_map_ref
      let ghost_stmts = ghost_stmts
      let body_imp_loc = imp_loc
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
        let* closing_cbrace_loc = LocAux.get_last_col_loc loc in
        let body =
          Ast.Func
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
              Some (vf_local_decls @ vf_bblocks, closing_cbrace_loc),
              Ast.Static,
              Ast.Package )
        in
        Ok (body, ({ id = loc; info = env_map } : VF0.debug_info_rust_fe))
    | DefKind.AssocFn -> failwith "Todo: MIR Body kind AssocFn"
    | _ -> Error (`TrBody "Unknown MIR Body kind")

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
    Ok (name, ty_info, vis, loc)

  let translate_to_vf_field_def
      ((name, ty_info, vis, loc) :
        string * Mir.ty_info * Mir.visibility * Ast.loc) =
    Ast.Field
      ( loc,
        Ast.Real (*ghostness*),
        Mir.basic_type_of ty_info,
        name,
        Ast.Instance (*method_binding*),
        (* Currently, the plan is to have all fields Public as they are in C
           and imposing constraints using separation logic *)
        Ast.Public
        (*visibility*),
        true (*final*),
        None (*expr option*) )

  let translate_variant_def (vdef_cpn : VariantDefRd.t) =
    let open VariantDefRd in
    let fields_cpn = fields_get_list vdef_cpn in
    let* fields = ListAux.try_map translate_field_def fields_cpn in
    let fields = List.map translate_to_vf_field_def fields in
    Ok fields

  let translate_adt_def (adt_def_cpn : AdtDefRd.t) =
    let open AdtDefRd in
    let id_cpn = id_get adt_def_cpn in
    let def_path = translate_adt_def_id id_cpn in
    let name = TrName.translate_def_path def_path in
    let variants_cpn = variants_get_list adt_def_cpn in
    let* variants = ListAux.try_map translate_variant_def variants_cpn in
    let span_cpn = span_get adt_def_cpn in
    let* def_loc = translate_span_data span_cpn in
    let kind_cpn = kind_get adt_def_cpn in
    match AdtKindRd.get kind_cpn with
    | StructKind ->
        let* field_defs =
          match variants with
          | [ field_defs ] -> Ok field_defs
          | _ -> Error (`TrAdtDef "Struct ADT kind should have one variant")
        in
        let struct_decl =
          Ast.Struct
            ( def_loc,
              name,
              Some
                ( [] (*base_spec list*),
                  field_defs (*field list*),
                  false (*is polymorphic*) ),
              [] (*struct_attr list*) )
        in
        Ok struct_decl
    | EnumKind -> failwith "Todo: AdtDef::Enum"
    | UnionKind -> failwith "Todo: AdtDef::Union"
    | Undefined _ -> Error (`TrAdtDef "Unknown ADT kind")

  let translate_vf_mir (vf_mir_cpn : VfMirRd.t) =
    let job _ =
      let module HeadersAux = HeadersAux.Make (struct
        include Args

        let aux_headers_dir = Filename.dirname Sys.executable_name
        let verbosity = 0
      end) in
      let adt_defs_cpn = VfMirRd.adt_defs_get vf_mir_cpn in
      let* adt_defs_cpn = CapnpAux.ind_list_get_list adt_defs_cpn in
      let* adt_defs = ListAux.try_map translate_adt_def adt_defs_cpn in
      let ghost_decl_batches_cpn =
        VfMirRd.ghost_decl_batches_get_list vf_mir_cpn
      in
      let* ghost_decl_batches =
        ListAux.try_map translate_ghost_decl_batch ghost_decl_batches_cpn
      in
      let ghost_decls = List.flatten ghost_decl_batches in
      let bodies_cpn = VfMirRd.bodies_get_list vf_mir_cpn in
      let* bodies_and_dbg_infos = ListAux.try_map translate_body bodies_cpn in
      let body_decls, debug_infos = List.split bodies_and_dbg_infos in
      let debug_infos = VF0.DbgInfoRustFe debug_infos in
      let decls = AstDecls.decls () in
      let decls = decls @ adt_defs @ ghost_decls @ body_decls in
      (* Todo @Nima: we should add necessary inclusions during translation *)
      let _ =
        List.iter Headers.add_decl
          [ "rust/std/alloc.h"; "rust/rust_belt/lifetime_logic.gh" ]
      in
      let header_names = Headers.decls () in
      let* headers = ListAux.try_map HeadersAux.parse_header header_names in
      let headers = List.concat headers in
      Ok
        ( headers,
          [ Ast.PackageDecl (Ast.dummy_loc, "", [], decls) ],
          Some debug_infos )
    in
    match job () with
    | Ok res -> res
    | Error err ->
        (print_string "MIR Translator Failed";
         match err with
         | `CalcIntWidth str
         | `CapnpIndListGetList str
         | `DisjointBatches str
         | `GetLastColLoc str
         | `IntAuxAdd str
         | `IsWellFormedLoc0 str
         | `IsWellFormedSrcPos str
         | `Sort str
         | `TrAdtDef str
         | `TrAdtTy str
         | `TrBinOp str
         | `TrBody str
         | `TrConstValue str
         | `TrConstantKind str
         | `TrFileName str
         | `TrFnCall str
         | `TrFnCallRExpr str
         | `TrFnDefTy str
         | `TrGenArg str
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
         | `TrVarDebugInfoContents str
         | `TrVisibility str
         | `TryCompareLoc str
         | `TryCompareSrcPos str
         | `UIntTyBitsLen str ->
             print_endline (": " ^ str)
         | `IntAuxToInt -> ());
        failwith "Todo: translate_vf_mir Error handling"
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
