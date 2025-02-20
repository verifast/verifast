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
        Some (loc, name, fun name -> Inductive (loc, name, tparams, ctors))
    | Struct (loc, name, tparams, definition_opt, attrs) ->
        Some
          ( loc,
            name,
            fun new_name ->
              Struct (loc, new_name, tparams, definition_opt, attrs) )
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
                (l, g, tparams, nbIndices, pts, inputParamCount, inductiveness)
          )
    | PredFamilyInstanceDecl (l, g, tparams, indices, ps, body) ->
        Some
          ( l,
            g,
            fun g -> PredFamilyInstanceDecl (l, g, tparams, indices, ps, body)
          )
    | PredCtorDecl (l, g, tparams, ctor_ps, ps, inputParamCount, body) ->
        Some
          ( l,
            g,
            fun g ->
              PredCtorDecl (l, g, tparams, ctor_ps, ps, inputParamCount, body)
          )
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

  let sort_decls_lexically ds =
    List.sort
      (fun d d1 ->
        compare
          (Ast.lexed_loc @@ decl_loc @@ snd d)
          (Ast.lexed_loc @@ decl_loc @@ snd d1))
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

  type generic_arg =
    | GenArgLifetime of string
    | GenArgType of ty_info
    | GenArgConst

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
    ty : ty_info Lazy.t;
    loc : Ast.loc;
  }

  type source_info = { span : Ast.loc; scope : unit }

  type terminator =
    | GotoTerminator of Ast.loc * string
    | EncodedTerminator (* The terminator is encoded into the statements *)

  type bb_walk_state = NotSeen | Walking of int * basic_block list | Exhausted

  and basic_block = {
    id : string;
    statements : Ast.stmt list;
    terminator_stmts : Ast.stmt list;
    terminator : terminator;
    successors : string list;
    mutable external_predecessor_count : int;
        (* Number of non-descendant predecessors (i.e. that jump to the start of the loop) *)
    mutable internal_predecessor_count : int;
        (* Number of descendant predecessors (i.e. that jump to the end of the loop body) *)
    mutable walk_state : bb_walk_state;
    mutable is_block_head : bool;
    mutable parent : basic_block option;
        (* If this BB is inside a block (i.e. not the head), points to the innermost containing block's block head *)
    mutable children : basic_block list;
  }

  type fn_call_dst_data = {
    dst : Ast.expr * bool (* place is mutable *);
    dst_bblock_id : string;
  }

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
  type visibility = Public | Restricted
  type adt_kind = Struct | Enum | Union

  let decl_mir_adt_kind (d : Ast.decl) =
    match d with
    | Ast.Struct _ -> Ok Struct
    | Ast.Inductive _ -> Ok Enum
    | Ast.Union _ -> failwith "Todo: Unsupported ADT"
    | _ -> failwith "decl_mir_adt_kind: Not an ADT"

  type aggregate_kind =
    | AggKindArray of ty_info
    | AggKindAdt of {
        adt_kind : adt_kind;
        adt_name : string;
        variant_name : string;
        field_names : string list;
      }
    | AggKindTuple

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
    lft_params : string list;
    fds : field_def_tr list;
    def : Ast.decl;
    aux_decls : Ast.decl list;
    full_bor_content : Ast.decl option;
    proof_obligs : Ast.decl list;
    delayed_proof_obligs : (adt_def_tr list -> Ast.decl) list;
  }
end

module TrTyTuple = struct
  let tuple0_name = "std_tuple_0_"
  let make_tuple_type_name arity = Printf.sprintf "std_tuple_%d_" arity
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

  let lft_name_without_apostrophe n =
    if String.starts_with ~prefix:"'" n then String.sub n 1 (String.length n - 1)
    else
      failwith
        ("Encountered a lifetime name that does not start with an apostrophe: "
       ^ n)

  let is_from_std_lib path = String.starts_with ~prefix:"std::" path

  let split_def_path mod_path def_path =
    let open String in
    let rel_def_path =
      (* e.g. mod_path = "ptr" && def_path = "ptr::NonNull::<T>::as_ptr" *)
      if starts_with ~prefix:(mod_path ^ "::") def_path then
        sub def_path
          (length mod_path + 2)
          (length def_path - length mod_path - 2)
      else
        (*
        - Empty module path => crate root
          - e.g. mod_path = "" && def_path = "foo"
          - e.g. mod_path = "" && def_path = "<impl std::clone::Clone for ptr::NonNull<T>>::clone"
        - The module path does not apear at the start of the path for trait implementations inside the module:
          - e.g. mod_path = "ptr" && def_path = "<ptr::NonNull<T> as std::clone::Clone>::clone"
        *)
        def_path
    in
    (mod_path, rel_def_path)
end

let split_item_name n =
  match String.rindex_opt n ':' with
  | None -> ("", n)
  | Some i ->
      let pac = String.sub n 0 (i - 1) in
      let item = String.sub n (i + 1) (String.length n - i - 1) in
      (pac, item)

let qualified_derived_name format name =
  let package, name = split_item_name name in
  if package = "" then Printf.sprintf format name
  else package ^ "::" ^ Printf.sprintf format name

let padding_pred_name sn = qualified_derived_name "struct_%s_padding" sn

module type VF_MIR_TRANSLATOR_ARGS = sig
  val data_model_opt : Ast.data_model option
  val report_should_fail : string -> Ast.loc0 -> unit
  val report_range : Lexer.range_kind -> Ast.loc0 -> unit
  val report_macro_call : Ast.loc0 -> Ast.loc0 -> unit
  val verbose_flags : string list
  val skip_specless_fns : bool
  val allow_ignore_ref_creation : bool
  val ignore_ref_creation : bool
  val ignore_unwind_paths : bool
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

  let prelude_path =
    Filename.concat (Filename.dirname Sys.executable_name) "rust/prelude.rsspec"

  let parse_prelude () =
    let prelude_name = Filename.basename prelude_path in
    let decls =
      let ds = VfMirAnnotParser.parse_rsspec_file prelude_path in
      let pos = (prelude_path, 1, 1) in
      let loc = Ast.Lexed (pos, pos) in
      [ Ast.PackageDecl (loc, "", [], ds) ]
    in
    let header =
      ( Ast.dummy_loc,
        (Lexer.AngleBracketInclude, prelude_name, prelude_path),
        [],
        decls )
    in
    [ header ]

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
      Rust_parser.flatten_module_decls loc []
        [ Ast.ModuleDecl (loc, crateName, [], ds) ]
    in
    let header =
      ( Ast.dummy_loc,
        (Lexer.AngleBracketInclude, header_name, header_path),
        [ prelude_path ],
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
        Ok (Some (VfMirAnnotParser.parse_func_contract loc annots))
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
    Ok (VfMirAnnotParser.parse_ghost_use_decl_or_decl_batch gh_decl_b)

  let translate_ghost_decl_block (gdb_cpn : BodyRd.GhostDeclBlock.t) =
    let open BodyRd.GhostDeclBlock in
    let open AnnotationRd in
    let* gh_decl_b = translate_annotation (start_get gdb_cpn) in
    let gh_decl_b_parser_input = translate_annot_to_vf_parser_inp gh_decl_b in
    let ghost_decls =
      VfMirAnnotParser.parse_ghost_decl_batch gh_decl_b_parser_input
    in
    let ghost_decls =
      if Args.ignore_unwind_paths then
        List.map Rust_parser.result_decl_of_outcome_decl ghost_decls
      else ghost_decls
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

  let vf_ty_arg_of_region loc (reg : string) =
    match reg with
    | "'static" | "'<erased>" -> Ast.ManifestTypeExpr (loc, StaticLifetime)
    | x -> Ast.IdentTypeExpr (loc, None, x)

  let translate_region_expr loc (reg_cpn : RegionRd.t) =
    vf_ty_arg_of_region loc (RegionRd.id_get reg_cpn)

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
    let fbc_name = ty_name ^ "_full_borrow_content" in
    let full_bor_content = RustBelt.simple_fbc loc fbc_name in
    let points_to tid l vid_op =
      (* Todo: The size and bounds of the integer that this assertion is specifying will depend on the pointer `l` type
         which is error-prone. It is helpful if we add a sanity-check or use elevated `integer_(...)` predicates with bound infos *)
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, RegularPointsTo, pat))
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
                shr = simple_shr loc fbc_name;
                full_bor_content;
                points_to;
                pointee_fbc = None;
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
    let fbc_name = ty_name ^ "_full_borrow_content" in
    let full_bor_content = RustBelt.simple_fbc loc fbc_name in
    let points_to tid l vid_op =
      (* Todo: The size and bounds of the integer that this assertion is specifying will depend on the pointer `l` type
         which is error-prone. It is helpful if we add a sanity-check or use elevated `integer_(...)` predicates with bound infos *)
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, RegularPointsTo, pat))
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
                shr = simple_shr loc fbc_name;
                full_bor_content;
                points_to;
                pointee_fbc = None;
              };
        }
    in
    Ok ty_info

  let translate_scalar_int (scalar_int_cpn : TyRd.ScalarInt.t)
      (ty : Ast.type_expr) (loc : Ast.loc) =
    let open TyRd.ScalarInt in
    let value =
      IntAux.Uint128.to_big_int (CapnpAux.uint128_get (data_get scalar_int_cpn))
    in
    let mk_const v =
      let open Ast in
      let lit =
        IntLit (loc, v, (*decimal*) true, (*U suffix*) false, LLSuffix)
      in
      Ok (CastExpr (loc, ty, lit))
    in
    let mk_signed_const width =
      let v =
        if Big_int.sign_big_int value >= 0 then value
        else
          Big_int.sub_big_int value
            (Big_int.shift_left_big_int Big_int.unit_big_int (8 * width))
      in
      mk_const v
    in
    match (ty, size_get scalar_int_cpn) with
    | ManifestTypeExpr (_, Bool), _ ->
        Ok
          (if Big_int.sign_big_int value <> 0 then Ast.True loc
           else Ast.False loc)
    | ManifestTypeExpr (_, RustChar), 4 ->
        let open Ast in
        Ok
          (CastExpr
             ( loc,
               ManifestTypeExpr (loc, RustChar),
               IntLit (loc, value, true, true, LLSuffix) ))
    | ManifestTypeExpr (_, Ast.Int (Signed, _)), size -> mk_signed_const size
    | ManifestTypeExpr (_, Ast.Int (Unsigned, _)), size -> mk_const value

  let canonicalize_item_name (name : string) =
    if String.starts_with ~prefix:"core::" name then
      "std::" ^ String.sub name 6 (String.length name - 6)
    else name

  let translate_adt_def_id (adt_def_id_cpn : AdtDefIdRd.t) =
    canonicalize_item_name @@ AdtDefIdRd.name_get adt_def_id_cpn

  let rec translate_adt_ty (adt_ty_cpn : AdtTyRd.t) (loc : Ast.loc) =
    let open AdtTyRd in
    let open Ast in
    let def_path = translate_adt_def_id @@ id_get @@ adt_ty_cpn in
    let name = TrName.translate_def_path def_path in
    let kind = AdtKindRd.get @@ kind_get @@ adt_ty_cpn in
    let substs_cpn = substs_get_list adt_ty_cpn in
    match kind with
    | StructKind | UnionKind -> (
        match def_path with
        | "std::cell::UnsafeCell" | "std::mem::ManuallyDrop" ->
            let [ arg_cpn ] = substs_cpn in
            let* (Mir.GenArgType arg_ty) = translate_generic_arg arg_cpn loc in
            Ok arg_ty
        | _ ->
            let* gen_args =
              ListAux.try_map
                (fun gen_arg_cpn -> translate_generic_arg gen_arg_cpn loc)
                substs_cpn
            in
            let targs =
              gen_args
              |> Util.flatmap @@ function
                 | Mir.GenArgType arg_ty -> [ Mir.basic_type_of arg_ty ]
                 | _ -> []
            in
            let lft_args =
              gen_args
              |> Util.flatmap @@ function
                 | Mir.GenArgLifetime name -> [ vf_ty_arg_of_region loc name ]
                 | _ -> []
            in
            let vf_targs = lft_args @ targs in
            let vf_ty = StructTypeExpr (loc, Some name, None, [], vf_targs) in
            let sz_expr = SizeofExpr (loc, TypeExpr vf_ty) in
            let own tid v =
              let args = List.map (fun x -> LitPat x) [ tid; v ] in
              Ok
                (CallExpr
                   ( loc,
                     name ^ "_own",
                     (*type arguments*) vf_targs,
                     (*indices*) [],
                     args,
                     if vf_targs = [] then PredFamCall else PredCtorCall ))
            in
            let shr lft tid l =
              Ok
                (CoefAsn
                   ( loc,
                     DummyPat,
                     CallExpr
                       ( loc,
                         name ^ "_share",
                         (*type arguments*) vf_targs,
                         (*indices*) [],
                         (*arguments*)
                         List.map (fun e -> LitPat e) [ lft; tid; l ],
                         if vf_targs = [] then PredFamCall else PredCtorCall )
                   ))
            in
            let full_bor_content =
              if lft_args = [] then
                RustBelt.simple_fbc loc (name ^ "_full_borrow_content")
              else fun tid l ->
                Ok
                  (CallExpr
                     ( loc,
                       name ^ "_full_borrow_content",
                       lft_args @ targs,
                       [],
                       List.map (fun e -> LitPat e) [ tid; l ],
                       Static ))
            in
            let points_to tid l vid_op =
              let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
              Ok (PointsTo (loc, l, RegularPointsTo, pat))
            in
            let interp =
              RustBelt.
                {
                  size = sz_expr;
                  own;
                  shr;
                  full_bor_content;
                  points_to;
                  pointee_fbc = None;
                }
            in
            let ty_info =
              Mir.TyInfoGeneric
                { vf_ty; interp; substs = gen_args; vf_ty_mono = vf_ty }
            in
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
             | Mir.GenArgLifetime _ ->
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
        let own tid v =
          Ok
            (ExprCallExpr
               (loc, TypePredExpr (loc, vf_ty, "own"), [ LitPat tid; LitPat v ]))
        in
        let shr lft tid l =
          Error
            "Expressing shared ownership of an enum value is not yet supported"
        in
        let full_bor_content tid l =
          Error
            "Expressing the full borrow content of an enum value is not yet \
             supported"
        in
        (* Todo: Nested structs *)
        let points_to tid l vid_op =
          let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
          Ok (PointsTo (loc, l, RegularPointsTo, pat))
        in
        let interp =
          RustBelt.
            {
              size = sz_expr;
              own;
              shr;
              full_bor_content;
              points_to;
              pointee_fbc = None;
            }
        in
        let ty_info = Mir.TyInfoBasic { vf_ty; interp } in
        Ok ty_info
    | Undefined _ -> Error (`TrAdtTy "Unknown ADT kind")

  and translate_tuple_ty (tys_cpn : TyRd.t list) (loc : Ast.loc) =
    let open Ast in
    let* tys =
      ListAux.try_map (fun ty_cpn -> translate_ty ty_cpn loc) tys_cpn
    in
    let name = TrTyTuple.make_tuple_type_name (List.length tys) in
    let tys = List.map Mir.basic_type_of tys in
    let vf_ty =
      if tys = [] then ManifestTypeExpr (loc, StructType (name, []))
      else StructTypeExpr (loc, Some name, None, [], tys)
    in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own t v =
      if tys = [] then Ok (True loc)
      else
        Ok
          (CallExpr (loc, name ^ "_own", tys, [], [ LitPat t; LitPat v ], Static))
    in
    let fbc_name = name ^ "_full_borrow_content" in
    let full_bor_content = RustBelt.simple_fbc loc fbc_name in
    let shr lft tid l =
      Ok
        (CallExpr
           ( loc,
             name ^ "_share",
             tys,
             [],
             [ LitPat lft; LitPat tid; LitPat l ],
             Static ))
    in
    let points_to tid l vid_op =
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, RegularPointsTo, pat))
    in
    let ty_info =
      Mir.TyInfoBasic
        {
          vf_ty;
          interp =
            RustBelt.
              {
                size;
                own;
                shr;
                full_bor_content;
                points_to;
                pointee_fbc = None;
              };
        }
    in
    Ok ty_info

  and bool_ty_info loc =
    let open Ast in
    let vf_ty = ManifestTypeExpr (loc, Bool) in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own _ _ = Ok (True loc) in
    let fbc_name = "bool_full_borrow_content" in
    let full_bor_content = RustBelt.simple_fbc loc fbc_name in
    let points_to tid l vid_op =
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, RegularPointsTo, pat))
    in
    Mir.TyInfoBasic
      {
        vf_ty;
        interp =
          RustBelt.
            {
              size;
              own;
              shr = simple_shr loc fbc_name;
              full_bor_content;
              points_to;
              pointee_fbc = None;
            };
      }

  and char_ty_info loc =
    let open Ast in
    let vf_ty =
      ManifestTypeExpr (loc, RustChar)
      (* https://doc.rust-lang.org/reference/types/textual.html *)
    in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own tid c =
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
    in
    let shr = Ok (Var (loc, "char_share")) in
    let fbc_name = "char_full_borrow_content" in
    let full_bor_content = RustBelt.simple_fbc loc fbc_name in
    let points_to tid l vid_op =
      match vid_op with
      | Some vid when vid != "" ->
          let var_pat = VarPat (loc, vid) in
          let var_expr = Var (loc, vid) in
          let* own = own tid var_expr in
          Ok (Sep (loc, PointsTo (loc, l, RegularPointsTo, var_pat), own))
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
              shr = simple_shr loc fbc_name;
              full_bor_content;
              points_to;
              pointee_fbc = None;
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
    let shr lft tid l =
      Error
        "Expressing the shared ownership of the never type is not yet supported"
    in
    let full_bor_content tid l =
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
            { size; own; shr; full_bor_content; points_to; pointee_fbc = None };
      }

  and str_ref_ty_info loc lft mut =
    let open Ast in
    if mut <> Mir.Not then
      static_error loc "Mutable string references are not yet supported" None;
    let vf_ty = StructTypeExpr (loc, Some "str_ref", None, [], [ lft ]) in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own tid vs =
      Error "Expressing ownership of &str values is not yet supported"
    in
    let shr lft tid l =
      Error "Expressing shared ownership of &str values is not yet supported"
    in
    let full_bor_content tid l =
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
            { size; own; shr; full_bor_content; points_to; pointee_fbc = None };
      }

  and slice_ref_ty_info loc lft mut elem_ty_info =
    let open Ast in
    if mut <> Mir.Not then
      static_error loc "Mutable slice references are not yet supported" None;
    let vf_ty =
      StructTypeExpr
        ( loc,
          Some "slice_ref",
          None,
          [],
          [ lft; Mir.basic_type_of elem_ty_info ] )
    in
    let size = SizeofExpr (loc, TypeExpr vf_ty) in
    let own tid vs =
      Error "Expressing ownership of &[_] values is not yet supported"
    in
    let shr lft tid l =
      Error "Expressing shared ownership of &[_] values is not yet supported"
    in
    let full_bor_content tid l =
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
            { size; own; shr; full_bor_content; points_to; pointee_fbc = None };
      }

  and translate_generic_arg (gen_arg_cpn : GenArgRd.t) (loc : Ast.loc) =
    let open GenArgRd in
    let kind_cpn = kind_get gen_arg_cpn in
    let open GenArgKindRd in
    match get kind_cpn with
    | Lifetime region_cpn ->
        let region = translate_region region_cpn in
        Ok (Mir.GenArgLifetime region)
    | Type ty_cpn ->
        let* ty_info = translate_ty ty_cpn loc in
        Ok (Mir.GenArgType ty_info)
    | Const _ -> Ok Mir.GenArgConst
    | Undefined _ -> Error (`TrGenArg "Unknown generic arg. kind")

  and decode_generic_param (gen_param_cpn : VfMirStub.Reader.GenericParamDef.t)
      =
    let open VfMirStub.Reader.GenericParamDef in
    let open VfMirStub.Reader.GenericParamDefKind in
    let name = name_get gen_param_cpn in
    match get (kind_get gen_param_cpn) with
    | Type -> `Type name
    | Lifetime -> `Lifetime name
    | Const -> failwith "Const generic parameters are not yet supported"

  and decode_generic_arg (gen_arg_cpn : GenArgRd.t) =
    let open GenArgRd in
    let kind_cpn = kind_get gen_arg_cpn in
    let open GenArgKindRd in
    match get kind_cpn with
    | Lifetime region -> `Lifetime (translate_region region)
    | Type ty_cpn -> `Type (decode_ty ty_cpn)
    | Const _ -> `Const

  and string_of_generic_arg arg =
    match arg with
    | `Lifetime r -> r
    | `Type ty -> string_of_decoded_type ty
    | `Const -> "(const)"
    | _ -> "(unknown)"

  and extract_implicit_outlives_preds_from_generic_arg regions arg =
    match arg with
    | `Lifetime region -> List.map (fun r -> (region, r)) regions
    | `Type ty -> extract_implicit_outlives_preds regions ty
    | _ -> []

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
    let late_bound_generic_param_count =
      late_bound_generic_param_count_get fn_def_ty_cpn
    in
    let substs_cpn = substs_get_list fn_def_ty_cpn in
    let* substs =
      ListAux.try_map
        (fun subst_cpn -> translate_generic_arg subst_cpn loc)
        substs_cpn
    in
    let substs =
      substs
      @ List.init late_bound_generic_param_count (fun i ->
            Mir.GenArgLifetime "'erased")
    in
    let vf_ty =
      Ast.ManifestTypeExpr
        (loc, Ast.FuncType (translate_fn_name name substs_cpn))
    in
    let id_mono_cpn = id_mono_get fn_def_ty_cpn in
    match OptionRd.get id_mono_cpn with
    | Nothing ->
        if not (ListAux.is_empty substs) then
          Error (`TrFnDefTy "Simple function type with generic arg(s)")
        else Ok (Mir.TyInfoBasic { vf_ty; interp = RustBelt.emp_ty_interp loc })
    | Something ptr_cpn ->
        if ListAux.is_empty substs then
          Error (`TrFnDefTy "Generic function type without generic arg(s)")
        else
          let id_mono_cpn = VfMirStub.Reader.of_pointer ptr_cpn in
          let id_mono = FnDefIdRd.name_get id_mono_cpn in
          let name_mono = TrName.translate_def_path id_mono in
          let vf_ty_mono = Ast.ManifestTypeExpr (loc, Ast.FuncType name_mono) in
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
    let rt =
      if Args.ignore_unwind_paths then output_ty
      else ConstructedTypeExpr (loc, "fn_outcome", [ output_ty ])
    in
    Ok
      (Mir.TyInfoBasic
         {
           vf_ty = FuncTypeExpr (loc, rt, []);
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
    let fbc_name = "raw_ptr_full_borrow_content" in
    let full_bor_content = RustBelt.simple_fbc loc fbc_name in
    let points_to tid l vid_op =
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (PointsTo (loc, l, RegularPointsTo, pat))
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
                shr = simple_shr loc fbc_name;
                full_bor_content;
                points_to;
                pointee_fbc = None;
              };
        }
    in
    Ok ty_info

  and translate_ref_ty (ref_ty_cpn : RefTyRd.t) (loc : Ast.loc) =
    let open RefTyRd in
    let open Ast in
    let region_cpn = region_get ref_ty_cpn in
    let region = translate_region_expr loc region_cpn in
    let lft = Rust_parser.expr_of_lft_param_expr loc region in
    let mut_cpn = mutability_get ref_ty_cpn in
    let* mut = translate_mutability mut_cpn in
    let ty_cpn = ty_get ref_ty_cpn in
    match TyRd.TyKind.get @@ TyRd.kind_get ty_cpn with
    | Str -> Ok (str_ref_ty_info loc region mut)
    | Slice elem_ty_cpn ->
        let* elem_ty_info = translate_ty elem_ty_cpn loc in
        Ok (slice_ref_ty_info loc region mut elem_ty_info)
    | _ ->
        let* pointee_ty_info = translate_ty ty_cpn loc in
        let pointee_ty = Mir.basic_type_of pointee_ty_info in
        let rust_ref_kind = match mut with Mut -> Mutable | Not -> Shared in
        let vf_ty = RustRefTypeExpr (loc, region, rust_ref_kind, pointee_ty) in
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
        let* own, shr, full_bor_content, points_to, pointee_fbc =
          match mut with
          | Mir.Mut ->
              let own tid l =
                let* ptee_fbc = ptee_fbc tid l in
                Ok
                  (CallExpr
                     ( loc,
                       "full_borrow",
                       (*type arguments*) [],
                       (*indices*) [],
                       (*arguments*)
                       [ LitPat lft; LitPat ptee_fbc ],
                       Static ))
              in
              let shr lft tid l =
                Error
                  "Calling a function with a mutable reference type as a \
                   generic type argument is not yet supported"
              in
              let full_bor_content tid l =
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
                let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
                Ok (PointsTo (loc, l, RegularPointsTo, pat))
              in
              let pointee_fbc tid l suffix =
                let value_id = Printf.sprintf "_v%s_%s" suffix l in
                let* pointee_own = ptee_own tid (Var (loc, value_id)) in
                Ok
                  (Sep
                     ( loc,
                       PointsTo
                         ( loc,
                           Deref (loc, Var (loc, l)),
                           RegularPointsTo,
                           VarPat (loc, value_id) ),
                       pointee_own ))
              in
              Ok (own, shr, full_bor_content, points_to, Some pointee_fbc)
          | Mir.Not ->
              let own tid l = ptee_shr lft tid l in
              let shr lft tid l =
                Error
                  "Calling a function with a shared reference type as a \
                   generic type argument is not yet supported"
              in
              let full_bor_content tid l =
                Error
                  "Expressing the full borrow content of a shared reference \
                   type is not yet supported"
              in
              let points_to tid l vid_op =
                let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
                Ok (PointsTo (loc, l, RegularPointsTo, pat))
              in
              Ok (own, shr, full_bor_content, points_to, None)
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
                    shr;
                    full_bor_content;
                    points_to;
                    pointee_fbc;
                  };
            }
        in
        Ok ty_info

  and decode_adt_ty (adt_ty_cpn : AdtTyRd.t) =
    let open AdtTyRd in
    let def_path = translate_adt_def_id @@ id_get @@ adt_ty_cpn in
    let kind = AdtKindRd.get @@ kind_get @@ adt_ty_cpn in
    let substs_cpn = substs_get_list adt_ty_cpn in
    (def_path, kind, List.map decode_generic_arg substs_cpn)

  and decode_ref_ty (ref_ty_cpn : TyRd.RefTy.t) =
    let open TyRd.RefTy in
    let region_cpn = region_get ref_ty_cpn in
    let region = translate_region region_cpn in
    let mut_cpn = mutability_get ref_ty_cpn in
    let mut =
      match MutabilityRd.get mut_cpn with Mut -> true | Not -> false
    in
    let ty_cpn = ty_get ref_ty_cpn in
    let ty = decode_ty ty_cpn in
    (region, mut, ty)

  and decode_ty (ty_cpn : TyRd.t) =
    let open TyRd in
    let kind_cpn = kind_get ty_cpn in
    match TyRd.TyKind.get kind_cpn with
    | Bool -> `Bool
    | Int int_ty_cpn -> `Int
    | UInt u_int_ty_cpn -> `Uint
    | Char -> `Char
    | Float -> `Float
    | Adt adt_ty_cpn -> `Adt (decode_adt_ty adt_ty_cpn)
    | Foreign -> `Foreign
    | RawPtr raw_ptr_ty_cpn -> `RawPtr
    | Ref ref_ty_cpn -> `Ref (decode_ref_ty ref_ty_cpn)
    | FnDef fn_def_ty_cpn -> `FnDef
    | FnPtr fn_ptr_ty_cpn -> `FnPtr
    | Dynamic -> `Dynamic
    | Closure -> `Closure
    | CoroutineClosure -> `CoroutineClosure
    | Coroutine -> `Coroutine
    | CoroutineWitness -> `CoroutineWitness
    | Never -> `Never
    | Tuple substs_cpn -> `Tuple
    | Alias _ -> `Alias
    | Param name -> `Param name
    | Bound -> `Bound
    | Placeholder -> `Placeholder
    | Infer -> `Infer
    | Error -> `Error
    | Str -> `Str
    | Array array_ty_cpn -> `Array
    | Pattern -> `Pattern
    | Slice elem_ty_cpn -> `Slice (decode_ty elem_ty_cpn)

  and string_of_decoded_type ty =
    match ty with
    | `Bool -> "bool"
    | `Adt (name, kind, args) ->
        if args = [] then name
        else
          Printf.sprintf "%s<%s>" name
            (String.concat ", " (List.map string_of_generic_arg args))
    | _ -> "(type)"

  and extract_implicit_outlives_preds regions ty =
    match ty with
    | `Ref (r, mut, ty) ->
        List.map (fun r' -> (r, r')) regions
        @ extract_implicit_outlives_preds (r :: regions) ty
    | `Adt (name, kind, args) ->
        args
        |> Util.flatmap
             (extract_implicit_outlives_preds_from_generic_arg regions)
    | _ -> []

  and translate_param_ty (name : string) (loc : Ast.loc) =
    let open Ast in
    let vf_ty = IdentTypeExpr (loc, None, name) in
    let interp : RustBelt.ty_interp =
      {
        size = SizeofExpr (loc, TypeExpr vf_ty);
        own =
          (fun t v ->
            Ok
              (Ast.ExprCallExpr
                 ( loc,
                   TypePredExpr (loc, IdentTypeExpr (loc, None, name), "own"),
                   [ LitPat t; LitPat v ] )));
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
                       [ LitPat k; LitPat t; LitPat l ] ) )));
        full_bor_content =
          (fun tid l ->
            Ok
              (ExprCallExpr
                 ( loc,
                   TypePredExpr
                     ( loc,
                       IdentTypeExpr (loc, None, name),
                       "full_borrow_content" ),
                   [ LitPat tid; LitPat l ] )));
        points_to =
          (fun t l vid ->
            let rhs =
              match vid with None -> DummyPat | Some vid -> VarPat (loc, vid)
            in
            Ok (Ast.PointsTo (loc, l, RegularPointsTo, rhs)));
        pointee_fbc = None;
      }
    in
    Ok (Mir.TyInfoBasic { vf_ty; interp })

  and translate_ty_const_kind (ck_cpn : TyRd.ConstKind.t) (loc : Ast.loc) =
    let open TyRd.ConstKind in
    match get ck_cpn with
    | Param _ -> Ast.static_error loc "Todo: ConstKind::Param" None
    | Infer -> Ast.static_error loc "Todo: ConstKind::Infer" None
    | Bound -> Ast.static_error loc "Todo: ConstKind::Bound" None
    | Placeholder -> Ast.static_error loc "Todo: ConstKind::Placeholder" None
    | Unevaluated -> Ast.static_error loc "Todo: ConstKind::Unevaluated" None
    | Value v_cpn -> (
        let open Value in
        let* ty = translate_ty (ty_get v_cpn) loc in
        let val_tree = val_tree_get v_cpn in
        let open ValTree in
        match get val_tree with
        | Leaf scalar_int_cpn ->
            translate_scalar_int scalar_int_cpn (Mir.basic_type_of ty) loc
        | Branch -> failwith "Todo: ConstKind::ValTree::Branch")
    | Error -> Ast.static_error loc "Todo: ConstKind::Error" None
    | Expr -> Ast.static_error loc "Todo: ConstKind::Expr" None

  and translate_ty_const (ty_const_cpn : TyRd.Const.t) (loc : Ast.loc) =
    let open TyRd.Const in
    translate_ty_const_kind (kind_get ty_const_cpn) loc

  and translate_array_ty (array_ty_cpn : TyRd.ArrayTy.t) (loc : Ast.loc) =
    let open TyRd.ArrayTy in
    let elem_ty_cpn = elem_ty_get array_ty_cpn in
    let* elem_ty_info = translate_ty elem_ty_cpn loc in
    let elem_ty = Mir.basic_type_of elem_ty_info in
    let len_cpn = size_get array_ty_cpn in
    let* (CastExpr (_, _, IntLit (_, len, _, _, _))) =
      translate_ty_const len_cpn loc
    in
    let vf_ty =
      Ast.StaticArrayTypeExpr
        (loc, elem_ty, LiteralConstTypeExpr (loc, Big_int.int_of_big_int len))
    in
    let size = Ast.SizeofExpr (loc, TypeExpr vf_ty) in
    let own tid vs =
      Error "Expressing ownership of an array is not yet supported"
    in
    let full_bor_content t l =
      Error
        "Expressing the full borrow content of an array is not yet supported"
    in
    let points_to tid l vid_op =
      let* pat = RustBelt.Aux.vid_op_to_var_pat vid_op loc in
      Ok (Ast.PointsTo (loc, l, RegularPointsTo, pat))
    in
    let interp =
      RustBelt.
        {
          size;
          own;
          shr =
            (fun k t l ->
              Error
                "Expressing the shared ownership of an array is not yet \
                 supported");
          full_bor_content;
          points_to;
          pointee_fbc = None;
        }
    in
    Ok (Mir.TyInfoBasic { vf_ty; interp })

  and translate_ty (ty_cpn : TyRd.t) (loc : Ast.loc) =
    let open Ast in
    let open TyRd in
    let kind_cpn = kind_get ty_cpn in
    match TyRd.TyKind.get kind_cpn with
    | Bool -> Ok (bool_ty_info loc)
    | Int int_ty_cpn -> translate_int_ty int_ty_cpn loc
    | UInt u_int_ty_cpn -> translate_u_int_ty u_int_ty_cpn loc
    | Char -> Ok (char_ty_info loc)
    | Float ->
        Ast.static_error loc "Floating point types are not yet supported" None
    | Adt adt_ty_cpn -> translate_adt_ty adt_ty_cpn loc
    | Foreign -> Ast.static_error loc "Foreign types are not yet supported" None
    | RawPtr raw_ptr_ty_cpn -> translate_raw_ptr_ty raw_ptr_ty_cpn loc
    | Ref ref_ty_cpn -> translate_ref_ty ref_ty_cpn loc
    | FnDef fn_def_ty_cpn -> translate_fn_def_ty fn_def_ty_cpn loc
    | FnPtr fn_ptr_ty_cpn -> translate_fn_ptr_ty fn_ptr_ty_cpn loc
    | Dynamic -> Ast.static_error loc "Dynamic types are not yet supported" None
    | Closure -> Ast.static_error loc "Closure types are not yet supported" None
    | CoroutineClosure ->
        Ast.static_error loc "Coroutine closure types are not yet supported"
          None
    | Coroutine ->
        Ast.static_error loc "Coroutine types are not yet supported" None
    | CoroutineWitness ->
        Ast.static_error loc "Coroutine witness types are not yet supported"
          None
    | Never -> Ok (never_ty_info loc)
    | Tuple tys_cpn ->
        let tys_cpn = Capnp.Array.to_list tys_cpn in
        translate_tuple_ty tys_cpn loc
    | Alias _ -> Ast.static_error loc "Alias types are not yet supported" None
    | Param name -> translate_param_ty name loc
    | Bound -> Ast.static_error loc "Bound types are not yet supported" None
    | Placeholder ->
        Ast.static_error loc "Placeholder types are not yet supported" None
    | Infer -> Ast.static_error loc "Infer types are not yet supported" None
    | Error -> Ast.static_error loc "Error types are not yet supported" None
    | Str -> Ast.static_error loc "Str types are not yet supported" None
    | Array array_ty_cpn -> translate_array_ty array_ty_cpn loc
    | Pattern -> Ast.static_error loc "Pattern types are not yet supported" None
    | Slice _ -> Ast.static_error loc "Slice types are not yet supported" None
    | Undefined _ -> Error (`TrTy "Unknown Rust type kind")

  type body_tr_defs_ctx = {
    adt_defs : Mir.adt_def_tr list;
    directives : Mir.annot list;
  }

  type var_id_trs_entry = { id : string; internal_name : string }
  type var_id_trs_map = var_id_trs_entry list

  module TranslatorArgs = Args

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
      let ty_info =
        lazy
          (match translate_ty ty_cpn loc with
          | Ok ty -> ty
          | _ ->
              Ast.static_error loc
                "The type of this local variable is not yet supported" None)
      in
      let local_decl : Mir.local_decl = { mutability; id; ty = ty_info; loc } in
      Ok local_decl

    let translate_to_vf_local_decl
        ({ mutability = mut; id; ty = (lazy ty_info); loc } : Mir.local_decl) =
      let ty = Mir.basic_type_of ty_info in
      Ast.DeclStmt
        ( loc,
          [
            ( loc,
              Some (match mut with Mut -> ty | Not -> ConstTypeExpr (loc, ty)),
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
        (e : Ast.expr) (e_is_mutable : bool) :
        Ast.expr * bool (* result is mutable *) =
      let rec iter elems =
        match elems with
        | [] -> (e, e_is_mutable)
        | Deref :: elems ->
            let e1, e1_is_mutable = iter elems in
            (Ast.Deref (loc, e1), true)
        | Field (_, field_idx) :: Downcast variant_idx :: elems ->
            let e1, e1_is_mutable = iter elems in
            ( Ast.CallExpr
                ( loc,
                  "#inductive_projection",
                  [],
                  [],
                  [
                    LitPat e1;
                    LitPat (WIntLit (loc, Big_int.big_int_of_int variant_idx));
                    LitPat (WIntLit (loc, Big_int.big_int_of_int field_idx));
                  ],
                  Static ),
              e1_is_mutable )
        | Field (Some name, _) :: elems ->
            let e1, e1_is_mutable = iter elems in
            (Ast.Select (loc, e1, name), e1_is_mutable)
        | Field (None, _) :: _ ->
            failwith "Not yet supported: Field(None, _)::_"
        | Downcast _ :: _ -> failwith "Not yet supported: Downcast _::_"
      in
      iter elems

    let translate_place (place_cpn : PlaceRd.t) (loc : Ast.loc) :
        (Ast.expr * bool (* the place is mutable *), _) result =
      let open PlaceRd in
      let id_cpn = local_get place_cpn in
      let local_is_mutable = local_is_mutable_get place_cpn in
      let id = translate_local_decl_id id_cpn in
      let projection_cpn = projection_get_list place_cpn in
      let place_elems = List.map decode_place_element projection_cpn in
      Ok
        (translate_projection loc (List.rev place_elems)
           (Ast.Var (loc, id))
           local_is_mutable)

    let translate_scalar (s_cpn : ScalarRd.t) (ty : Ast.type_expr)
        (loc : Ast.loc) =
      let open ScalarRd in
      match get s_cpn with
      | Int scalar_int_cpn -> translate_scalar_int scalar_int_cpn ty loc
      | Ptr ->
          Ast.static_error loc "Pointer constants are not yet supported" None

    let mk_unit_expr loc =
      Ast.CastExpr
        ( loc,
          StructTypeExpr (loc, Some TrTyTuple.tuple0_name, None, [], []),
          InitializerList (loc, []) )

    let translate_unit_constant (loc : Ast.loc) = Ok `TrUnitConstant

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

    let translate_mir_ty_const (ty_const_cpn : ConstOperandRd.Const.TyConst.t)
        (loc : Ast.loc) =
      let open ConstOperandRd.Const.TyConst in
      let ty_cpn = ty_get ty_const_cpn in
      let* ty_info = translate_ty ty_cpn loc in
      let ty_expr = Mir.raw_type_of ty_info in
      let ty =
        match ty_expr with
        | Ast.ManifestTypeExpr ((*loc*) _, ty) -> ty
        | _ ->
            failwith
              ("Todo: Unsupported type_expr: "
              ^ Ocaml_expr_formatter.string_of_ocaml_expr false
                  (Ocaml_expr_of_ast.of_type_expr ty_expr))
      in
      match ty with
      | Ast.StructType (st_name, _) ->
          if st_name != TrTyTuple.make_tuple_type_name 0 then
            failwith
              ("Todo: Constants of type struct " ^ st_name
             ^ " are not supported yet")
          else translate_unit_constant loc
      | Ast.FuncType _ -> Ok (`TrTypedConstantFn ty_info)
      | Ast.Int (_, _) | Ast.Bool ->
          let const_cpn = const_get ty_const_cpn in
          let* e = translate_ty_const const_cpn loc in
          Ok (`TrTypedConstantScalar e)
      | _ -> failwith "Todo: Constant of unsupported type"

    let translate_mir_const (constant_kind_cpn : ConstOperandRd.Const.t)
        (loc : Ast.loc) =
      let open ConstOperandRd.Const in
      match get constant_kind_cpn with
      | Ty ty_const_cpn -> translate_mir_ty_const ty_const_cpn loc
      | Val val_cpn -> (
          let open ConstOperandRd.Const.Val in
          let* ty_info = translate_ty (ty_get val_cpn) loc in
          let ty_expr = Mir.raw_type_of ty_info in
          match ty_expr with
          | Ast.ManifestTypeExpr (_, Ast.FuncType _) ->
              Ok (`TrTypedConstantFn ty_info)
          | Ast.StructTypeExpr (_, Some "str_ref", _, _, [ lft ]) -> (
              match ConstValueRd.get @@ const_value_get val_cpn with
              | Slice bytes ->
                  Ok
                    (`TrTypedConstantScalar
                      (Ast.CastExpr
                         ( loc,
                           StructTypeExpr
                             ( loc,
                               Some "str_ref",
                               None,
                               [],
                               [ ManifestTypeExpr (loc, StaticLifetime) ] ),
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
      translate_mir_const const_cpn loc

    let translate_operand (operand_cpn : OperandRd.t) (loc : Ast.loc) =
      let open OperandRd in
      (* Todo @Nima: Move and Copy are ignored for now. It is checked by the Rust compiler that
         - Only Places of type Copy get used for Operand::Copy
         - Places used by Operand::Move will never get used again (obviously raw pointers are not tracked)
      *)
      match get operand_cpn with
      | Copy place_cpn ->
          let* place, place_is_mutable = translate_place place_cpn loc in
          Ok (`TrOperandCopy place)
      | Move place_cpn ->
          let* place, place_is_mutable = translate_place place_cpn loc in
          Ok (`TrOperandMove (place, place_is_mutable))
      | Constant constant_cpn -> translate_const_operand constant_cpn
      | Undefined _ -> Error (`TrOperand "Unknown Mir Operand kind")

    let translate_operands (oprs : (OperandRd.t * Ast.loc) list) =
      (* We want to preserve Rust's left to right argument evaluation *)
      let tmp_rvalue_binders = ref [] in
      let translate_opr ((opr_cpn, loc) : OperandRd.t * Ast.loc) =
        let* opr = translate_operand opr_cpn loc in
        match opr with
        | `TrOperandCopy operand_expr
        | `TrOperandMove (operand_expr, _ (*place_is_mutable*)) ->
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

    let translate_ghost_generic_arg_list (ggal_cpn : AnnotationRd.t) =
      let* ggal = translate_annotation ggal_cpn in
      let ggal = translate_annot_to_vf_parser_inp ggal in
      Ok (VfMirAnnotParser.parse_ghost_generic_arg_list ggal)

    type fn_call_result =
      | FnCallResult of Ast.expr
      | FnCallOutcome of Ast.expr (* 'returning(result)' or 'unwinding' *)

    let translate_fn_call_rexpr (callee_cpn : OperandRd.t)
        (args_cpn : OperandRd.t list) (call_loc : Ast.loc) (fn_loc : Ast.loc)
        (ghost_generic_arg_list_opt_cpn : OptionRd.t) =
      let translate_regular_fn_call substs fn_name =
        (* Todo @Nima: There should be a way to get separated source spans for args *)
        let args = List.map (fun arg_cpn -> (arg_cpn, fn_loc)) args_cpn in
        let* tmp_rvalue_binders, args = translate_operands args in
        let targs =
          substs
          |> Util.flatmap @@ function
             | Mir.GenArgType ty -> [ Mir.raw_type_of ty ]
             | Mir.GenArgLifetime region ->
                 [ Ast.ManifestTypeExpr (call_loc, StaticLifetime) ]
             | _ -> []
        in
        let* targs =
          match OptionRd.get ghost_generic_arg_list_opt_cpn with
          | Nothing -> Ok targs
          | Something ptr_cpn ->
              let ghost_generic_arg_list_cpn =
                VfMirStub.Reader.of_pointer ptr_cpn
              in
              translate_ghost_generic_arg_list ghost_generic_arg_list_cpn
        in
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
        Ok (tmp_rvalue_binders, FnCallOutcome call_expr)
      in
      let* callee = translate_operand callee_cpn call_loc in
      match callee with
      | `TrOperandMove (Var (_, fn_name), place_is_mutable) ->
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
              | "std::ptr::mut_ptr::<impl *mut T>::is_null" -> (
                  match (substs, args_cpn) with
                  | [ Mir.GenArgType gen_arg_ty_info ], [ arg_cpn ] ->
                      let* tmp_rvalue_binders, [ arg ] =
                        translate_operands [ (arg_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          FnCallResult
                            (Ast.Operation
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
                                 ] )) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          "Invalid (generic) arg(s) for \
                           std::ptr::mut_ptr::<impl *mut T>::is_null"))
              | "std::ptr::mut_ptr::<impl *const T>::cast"
              | "std::ptr::mut_ptr::<impl *mut T>::cast" ->
                  let [ _; Mir.GenArgType gen_arg_ty_info ], [ arg_cpn ] =
                    (substs, args_cpn)
                  in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  Ok
                    ( tmp_rvalue_binders,
                      FnCallResult
                        (Ast.CastExpr
                           ( fn_loc,
                             PtrTypeExpr
                               (fn_loc, Mir.basic_type_of gen_arg_ty_info),
                             arg )) )
              | "std::ptr::const_ptr::<impl *const T>::offset"
              | "std::ptr::mut_ptr::<impl *mut T>::offset" -> (
                  match (substs, args_cpn) with
                  | [ Mir.GenArgType gen_arg_ty_info ], [ arg1_cpn; arg2_cpn ]
                    ->
                      let* tmp_rvalue_binders, [ arg1; arg2 ] =
                        translate_operands
                          [ (arg1_cpn, fn_loc); (arg2_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          FnCallResult
                            (Ast.Operation (fn_loc, Ast.Add, [ arg1; arg2 ])) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          (Printf.sprintf "Invalid (generic) arg(s) for %s"
                             fn_name)))
              | "std::ptr::const_ptr::<impl *const T>::offset_from"
              | "std::ptr::mut_ptr::<impl *mut T>::offset_from" -> (
                  match (substs, args_cpn) with
                  | [ Mir.GenArgType gen_arg_ty_info ], [ arg1_cpn; arg2_cpn ]
                    ->
                      let* tmp_rvalue_binders, [ arg1; arg2 ] =
                        translate_operands
                          [ (arg1_cpn, fn_loc); (arg2_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          FnCallOutcome
                            (Ast.CallExpr
                               ( fn_loc,
                                 "std::intrinsics::ptr_offset_from",
                                 [ Mir.basic_type_of gen_arg_ty_info ],
                                 [],
                                 [ LitPat arg1; LitPat arg2 ],
                                 Static )) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          (Printf.sprintf "Invalid (generic) arg(s) for %s"
                             fn_name)))
              | "std::ptr::const_ptr::<impl *const T>::add"
              | "std::ptr::mut_ptr::<impl *mut T>::add" -> (
                  match (substs, args_cpn) with
                  | [ Mir.GenArgType gen_arg_ty_info ], [ arg1_cpn; arg2_cpn ]
                    ->
                      let* tmp_rvalue_binders, [ arg1; arg2 ] =
                        translate_operands
                          [ (arg1_cpn, fn_loc); (arg2_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          FnCallResult
                            (Ast.Operation
                               ( fn_loc,
                                 Ast.Add,
                                 [
                                   arg1;
                                   CastExpr
                                     ( fn_loc,
                                       ManifestTypeExpr
                                         (fn_loc, Int (Signed, PtrRank)),
                                       arg2 );
                                 ] )) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          (Printf.sprintf "Invalid (generic) arg(s) for %s"
                             fn_name)))
              | "std::ptr::const_ptr::<impl *const T>::sub"
              | "std::ptr::mut_ptr::<impl *mut T>::sub" -> (
                  match (substs, args_cpn) with
                  | [ Mir.GenArgType gen_arg_ty_info ], [ arg1_cpn; arg2_cpn ]
                    ->
                      let* tmp_rvalue_binders, [ arg1; arg2 ] =
                        translate_operands
                          [ (arg1_cpn, fn_loc); (arg2_cpn, fn_loc) ]
                      in
                      Ok
                        ( tmp_rvalue_binders,
                          FnCallResult
                            (Ast.Operation
                               ( fn_loc,
                                 Ast.Sub,
                                 [
                                   arg1;
                                   CastExpr
                                     ( fn_loc,
                                       ManifestTypeExpr
                                         (fn_loc, Int (Signed, PtrRank)),
                                       arg2 );
                                 ] )) )
                  | _ ->
                      Error
                        (`TrFnCallRExpr
                          (Printf.sprintf "Invalid (generic) arg(s) for %s"
                             fn_name)))
              | "std::ptr::null_mut" ->
                  Ok
                    ( [],
                      FnCallResult
                        (IntLit
                           ( fn_loc,
                             Big_int.zero_big_int,
                             (*decimal*) true,
                             (*U suffix*) false,
                             (*int literal*) Ast.NoLSuffix )) )
              | "std::ptr::read" | "std::ptr::mut_ptr::<impl *mut T>::read" ->
                  let [ src_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ src ] =
                    translate_operands [ (src_cpn, fn_loc) ]
                  in
                  Ok (tmp_rvalue_binders, FnCallResult (Ast.Deref (fn_loc, src)))
              | "std::ptr::write" | "std::ptr::mut_ptr::<impl *mut T>::write" ->
                  let [ dst_cpn; src_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ dst; src ] =
                    translate_operands [ (dst_cpn, fn_loc); (src_cpn, fn_loc) ]
                  in
                  Ok
                    ( tmp_rvalue_binders
                      @ [
                          Ast.ExprStmt
                            (AssignExpr
                               (fn_loc, Deref (fn_loc, dst), Mutation, src));
                        ],
                      FnCallResult (mk_unit_expr fn_loc) )
              | "std::cell::UnsafeCell::<T>::new"
              | "std::mem::ManuallyDrop::<T>::new"
              | "std::mem::ManuallyDrop::deref"
              | "std::mem::ManuallyDrop::deref_mut" ->
                  let [ arg_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  Ok (tmp_rvalue_binders, FnCallResult arg)
              | "std::cell::UnsafeCell::<T>::get" ->
                  let [ arg_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  Ok
                    ( tmp_rvalue_binders,
                      FnCallResult
                        (CallExpr
                           (fn_loc, "ref_origin", [], [], [ LitPat arg ], Static))
                    )
              | "core::str::<impl str>::as_ptr"
              | "core::slice::<impl [T]>::as_ptr" ->
                  let [ arg_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  Ok
                    ( tmp_rvalue_binders,
                      FnCallResult (Ast.Select (fn_loc, arg, "ptr")) )
              | "core::str::<impl str>::len" | "core::slice::<impl [T]>::len" ->
                  let [ arg_cpn ] = args_cpn in
                  let* tmp_rvalue_binders, [ arg ] =
                    translate_operands [ (arg_cpn, fn_loc) ]
                  in
                  Ok
                    ( tmp_rvalue_binders,
                      FnCallResult (Ast.Select (fn_loc, arg, "len")) )
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
                          ManifestTypeExpr (fn_loc, StaticLifetime);
                          ManifestTypeExpr
                            (fn_loc, Int (Unsigned, FixedWidthRank 0));
                        ] )
                  in
                  Ok
                    ( tmp_rvalue_binders,
                      FnCallResult
                        (Ast.CastExpr
                           ( fn_loc,
                             slice_u8_ref_ty,
                             InitializerList
                               ( fn_loc,
                                 [
                                   (None, Select (fn_loc, arg, "ptr"));
                                   (None, Select (fn_loc, arg, "len"));
                                 ] ) )) )
              | _ -> translate_regular_fn_call substs fn_name)
          | _ ->
              Error
                (`TrFnCallRExpr "Invalid function definition type translation"))
      | _ -> Error (`TrFnCall "Invalid callee operand for function call")

    let translate_basic_block_id (bblock_id_cpn : BasicBlockIdRd.t) =
      Stdint.Uint32.to_string (BasicBlockIdRd.index_get bblock_id_cpn)

    let translate_destination_data (dst_data_cpn : DestinationDataRd.t)
        (loc : Ast.loc) =
      let open DestinationDataRd in
      let place_cpn = place_get dst_data_cpn in
      let* dst = translate_place place_cpn loc in
      let dst_bblock_id_cpn = basic_block_id_get dst_data_cpn in
      let dst_bblock_id = translate_basic_block_id dst_bblock_id_cpn in
      let dst_data : Mir.fn_call_dst_data = { dst; dst_bblock_id } in
      Ok dst_data

    let translate_unwind_action (unwind_action_cpn : UnwindActionRd.t)
        (loc : Ast.loc) =
      let open UnwindActionRd in
      match get unwind_action_cpn with
      | Continue ->
          ( [
              Ast.ReturnStmt
                (loc, Some (Ast.CallExpr (loc, "unwinding", [], [], [], Static)));
            ],
            [] )
      | Unreachable -> ([ Ast.Assert (loc, Ast.False loc) ], [])
      | Terminate ->
          ( [
              Ast.ExprStmt
                (CallExpr (loc, "std::process::abort", [], [], [], Static));
            ],
            [] )
      | Cleanup bblock_id_cpn ->
          let bblock_id = translate_basic_block_id bblock_id_cpn in
          ([ Ast.GotoStmt (loc, bblock_id) ], [ bblock_id ])

    let translate_fn_call (fn_call_data_cpn : FnCallDataRd.t) (loc : Ast.loc) =
      let open FnCallDataRd in
      let func_cpn = func_get fn_call_data_cpn in
      let fn_span_cpn = call_span_get fn_call_data_cpn in
      let* fn_loc = translate_span_data fn_span_cpn in
      let args_cpn = args_get_list fn_call_data_cpn in
      let ghost_generic_arg_list_opt_cpn =
        ghost_generic_arg_list_get fn_call_data_cpn
      in
      let unwind_stmts, unwind_targets =
        if TranslatorArgs.ignore_unwind_paths then ([], [])
        else translate_unwind_action (unwind_action_get fn_call_data_cpn) loc
      in
      let* fn_call_tmp_rval_ctx, fn_call_rexpr =
        translate_fn_call_rexpr func_cpn args_cpn loc fn_loc
          ghost_generic_arg_list_opt_cpn
      in
      let destination_cpn = destination_get fn_call_data_cpn in
      let* call_stmts, terminator, targets =
        match OptionRd.get destination_cpn with
        | Nothing ->
            (*Diverging call*)
            let call_expr =
              match fn_call_rexpr with
              | FnCallResult e -> e
              | FnCallOutcome e -> e
            in
            Ok
              ( [ Ast.ExprStmt call_expr ] @ unwind_stmts,
                Mir.EncodedTerminator,
                [] )
        | Something ptr_cpn ->
            let destination_data_cpn = VfMirStub.Reader.of_pointer ptr_cpn in
            let* { Mir.dst = dst, dst_is_mutable; Mir.dst_bblock_id } =
              translate_destination_data destination_data_cpn loc
            in
            let assignment e =
              Ast.ExprStmt
                (Ast.AssignExpr
                   ( loc,
                     dst,
                     (if dst_is_mutable then Mutation else Initialization),
                     e ))
            in
            let call_stmt =
              match fn_call_rexpr with
              | FnCallResult e -> assignment e
              | FnCallOutcome e ->
                  if TranslatorArgs.ignore_unwind_paths then assignment e
                  else
                    Ast.SwitchStmt
                      ( loc,
                        e,
                        [
                          Ast.SwitchStmtClause
                            ( loc,
                              CallExpr
                                ( loc,
                                  "returning",
                                  [],
                                  [],
                                  [ LitPat (Var (loc, "__result")) ],
                                  Static ),
                              [ assignment (Ast.Var (loc, "__result")) ] );
                          Ast.SwitchStmtClause
                            ( loc,
                              CallExpr (loc, "unwinding", [], [], [], Static),
                              unwind_stmts );
                        ] )
            in
            Ok
              ( [ call_stmt ],
                Mir.GotoTerminator (loc, dst_bblock_id),
                [ dst_bblock_id ] )
        | Undefined _ -> Error (`TrFnCall "Unknown Option kind")
      in
      let full_call_stmts, targets =
        match fn_call_rexpr with
        | FnCallOutcome
            (Ast.CallExpr
              ( call_loc,
                "VeriFast_ghost_command",
                [] (*type arguments*),
                [] (*indices, in case this is really a predicate assertion*),
                [],
                Ast.Static (*method_binding*) )) ->
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
            ([ ghost_stmt ], targets)
        | _ ->
            ( (if ListAux.is_empty fn_call_tmp_rval_ctx then call_stmts
               else
                 [
                   Ast.BlockStmt
                     ( loc,
                       (*decl list*) [],
                       fn_call_tmp_rval_ctx @ call_stmts,
                       loc,
                       ref [] );
                 ]),
              targets @ unwind_targets )
      in
      Ok (full_call_stmts, terminator, targets)

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
                 (Verifast0.rust_string_of_type tp))
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
          Ok ([], Mir.GotoTerminator (loc, bb_id), [ bb_id ])
      | SwitchInt sw_int_data_cpn ->
          let* sw_stmt, targets = translate_sw_int sw_int_data_cpn loc in
          Ok ([ sw_stmt ], Mir.EncodedTerminator, targets)
      | Return ->
          let result = Ast.Var (loc, ret_place_id) in
          let result =
            if TranslatorArgs.ignore_unwind_paths then result
            else
              Ast.CallExpr (loc, "returning", [], [], [ LitPat result ], Static)
          in
          Ok ([ Ast.ReturnStmt (loc, Some result) ], EncodedTerminator, [])
      | Unreachable ->
          Ok ([ Ast.Assert (loc, False loc) ], EncodedTerminator, [])
      | Call fn_call_data_cpn -> translate_fn_call fn_call_data_cpn loc
      | Drop drop_data_cpn ->
          let open DropData in
          let place_cpn = place_get drop_data_cpn in
          let* place, place_is_mutable = translate_place place_cpn loc in
          let target_cpn = target_get drop_data_cpn in
          let target = translate_basic_block_id target_cpn in
          let unfreeze_stmts, freeze_stmts =
            if place_is_mutable then ([], [])
            else
              ( [
                  Ast.ExprStmt
                    (CallExpr
                       ( loc,
                         "std::mem::verifast::unfreeze",
                         [],
                         [],
                         [ LitPat (AddressOf (loc, place)) ],
                         Static ));
                ],
                [
                  Ast.ExprStmt
                    (CallExpr
                       ( loc,
                         "std::mem::verifast::freeze",
                         [],
                         [],
                         [ LitPat (AddressOf (loc, place)) ],
                         Static ));
                ] )
          in
          Ok
            ( unfreeze_stmts
              @ [
                  Ast.ExprStmt
                    (CallExpr
                       ( loc,
                         "std::ptr::drop_in_place",
                         [],
                         [],
                         [ LitPat (AddressOf (loc, place)) ],
                         Static ));
                ]
              @ freeze_stmts,
              Mir.GotoTerminator (loc, target),
              [ target ] )
      | UnwindResume ->
          Ok
            ( [
                Ast.ReturnStmt
                  ( loc,
                    Some (Ast.CallExpr (loc, "unwinding", [], [], [], Static))
                  );
              ],
              EncodedTerminator,
              [] )
      | UnwindTerminate ->
          Ok
            ( [
                Ast.ExprStmt
                  (CallExpr (loc, "std::process::abort", [], [], [], Static));
              ],
              EncodedTerminator,
              [] )

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

    let translate_aggregate_kind (agg_kind_cpn : AggregateKindRd.t)
        (loc : Ast.loc) =
      let open AggregateKindRd in
      match get agg_kind_cpn with
      | Array es_ty_cpn ->
          let* elem_ty = translate_ty es_ty_cpn loc in
          Ok (Mir.AggKindArray elem_ty)
      | Tuple -> Ok Mir.AggKindTuple
      | Adt adt_data_cpn ->
          let open AdtData in
          let adt_id_cpn = adt_id_get adt_data_cpn in
          let adt_def_path = translate_adt_def_id adt_id_cpn in
          let adt_name = TrName.translate_def_path adt_def_path in
          let adt_kind =
            match AdtKindRd.get (adt_kind_get adt_data_cpn) with
            | StructKind -> Mir.Struct
            | EnumKind -> Mir.Enum
            | UnionKind -> Mir.Union
          in
          let variant_idx_cpn = variant_idx_get adt_data_cpn in
          let variant_name = variant_id_get adt_data_cpn in
          let substs_cpn = gen_args_get_list adt_data_cpn in
          let field_names = field_names_get_list adt_data_cpn in
          Ok Mir.(AggKindAdt { adt_kind; adt_name; variant_name; field_names })
      | Closure -> failwith "Todo: AggregateKind::Closure"
      | Coroutine -> failwith "Todo: AggregateKind::Coroutine"
      | CoroutineClosure -> failwith "Todo: AggregateKind::CoroutineClosure"
      | RawPtr -> failwith "Todo: AggregateKind::RawPtr"
      | Undefined _ -> Error (`TrAggregateKind "Unknown AggregateKind")

    let translate_aggregate (agg_data_cpn : AggregateDataRd.t) (loc : Ast.loc) =
      let open AggregateDataRd in
      let operands_cpn = operands_get_list agg_data_cpn in
      let operands_cpn = List.map (fun op -> (op, loc)) operands_cpn in
      let* tmp_rvalue_binders, operand_exprs =
        translate_operands operands_cpn
      in
      let agg_kind_cpn = aggregate_kind_get agg_data_cpn in
      let* agg_kind = translate_aggregate_kind agg_kind_cpn loc in
      match agg_kind with
      | AggKindArray elem_ty ->
          let init_stmts_builder (lhs_place, lhs_place_is_mutable) =
            List.mapi
              (fun i operand_expr ->
                let open Ast in
                ExprStmt
                  (AssignExpr
                     ( loc,
                       ReadArray
                         ( loc,
                           lhs_place,
                           IntLit
                             ( loc,
                               Big_int.big_int_of_int i,
                               true,
                               false,
                               NoLSuffix ) ),
                       (if lhs_place_is_mutable then Mutation
                        else Initialization),
                       operand_expr )))
              operand_exprs
          in
          Ok (`TrRvalueAggregate init_stmts_builder)
      | AggKindTuple ->
          let tuple_struct_name =
            TrTyTuple.make_tuple_type_name (List.length operands_cpn)
          in
          let init_stmts_builder (lhs_place, lhs_place_is_mutable) =
            let field_init_stmts =
              List.mapi
                (fun i init_expr ->
                  let open Ast in
                  ExprStmt
                    (AssignExpr
                       ( loc,
                         Select (loc, lhs_place, string_of_int i),
                         (if lhs_place_is_mutable then Mutation
                          else Initialization),
                         init_expr )))
                operand_exprs
            in
            tmp_rvalue_binders @ field_init_stmts
          in
          Ok (`TrRvalueAggregate init_stmts_builder)
      | AggKindAdt { adt_kind; adt_name; variant_name; field_names } -> (
          match adt_kind with
          | Enum ->
              let init_stmts_builder (lhs_place, lhs_place_is_mutable) =
                let arg_pats = List.map (fun e -> Ast.LitPat e) operand_exprs in
                let assignment =
                  Ast.ExprStmt
                    (AssignExpr
                       ( loc,
                         lhs_place,
                         (if lhs_place_is_mutable then Mutation
                          else Initialization),
                         CallExpr
                           ( loc,
                             adt_name ^ "::" ^ variant_name,
                             [],
                             [],
                             arg_pats,
                             Static ) ))
                in
                tmp_rvalue_binders @ [ assignment ]
              in
              Ok (`TrRvalueAggregate init_stmts_builder)
          | Union -> failwith "Todo: Unsupported Adt kind for aggregate"
          | Struct ->
              if List.length operands_cpn <> List.length field_names then
                Error
                  (`TrAggregate
                    "The number of struct fields and initializing operands are \
                     different")
              else
                let init_stmts_builder (lhs_place, lhs_place_is_mutable) =
                  let field_init_stmts =
                    List.map
                      (fun (field_name, init_expr) ->
                        let open Ast in
                        ExprStmt
                          (AssignExpr
                             ( loc,
                               Select (loc, lhs_place, field_name),
                               (if lhs_place_is_mutable then Mutation
                                else Initialization),
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
        | `TrOperandMove (expr, _ (*place_is_mutable*))
        | `TrTypedConstantScalar expr ->
            Ok (`TrRvalueExpr expr)
        | `TrTypedConstantRvalueBinderBuilder rvalue_binder_builder ->
            Ok (`TrRvalueRvalueBinderBuilder rvalue_binder_builder)
        | `TrUnitConstant -> Ok `TrRvalueUnitConstant
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
          let bor_kind = BorrowKind.get bor_kind_cpn in
          let place_cpn = place_get ref_data_cpn in
          let* place_expr, place_is_mutable = translate_place place_cpn loc in
          let (path, line, _), _ = Ast.lexed_loc loc in
          let ignore_ref_creation =
            bor_kind = Mut
            ||
            (* ignore &mut E for now *)
            if TranslatorArgs.ignore_ref_creation then true
            else
              let directives =
                Util.flatmap
                  (fun { Mir.span; raw } ->
                    if
                      raw = "ignore_ref_creation"
                      &&
                      let (path', line', _), _ = Ast.lexed_loc span in
                      path' = path && line' = line
                    then [ span ]
                    else [])
                  Args.body_tr_defs_ctx.directives
              in
              match directives with
              | directive_span :: _ ->
                  if not TranslatorArgs.allow_ignore_ref_creation then
                    Ast.static_error directive_span
                      "Ignoring reference creation is not allowed; specify \
                       -allow_ignore_ref_creation on the command line to allow"
                      None;
                  true
              | [] -> false
          in
          if ignore_ref_creation then
            Ok (`TrRvalueExpr (Ast.AddressOf (loc, place_expr)))
          else
            let place_ty = decode_ty (place_ty_get ref_data_cpn) in
            let is_implicit = is_implicit_get ref_data_cpn in
            let place_kind =
              BodyRd.PlaceKind.get (BodyRd.Place.kind_get place_cpn)
            in
            (*
            Printf.printf "ref creation at %s: place_ty=%s, bor_kind=%s, place_kind=%s, is_implicit=%b\n"
              (Ast.string_of_loc loc)
              (string_of_decoded_type place_ty)
              (match bor_kind with Mut -> "Mut" | Shared -> "Shared")
              (match place_kind with MutableRef -> "MutableRef" | SharedRef -> "SharedRef" | _ -> "Other")
              is_implicit;
            *)
            let fn_name =
              match (place_ty, bor_kind, place_kind, is_implicit) with
              | `Str, Shared, SharedRef, _ -> "reborrow_str_ref"
              | `Str, Shared, _, _ -> "create_str_ref"
              | `Slice _, Mut, _, _ -> "create_slice_ref_mut"
              | `Slice _, Shared, SharedRef, _ -> "reborrow_slice_ref"
              | `Slice _, Shared, _, _ -> "create_slice_ref"
              | `Adt ("std::cell::UnsafeCell", _, _), Shared, _, _ ->
                  "create_ref_UnsafeCell"
              | _, Mut, MutableRef, true -> "reborrow_ref_mut_implicit"
              | _, Mut, MutableRef, _ -> "reborrow_ref_mut"
              | _, Mut, _, _ -> "create_ref_mut"
              | _, Shared, SharedRef, true -> "reborrow_ref_implicit"
              | _, Shared, SharedRef, _ -> "reborrow_ref"
              | _, Shared, _, _ -> "create_ref"
            in
            let expr =
              Ast.CallExpr
                ( loc,
                  fn_name,
                  [],
                  [],
                  [ LitPat (AddressOf (loc, place_expr)) ],
                  Static )
            in
            let expr =
              if TranslatorArgs.ignore_unwind_paths then expr
              else
                Ast.CallExpr
                  (loc, "fn_outcome_result", [], [], [ LitPat expr ], Static)
            in
            Ok (`TrRvalueExpr expr)
      | AddressOf address_of_data_cpn ->
          let open AddressOfData in
          let mut_cpn = mutability_get address_of_data_cpn in
          let place_cpn = place_get address_of_data_cpn in
          let* place_expr, place_is_mutable = translate_place place_cpn loc in
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
          | `TrOperandMove (expr, _ (*place_is_mutable*))
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
          let* place_expr, place_is_mutable = translate_place place_cpn loc in
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
          let* lhs_place, lhs_place_is_mutable =
            translate_place lhs_place_cpn loc
          in
          let rhs_rvalue_cpn = AssignData.rhs_rvalue_get assign_data_cpn in
          let* rhs_rvalue = translate_rvalue rhs_rvalue_cpn loc in
          match rhs_rvalue with
          | `TrRvalueExpr rhs_expr ->
              let assign_stmt =
                Ast.ExprStmt
                  (Ast.AssignExpr
                     ( loc,
                       lhs_place,
                       (if lhs_place_is_mutable then Mutation
                        else Initialization),
                       rhs_expr ))
              in
              Ok [ assign_stmt ]
          | `TrRvalueUnitConstant -> Ok []
          | `TrRvalueRvalueBinderBuilder rvalue_binder_builder ->
              (* Todo @Nima: Is this correct to use `loc` for subparts of the block that represents the assignment statement *)
              let tmp_var_name = TrName.make_tmp_var_name "" in
              let rvalue_binder_stmt = rvalue_binder_builder tmp_var_name in
              let assign_stmt =
                Ast.ExprStmt
                  (Ast.AssignExpr
                     ( loc,
                       lhs_place,
                       (if lhs_place_is_mutable then Mutation
                        else Initialization),
                       Ast.Var (loc, tmp_var_name) ))
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
                       (if lhs_place_is_mutable then Mutation
                        else Initialization),
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
                       (if lhs_place_is_mutable then Mutation
                        else Initialization),
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
              Ok (init_stmts_builder (lhs_place, lhs_place_is_mutable)))
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
      if is_cleanup_get bblock_cpn && TranslatorArgs.ignore_unwind_paths then
        (* Todo @Nima: For now we are ignoring cleanup basic-blocks *)
        Ok None
      else
        let statements_cpn = statements_get_list bblock_cpn in
        let* statements = ListAux.try_map translate_statement statements_cpn in
        let statements = List.concat statements in
        let terminator_cpn = terminator_get bblock_cpn in
        let* terminator_stmts, terminator, successors =
          translate_terminator ret_place_id terminator_cpn
        in
        let bblock : Mir.basic_block =
          {
            id;
            statements;
            terminator_stmts;
            terminator;
            successors;
            external_predecessor_count = 0;
            internal_predecessor_count = 0;
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
             match bb.terminator_stmts with
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
             ] ->
                 let id =
                   Printf.sprintf "bh%d"
                     (Hashtbl.length explicit_block_heads_table)
                 in
                 let fixed_bb =
                   {
                     bb with
                     terminator_stmts = [];
                     terminator = GotoTerminator (l, id);
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
             ] ->
                 explicit_block_ends :=
                   (closeBraceLoc, bb.terminator, bb) :: !explicit_block_ends
             | _ -> Hashtbl.add bblocks_table bb.id bb);
      !explicit_block_ends
      |> List.iter (fun (closeBraceLoc, gotoStmt, (bb : Mir.basic_block)) ->
             let head_bb =
               Hashtbl.find explicit_block_heads_table closeBraceLoc
             in
             Hashtbl.add bblocks_table bb.id
               {
                 bb with
                 terminator_stmts = [];
                 terminator = gotoStmt;
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
            bb.external_predecessor_count <- bb.external_predecessor_count + 1;
            let path = bb :: path in
            bb.walk_state <- Walking (k, path);
            bb.successors
            |> List.iter (fun succ_id -> iter path (k + 1) succ_id);
            bb.walk_state <- Exhausted;
            match bb.parent with
            | None -> toplevel_blocks := bb :: !toplevel_blocks
            | Some bb' -> bb'.children <- bb :: bb'.children)
        | Walking (k', _) ->
            bb.internal_predecessor_count <- bb.internal_predecessor_count + 1;
            (*Printf.printf "Found a loop with head at rank %d: %s\n" k' (String.concat " -> " (List.map (fun (bb: basic_block) -> bb.id) (List.rev (bb::path))));*)
            bb.is_block_head <- true;
            set_parent bb k' (k - 1) path
        | Exhausted -> (
            bb.external_predecessor_count <- bb.external_predecessor_count + 1;
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
           terminator_stmts = trmStmts;
           terminator = trm;
           successors;
           external_predecessor_count;
           internal_predecessor_count;
           is_block_head;
           children;
         } :
          Mir.basic_block) =
      let stmts1 = stmts0 @ trmStmts in
      let stmts =
        stmts1
        @
        match trm with
        | GotoTerminator (l, lbl) -> [ Ast.GotoStmt (l, lbl) ]
        | EncodedTerminator -> []
      in
      let loc = stmts |> List.hd |> Ast.stmt_loc in
      let predecessor_count, stmts, trm =
        if is_block_head then
          match (trmStmts, trm) with
          | ( [
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
              ],
              GotoTerminator (lg, target) ) ->
              let children_stmts =
                translate_basic_blocks_to_stmts children []
              in
              ( external_predecessor_count + internal_predecessor_count,
                [
                  Ast.BlockStmt
                    ( loc,
                      decls,
                      Ast.LabelStmt (loc, id)
                      :: (stmts0
                         @ [ Ast.GotoStmt (lg, target) ]
                         @ children_stmts),
                      closeBraceLoc,
                      ref [] );
                ],
                Mir.EncodedTerminator )
          | _ ->
              let predecessor_count, stmt =
                match stmts with
                | Ast.PureStmt (lp, InvariantStmt (linv, inv)) :: stmts ->
                    let children_stmts =
                      translate_basic_blocks_to_stmts children
                        [
                          ( id,
                            internal_predecessor_count,
                            loc,
                            [],
                            Mir.EncodedTerminator );
                        ]
                    in
                    ( external_predecessor_count,
                      Ast.WhileStmt
                        ( loc,
                          True loc,
                          Some (LoopInv inv),
                          None,
                          stmts @ children_stmts,
                          [] ) )
                | Ast.PureStmt (lp, Ast.SpecStmt (lspec, req, ens)) :: stmts ->
                    let children_stmts =
                      translate_basic_blocks_to_stmts children
                        [
                          ( id,
                            internal_predecessor_count,
                            loc,
                            [],
                            Mir.EncodedTerminator );
                        ]
                    in
                    ( external_predecessor_count,
                      Ast.WhileStmt
                        ( loc,
                          True loc,
                          Some (LoopSpec (req, ens)),
                          None,
                          stmts @ children_stmts,
                          [] ) )
                | _ ->
                    let children_stmts =
                      translate_basic_blocks_to_stmts children []
                    in
                    ( external_predecessor_count + internal_predecessor_count,
                      Ast.BlockStmt
                        ( loc,
                          [],
                          Ast.LabelStmt (loc, id) :: (stmts @ children_stmts),
                          loc,
                          ref [] ) )
              in
              (predecessor_count, [ stmt ], EncodedTerminator)
        else
          (external_predecessor_count + internal_predecessor_count, stmts1, trm)
      in
      (id, predecessor_count, loc, stmts, trm)

    and translate_basic_blocks_to_stmts (bblocks : Mir.basic_block list) epilog
        =
      let bbs = List.map translate_to_vf_basic_block bblocks @ epilog in
      let rec iter trm bbs =
        match (trm, bbs) with
        | Mir.EncodedTerminator, (id, predecessor_count, loc, stmts, trm) :: bbs
          ->
            (Ast.LabelStmt (loc, id) :: stmts) @ iter trm bbs
        | Mir.EncodedTerminator, [] -> []
        | ( Mir.GotoTerminator (l, lbl),
            (id, predecessor_count, loc, stmts, trm) :: bbs ) ->
            if predecessor_count = 1 && lbl = id then stmts @ iter trm bbs
            else
              (Ast.GotoStmt (l, lbl) :: Ast.LabelStmt (loc, id) :: stmts)
              @ iter trm bbs
        | Mir.GotoTerminator (l, lbl), [] -> [ Ast.GotoStmt (l, lbl) ]
      in
      iter EncodedTerminator bbs

    let translate_var_debug_info_contents (vdic_cpn : VarDebugInfoContentsRd.t)
        (loc : Ast.loc) =
      let open VarDebugInfoContentsRd in
      match get vdic_cpn with
      | Place place_cpn -> (
          let* place, place_is_mutable = translate_place place_cpn loc in
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

  let rec mk_list_pat l = function
    | [] -> Ast.LitPat (Var (l, "nil"))
    | h :: t -> Ast.CtorPat (l, "cons", [ h; mk_list_pat l t ])

  let mk_send_asn loc tparam =
    let open Ast in
    ExprAsn
      ( loc,
        CallExpr
          ( loc,
            "is_Send",
            [],
            [],
            [
              LitPat
                (Typeid (loc, TypeExpr (IdentTypeExpr (loc, None, tparam))));
            ],
            Static ) )

  let mk_sync_asn loc tparam =
    let open Ast in
    ExprAsn
      ( loc,
        CallExpr
          ( loc,
            "is_Sync",
            [],
            [],
            [
              LitPat
                (Typeid (loc, TypeExpr (IdentTypeExpr (loc, None, tparam))));
            ],
            Static ) )

  let gen_own_asn (adt_defs : Mir.adt_def_tr list) (thread_id : Ast.expr)
      (loc : Ast.loc) (v : Ast.expr) (ty_info : Mir.ty_info) =
    let raw_ty = Mir.raw_type_of ty_info in
    let RustBelt.{ size; own; shr } = Mir.interp_of ty_info in
    match own thread_id v with
    | Ok asn -> Ok asn
    | Error estr ->
        Error (`GenLocalTyAsn ("Owner assertion function error: " ^ estr))

  let gen_own_asns (adt_defs : Mir.adt_def_tr list) (loc : Ast.loc)
      (thread_id : Ast.expr) (vs : (Ast.loc * Ast.expr * Mir.ty_info) list) =
    let* ty_asns =
      ListAux.try_map
        (fun (v_loc, v, v_ty) -> gen_own_asn adt_defs thread_id v_loc v v_ty)
        vs
    in
    let ty_asns =
      List.filter
        (fun asn -> match asn with Ast.True _ -> false | _ -> true)
        ty_asns
    in
    Ok (AstAux.list_to_sep_conj (List.map (fun asn -> (loc, asn)) ty_asns) None)

  let rec type_is_trivially_droppable = function
    | Ast.ManifestTypeExpr
        ( _,
          ( Int (_, _)
          | RustRefType _ | PtrType _ | Bool | Float | Double | LongDouble ) )
    | Ast.PtrTypeExpr (_, _)
    | Ast.RustRefTypeExpr (_, _, _, _) ->
        true
    | Ast.StructTypeExpr
        (_, Some ("std::ptr::NonNull" | "std::marker::PhantomData"), _, _, _) ->
        true
    | Ast.ConstructedTypeExpr (_, "std::option::Option", [ arg ]) ->
        type_is_trivially_droppable arg
    | _ -> false

  let gen_adt_drop_proof_oblig (adt_defs : Mir.adt_def_tr list)
      (adt_def_loc : Ast.loc) (adt_name : string) (tparams : string list)
      (adt_fields : (Ast.loc * string * Mir.ty_info) list) =
    let open Ast in
    let targs =
      List.map (fun x -> IdentTypeExpr (adt_def_loc, None, x)) tparams
    in
    let pre =
      CallExpr
        ( adt_def_loc,
          adt_name ^ "_own",
          targs,
          [],
          [ VarPat (adt_def_loc, "_t"); VarPat (adt_def_loc, "_v") ],
          if targs = [] then PredFamCall else PredCtorCall )
    in
    let post =
      Result.get_ok
      @@ gen_own_asns adt_defs adt_def_loc
           (Var (adt_def_loc, "_t"))
           (Util.flatmap
              (fun (loc, id, ty) ->
                if type_is_trivially_droppable (Mir.basic_type_of ty) then []
                else [ (loc, Select (loc, Var (loc, "_v"), id), ty) ])
              adt_fields)
    in
    let post = match post with None -> True adt_def_loc | Some post -> post in
    Func
      ( adt_def_loc,
        Lemma
          ( false
            (*indicates whether an axiom should be generated for this lemma*),
            None (*trigger*) ),
        tparams (*type parameters*),
        None (*return type*),
        adt_name ^ "_drop",
        [],
        false (*nonghost_callers_only*),
        None
        (*implemented function type, with function type type arguments and function type arguments*),
        Some (pre, ("result", post)) (*contract*),
        false (*terminates*),
        None (*body*),
        false (*virtual*),
        [] (*overrides*) )

  let gen_contract (adt_defs : Mir.adt_def_tr list) (contract_loc : Ast.loc)
      (lft_vars : string list) (outlives_preds : (string * string) list)
      (send_tparams : string list) (sync_tparams : string list)
      (params : (Ast.loc * string * Mir.ty_info) list)
      (ret : Ast.loc * Mir.ty_info) =
    let ret_loc, ret_ty = ret in
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
    let ret_ty_has_elided_lifetimes =
      let rec check_type_expr state te =
        match te with
        | IdentTypeExpr (_, _, x) when String.starts_with ~prefix:"'_" x -> true
        | ManifestTypeExpr (_, tp) -> false
        | _ -> type_expr_fold_open check_type_expr state te
      in
      check_type_expr false (Mir.basic_type_of ret_ty)
    in
    let is_in_out_param (_, _, ty) =
      match Mir.basic_type_of ty with
      | RustRefTypeExpr (_, IdentTypeExpr (_, _, x), Mutable, _)
        when (not ret_ty_has_elided_lifetimes)
             && String.starts_with ~prefix:"'_" x ->
          true
      | _ -> false
    in
    let in_out_params, in_params = params |> List.partition is_in_out_param in
    let add_in_out_param_asns suffix asn =
      List.fold_right
        (fun (loc, id, ty) asn ->
          let (Some pointee_fbc) = (Mir.interp_of ty).pointee_fbc in
          let (Ok pointee_fbc) =
            pointee_fbc (Var (loc, thread_id_name)) id suffix
          in
          Sep (loc, pointee_fbc, asn))
        in_out_params asn
    in
    let pre_na_token =
      Sep
        ( contract_loc,
          nonatomic_token_b (bind_pat_b thread_id_name),
          Operation
            ( contract_loc,
              Eq,
              [ Var (contract_loc, "_t"); Var (contract_loc, "currentThread") ]
            ) )
    in
    let post_na_token = nonatomic_token_b (lit_pat_b thread_id_name) in
    let lft_token_b q_pat_b n =
      let coef_n = "_q_" ^ n in
      CoefAsn
        ( contract_loc,
          q_pat_b coef_n,
          CallExpr
            ( contract_loc,
              "lifetime_token",
              [] (*type arguments*),
              [] (*indices*),
              [ LitPat (Rust_parser.expr_of_lft_param contract_loc ("'" ^ n)) ]
              (*arguments*),
              Static ) )
    in
    let pre_lft_tks =
      if List.length lft_vars <= 1 then
        List.map (fun lft_var -> lft_token_b bind_pat_b lft_var) lft_vars
      else List.map (fun lft_var -> lft_token_b bind_pat_b lft_var) lft_vars
    in
    let outlives_asns =
      outlives_preds
      |> List.map @@ fun (r1, r2) ->
         Operation
           ( contract_loc,
             Eq,
             [
               CallExpr
                 ( contract_loc,
                   "lifetime_inclusion",
                   [],
                   [],
                   [
                     LitPat (Rust_parser.expr_of_lft_param contract_loc r2);
                     LitPat (Rust_parser.expr_of_lft_param contract_loc r1);
                   ],
                   Static );
               True contract_loc;
             ] )
    in
    let send_asns = send_tparams |> List.map (mk_send_asn contract_loc) in
    let sync_asns = sync_tparams |> List.map (mk_sync_asn contract_loc) in
    let pre_lft_tks = pre_lft_tks @ outlives_asns @ send_asns @ sync_asns in
    let post_lft_tks =
      List.map (fun lft_var -> lft_token_b lit_pat_b lft_var) lft_vars
    in
    let* params_ty_asns =
      gen_own_asns adt_defs contract_loc
        (Var (contract_loc, thread_id_name))
        (List.map (fun (loc, id, ty) -> (loc, Var (loc, id), ty)) in_params)
    in
    let pre_asn =
      AstAux.list_to_sep_conj
        (List.map (fun asn -> (contract_loc, asn)) pre_lft_tks)
        params_ty_asns
    in
    let pre_asn =
      match pre_asn with None -> EmpAsn contract_loc | Some asn -> asn
    in
    let pre_asn =
      Sep (contract_loc, pre_na_token, add_in_out_param_asns "0" pre_asn)
    in
    let* ret_ty_asn =
      gen_own_asn adt_defs
        (Var (contract_loc, thread_id_name))
        ret_loc
        (Var (ret_loc, "result"))
        ret_ty
    in
    let (Some post_asn) =
      AstAux.list_to_sep_conj
        (List.map (fun asn -> (contract_loc, asn)) post_lft_tks)
        (Some (add_in_out_param_asns "1" ret_ty_asn))
      (*might be just True*)
    in
    let post_asn = Sep (contract_loc, post_na_token, post_asn) in
    let (Some unwind_post_asn) =
      AstAux.list_to_sep_conj
        (List.map (fun asn -> (contract_loc, asn)) post_lft_tks)
        (Some (add_in_out_param_asns "1" (EmpAsn contract_loc)))
      (*might be just True*)
    in
    let unwind_post_asn = Sep (contract_loc, post_na_token, unwind_post_asn) in
    Ok
      ( pre_asn,
        Rust_parser.mk_outcome_post contract_loc post_asn unwind_post_asn )

  let gen_drop_contract adt_defs self_ty self_ty_targs self_lft_args limpl =
    let outlives_preds = [] in
    let open Ast in
    let ({ loc = ls; tparams; lft_params; fds } : Mir.adt_def_tr) =
      List.find
        (function ({ name } : Mir.adt_def_tr) -> name = self_ty)
        adt_defs
    in
    (* TODO: Eliminate code duplication between gen_contract and gen_drop_contract *)
    let bind_pat_b n = VarPat (limpl, n) in
    let lit_pat_b n = LitPat (Var (limpl, n)) in
    (* Todo @Nima: Move RustBelt token, etc. constructors like the following to the RustBelt module so
       The hard-coded names will be in the same place and the code will be reusable *)
    let nonatomic_token_b pat =
      CallExpr
        ( limpl,
          "thread_token",
          [] (*type arguments*),
          [] (*indices*),
          [ pat ] (*arguments*),
          Static )
    in
    let thread_id_name = "_t" in
    let pre_na_token =
      Sep
        ( limpl,
          nonatomic_token_b (bind_pat_b thread_id_name),
          Operation
            (limpl, Eq, [ Var (limpl, "_t"); Var (limpl, "currentThread") ]) )
    in
    let post_na_token = nonatomic_token_b (lit_pat_b thread_id_name) in
    let lft_token_b q_pat_b n =
      let coef_n = "_q_" ^ n in
      CoefAsn
        ( limpl,
          q_pat_b coef_n,
          CallExpr
            ( limpl,
              "lifetime_token",
              [] (*type arguments*),
              [] (*indices*),
              [ LitPat (Rust_parser.expr_of_lft_param limpl ("'" ^ n)) ]
              (*arguments*),
              Static ) )
    in
    let pre_lft_tks =
      List.map (fun lft_var -> lft_token_b bind_pat_b lft_var) self_lft_args
    in
    let outlives_asns =
      outlives_preds
      |> List.map @@ fun (r1, r2) ->
         Operation
           ( limpl,
             Eq,
             [
               CallExpr
                 ( limpl,
                   "lifetime_inclusion",
                   [],
                   [],
                   [
                     LitPat (Rust_parser.expr_of_lft_param limpl r2);
                     LitPat (Rust_parser.expr_of_lft_param limpl r1);
                   ],
                   Static );
               True limpl;
             ] )
    in
    let pre_lft_tks = pre_lft_tks @ outlives_asns in
    let post_lft_tks =
      List.map (fun lft_var -> lft_token_b lit_pat_b lft_var) self_lft_args
    in
    let (Some pre) =
      AstAux.list_to_sep_conj
        (List.map (fun e -> (limpl, e)) pre_lft_tks)
        (Some
           (Ast.Sep
              ( ls,
                pre_na_token,
                Ast.CallExpr
                  ( ls,
                    self_ty ^ "_full_borrow_content",
                    self_ty_targs,
                    List.map
                      (fun x -> Ast.LitPat (Var (ls, x)))
                      [ "_t"; "self" ],
                    [],
                    Static ) )))
    in
    List.iter2
      (fun targ tparam ->
        match targ with
        | Ast.IdentTypeExpr (_, None, x) when x = tparam -> ()
        | _ ->
            raise
              (Ast.StaticError
                 ( limpl,
                   "A drop function for a struct type whose type arguments are \
                    not identical to its type parameters is not yet supported",
                   None )))
      self_ty_targs (lft_params @ tparams);
    if
      self_lft_args
      <> List.map (fun x -> TrName.lft_name_without_apostrophe x) lft_params
    then
      raise
        (Ast.StaticError
           ( limpl,
             "A drop function for a struct type whose lifetime arguments are \
              not identical to its lifetime parameters is not yet supported",
             None ));
    let tid = Ast.Var (limpl, "_t") in
    let (Some post) =
      AstAux.list_to_sep_conj
        (List.map (fun e -> (limpl, e)) post_lft_tks)
        (Some
           (Ast.Sep
              ( ls,
                post_na_token,
                List.fold_right
                  (fun ({ name; ty; loc } : Mir.field_def_tr) asn ->
                    match
                      let ty_interp = Mir.interp_of ty in
                      let* points_to_asn =
                        ty_interp.points_to tid
                          (Read (loc, Var (loc, "self"), name))
                          (Some name)
                      in
                      let* own_asn = ty_interp.own tid (Var (loc, name)) in
                      Ok
                        (Ast.Sep
                           (loc, Ast.Sep (loc, points_to_asn, own_asn), asn))
                    with
                    | Ok asn -> asn
                    | Error msg ->
                        raise
                          (Ast.StaticError
                             ( loc,
                               "Could not generate drop postcondition \
                                conjuncts for this field",
                               None )))
                  fds
                  (Ast.CallExpr
                     ( limpl,
                       padding_pred_name self_ty,
                       self_ty_targs,
                       [],
                       [ LitPat (Var (limpl, "self")) ],
                       Static )) )))
    in
    Ok (pre, Rust_parser.mk_outcome_post limpl post post)

  (** makes the mappings used for substituting the MIR level local declaration ids with names closer to variables surface name *)
  let make_var_id_name_maps (loc : Ast.loc) (vdis : Mir.var_debug_info list) =
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
          (*
          Ast.static_error loc
            (Printf.sprintf
               "This function shadows local variable name '%s'; this is not \
                yet supported in VeriFast"
               surf_name)
            None
          *)
          counter := succ !counter;
          let internal_name =
            (*TrName.tag_internal*) surf_name ^ "_" ^ string_of_int !counter
          in
          let env_entry_opt : VF0.var_debug_info option =
            (*Some { internal_name; surf_name }*) None
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
        Ok ("'_" ^ Stdint.Uint128.to_string (CapnpAux.uint128_get id_cpn), loc)
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
    let* ( ( (nonghost_callers_only : bool),
             (fn_type_clause : _ option),
             (pre_post : _ option),
             (terminates : bool) ),
           (assume_correct : bool) ) =
      if unsafe then Ok (VfMirAnnotParser.parse_func_contract loc annots)
      else (
        if contract <> [] then
          raise
            (Ast.StaticError
               ( loc,
                 "An explicit spec on a safe trait required function is not \
                  yet supported",
                 None ));
        let params =
          List.combine arg_names input_infos
          |> List.map (fun (arg_name, ty_info) -> (loc, arg_name, ty_info))
        in
        let result = (loc, output) in
        let* contract =
          gen_contract adt_defs loc
            (List.map TrName.lft_name_without_apostrophe
               (lifetime_params_get_list required_fn_cpn))
            [] [] [] params result
        in
        Ok ((false, None, Some contract, false), false))
    in
    if assume_correct then
      Ast.static_error loc
        "assume_correct does not make sense on trait required functions" None;
    let ret_ty, pre_post =
      if Args.ignore_unwind_paths then
        (ret_ty, Option.map Rust_parser.result_spec_of_outcome_spec pre_post)
      else
        ( Ast.ConstructedTypeExpr
            (Ast.type_expr_loc ret_ty, "fn_outcome", [ ret_ty ]),
          pre_post )
    in
    let decl =
      Ast.Func
        ( loc,
          Ast.Regular,
          (*type params*) [ "Self" ] @ lifetime_params_get_list required_fn_cpn,
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

  let translate_trait (adt_defs : Mir.adt_def_tr list)
      (skip_specless_fns : bool) (trait_cpn : TraitRd.t) =
    let name = TraitRd.name_get trait_cpn in
    let* required_fns =
      CapnpAux.ind_list_get_list (TraitRd.required_fns_get trait_cpn)
    in
    let required_fns =
      if skip_specless_fns then
        required_fns
        |> List.filter (fun required_fn_cpn ->
               not
                 (Capnp.Array.is_empty
                    (TraitRd.RequiredFn.contract_get required_fn_cpn)))
      else required_fns
    in
    ListAux.try_map (translate_trait_required_fn adt_defs name) required_fns

  let decode_predicate (pred_cpn : VfMirStub.Reader.Predicate.t) =
    let open VfMirStub.Reader.Predicate in
    match get pred_cpn with
    | Outlives outlives_pred_cpn ->
        let open Outlives in
        `Outlives
          ( translate_region (region1_get outlives_pred_cpn),
            translate_region (region2_get outlives_pred_cpn) )
    | Trait trait_pred_cpn ->
        let open Trait in
        let args =
          args_get_list trait_pred_cpn |> List.map decode_generic_arg
        in
        `Trait (def_id_get trait_pred_cpn, args)
    | Projection proj_pred_cpn -> `Projection proj_pred_cpn
    | _ -> `Ignored

  let string_of_predicate pred =
    match pred with
    | `Outlives (r1, r2) -> Printf.sprintf "%s : %s" r1 r2
    | `Trait (name, `Type arg :: args) ->
        Printf.sprintf "%s : %s<%s>"
          (string_of_decoded_type arg)
          name
          (String.concat ", " (List.map string_of_generic_arg args))
    | `Ignored -> "(ignored)"
    | _ -> "(unknown)"

  let compute_send_tparams preds =
    preds
    |> Util.flatmap (function
         | `Trait ("std::marker::Send", [ `Type (`Param tparam) ]) -> [ tparam ]
         | _ -> [])

  let compute_sync_tparams preds =
    preds
    |> Util.flatmap (function
         | `Trait ("std::marker::Sync", [ `Type (`Param tparam) ]) -> [ tparam ]
         | _ -> [])

  let translate_projection_pred (loc : Ast.loc)
      (proj_pred_cpn : VfMirStub.Reader.Predicate.Projection.t) =
    let open VfMirStub.Reader.Predicate.Projection in
    let* assoc_type_def_id, tparam :: trait_args =
      let projection_term_cpn = projection_term_get proj_pred_cpn in
      let open AliasTerm in
      let* trait_args =
        args_get_list projection_term_cpn
        |> ListAux.try_map (fun genarg_cpn ->
               let* arg = translate_generic_arg genarg_cpn loc in
               match arg with
               | Mir.GenArgLifetime _ -> assert false
               | Mir.GenArgType ty -> Ok (Mir.basic_type_of ty)
               | Mir.GenArgConst -> assert false)
      in
      Ok (def_id_get projection_term_cpn, trait_args)
    in
    let trait_name, assoc_type_name =
      String.rindex assoc_type_def_id ':' |> fun i ->
      ( String.sub assoc_type_def_id 0 (i - 1),
        String.sub assoc_type_def_id (i + 1)
          (String.length assoc_type_def_id - i - 1) )
    in
    let* rhs =
      let term = term_get proj_pred_cpn in
      let open Term in
      match get term with
      | Ty ty_cpn ->
          let* ty = translate_ty ty_cpn loc in
          Ok (Mir.basic_type_of ty)
      | Const const_cpn -> assert false
    in
    Ok
      (Ast.ExprStmt
         (CallExpr
            ( loc,
              "#register_type_projection_equality",
              [
                ProjectionTypeExpr
                  (loc, tparam, trait_name, trait_args, assoc_type_name);
                rhs;
              ],
              [],
              [],
              Static )))

  let translate_body (body_tr_defs_ctx : body_tr_defs_ctx) (body_cpn : BodyRd.t)
      =
    let open BodyRd in
    let var_id_trs_map_ref = ref [] in
    let* fn_sig_loc = translate_span_data (fn_sig_span_get body_cpn) in
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
    let env_map, trs_map = make_var_id_name_maps imp_loc vdis in
    let _ = var_id_trs_map_ref := trs_map in
    let def_kind_cpn = def_kind_get body_cpn in
    let def_kind = DefKind.get def_kind_cpn in
    match def_kind with
    | DefKind.Fn ->
        let def_path = def_path_get body_cpn in
        let name = TrName.translate_def_path def_path in
        let moduleName = module_def_path_get body_cpn in
        (* print_endline ("Translating Mod: " ^ moduleName ^ " --- Body: " ^ name); *)
        let split_name = TrName.split_def_path moduleName name in
        let* impl_block_gens =
          match impl_block_hir_generics_get body_cpn |> OptionRd.get with
          | Nothing -> Ok []
          | Something hir_gens_cpn_ptr ->
              let hir_gens_cpn = VfMirStub.Reader.of_pointer hir_gens_cpn_ptr in
              let* gens, gens_loc = translate_hir_generics hir_gens_cpn in
              Ok gens
        in
        let hir_gens_cpn = hir_generics_get body_cpn in
        let* gens, gens_loc = translate_hir_generics hir_gens_cpn in
        let early_bound_generic_param_names =
          generics_get_list body_cpn
          |> List.map @@ fun generic_param ->
             VfMirStub.Reader.GenericParamDef.name_get generic_param
        in
        let early_gens, late_gens =
          List.partition
            (fun (name, kind, loc) ->
              List.mem name early_bound_generic_param_names)
            gens
        in
        let gens = impl_block_gens @ early_gens @ late_gens in
        let vf_tparams = List.map (fun (name, _, _) -> name) gens in
        let* primed_lft_param_names =
          ListAux.try_filter_map
            (fun (name, kind, loc) ->
              if kind = Hir.GenParamLifetime then Ok (Some name) else Ok None)
            gens
        in
        let lft_param_names =
          List.map TrName.lft_name_without_apostrophe primed_lft_param_names
        in
        let vf_tparams =
          if is_trait_fn_get body_cpn then "Self" :: vf_tparams else vf_tparams
        in
        let preds =
          impl_block_predicates_get_list body_cpn @ predicates_get_list body_cpn
          |> List.map decode_predicate
        in
        let projection_preds =
          preds
          |> Util.flatmap (function
               | `Projection proj_pred_cpn -> [ proj_pred_cpn ]
               | _ -> [])
        in
        let* projection_pred_stmts =
          ListAux.try_map
            (translate_projection_pred fn_sig_loc)
            projection_preds
        in
        let outlives_preds =
          preds
          |> Util.flatmap (function
               | `Outlives (r1, r2) -> [ (r1, r2) ]
               | _ -> [])
        in
        let implicit_outlives_preds =
          output_get body_cpn :: inputs_get_list body_cpn
          |> Util.flatmap @@ fun ty_cpn ->
             ty_cpn |> decode_ty |> extract_implicit_outlives_preds []
        in
        let outlives_preds = implicit_outlives_preds @ outlives_preds in
        let send_tparams = compute_send_tparams preds in
        let sync_tparams = compute_sync_tparams preds in
        let inputs = inputs_get_list body_cpn in
        let arg_count = List.length inputs in
        let local_decls_cpn = local_decls_get_list body_cpn in
        let* local_decls =
          ListAux.try_map translate_local_decl local_decls_cpn
        in
        (* There should always be a return place for each function *)
        let (ret_place_decl :: local_decls) = local_decls in
        let* ret_ty_info =
          translate_ty (output_get body_cpn) ret_place_decl.loc
        in
        let ret_place_decl = { ret_place_decl with ty = lazy ret_ty_info } in
        let ({
               mutability = ret_mut;
               id = ret_place_id;
               ty = (lazy ret_ty_info);
               loc = ret_place_loc;
             }
              : Mir.local_decl) =
          ret_place_decl
        in
        let ret_ty = Mir.basic_type_of ret_ty_info in
        let param_decls, local_decls =
          ListAux.partitioni (fun idx _ -> idx < arg_count) local_decls
        in
        let* param_tys =
          ListAux.try_map
            (fun (ty_cpn, ({ loc } : Mir.local_decl)) ->
              translate_ty ty_cpn loc)
            (List.combine inputs param_decls)
        in
        let param_decls =
          List.map2
            (fun (decl : Mir.local_decl) ty -> (decl.loc, decl.id, ty))
            param_decls param_tys
        in
        let vf_param_decls =
          List.map
            (fun (loc, id, ty_info) ->
              let ty = Mir.basic_type_of ty_info in
              (ty, id))
            param_decls
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
                let ((_, _, self_ty) :: _) = param_decls in
                let ( PtrTypeExpr
                        ( _,
                          StructTypeExpr (_, Some self_ty, _, _, self_ty_targs)
                        )
                    | RustRefTypeExpr
                        ( _,
                          _,
                          _,
                          StructTypeExpr (_, Some self_ty, _, _, self_ty_targs)
                        ) ) =
                  Mir.basic_type_of self_ty
                in
                let (input0 :: _) = inputs_get_list body_cpn in
                let self_gen_args =
                  match decode_ty input0 with
                  | `Ref (_, _, `Adt (_, _, self_gen_args)) -> self_gen_args
                  | _ -> assert false
                in
                let self_lft_args =
                  Util.flatmap
                    (function
                      | `Lifetime name ->
                          [ TrName.lft_name_without_apostrophe name ]
                      | _ -> [])
                    self_gen_args
                in
                gen_drop_contract body_tr_defs_ctx.adt_defs self_ty
                  self_ty_targs self_lft_args fn_sig_loc
              else
                gen_contract body_tr_defs_ctx.adt_defs fn_sig_loc
                  lft_param_names outlives_preds send_tparams sync_tparams
                  param_decls
                  (ret_place_loc, ret_ty_info)
            in
            let contract_template =
              (false, None, Some pre_post_template, false)
            in
            match contract_opt with
            | None -> Ok (None, (contract_template, false))
            | Some contract -> Ok (Some contract_template, contract)
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
              (*type params*) vf_tparams,
              Some
                (if TranslatorArgs.ignore_unwind_paths then ret_ty
                 else
                   Ast.ConstructedTypeExpr
                     (Ast.type_expr_loc ret_ty, "fn_outcome", [ ret_ty ])),
              name,
              vf_param_decls,
              nonghost_callers_only,
              fn_type_clause,
              (if TranslatorArgs.ignore_unwind_paths then
                 Option.map Rust_parser.result_spec_of_outcome_spec pre_post
               else pre_post),
              terminates,
              body,
              (*virtual*) false,
              (*overrides*) [] )
        in
        let contract, assume_false = contract in
        let* body =
          if assume_false then
            Ok
              (mk_fn_decl contract
                 (Some
                    ( [
                        Ast.PureStmt
                          ( loc,
                            ExprStmt
                              (CallExpr
                                 ( loc,
                                   "assume",
                                   [],
                                   [],
                                   [ LitPat (False loc) ],
                                   Static )) );
                      ],
                      closing_cbrace_loc )))
          else
            let vf_local_decls =
              List.map translate_to_vf_local_decl (ret_place_decl :: local_decls)
            in
            let bblocks_cpn = basic_blocks_get_list body_cpn in
            let* bblocks =
              ListAux.try_filter_map
                (fun bblock_cpn ->
                  translate_basic_block ret_place_id bblock_cpn)
                bblocks_cpn
            in
            let toplevel_blocks = find_blocks bblocks in
            let vf_bblocks =
              translate_basic_blocks_to_stmts toplevel_blocks []
            in
            Ok
              (mk_fn_decl contract
                 (Some
                    ( projection_pred_stmts @ vf_local_decls @ vf_bblocks,
                      closing_cbrace_loc )))
        in
        let body_sig_opt =
          match contract_template_opt with
          | None -> None
          | Some contract_template ->
              let body_sig = mk_fn_decl contract_template None in
              Some (split_name, body_sig)
        in
        Ok
          ( body_sig_opt,
            (split_name, body),
            ({ id = loc; info = env_map } : VF0.debug_info_rust_fe) )
    | DefKind.AssocFn -> failwith "Todo: MIR Body kind AssocFn"
    | _ -> Error (`TrBodyFatal "Unknown MIR Body kind")

  let translate_visibility (vis_cpn : VisibilityRd.t) =
    let open VisibilityRd in
    match get vis_cpn with
    | Public -> Ok Mir.Public
    | Restricted -> Ok Mir.Restricted
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
    let open Mir in
    Ok Mir.{ loc; name; fields }

  (* TODO: If `<T>.own` is precise make `<T>.fbc` precise too.
     Note that it is only helpful if VeriFast auto open/close precise predicates
     that are made by predicate constructors. *)
  let gen_adt_full_borrow_content adt_kind name tparams lft_params
      (variants : Mir.variant_def_tr list) adt_def_loc =
    let open Ast in
    match adt_kind with
    | Mir.Enum | Mir.Union ->
        failwith "Todo: Gen ADT full borrow content for Enum or Union"
    | Mir.Struct ->
        let fbor_content_name = name ^ "_full_borrow_content" in
        let tid_param_name = "tid" in
        let ptr_param_name = "l" in
        let vf_tparams = lft_params @ tparams in
        let fbor_content_params =
          [
            ( IdentTypeExpr (adt_def_loc, None (*package name*), "thread_id_t"),
              tid_param_name );
            ( PtrTypeExpr
                ( adt_def_loc,
                  StructTypeExpr
                    ( adt_def_loc,
                      Some name,
                      None,
                      [],
                      List.map
                        (fun x -> IdentTypeExpr (adt_def_loc, None, x))
                        vf_tparams ) ),
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
          [
            LitPat (Var (adt_def_loc, tid_param_name));
            LitPat
              (CastExpr
                 ( adt_def_loc,
                   Ast.StructTypeExpr
                     ( adt_def_loc,
                       Some name,
                       None,
                       [],
                       List.map
                         (fun x -> IdentTypeExpr (adt_def_loc, None, x))
                         vf_tparams ),
                   InitializerList
                     ( adt_def_loc,
                       List.map
                         (fun (f : Mir.field_def_tr) ->
                           (None, Var (f.loc, f.name)))
                         fields ) ));
          ]
        in
        let own_pred =
          CallExpr
            ( adt_def_loc,
              name ^ "_own",
              (*type arguments*)
              List.map
                (fun x -> IdentTypeExpr (adt_def_loc, None, x))
                vf_tparams,
              (*indices*) [],
              (*arguments*)
              own_args,
              if vf_tparams = [] then PredFamCall else PredCtorCall )
        in
        let padding_pred =
          CallExpr
            ( adt_def_loc,
              padding_pred_name name,
              List.map
                (fun x -> IdentTypeExpr (adt_def_loc, None, x))
                vf_tparams,
              [],
              [ LitPat (Var (adt_def_loc, ptr_param_name)) ],
              PredFamCall )
        in
        let (Some body_asn) =
          AstAux.list_to_sep_conj field_chunks
            (Some (Ast.Sep (adt_def_loc, padding_pred, own_pred)))
        in
        let fbor_content_pred_ctor =
          PredCtorDecl
            ( adt_def_loc,
              fbor_content_name,
              vf_tparams (* type parameters*),
              fbor_content_params,
              [],
              None
              (* (Some n) means the predicate is precise and the first n parameters are input parameters *),
              body_asn )
        in
        Ok fbor_content_pred_ctor

  let add_type_interp_asns loc tparams asn =
    List.fold_right
      (fun x asn ->
        Ast.Sep
          ( loc,
            CallExpr
              ( loc,
                "type_interp",
                [ IdentTypeExpr (loc, None, x) ],
                [],
                [],
                Static ),
            asn ))
      tparams asn

  let add_send_asns loc send_tparams asn =
    List.fold_right
      (fun x asn -> Ast.Sep (loc, mk_send_asn loc x, asn))
      send_tparams asn

  let add_sync_asns loc sync_tparams asn =
    List.fold_right
      (fun x asn -> Ast.Sep (loc, mk_sync_asn loc x, asn))
      sync_tparams asn

  let gen_send_proof_oblig adt_def_loc name tparams vf_tparams send_tparams
      sync_tparams =
    let open Ast in
    let params = [ (IdentTypeExpr (adt_def_loc, None, "thread_id_t"), "t1") ] in
    let tparams_targs =
      List.map (fun x -> IdentTypeExpr (adt_def_loc, None, x)) vf_tparams
    in
    let pre =
      CallExpr
        ( adt_def_loc,
          name ^ "_own",
          tparams_targs,
          [],
          [ VarPat (adt_def_loc, "t0"); VarPat (adt_def_loc, "v") ],
          if vf_tparams = [] then PredFamCall else PredCtorCall )
    in
    let pre =
      add_type_interp_asns adt_def_loc tparams
        (add_send_asns adt_def_loc send_tparams
           (add_sync_asns adt_def_loc sync_tparams pre))
    in
    let post =
      CallExpr
        ( adt_def_loc,
          name ^ "_own",
          tparams_targs,
          [],
          [ LitPat (Var (adt_def_loc, "t1")); LitPat (Var (adt_def_loc, "v")) ],
          if vf_tparams = [] then PredFamCall else PredCtorCall )
    in
    let post = add_type_interp_asns adt_def_loc tparams post in
    Func
      ( adt_def_loc,
        Lemma
          ( false
            (*indicates whether an axiom should be generated for this lemma*),
            None (*trigger*) ),
        vf_tparams (*type parameters*),
        None (*return type*),
        name ^ "_send",
        params,
        false (*nonghost_callers_only*),
        None
        (*implemented function type, with function type type arguments and function type arguments*),
        Some (pre, ("result", post)) (*contract*),
        false (*terminates*),
        None (*body*),
        false (*virtual*),
        [] (*overrides*) )

  let gen_own_variance_proof_oblig adt_def_loc name lft_params tparams variances
      fds =
    let open Ast in
    assert (List.length variances = List.length lft_params + List.length tparams);
    let lft_param_variances, tparam_variances =
      Util.take_drop (List.length lft_params) variances
    in
    let lft_params01, all_lft_params_and_pres =
      List.split
        (List.map2
           (fun x variance ->
             if variance = VarianceRd.Invariant then ((x, x), ([ x ], []))
             else
               let x0 = x ^ "0" in
               let x1 = x ^ "1" in
               ( (x0, x1),
                 ( [ x0; x1 ],
                   match variance with
                   | Covariant ->
                       [
                         ExprAsn
                           ( adt_def_loc,
                             CallExpr
                               ( adt_def_loc,
                                 "lifetime_inclusion",
                                 [],
                                 [],
                                 [
                                   LitPat
                                     (Rust_parser.expr_of_lft_param adt_def_loc
                                        x1);
                                   LitPat
                                     (Rust_parser.expr_of_lft_param adt_def_loc
                                        x0);
                                 ],
                                 Static ) );
                       ]
                   | Contravariant ->
                       [
                         ExprAsn
                           ( adt_def_loc,
                             CallExpr
                               ( adt_def_loc,
                                 "lifetime_inclusion",
                                 [],
                                 [],
                                 [
                                   LitPat
                                     (Rust_parser.expr_of_lft_param adt_def_loc
                                        x0);
                                   LitPat
                                     (Rust_parser.expr_of_lft_param adt_def_loc
                                        x1);
                                 ],
                                 Static ) );
                       ]
                   | _ -> [] ) ))
           lft_params lft_param_variances)
    in
    let all_lft_params, lft_param_pres = List.split all_lft_params_and_pres in
    let all_lft_params = List.flatten all_lft_params in
    let lft_param_pres = List.flatten lft_param_pres in
    let lft_params0, lft_params1 = List.split lft_params01 in
    let tparams01, all_tparams_and_pres =
      List.split
        (List.map2
           (fun x variance ->
             if variance = VarianceRd.Invariant then ((x, x), ([ x ], []))
             else
               let x0 = x ^ "0" in
               let x1 = x ^ "1" in
               ( (x0, x1),
                 ( [ x0; x1 ],
                   match variance with
                   | Covariant ->
                       [
                         ExprAsn
                           ( adt_def_loc,
                             CallExpr
                               ( adt_def_loc,
                                 "is_subtype_of",
                                 [
                                   IdentTypeExpr (adt_def_loc, None, x0);
                                   IdentTypeExpr (adt_def_loc, None, x1);
                                 ],
                                 [],
                                 [],
                                 Static ) );
                       ]
                   | Contravariant ->
                       [
                         ExprAsn
                           ( adt_def_loc,
                             CallExpr
                               ( adt_def_loc,
                                 "is_subtype_of",
                                 [
                                   IdentTypeExpr (adt_def_loc, None, x1);
                                   IdentTypeExpr (adt_def_loc, None, x0);
                                 ],
                                 [],
                                 [],
                                 Static ) );
                       ]
                   | _ -> [] ) ))
           tparams tparam_variances)
    in
    let all_tparams, tparam_pres = List.split all_tparams_and_pres in
    let all_tparams = List.flatten all_tparams in
    let tparam_pres = List.flatten tparam_pres in
    let tparams0, tparams1 = List.split tparams01 in
    let vf_tparams = all_lft_params @ all_tparams in
    let vf_tparams0 = lft_params0 @ tparams0 in
    let tparams_targs0 =
      List.map (fun x -> IdentTypeExpr (adt_def_loc, None, x)) vf_tparams0
    in
    let vf_tparams1 = lft_params1 @ tparams1 in
    let tparams_targs1 =
      List.map (fun x -> IdentTypeExpr (adt_def_loc, None, x)) vf_tparams1
    in
    let pre =
      CallExpr
        ( adt_def_loc,
          name ^ "_own",
          tparams_targs0,
          [],
          [ VarPat (adt_def_loc, "t"); VarPat (adt_def_loc, "v") ],
          if vf_tparams = [] then PredFamCall else PredCtorCall )
    in
    let pre =
      List.fold_left (fun a1 a2 -> Sep (adt_def_loc, a1, a2)) pre lft_param_pres
    in
    let pre =
      List.fold_left (fun a1 a2 -> Sep (adt_def_loc, a1, a2)) pre tparam_pres
    in
    let pre = add_type_interp_asns adt_def_loc all_tparams pre in
    let tp0 =
      StructTypeExpr (adt_def_loc, Some name, None, [], tparams_targs0)
    in
    let tp1 =
      StructTypeExpr (adt_def_loc, Some name, None, [], tparams_targs1)
    in
    let init_for_fd ({ name = f; ty; vis; loc = l } : Mir.field_def_tr) =
      let e =
        match Mir.basic_type_of ty with
        | PtrTypeExpr (_, _) | RustRefTypeExpr (_, _, _, _) ->
            CastExpr
              ( l,
                ManifestTypeExpr (adt_def_loc, PtrType Void),
                Select (l, Var (l, "v"), f) )
        | _ ->
            CallExpr
              ( l,
                "upcast",
                [],
                [],
                [ LitPat (Select (l, Var (l, "v"), f)) ],
                Static )
      in
      (Some (l, f), e)
    in
    let upcast_call =
      CallExpr
        ( adt_def_loc,
          "upcast",
          [ tp0; tp1 ],
          [],
          [ LitPat (Var (adt_def_loc, "v")) ],
          Static )
    in
    let upcast_expr =
      CastExpr
        ( adt_def_loc,
          tp1,
          InitializerList (adt_def_loc, List.map init_for_fd fds) )
    in
    let post =
      CallExpr
        ( adt_def_loc,
          name ^ "_own",
          tparams_targs1,
          [],
          [ LitPat (Var (adt_def_loc, "t")); LitPat upcast_expr ],
          if vf_tparams = [] then PredFamCall else PredCtorCall )
    in
    let post = add_type_interp_asns adt_def_loc all_tparams post in
    ( [
        Func
          ( adt_def_loc,
            Lemma
              ( false
                (*indicates whether an axiom should be generated for this lemma*),
                None (*trigger*) ),
            vf_tparams (*type parameters*),
            None (*return type*),
            name ^ "_own_mono",
            [],
            false (*nonghost_callers_only*),
            None
            (*implemented function type, with function type type arguments and function type arguments*),
            Some (pre, ("result", post)) (*contract*),
            false (*terminates*),
            None (*body*),
            false (*virtual*),
            [] (*overrides*) );
      ],
      let post =
        ExprAsn
          ( adt_def_loc,
            Operation (adt_def_loc, Eq, [ upcast_call; upcast_expr ]) )
      in
      [
        Func
          ( adt_def_loc,
            Lemma
              ( false
                (*indicates whether an axiom should be generated for this lemma*),
                None (*trigger*) ),
            vf_tparams (*type parameters*),
            None (*return type*),
            name ^ "_upcast",
            [ (tp0, "v") ],
            false (*nonghost_callers_only*),
            None
            (*implemented function type, with function type type arguments and function type arguments*),
            Some (EmpAsn adt_def_loc, ("result", post)) (*contract*),
            false (*terminates*),
            Some
              ( [
                  ExprStmt
                    (CallExpr
                       ( adt_def_loc,
                         "#assume",
                         [],
                         [],
                         [ LitPat (False adt_def_loc) ],
                         Static ));
                ],
                adt_def_loc )
            (*body*),
            false (*virtual*),
            [] (*overrides*) );
      ] )

  let gen_sync_proof_oblig adt_def_loc name lft_params tparams sync_tparams =
    let open Ast in
    let vf_tparams = lft_params @ tparams in
    let tparams_targs =
      List.map (fun x -> IdentTypeExpr (adt_def_loc, None, x)) vf_tparams
    in
    let params = [ (IdentTypeExpr (adt_def_loc, None, "thread_id_t"), "t1") ] in
    let pre =
      CoefAsn
        ( adt_def_loc,
          DummyPat,
          CallExpr
            ( adt_def_loc,
              name ^ "_share",
              tparams_targs,
              [],
              [
                VarPat (adt_def_loc, "k");
                VarPat (adt_def_loc, "t0");
                VarPat (adt_def_loc, "l");
              ],
              if vf_tparams = [] then PredFamCall else PredCtorCall ) )
    in
    let pre =
      add_type_interp_asns adt_def_loc tparams
        (add_sync_asns adt_def_loc sync_tparams pre)
    in
    let post =
      CoefAsn
        ( adt_def_loc,
          DummyPat,
          CallExpr
            ( adt_def_loc,
              name ^ "_share",
              tparams_targs,
              [],
              [
                LitPat (Var (adt_def_loc, "k"));
                LitPat (Var (adt_def_loc, "t1"));
                LitPat (Var (adt_def_loc, "l"));
              ],
              if vf_tparams = [] then PredFamCall else PredCtorCall ) )
    in
    let post = add_type_interp_asns adt_def_loc tparams post in
    Func
      ( adt_def_loc,
        Lemma
          ( false
            (*indicates whether an axiom should be generated for this lemma*),
            None (*trigger*) ),
        vf_tparams (*type parameters*),
        None (*return type*),
        name ^ "_sync",
        params,
        false (*nonghost_callers_only*),
        None
        (*implemented function type, with function type type arguments and function type arguments*),
        Some (pre, ("result", post)) (*contract*),
        false (*terminates*),
        None (*body*),
        false (*virtual*),
        [] (*overrides*) )

  let gen_share_proof_obligs adt_def lft_params tparams send_tparams sync_preds
      =
    let open Ast in
    let* adt_kind = Mir.decl_mir_adt_kind adt_def in
    match adt_kind with
    | Mir.Enum | Mir.Union ->
        failwith "Todo: Gen proof obligs for Enum or Union"
    | Mir.Struct ->
        let adt_def_loc = AstAux.decl_loc adt_def in
        let tparams_targs =
          List.map
            (fun x -> IdentTypeExpr (adt_def_loc, None, x))
            (lft_params @ tparams)
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
                  if tparams_targs = [] then PredFamCall else PredCtorCall ) )
        in
        let pre =
          add_type_interp_asns adt_def_loc tparams
            (add_send_asns adt_def_loc send_tparams
               (Sep (adt_def_loc, lft_inc_asn, shr_asn "k")))
        in
        let post = add_type_interp_asns adt_def_loc tparams (shr_asn "k1") in
        let share_mono_po =
          Func
            ( adt_def_loc,
              Lemma
                ( false
                  (*indicates whether an axiom should be generated for this lemma*),
                  None (*trigger*) ),
              lft_params @ tparams (*type parameters*),
              None (*return type*),
              name ^ "_share_mono",
              params,
              false (*nonghost_callers_only*),
              None
              (*implemented function type, with function type type arguments and function type arguments*),
              Some (pre, ("result", post)) (*contract*),
              false (*terminates*),
              None (*body*),
              false (*virtual*),
              [] (*overrides*) )
        in
        (*TY-SHR*)
        let params =
          [ lft_param "k"; thread_id_param "t"; void_ptr_param "l" ]
        in
        let atomic_mask_token mask =
          CallExpr
            ( adt_def_loc,
              "atomic_mask",
              (*type arguments*) [],
              (*indices*) [],
              (*arguments*)
              [ lpat_var mask ],
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
                 atomic_mask_token "MaskTop";
                 fbor_pred;
                 lft_token (VarPat (adt_def_loc, "q"));
                 Operation
                   ( adt_def_loc,
                     Eq,
                     [
                       CallExpr
                         ( adt_def_loc,
                           "ref_origin",
                           [],
                           [],
                           [ LitPat (Var (adt_def_loc, "l")) ],
                           Static );
                       Var (adt_def_loc, "l");
                     ] );
               ])
            None
        in
        let pre =
          add_type_interp_asns adt_def_loc tparams
            (add_send_asns adt_def_loc send_tparams pre)
        in
        let share_pred l =
          CoefAsn
            ( adt_def_loc,
              DummyPat,
              CallExpr
                ( adt_def_loc,
                  name ^ "_share",
                  (*type arguments*) tparams_targs,
                  (*indices*) [],
                  (*arguments*)
                  List.map lpat_var [ "k"; "t"; l ],
                  if tparams_targs = [] then PredFamCall else PredCtorCall ) )
        in
        let (Some post) =
          AstAux.list_to_sep_conj
            (List.map
               (fun asn -> (adt_def_loc, asn))
               [
                 atomic_mask_token "MaskTop";
                 share_pred "l";
                 lft_token (lpat_var "q");
               ])
            None
        in
        let post = add_type_interp_asns adt_def_loc tparams post in
        let share_po =
          Func
            ( adt_def_loc,
              Lemma
                ( false
                  (*indicates whether an axiom should be generated for this lemma*),
                  None (*trigger*) ),
              lft_params @ tparams (*type parameters*),
              None (*return type*),
              name ^ "_share_full",
              params,
              false (*nonghost_callers_only*),
              None
              (*implemented function type, with function type type arguments and function type arguments*),
              Some (pre, ("result", post)) (*contract*),
              false (*terminates*),
              None (*body*),
              false (*virtual*),
              [] (*overrides*) )
        in
        (* init_ref_S *)
        let ref_init_perm =
          CallExpr
            ( adt_def_loc,
              "ref_init_perm",
              [],
              [],
              [ lpat_var "p"; VarPat (adt_def_loc, "x") ],
              Static )
        in
        let pre_shr_asn =
          CoefAsn
            ( adt_def_loc,
              DummyPat,
              CallExpr
                ( adt_def_loc,
                  name ^ "_share",
                  (*type arguments*) tparams_targs,
                  (*indices*) [],
                  (*arguments*)
                  [
                    VarPat (adt_def_loc, "k");
                    VarPat (adt_def_loc, "t");
                    lpat_var "x";
                  ],
                  if tparams_targs = [] then PredFamCall else PredCtorCall ) )
        in
        let (Some pre) =
          AstAux.list_to_sep_conj
            (List.map
               (fun asn -> (adt_def_loc, asn))
               [
                 atomic_mask_token "Nlft";
                 ref_init_perm;
                 pre_shr_asn;
                 lft_token (VarPat (adt_def_loc, "q"));
               ])
            None
        in
        let pre =
          add_type_interp_asns adt_def_loc tparams
            (add_send_asns adt_def_loc send_tparams pre)
        in
        let post_shr_asn =
          CoefAsn
            ( adt_def_loc,
              DummyPat,
              CallExpr
                ( adt_def_loc,
                  name ^ "_share",
                  (*type arguments*) tparams_targs,
                  (*indices*) [],
                  (*arguments*)
                  [ lpat_var "k"; lpat_var "t"; lpat_var "p" ],
                  if tparams_targs = [] then PredFamCall else PredCtorCall ) )
        in
        let ref_initialized_asn =
          CoefAsn
            ( adt_def_loc,
              DummyPat,
              CallExpr
                ( adt_def_loc,
                  "frac_borrow",
                  [],
                  [],
                  [
                    lpat_var "k";
                    LitPat
                      (CallExpr
                         ( adt_def_loc,
                           "ref_initialized_",
                           [],
                           [],
                           [ lpat_var "p" ],
                           Static ));
                  ],
                  Static ) )
        in
        let (Some post) =
          AstAux.list_to_sep_conj
            (List.map
               (fun asn -> (adt_def_loc, asn))
               [
                 atomic_mask_token "Nlft";
                 lft_token (lpat_var "q");
                 post_shr_asn;
                 ref_initialized_asn;
               ])
            None
        in
        let post = add_type_interp_asns adt_def_loc tparams post in
        let init_ref_po =
          Func
            ( adt_def_loc,
              Lemma
                ( false
                  (*indicates whether an axiom should be generated for this lemma*),
                  None (*trigger*) ),
              lft_params @ tparams (*type parameters*),
              None (*return type*),
              qualified_derived_name "init_ref_%s" name,
              [
                ( PtrTypeExpr
                    ( adt_def_loc,
                      StructTypeExpr
                        (adt_def_loc, Some name, None, [], tparams_targs) ),
                  "p" );
              ],
              false (*nonghost_callers_only*),
              None
              (*implemented function type, with function type type arguments and function type arguments*),
              Some (pre, ("result", post)) (*contract*),
              false (*terminates*),
              None (*body*),
              false (*virtual*),
              [] (*overrides*) )
        in
        let sync_pos =
          match sync_preds with
          | None -> []
          | Some sync_preds ->
              let sync_tparams =
                List.filter
                  (fun x -> List.mem (x, "std::marker::Sync") sync_preds)
                  tparams
              in
              [
                gen_sync_proof_oblig adt_def_loc name lft_params tparams
                  sync_tparams;
              ]
        in
        Ok ([ share_mono_po; share_po; init_ref_po ] @ sync_pos)

  type trait_impl = {
    trait_impl_cpn : TraitImplRd.t;
    loc : Ast.loc;
    is_unsafe : bool;
    is_negative : bool;
    of_trait : string;
    self_ty : string;
    items : string list;
  }

  let sep loc = function
    | [] -> Ast.True loc
    | x :: xs -> List.fold_left (fun a1 a2 -> Ast.Sep (loc, a1, a2)) x xs

  let default_struct_own (loc : Ast.loc) (fds : Mir.field_def_tr list)
      (t : string) (v : string) =
    let field_own_asns =
      fds
      |> List.map @@ fun (fd : Mir.field_def_tr) ->
         let interp = Mir.interp_of fd.ty in
         match
           interp.own
             (Ast.Var (loc, "t"))
             (Ast.Select (loc, Ast.Var (loc, "v"), fd.name))
         with
         | Ok asn -> asn
         | Error msg ->
             Ast.static_error loc
               (Printf.sprintf
                  "Error while building default .own predicate conjunct for \
                   field %s: %s"
                  fd.name msg)
               None
    in
    sep loc field_own_asns

  let pointer_within_limits_asn loc l =
    Ast.Operation
      ( loc,
        Eq,
        [
          Ast.CallExpr
            (loc, "pointer_within_limits", [], [], [ Ast.LitPat l ], Ast.Static);
          Ast.True loc;
        ] )

  let default_struct_share (loc : Ast.loc) (fds : Mir.field_def_tr list)
      (k : string) (t : string) (l : string) =
    let field_share_asns =
      fds
      |> List.map @@ fun (fd : Mir.field_def_tr) ->
         let interp = Mir.interp_of fd.ty in
         let lf =
           Ast.AddressOf (loc, Read (loc, Ast.Var (loc, "l"), fd.name))
         in
         match interp.shr (Ast.Var (loc, "k")) (Ast.Var (loc, "t")) lf with
         | Ok asn -> Ast.Sep (loc, pointer_within_limits_asn loc lf, asn)
         | Error msg ->
             Ast.static_error loc
               (Printf.sprintf
                  "Error while building default .share predicate conjunct for \
                   field %s: %s"
                  fd.name msg)
               None
    in
    sep loc field_share_asns

  let translate_adt_def (ghost_decl_map : (string * Ast.decl) list)
      (ghost_decls : Ast.decl list) (trait_impls : trait_impl list)
      (adt_def_cpn : AdtDefRd.t) =
    let open AdtDefRd in
    let id_cpn = id_get adt_def_cpn in
    let def_path = translate_adt_def_id id_cpn in
    if TrName.is_from_std_lib def_path then Ok None
    else
      let name = TrName.translate_def_path def_path in
      let* generics =
        hir_generics_get adt_def_cpn
        |> HirGenericsRd.params_get_list
        |> ListAux.try_map @@ fun param_cpn ->
           let* l =
             translate_span_data (HirGenericParamRd.span_get param_cpn)
           in
           let name =
             match
               HirGenericParamRd.name_get param_cpn |> HirGenericParamNameRd.get
             with
             | Plain ident -> IdentRd.name_get ident |> SymbolRd.name_get
             | Fresh _ ->
                 raise
                   (Ast.StaticError
                      ( l,
                        "Structs with inferred type parameters are not yet \
                         supported",
                        None ))
           in
           match
             HirGenericParamRd.kind_get param_cpn |> HirGenericParamKindRd.get
           with
           | Lifetime -> Ok (`Lifetime name)
           | Type -> Ok (`Type name)
           | Const ->
               raise
                 (Ast.StaticError
                    ( l,
                      "Structs with const parameters are not yet supported",
                      None ))
      in
      let tparams =
        Util.flatmap (function `Type x -> [ x ] | _ -> []) generics
      in
      let lft_params =
        Util.flatmap (function `Lifetime x -> [ x ] | _ -> []) generics
      in
      let vf_tparams = lft_params @ tparams in
      let variances = variances_get_list adt_def_cpn in
      let variants_cpn = variants_get_list adt_def_cpn in
      let* variants = ListAux.try_map translate_variant_def variants_cpn in
      let span_cpn = def_span_get adt_def_cpn in
      let* def_loc = translate_span_data span_cpn in
      let preds =
        predicates_get_list adt_def_cpn |> List.map decode_predicate
      in
      let send_tparams = compute_send_tparams preds in
      let tparams_targs =
        List.map (fun x -> Ast.IdentTypeExpr (def_loc, None, x)) vf_tparams
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
                  vf_tparams,
                  Some
                    ( (*base_spec list*) [],
                      (*field list*) field_defs,
                      (*instance_pred_decl list*) [],
                      (*is polymorphic*) false ),
                  (*struct_attr list*)
                  if is_repr_c_get adt_def_cpn then [ ReprC ] else [] )
            in
            let struct_typedef_aux =
              Ast.TypedefDecl
                ( def_loc,
                  StructTypeExpr (def_loc, Some name, None, [], tparams_targs),
                  name,
                  lft_params @ tparams )
            in
            Ok (Mir.Struct, fds, struct_decl, [ struct_typedef_aux ])
        | EnumKind ->
            let ctors =
              (* VeriFast does not support zero-ctor inductives, so add a dummy ctor. *)
              if variants = [] then [ Ast.Ctor (def_loc, name ^ "::Dummy", []) ]
              else
                variants
                |> List.map @@ fun Mir.{ loc; name = variant_name; fields } ->
                   let ps =
                     fields
                     |> List.map @@ fun Mir.{ name; ty } ->
                        (name, Mir.basic_type_of ty)
                   in
                   Ast.Ctor (loc, name ^ "::" ^ variant_name, ps)
            in
            let decl = Ast.Inductive (def_loc, name, tparams, ctors) in
            Ok (Mir.Enum, [], decl, [])
        | UnionKind -> failwith "Todo: AdtDef::Union"
        | Undefined _ -> Error (`TrAdtDef "Unknown ADT kind")
      in
      let user_provided_type_pred_defs_for p =
        let rec iter modulePath decls =
          if not (String.starts_with ~prefix:modulePath name) then []
          else
            decls
            |> Util.flatmap @@ function
               | Ast.TypePredDef
                   ( _,
                     _,
                     ( IdentTypeExpr (_, None, sn)
                     | ConstructedTypeExpr (_, sn, _) ),
                     p',
                     body )
                 when String.ends_with ~suffix:sn name
                      && (if modulePath = "" then sn else modulePath ^ "::" ^ sn)
                         = name
                      && p' = p ->
                   [ body ]
               | ModuleDecl (loc, moduleName, _, decls') ->
                   let modulePath =
                     if modulePath = "" then moduleName
                     else modulePath ^ "::" ^ moduleName
                   in
                   iter modulePath decls'
               | _ -> []
        in
        iter "" ghost_decls
      in
      let* full_bor_content, proof_obligs, delayed_proof_obligs, aux_decls' =
        if is_local && AdtKindRd.get kind_cpn = StructKind then (
          let user_provided_own_defs = user_provided_type_pred_defs_for "own" in
          let user_provided_share_defs =
            user_provided_type_pred_defs_for "share"
          in
          let has_public_fields =
            List.exists (fun x -> x.Mir.vis = Public) fds
          in
          if
            has_public_fields
            && (user_provided_own_defs <> [] || user_provided_share_defs <> [])
          then
            Ast.static_error def_loc
              "User-provided .own or .share predicates for structs with public \
               fields are not yet supported"
              None;
          let field_types =
            variants_cpn
            |> Util.flatmap @@ fun variant_cpn ->
               VariantDef.fields_get_list variant_cpn
               |> List.map @@ fun field_cpn ->
                  VariantDef.FieldDef.ty_get field_cpn |> decode_ty
          in
          (* If send_preds = None, it means this ADT is never Send.
             If send_preds = Some xs, then xs is a list of type parameters such that if any of them are not Send, then this ADT is not Send.
             Note that Some [] is always a valid value for send_preds, and that if Some xs is a valid value, then Some (xs @ ys) is also a valid value.
             Similarly, if sync_preds = None, it means this ADT is never Sync.
             If sync_preds = Some xs, then xs is a list of type parameters such that if any of them are not Sync, then this ADT is not Sync.
             xs may contain duplicates. *)
          let send_preds, sync_preds =
            let check_impl_generics_matches_adt loc trait_impl_cpn =
              let impl_generics =
                TraitImplRd.generics_get_list trait_impl_cpn
                |> List.map decode_generic_param
              in
              if impl_generics <> generics then
                Ast.static_error loc
                  "Impl generic parameter names must match ADT generic \
                   parameter names"
                  None;
              let [ `Type (`Adt (_, _, self_ty_gen_args)) ] =
                TraitImplRd.gen_args_get_list trait_impl_cpn
                |> List.map decode_generic_arg
              in
              match Util.zip impl_generics self_ty_gen_args with
              | None ->
                  Ast.static_error loc
                    "Number of trait self type generic arguments does not \
                     match impl generic parameter list"
                    None
              | Some bs -> (
                  bs
                  |> List.iter @@ function
                     | `Type x, `Type (`Param y) when x = y -> ()
                     | `Lifetime x, `Lifetime y when x = y -> ()
                     | _ ->
                         Ast.static_error loc
                           "Trait self type generic arguments do not match \
                            impl generic parameter list"
                           None)
            in
            let check_impl_covers_adt { loc; trait_impl_cpn } =
              check_impl_generics_matches_adt loc trait_impl_cpn;
              let impl_preds =
                TraitImplRd.predicates_get_list trait_impl_cpn
                |> List.map decode_predicate
              in
              impl_preds
              |> List.iter @@ fun impl_pred ->
                 if not (List.mem impl_pred preds) then
                   let string_of_preds preds =
                     String.concat ", " (List.map string_of_predicate preds)
                   in
                   Ast.static_error loc
                     (Printf.sprintf
                        "Trait generic parameter constraint %s does not match \
                         any of the ADT generic parameter constraints %s"
                        (string_of_predicate impl_pred)
                        (string_of_preds preds))
                     None
            in
            let get_impl_preds { loc; trait_impl_cpn } =
              check_impl_generics_matches_adt loc trait_impl_cpn;
              let impl_preds =
                TraitImplRd.predicates_get_list trait_impl_cpn
                |> List.map decode_predicate
              in
              impl_preds
              |> Util.flatmap (function
                   | `Trait (trait_name', `Type (`Param x) :: _) ->
                       [ (x, trait_name') ]
                   | _ -> [])
            in
            let preds_union preds1 preds2 =
              match (preds1, preds2) with
              | Some xs1, Some xs2 ->
                  Some (xs1 @ xs2) (* May introduce duplicates *)
              | _ -> None
            in
            let preds_intersection preds1 preds2 =
              match (preds1, preds2) with
              | Some xs1, Some xs2 ->
                  Some (List.filter (fun x -> List.mem x xs2) xs1)
              | Some xs1, None -> Some xs1
              | None, Some xs2 -> Some xs2
              | None, None -> None
            in
            let rec send_preds_of = function
              | `Param x -> Some [ x ]
              | `RawPtr -> None
              | `Adt ("std::ptr::NonNull", _, _) -> None
              | `Adt
                  ( ( "std::cell::UnsafeCell" | "std::marker::PhantomData"
                    | "std::boxed::Box" | "std::option::Option" ),
                    _,
                    [ `Type tp ] ) ->
                  send_preds_of tp
              | _ -> Some []
              (* Conservatively assume the type is always Send. TODO: Make this more precise. *)
            in
            let rec sync_preds_of = function
              | `Param x -> Some [ x ]
              | `RawPtr -> None
              | `Adt ("std::ptr::NonNull", _, _) -> None
              | `Adt ("std::cell::UnsafeCell", _, _) -> None
              | `Adt
                  ( ( "std::marker::PhantomData" | "std::boxed::Box"
                    | "std::option::Option" ),
                    _,
                    [ `Type tp ] ) ->
                  sync_preds_of tp
              | _ -> Some []
              (* Conservatively assume the type is always Sync. TODO: Make this more precise. *)
            in
            let send_preds =
              field_types
              |> List.fold_left
                   (fun preds ty -> preds_union preds (send_preds_of ty))
                   (Some [])
            in
            let send_impls =
              trait_impls
              |> List.filter (fun { of_trait; self_ty } ->
                     of_trait = "std::marker::Send" && self_ty = name)
            in
            let negative_send_impls, positive_send_impls =
              send_impls |> List.partition (fun { is_negative } -> is_negative)
            in
            let send_preds =
              match send_preds with
              | None -> None
              | Some xs -> (
                  match negative_send_impls with
                  | [] -> Some xs
                  | impl :: _ ->
                      check_impl_covers_adt impl;
                      (* OK, this negative impl covers all instantiations of the ADT so it cancels out the implicit send *)
                      None)
            in
            let send_preds =
              send_preds
              |> Option.map @@ List.map @@ fun x -> (x, "std::marker::Send")
            in
            let send_preds =
              positive_send_impls
              |> List.fold_left
                   (fun preds trait_impl ->
                     preds_intersection preds (Some (get_impl_preds trait_impl)))
                   send_preds
            in
            let variable_occurs_in_expr x e =
              let rec iter acc e =
                match e with
                | Ast.Var (_, y) when x = y -> true
                | _ -> Ast.expr_fold_open iter acc e
              in
              iter false e
            in
            let send_preds =
              match send_preds with
              | None -> None
              | Some _ -> (
                  match user_provided_own_defs with
                  | [ Right ([ t; v ], _, body) ]
                    when not (variable_occurs_in_expr t body) ->
                      None
                  | _ -> send_preds)
            in
            let sync_preds =
              field_types
              |> List.fold_left
                   (fun preds ty -> preds_union preds (sync_preds_of ty))
                   (Some [])
            in
            let sync_impls =
              trait_impls
              |> List.filter (fun { of_trait; self_ty } ->
                     of_trait = "std::marker::Sync" && self_ty = name)
            in
            let negative_sync_impls, positive_sync_impls =
              sync_impls |> List.partition (fun { is_negative } -> is_negative)
            in
            let sync_preds =
              match sync_preds with
              | None -> None
              | Some xs -> (
                  match negative_sync_impls with
                  | [] -> Some xs
                  | impl :: _ ->
                      check_impl_covers_adt impl;
                      None)
            in
            let sync_preds =
              sync_preds
              |> Option.map @@ List.map @@ fun x -> (x, "std::marker::Sync")
            in
            let sync_preds =
              positive_sync_impls
              |> List.fold_left
                   (fun preds trait_impl ->
                     preds_intersection preds (Some (get_impl_preds trait_impl)))
                   sync_preds
            in
            let sync_preds =
              match sync_preds with
              | None -> None
              | Some _ -> (
                  match user_provided_share_defs with
                  | [ Right ([ k; t; l ], _, body) ]
                    when not (variable_occurs_in_expr t body) ->
                      None
                  | _ -> sync_preds)
            in
            (send_preds, sync_preds)
          in
          let* full_bor_content =
            gen_adt_full_borrow_content kind name tparams lft_params variants
              def_loc
          in
          let own_proof_obligs =
            match send_preds with
            | Some xs when user_provided_own_defs <> [] ->
                let send_tparams =
                  List.filter
                    (fun x ->
                      List.mem (x, "std::marker::Send") xs
                      || List.mem x send_tparams)
                    tparams
                in
                let sync_tparams =
                  List.filter
                    (fun x -> List.mem (x, "std::marker::Sync") xs)
                    tparams
                in
                [
                  gen_send_proof_oblig def_loc name tparams vf_tparams
                    send_tparams sync_tparams;
                ]
            | _ -> []
          in
          let own_variance_proof_obligs, upcast_lemmas =
            if
              user_provided_own_defs <> []
              && List.exists
                   (fun variance -> variance <> VarianceRd.Invariant)
                   variances
            then
              gen_own_variance_proof_oblig def_loc name lft_params tparams
                variances fds
            else ([], [])
          in
          let own_proof_obligs = own_variance_proof_obligs @ own_proof_obligs in
          let* share_proof_obligs =
            if user_provided_share_defs <> [] then
              gen_share_proof_obligs def lft_params tparams send_tparams
                sync_preds
            else Ok []
          in
          let type_pred_defs =
            (if user_provided_own_defs <> [] then []
             else
               [
                 (let inputParamCount, body =
                    if has_public_fields then
                      (None, default_struct_own def_loc fds "t" "v")
                    else (Some 2, False def_loc)
                  in
                  Ast.TypePredDef
                    ( def_loc,
                      vf_tparams,
                      StructTypeExpr
                        (def_loc, Some name, None, [], tparams_targs),
                      "own",
                      Right ([ "t"; "v" ], inputParamCount, body) ));
               ])
            @ [
                Ast.TypePredDef
                  ( def_loc,
                    vf_tparams,
                    StructTypeExpr (def_loc, Some name, None, [], tparams_targs),
                    "full_borrow_content",
                    Left (def_loc, name ^ "_full_borrow_content") );
              ]
            @
            if user_provided_share_defs <> [] then []
            else
              [
                (let inputParamCount, body =
                   if has_public_fields then
                     (None, default_struct_share def_loc fds "k" "t" "v")
                   else (Some 3, True def_loc)
                 in
                 Ast.TypePredDef
                   ( def_loc,
                     vf_tparams,
                     StructTypeExpr (def_loc, Some name, None, [], tparams_targs),
                     "share",
                     Right ([ "k"; "t"; "l" ], inputParamCount, body) ));
              ]
          in
          let delayed_proof_obligs =
            if user_provided_own_defs <> [] then
              let is_trivially_droppable =
                fds
                |> List.for_all @@ fun (fd : Mir.field_def_tr) ->
                   type_is_trivially_droppable (Mir.basic_type_of fd.ty)
              in
              if is_trivially_droppable || implements_drop_get adt_def_cpn then
                []
              else
                [
                  (fun adt_defs ->
                    gen_adt_drop_proof_oblig adt_defs def_loc name vf_tparams
                      (List.map
                         (fun (fd : Mir.field_def_tr) ->
                           (fd.loc, fd.name, fd.ty))
                         fds));
                ]
            else []
          in
          let open_ref_init_perm_lemma =
            let pre =
              Ast.CallExpr
                ( def_loc,
                  "ref_init_perm",
                  [],
                  [],
                  [ LitPat (Var (def_loc, "p")); VarPat (def_loc, "x") ],
                  Static )
            in
            let post =
              let fd_ref_init_perm_asns =
                List.combine fds field_types
                |> Util.flatmap (fun (fd, fd_ty) ->
                       match fd_ty with
                       | `Adt ("std::cell::UnsafeCell", _, _) -> []
                       | _ ->
                           [
                             Ast.CallExpr
                               ( def_loc,
                                 "ref_init_perm",
                                 [],
                                 [],
                                 [
                                   LitPat
                                     (AddressOf
                                        ( def_loc,
                                          Select
                                            ( def_loc,
                                              Deref (def_loc, Var (def_loc, "p")),
                                              (fd : Mir.field_def_tr).name ) ));
                                   LitPat
                                     (AddressOf
                                        ( def_loc,
                                          Select
                                            ( def_loc,
                                              Deref (def_loc, Var (def_loc, "x")),
                                              (fd : Mir.field_def_tr).name ) ));
                                 ],
                                 Static );
                           ])
              in
              let ref_padding_init_perm_asn =
                Ast.CallExpr
                  ( def_loc,
                    "ref_padding_init_perm",
                    [],
                    [],
                    [ LitPat (Var (def_loc, "p")); LitPat (Var (def_loc, "x")) ],
                    Static )
              in
              List.fold_right
                (fun a asn -> Ast.Sep (def_loc, a, asn))
                fd_ref_init_perm_asns ref_padding_init_perm_asn
            in
            Ast.Func
              ( def_loc,
                Lemma
                  ( false
                    (*indicates whether an axiom should be generated for this lemma*),
                    None (*trigger*) ),
                lft_params @ tparams (*type parameters*),
                None (*return type*),
                qualified_derived_name "open_ref_init_perm_%s" name,
                [
                  ( PtrTypeExpr
                      ( def_loc,
                        StructTypeExpr
                          (def_loc, Some name, None, [], tparams_targs) ),
                    "p" );
                ],
                false (*nonghost_callers_only*),
                None
                (*implemented function type, with function type type arguments and function type arguments*),
                Some (pre, ("result", post)) (*contract*),
                false (*terminates*),
                Some
                  ( [
                      ExprStmt
                        (CallExpr
                           ( def_loc,
                             "#assume",
                             [],
                             [],
                             [ LitPat (False def_loc) ],
                             Static ));
                    ],
                    def_loc )
                (*body*),
                false (*virtual*),
                [] (*overrides*) )
          in
          let init_ref_padding_lemma =
            let ref_padding_init_perm_asn =
              Ast.CallExpr
                ( def_loc,
                  "ref_padding_init_perm",
                  [],
                  [],
                  [ LitPat (Var (def_loc, "p")); VarPat (def_loc, "x") ],
                  Static )
            in
            let padding_asn coefpat l =
              Ast.CoefAsn
                ( def_loc,
                  coefpat,
                  Ast.CallExpr
                    ( def_loc,
                      padding_pred_name name,
                      [],
                      [],
                      [ LitPat (Var (def_loc, l)) ],
                      Static ) )
            in
            let coef_limits =
              Ast.ExprAsn
                ( def_loc,
                  Operation
                    ( def_loc,
                      And,
                      [
                        Ast.Operation
                          ( def_loc,
                            Ast.Lt,
                            [
                              IntLit
                                ( def_loc,
                                  Big_int.zero_big_int,
                                  true,
                                  false,
                                  NoLSuffix );
                              Var (def_loc, "coef");
                            ] );
                        Ast.Operation
                          ( def_loc,
                            Ast.Lt,
                            [
                              Var (def_loc, "coef");
                              IntLit
                                ( def_loc,
                                  Big_int.unit_big_int,
                                  true,
                                  false,
                                  NoLSuffix );
                            ] );
                      ] ) )
            in
            let pre =
              Ast.Sep
                ( def_loc,
                  ref_padding_init_perm_asn,
                  Sep
                    ( def_loc,
                      padding_asn (VarPat (def_loc, "f")) "x",
                      coef_limits ) )
            in
            let one_minus_coef =
              Ast.Operation
                ( def_loc,
                  Sub,
                  [
                    IntLit
                      (def_loc, Big_int.unit_big_int, true, false, NoLSuffix);
                    Var (def_loc, "coef");
                  ] )
            in
            let f_times_one_minus_coef =
              Ast.Operation
                (def_loc, Mul, [ Var (def_loc, "f"); one_minus_coef ])
            in
            let f_times_coef =
              Ast.Operation
                (def_loc, Mul, [ Var (def_loc, "f"); Var (def_loc, "coef") ])
            in
            let ref_padding_initialized_asn =
              Ast.CallExpr
                ( def_loc,
                  "ref_padding_initialized",
                  [],
                  [],
                  [ LitPat (Var (def_loc, "p")) ],
                  Static )
            in
            let ref_padding_end_token_asn =
              Ast.CallExpr
                ( def_loc,
                  "ref_padding_end_token",
                  [],
                  [],
                  [
                    LitPat (Var (def_loc, "p"));
                    LitPat (Var (def_loc, "x"));
                    LitPat f_times_coef;
                  ],
                  Static )
            in
            let post =
              Ast.Sep
                ( def_loc,
                  padding_asn (LitPat f_times_one_minus_coef) "x",
                  Sep
                    ( def_loc,
                      padding_asn (LitPat f_times_coef) "p",
                      Sep
                        ( def_loc,
                          ref_padding_initialized_asn,
                          ref_padding_end_token_asn ) ) )
            in
            Ast.Func
              ( def_loc,
                Lemma
                  ( false
                    (*indicates whether an axiom should be generated for this lemma*),
                    None (*trigger*) ),
                lft_params @ tparams (*type parameters*),
                None (*return type*),
                qualified_derived_name "init_ref_padding_%s" name,
                [
                  ( PtrTypeExpr
                      ( def_loc,
                        StructTypeExpr
                          (def_loc, Some name, None, [], tparams_targs) ),
                    "p" );
                  (ManifestTypeExpr (def_loc, RealType), "coef");
                ],
                false (*nonghost_callers_only*),
                None
                (*implemented function type, with function type type arguments and function type arguments*),
                Some (pre, ("result", post)) (*contract*),
                false (*terminates*),
                Some
                  ( [
                      ExprStmt
                        (CallExpr
                           ( def_loc,
                             "#assume",
                             [],
                             [],
                             [ LitPat (False def_loc) ],
                             Static ));
                    ],
                    def_loc )
                (*body*),
                false (*virtual*),
                [] (*overrides*) )
          in
          let end_ref_padding_lemma =
            let ref_padding_initialized_asn =
              Ast.CallExpr
                ( def_loc,
                  "ref_padding_initialized",
                  [],
                  [],
                  [ LitPat (Var (def_loc, "p")) ],
                  Static )
            in
            let ref_padding_end_token_asn =
              Ast.CallExpr
                ( def_loc,
                  "ref_padding_end_token",
                  [],
                  [],
                  [
                    LitPat (Var (def_loc, "p"));
                    VarPat (def_loc, "x");
                    VarPat (def_loc, "f");
                  ],
                  Static )
            in
            let padding_asn coefpat l =
              Ast.CoefAsn
                ( def_loc,
                  coefpat,
                  Ast.CallExpr
                    ( def_loc,
                      padding_pred_name name,
                      [],
                      [],
                      [ LitPat (Var (def_loc, l)) ],
                      Static ) )
            in
            let pre =
              Ast.Sep
                ( def_loc,
                  ref_padding_initialized_asn,
                  Sep
                    ( def_loc,
                      ref_padding_end_token_asn,
                      padding_asn (LitPat (Var (def_loc, "f"))) "p" ) )
            in
            let post = padding_asn (LitPat (Var (def_loc, "f"))) "x" in
            Ast.Func
              ( def_loc,
                Lemma
                  ( false
                    (*indicates whether an axiom should be generated for this lemma*),
                    None (*trigger*) ),
                lft_params @ tparams (*type parameters*),
                None (*return type*),
                qualified_derived_name "end_ref_padding_%s" name,
                [
                  ( PtrTypeExpr
                      ( def_loc,
                        StructTypeExpr
                          (def_loc, Some name, None, [], tparams_targs) ),
                    "p" );
                ],
                false (*nonghost_callers_only*),
                None
                (*implemented function type, with function type type arguments and function type arguments*),
                Some (pre, ("result", post)) (*contract*),
                false (*terminates*),
                Some
                  ( [
                      ExprStmt
                        (CallExpr
                           ( def_loc,
                             "#assume",
                             [],
                             [],
                             [ LitPat (False def_loc) ],
                             Static ));
                    ],
                    def_loc )
                (*body*),
                false (*virtual*),
                [] (*overrides*) )
          in
          let close_ref_initialized_lemma =
            let pre =
              let ref_padding_initialized_asn =
                Ast.CoefAsn
                  ( def_loc,
                    VarPat (def_loc, "f"),
                    CallExpr
                      ( def_loc,
                        "ref_padding_initialized",
                        [],
                        [],
                        [ LitPat (Var (def_loc, "p")) ],
                        Static ) )
              in
              let fd_ref_initialized_asns =
                List.combine fds field_types
                |> Util.flatmap (fun (fd, fd_ty) ->
                       match fd_ty with
                       | `Adt ("std::cell::UnsafeCell", _, _) -> []
                       | _ ->
                           [
                             Ast.CoefAsn
                               ( def_loc,
                                 LitPat (Var (def_loc, "f")),
                                 CallExpr
                                   ( def_loc,
                                     "ref_initialized",
                                     [],
                                     [],
                                     [
                                       LitPat
                                         (AddressOf
                                            ( def_loc,
                                              Select
                                                ( def_loc,
                                                  Deref
                                                    (def_loc, Var (def_loc, "p")),
                                                  (fd : Mir.field_def_tr).name
                                                ) ));
                                     ],
                                     Static ) );
                           ])
              in
              Ast.Sep
                ( def_loc,
                  ref_padding_initialized_asn,
                  List.fold_right
                    (fun a asn -> Ast.Sep (def_loc, a, asn))
                    fd_ref_initialized_asns (EmpAsn def_loc) )
            in
            let post =
              Ast.CoefAsn
                ( def_loc,
                  LitPat (Var (def_loc, "f")),
                  CallExpr
                    ( def_loc,
                      "ref_initialized",
                      [],
                      [],
                      [ LitPat (Var (def_loc, "p")) ],
                      Static ) )
            in
            Ast.Func
              ( def_loc,
                Lemma
                  ( false
                    (*indicates whether an axiom should be generated for this lemma*),
                    None (*trigger*) ),
                lft_params @ tparams (*type parameters*),
                None (*return type*),
                qualified_derived_name "close_ref_initialized_%s" name,
                [
                  ( PtrTypeExpr
                      ( def_loc,
                        StructTypeExpr
                          (def_loc, Some name, None, [], tparams_targs) ),
                    "p" );
                ],
                false (*nonghost_callers_only*),
                None
                (*implemented function type, with function type type arguments and function type arguments*),
                Some (pre, ("result", post)) (*contract*),
                false (*terminates*),
                Some
                  ( [
                      ExprStmt
                        (CallExpr
                           ( def_loc,
                             "#assume",
                             [],
                             [],
                             [ LitPat (False def_loc) ],
                             Static ));
                    ],
                    def_loc )
                (*body*),
                false (*virtual*),
                [] (*overrides*) )
          in
          let open_ref_initialized_lemma =
            let pre =
              Ast.CoefAsn
                ( def_loc,
                  VarPat (def_loc, "f"),
                  CallExpr
                    ( def_loc,
                      "ref_initialized",
                      [],
                      [],
                      [ LitPat (Var (def_loc, "p")) ],
                      Static ) )
            in
            let post =
              let fd_ref_initialized_asns =
                List.combine fds field_types
                |> Util.flatmap (fun (fd, fd_ty) ->
                       match fd_ty with
                       | `Adt ("std::cell::UnsafeCell", _, _) -> []
                       | _ ->
                           [
                             Ast.CoefAsn
                               ( def_loc,
                                 LitPat (Var (def_loc, "f")),
                                 CallExpr
                                   ( def_loc,
                                     "ref_initialized",
                                     [],
                                     [],
                                     [
                                       LitPat
                                         (AddressOf
                                            ( def_loc,
                                              Select
                                                ( def_loc,
                                                  Deref
                                                    (def_loc, Var (def_loc, "p")),
                                                  (fd : Mir.field_def_tr).name
                                                ) ));
                                     ],
                                     Static ) );
                           ])
              in
              let ref_padding_initialized_asn =
                Ast.CoefAsn
                  ( def_loc,
                    LitPat (Var (def_loc, "f")),
                    CallExpr
                      ( def_loc,
                        "ref_padding_initialized",
                        [],
                        [],
                        [ LitPat (Var (def_loc, "p")) ],
                        Static ) )
              in
              List.fold_right
                (fun a asn -> Ast.Sep (def_loc, a, asn))
                fd_ref_initialized_asns ref_padding_initialized_asn
            in
            Ast.Func
              ( def_loc,
                Lemma
                  ( false
                    (*indicates whether an axiom should be generated for this lemma*),
                    None (*trigger*) ),
                lft_params @ tparams (*type parameters*),
                None (*return type*),
                qualified_derived_name "open_ref_initialized_%s" name,
                [
                  ( PtrTypeExpr
                      ( def_loc,
                        StructTypeExpr
                          (def_loc, Some name, None, [], tparams_targs) ),
                    "p" );
                ],
                false (*nonghost_callers_only*),
                None
                (*implemented function type, with function type type arguments and function type arguments*),
                Some (pre, ("result", post)) (*contract*),
                false (*terminates*),
                Some
                  ( [
                      ExprStmt
                        (CallExpr
                           ( def_loc,
                             "#assume",
                             [],
                             [],
                             [ LitPat (False def_loc) ],
                             Static ));
                    ],
                    def_loc )
                (*body*),
                false (*virtual*),
                [] (*overrides*) )
          in
          Ok
            ( Some full_bor_content,
              own_proof_obligs @ share_proof_obligs,
              delayed_proof_obligs,
              upcast_lemmas
              @ open_ref_init_perm_lemma :: init_ref_padding_lemma
                :: close_ref_initialized_lemma :: open_ref_initialized_lemma
                :: end_ref_padding_lemma :: type_pred_defs ))
        else Ok (None, [], [], [])
      in
      Ok
        (Some
           Mir.
             {
               loc = def_loc;
               name;
               tparams;
               lft_params;
               fds;
               def;
               aux_decls = aux_decls @ aux_decls';
               full_bor_content;
               proof_obligs;
               delayed_proof_obligs;
             })

  (** Checks for the existence of a lemma for proof obligation in ghost code.
      The consistency of the lemma with proof obligation will be checked by VeriFast later *)
  let check_proof_obligations gh_decl_map proof_obligs =
    let unmet_proof_obligs =
      proof_obligs
      |> List.filter @@ fun po ->
         let (Some po_name) = AstAux.decl_name po in
         match Util.try_assoc po_name gh_decl_map with
         | Some (Ast.Func (_, _, _, _, _, _, _, _, _, _, Some body, _, _)) ->
             false
         | _ -> true
    in
    if unmet_proof_obligs <> [] then
      let loc = AstAux.decl_loc (List.hd unmet_proof_obligs) in
      let unmet_proof_obligs_at_loc =
        List.filter (fun po -> AstAux.decl_loc po = loc) unmet_proof_obligs
      in
      let msg, descr =
        match unmet_proof_obligs_at_loc with
        | [ po ] ->
            ( Printf.sprintf "Lemma %s should be proven"
                (Option.get (AstAux.decl_name po)),
              "Insert lemma template" )
        | pos ->
            ( Printf.sprintf "Lemmas %s should be proven"
                (String.concat ", "
                   (List.map (fun po -> Option.get (AstAux.decl_name po)) pos)),
              "Insert lemma templates" )
      in
      let (Lexed (_, end_pos)) = loc in
      let text_to_insert =
        Printf.sprintf "\n\n/*@\n\n%s\n\n@*/"
        @@ String.concat "\n\n"
        @@ List.map Ast_to_src.string_of_decl unmet_proof_obligs_at_loc
      in
      raise
        (Ast.StaticError
           ( loc,
             msg,
             Some
               [
                 HelpTopic "rust-struct-proof-obligations";
                 QuickFix (descr, InsertTextAt (end_pos, text_to_insert));
               ] ))
    else Ok ()

  let translate_trait_impls (trait_impls_cpn : TraitImplRd.t list) =
    trait_impls_cpn
    |> ListAux.try_map (fun trait_impl_cpn ->
           let open TraitImplRd in
           let* loc = translate_span_data (span_get trait_impl_cpn) in
           let is_unsafe = is_unsafe_get trait_impl_cpn in
           let is_negative = is_negative_get trait_impl_cpn in
           let of_trait = of_trait_get trait_impl_cpn in
           let self_ty = self_ty_get trait_impl_cpn in
           let items = items_get_list trait_impl_cpn in
           Ok
             ({
                trait_impl_cpn;
                loc;
                is_unsafe;
                is_negative;
                of_trait;
                self_ty;
                items;
              }
               : trait_impl))

  let compute_trait_impl_prototypes (adt_defs : Mir.adt_def_tr list)
      traits_and_body_decls trait_impls =
    trait_impls
    |> Util.flatmap (fun { loc = limpl; of_trait; self_ty; items } ->
           if of_trait = "std::ops::Drop" then (
             assert (items = [ "drop" ]);
             [] (* drop is safe *))
           else if of_trait = "std::ops::Deref" then (
             assert (items = [ "Target"; "deref" ]);
             [] (* Deref is safe *))
           else if of_trait = "std::ops::DerefMut" then (
             assert (items = [ "deref_mut" ]);
             [] (* DerefMut is safe *))
           else if of_trait = "std::clone::Clone" then []
             (* clone is safe *)
             (* TODO: Support for traits from other crates. I think it is generally sound to ignore safe traits here *)
           else
             items
             |> Util.flatmap (fun item ->
                    let trait_fn_name = Printf.sprintf "%s::%s" of_trait item in
                    let impl_fn_name =
                      Printf.sprintf "<%s as %s>::%s" self_ty of_trait item
                    in
                    match
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
                                 Some (pre, (result_var, post)),
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
                                           ( lf,
                                             pre,
                                             Ast.EnsuresAsn
                                               (lf, result_var, post) ) ) )
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
                                      Some (pre, ("result", post)),
                                      terminates,
                                      None,
                                      false,
                                      [] ))
                           | _ -> None)
                    with
                    | Some prototype -> [ prototype ]
                    | None -> []))

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
    let imports, decls = List.partition_map (fun x -> x) ghost_decl_batches in
    let decls = List.flatten decls in
    let decls =
      if Args.ignore_unwind_paths then
        List.map Rust_parser.result_decl_of_outcome_decl decls
      else decls
    in
    Ok (Ast.ModuleDecl (loc, name, List.flatten imports, submodules @ decls))

  let modularize_decl module_imports_map (d : Ast.decl) : Ast.decl =
    match AstAux.decl_loc_name_and_name_setter d with
    | None -> d
    | Some (l, name, name_setter) ->
        if String.contains name ':' then
          let segments = String.split_on_char ':' name in
          let rec iter segs = function
            | segment :: "" :: segments ->
                let segs = segment :: segs in
                let imports =
                  match segments with
                  | [ _ ] -> (
                      let moduleName = String.concat "::" (List.rev segs) in
                      match List.assoc_opt moduleName module_imports_map with
                      | None -> []
                      | Some imports -> imports)
                  | _ -> []
                in
                Ast.ModuleDecl (l, segment, imports, [ iter segs segments ])
            | [ segment ] -> name_setter segment
            | _ ->
                failwith
                  (Printf.sprintf "Unexpected shape of Rust item name: '%s'"
                     name)
          in
          iter [] segments
        else d

  let modularize_fn_decl module_imports_map
      (((moduleName : string), (fnName : string)), (d : Ast.decl)) : Ast.decl =
    let (Some (l, name, name_setter)) =
      AstAux.decl_loc_name_and_name_setter d
    in
    if moduleName <> "" then
      let imports =
        match List.assoc_opt moduleName module_imports_map with
        | None -> []
        | Some imports -> imports
      in
      let d = name_setter fnName in
      let segments = String.split_on_char ':' moduleName in
      let rec iter = function
        | segment :: "" :: segments ->
            Ast.ModuleDecl (l, segment, [], [ iter segments ])
        | [ segment ] -> Ast.ModuleDecl (l, segment, imports, [ d ])
        | _ ->
            failwith
              (Printf.sprintf "Unexpected shape of Rust module name: '%s'"
                 moduleName)
      in
      iter segments
    else d

  let translate_vf_mir (extern_specs : string list) (vf_mir_cpn : VfMirRd.t) =
    let job _ =
      let directives_cpn = VfMirRd.directives_get_list vf_mir_cpn in
      let* directives = ListAux.try_map translate_annotation directives_cpn in
      let vf_mir_translator_directives, vf_directives =
        directives
        |> List.partition (fun { Mir.raw } -> raw = "ignore_ref_creation")
      in
      vf_directives
      |> List.iter (fun ({ span; raw } : Mir.annot) ->
             Args.report_should_fail raw (Ast.lexed_loc span));
      let* module_decls =
        ListAux.try_map translate_module (VfMirRd.modules_get_list vf_mir_cpn)
      in
      let module_imports_map =
        let rec iter moduleName module_decls =
          List.concat_map
            (function
              | Ast.ModuleDecl (_, name, imports, submodules) ->
                  let name =
                    if moduleName = "" then name else moduleName ^ "::" ^ name
                  in
                  (name, imports) :: iter name submodules
              | _ -> [])
            module_decls
        in
        iter "" module_decls
      in
      let ghost_decl_batches_cpn =
        VfMirRd.ghost_decl_batches_get_list vf_mir_cpn
      in
      let* ghost_decl_batches =
        ListAux.try_map translate_ghost_decl_batch ghost_decl_batches_cpn
      in
      let ghost_imports, ghost_decl_batches =
        List.partition_map (fun x -> x) ghost_decl_batches
      in
      let ghost_decl_batches = List.flatten ghost_decl_batches in
      let ghost_decl_batches =
        if Args.ignore_unwind_paths then
          List.map Rust_parser.result_decl_of_outcome_decl ghost_decl_batches
        else ghost_decl_batches
      in
      let ghost_decls = module_decls @ ghost_decl_batches in
      let ghost_decl_map = AstAux.decl_map_of ghost_decls in
      let* trait_impls =
        translate_trait_impls (VfMirRd.trait_impls_get_list vf_mir_cpn)
      in
      let adt_defs_cpn = VfMirRd.adt_defs_get vf_mir_cpn in
      let* adt_defs_cpn = CapnpAux.ind_list_get_list adt_defs_cpn in
      let* adt_defs =
        ListAux.try_map
          (translate_adt_def ghost_decl_map ghost_decls trait_impls)
          adt_defs_cpn
      in
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
      let adts_proof_obligs =
        Util.flatmap
          (fun (adt_def : Mir.adt_def_tr) ->
            List.map (fun ob -> ob adt_defs) adt_def.delayed_proof_obligs)
          adt_defs
        @ adts_proof_obligs
      in
      let adts_full_bor_content_preds =
        List.filter_map Fun.id adts_full_bor_content_preds
      in
      let* _ = check_proof_obligations ghost_decl_map adts_proof_obligs in
      let* traits_cpn =
        CapnpAux.ind_list_get_list (VfMirRd.traits_get vf_mir_cpn)
      in
      let* traits_decls =
        ListAux.try_map
          (translate_trait adt_defs Args.skip_specless_fns)
          traits_cpn
      in
      let traits_decls = List.flatten traits_decls in
      let bodies_cpn = VfMirRd.bodies_get_list vf_mir_cpn in
      let bodies_cpn =
        if Args.skip_specless_fns then
          List.filter
            (fun body_cpn ->
              not
                (Capnp.Array.is_empty
                   (ContractRd.annotations_get (BodyRd.contract_get body_cpn))))
            bodies_cpn
        else bodies_cpn
      in
      let body_tr_defs_ctx =
        { adt_defs; directives = vf_mir_translator_directives }
      in
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
      let traits_and_body_decls = traits_decls @ List.map snd body_decls in
      let debug_infos = VF0.DbgInfoRustFe debug_infos in
      let trait_impl_prototypes =
        compute_trait_impl_prototypes adt_defs traits_and_body_decls trait_impls
      in
      (* Hack: for structs, functions, and other item-likes inside modules we
         currently generate toplevel VF declarations with paths as names. However, to properly resolve names inside those declarations,
         they need to be inside appropriate `ModuleDecl`s. `modularize_decl` does this. TODO: Generate the declarations inside the right
         module declarations from the start. This will become necessary once we want to take real `use` items into account inside annotations.*)
      let decls =
        List.map
          (modularize_decl module_imports_map)
          (traits_decls @ trait_impl_prototypes @ adt_decls @ aux_decls
         @ adts_full_bor_content_preds @ adts_proof_obligs)
        @ ghost_decls
        @ List.map
            (modularize_fn_decl module_imports_map)
            (body_sigs @ body_decls)
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
        parse_prelude ()
        @ Util.flatmap
            (fun (crateName, header_path) -> parse_header crateName header_path)
            header_names
      in
      let headers =
        if TranslatorArgs.ignore_unwind_paths then
          List.map Rust_parser.result_header_of_outcome_header headers
        else headers
      in
      Ok
        ( headers,
          Rust_parser.flatten_module_decls Ast.dummy_loc
            (List.flatten ghost_imports)
            decls,
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
        | `CheckProofObligationFailed (loc, str) | `TrBodyFailed (loc, str) ->
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
