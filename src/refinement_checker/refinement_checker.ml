module VfMir = Vf_mir.Make (Capnp.BytesMessage)
module VfMirRd = VfMir.Reader

let error msg =
  Printf.printf "ERROR: %s\n" msg;
  exit 1

let decode_path path =
  let name = VfMirRd.SpanData.Loc.SourceFile.name_get path in
  match VfMirRd.SpanData.Loc.SourceFile.FileName.get name with
  | Real real_file_name -> (
      match
        VfMirRd.SpanData.Loc.SourceFile.FileName.RealFileName.get real_file_name
      with
      | LocalPath path -> path
      | Remapped _ -> failwith "Remapped file names are not yet supported")
  | QuoteExpansion _ -> failwith "Quote expansions are not yet supported"

let decode_loc loc =
  let path = decode_path @@ VfMirRd.SpanData.Loc.file_get loc in
  let line = Stdint.Uint64.to_int @@ VfMirRd.SpanData.Loc.line_get loc in
  let col =
    Stdint.Uint64.to_int @@ VfMirRd.SpanData.Loc.CharPos.pos_get
    @@ VfMirRd.SpanData.Loc.col_get loc
  in
  (path, line, col)

let decode_span span =
  let lo = VfMirRd.SpanData.lo_get span in
  let hi = VfMirRd.SpanData.hi_get span in
  (decode_loc lo, decode_loc hi)

let string_of_span span =
  let ((path_lo, line_lo, col_lo), (path_hi, line_hi, col_hi)) = decode_span span in
  assert (path_hi = path_lo);
  if line_lo = line_hi then
    Printf.sprintf "%s:%d:%d-%d" path_lo line_lo (col_lo + 1) (col_hi + 1)
  else
    Printf.sprintf "%s:%d:%d-%d:%d" path_lo line_lo (col_lo + 1) line_hi (col_hi + 1)

type int_width = FixedWidth of int (* log2 of width in bytes *) | PtrWidth

type literal_const_expr =
  BoolValue of bool
| I8Value of Stdint.int8
| I16Value of Stdint.int16
| I32Value of Stdint.int32
| I64Value of Stdint.int64
| I128Value of Stdint.int128
| U8Value of Stdint.uint8
| U16Value of Stdint.uint16
| U32Value of Stdint.uint32
| U64Value of Stdint.uint64
| U128Value of Stdint.uint128
| CharValue of Stdint.uint32

type const_expr =
  ParamConstExpr of string
| LiteralConstExpr of literal_const_expr

let decode_uint128 uint128_cpn =
  let h = VfMirRd.Util.UInt128.h_get uint128_cpn in
  let l = VfMirRd.Util.UInt128.l_get uint128_cpn in
  Stdint.Uint128.logor (Stdint.Uint128.shift_left (Stdint.Uint64.to_uint128 h) 64) (Stdint.Uint64.to_uint128 l)

type adt_kind = Struct | Enum | Union

type region = Region of string

type mutability = Mut | Shared

let decode_mutability mutability_cpn =
  match VfMirRd.Mutability.get mutability_cpn with
    VfMirRd.Mutability.Mut -> Mut
  | VfMirRd.Mutability.Not -> Shared

type ty =
  Bool
| Int of int_width
| UInt of int_width
| Char
| Adt of string * adt_kind * gen_arg list
| RawPtr of ty
| Ref of region * ty * mutability
| FnDef of string * gen_arg list
(*| FnPtr of ty list * ty*)
| Never
| Tuple of ty list
| Param of string
| Str
| Array of ty * const_expr
| Slice of ty
and gen_arg =
  Lifetime of region
| Type of ty
| Const of const_expr

let string_of_gen_arg genArg = "(gen arg)"

let rec decode_ty ty_cpn =
  match VfMirRd.Ty.TyKind.get (VfMirRd.Ty.kind_get ty_cpn) with
    Bool -> Bool
  | Int int_ty_cpn ->
    begin match VfMirRd.Ty.IntTy.get int_ty_cpn with
      I8 -> Int (FixedWidth 0)
    | I16 -> Int (FixedWidth 1)
    | I32 -> Int (FixedWidth 2)
    | I64 -> Int (FixedWidth 3)
    | I128 -> Int (FixedWidth 4)
    | ISize -> Int PtrWidth
    end
  | UInt uint_ty_cpn ->
    begin match VfMirRd.Ty.UIntTy.get uint_ty_cpn with
      U8 -> UInt (FixedWidth 0)
    | U16 -> UInt (FixedWidth 1)
    | U32 -> UInt (FixedWidth 2)
    | U64 -> UInt (FixedWidth 3)
    | U128 -> UInt (FixedWidth 4)
    | USize -> UInt PtrWidth
    end
  | Char -> Char
  | Adt adt_ty_cpn ->
    let name = VfMirRd.Ty.AdtDefId.name_get (VfMirRd.Ty.AdtTy.id_get adt_ty_cpn) in
    let kind =
      match VfMirRd.Ty.AdtKind.get (VfMirRd.Ty.AdtTy.kind_get adt_ty_cpn) with
        StructKind -> Struct
      | EnumKind -> Enum
      | UnionKind -> Union
    in
    let args = List.map decode_gen_arg (VfMirRd.Ty.AdtTy.substs_get_list adt_ty_cpn) in
    Adt (name, kind, args)
  | RawPtr raw_ptr_ty_cpn -> RawPtr (decode_ty (VfMirRd.Ty.RawPtrTy.ty_get raw_ptr_ty_cpn))
  | Ref ref_ty_cpn ->
    let region = Region (VfMirRd.Ty.Region.id_get (VfMirRd.Ty.RefTy.region_get ref_ty_cpn)) in
    let ty = VfMirRd.Ty.RefTy.ty_get ref_ty_cpn in
    let mutability = decode_mutability (VfMirRd.Ty.RefTy.mutability_get ref_ty_cpn) in
    Ref (region, decode_ty ty, mutability)
  | FnDef fn_def_ty_cpn ->
    let id = VfMirRd.Ty.FnDefId.name_get (VfMirRd.Ty.FnDefTy.id_get fn_def_ty_cpn) in
    let args = List.map decode_gen_arg (VfMirRd.Ty.FnDefTy.substs_get_list fn_def_ty_cpn) in
    FnDef (id, args)
  | Never -> Never
  | Tuple tys -> Tuple (Capnp.Array.map_list tys ~f:decode_ty)
  | Param param -> Param param
  | Str -> Str
  | Array array_ty_cpn ->
    let elem_ty = decode_ty (VfMirRd.Ty.ArrayTy.elem_ty_get array_ty_cpn) in
    let size = decode_const_expr (VfMirRd.Ty.ArrayTy.size_get array_ty_cpn) in
    Array (elem_ty, size)
  | Slice ty_cpn -> Slice (decode_ty ty_cpn)
and decode_gen_arg gen_arg_cpn =
  match VfMirRd.Ty.GenArg.GenArgKind.get (VfMirRd.Ty.GenArg.kind_get gen_arg_cpn) with
    Lifetime lifetime -> Lifetime (Region (VfMirRd.Ty.Region.id_get lifetime))
  | Type ty -> Type (decode_ty ty)
  | Const const -> Const (decode_const_expr const)
and decode_const_expr const_cpn =
  match VfMirRd.Ty.ConstKind.get (VfMirRd.Ty.Const.kind_get const_cpn) with
    Param param -> ParamConstExpr (VfMirRd.Ty.ConstKind.ParamConst.name_get param)
  | Value value_cpn ->
    let ty = decode_ty (VfMirRd.Ty.ConstKind.Value.ty_get value_cpn) in
    let valtree = VfMirRd.Ty.ConstKind.Value.val_tree_get value_cpn in
    match VfMirRd.Ty.ConstKind.ValTree.get valtree with
      Leaf scalar_int_cpn ->
        let data = decode_uint128 (VfMirRd.Ty.ScalarInt.data_get scalar_int_cpn) in
        let size = VfMirRd.Ty.ScalarInt.size_get scalar_int_cpn in
        begin match ty, size with
          Bool, 1 -> LiteralConstExpr (BoolValue (data <> Stdint.Uint128.zero))
        | Int (FixedWidth 0), 1 -> LiteralConstExpr (I8Value (Stdint.Uint128.to_int8 data))
        | Int (FixedWidth 1), 2 -> LiteralConstExpr (I16Value (Stdint.Uint128.to_int16 data))
        | Int (FixedWidth 2), 4 -> LiteralConstExpr (I32Value (Stdint.Uint128.to_int32 data))
        | Int (FixedWidth 3), 8 -> LiteralConstExpr (I64Value (Stdint.Uint128.to_int64 data))
        | Int (FixedWidth 4), 16 -> LiteralConstExpr (I128Value (Stdint.Uint128.to_int128 data))
        | UInt (FixedWidth 0), 1 -> LiteralConstExpr (U8Value (Stdint.Uint128.to_uint8 data))
        | UInt (FixedWidth 1), 2 -> LiteralConstExpr (U16Value (Stdint.Uint128.to_uint16 data))
        | UInt (FixedWidth 2), 4 -> LiteralConstExpr (U32Value (Stdint.Uint128.to_uint32 data))
        | UInt (FixedWidth 3), 8 -> LiteralConstExpr (U64Value (Stdint.Uint128.to_uint64 data))
        | UInt (FixedWidth 4), 16 -> LiteralConstExpr (U128Value data)
        | Char, 4 -> LiteralConstExpr (CharValue (Stdint.Uint128.to_uint32 data))
        end
    | Branch -> failwith "Branch not supported"

type term = Symbol of int | Tuple of term list | FnDef of string * gen_arg list

let rec string_of_term = function
  Symbol id -> Printf.sprintf "Symbol %d" id
| Tuple ts -> Printf.sprintf "Tuple [%s]" (String.concat "; " (List.map string_of_term ts))
| FnDef (fn, genArgs) -> Printf.sprintf "FnDef %s [%s]" fn (String.concat "; " (List.map string_of_gen_arg genArgs))

let next_symbol_id = ref 0

let fresh_symbol () =
  let id = !next_symbol_id in
  next_symbol_id := id + 1;
  Symbol id

type local_var_state =
  Value of term (* This local has not (yet) had its address taken. The term denote the value of the local. *)
| Address of term (* This local has its address taken somewhere in this function. The term denotes the address of the local. *)

let string_of_local_var_state = function
  Value v -> Printf.sprintf "Value %s" (string_of_term v)
| Address v -> Printf.sprintf "Address %s" (string_of_term v)

let string_of_env env =
  String.concat "; " (List.map (fun (x, v) -> Printf.sprintf "%s: %s" x (string_of_local_var_state v)) env)

let eval_const_operand const_operand_cpn =
  let mir_const_cpn = VfMirRd.Body.ConstOperand.const_get const_operand_cpn in
  match VfMirRd.Body.ConstOperand.Const.get mir_const_cpn with
    Ty mir_ty_const_cpn -> failwith "Using typesystem constant expressions as MIR constant operands is not yet supported"
  | Val mir_val_const_cpn ->
    let ty = decode_ty (VfMirRd.Body.ConstOperand.Const.Val.ty_get mir_val_const_cpn) in
    let mir_const_value_cpn = VfMirRd.Body.ConstOperand.Const.Val.const_value_get mir_val_const_cpn in
    begin match VfMirRd.Body.ConstValue.get mir_const_value_cpn with
      Scalar scalar_cpn -> failwith "MIR scalar constants are not yet supported"
    | ZeroSized ->
      begin match ty with
        Tuple [] -> Tuple []
      | FnDef (fn, genArgs) -> FnDef (fn, genArgs)
      | _ -> failwith "Zero-sized constants are not yet supported"
      end
    | Slice slice_cpn -> failwith "MIR slice constants are not yet supported"
    end
  | Unevaluated -> failwith "Unevaluated constant operands are not yet supported"

let update_env x v env = (x, v) :: List.remove_assoc x env

let rec process_assignments bblocks env i_bb i_s =
  let bb = Capnp.Array.get bblocks i_bb in
  let stmts = VfMirRd.Body.BasicBlock.statements_get bb in
  if i_s = Capnp.Array.length stmts then
    (env, i_bb, i_s)
  else
    let s = Capnp.Array.get stmts i_s in
    match VfMirRd.Body.BasicBlock.Statement.StatementKind.get (VfMirRd.Body.BasicBlock.Statement.kind_get s) with
      Assign assign_data ->
        let lhsPlace = VfMirRd.Body.BasicBlock.Statement.StatementKind.AssignData.lhs_place_get assign_data in
        let rhsRvalue = VfMirRd.Body.BasicBlock.Statement.StatementKind.AssignData.rhs_rvalue_get assign_data in
        let lhsProjection = VfMirRd.Body.Place.projection_get lhsPlace in
        if Capnp.Array.length lhsProjection <> 0 then
          (env, i_bb, i_s)
        else
          let lhsLocalId = VfMirRd.Body.Place.local_get lhsPlace in
          let lhsLocalName = VfMirRd.Body.LocalDeclId.name_get lhsLocalId in
          begin match VfMirRd.Body.BasicBlock.Rvalue.get rhsRvalue with
            Use operand ->
              begin match VfMirRd.Body.BasicBlock.Operand.get operand with
                Move place | Copy place ->
                  let placeProjection = VfMirRd.Body.Place.projection_get place in
                  if Capnp.Array.length placeProjection <> 0 then
                    (env, i_bb, i_s)
                  else
                    let placeLocalId = VfMirRd.Body.Place.local_get place in
                    let placeLocalName = VfMirRd.Body.LocalDeclId.name_get placeLocalId in
                    begin match List.assoc placeLocalName env with
                      Value placeValue ->
                        begin match List.assoc_opt lhsLocalName env with
                          Some (Address _) -> (env, i_bb, i_s)
                        | _ ->
                          let env = update_env lhsLocalName (Value placeValue) env in
                          process_assignments bblocks env i_bb (i_s + 1)
                        end
                    | _ -> (env, i_bb, i_s)
                      end
              | Constant constant ->
                  (env, i_bb, i_s)
              end
            | _ -> (env, i_bb, i_s)
            end
    | Nop -> process_assignments bblocks env i_bb (i_s + 1)

let values_equal (v0: term) (v1: term) = v0 = v1

let check_place_element_refines_place_element elem0 elem1 =
  match VfMirRd.Body.Place.PlaceElement.get elem0, VfMirRd.Body.Place.PlaceElement.get elem1 with
  | Deref, Deref -> ()
  | Field field0, Field field1 ->
      let fieldIndex0 = VfMirRd.Body.Place.PlaceElement.FieldData.index_get field0 in
      let fieldIndex1 = VfMirRd.Body.Place.PlaceElement.FieldData.index_get field1 in
      if fieldIndex0 <> fieldIndex1 then failwith "Field indices do not match"
  | Index, Index -> failwith "PlaceElement::Index not supported"
  | ConstantIndex, ConstantIndex -> failwith "PlaceElement::ConstantIndex not supported"
  | Subslice, Subslice -> failwith "PlaceElement::Subslice not supported"
  | Downcast variant_idx0, Downcast variant_idx1 ->
    if variant_idx0 <> variant_idx1 then failwith "Variant indices do not match"
  | OpaqueCast, OpaqueCast -> failwith "PlaceElement::OpaqueCast not supported"
  | Subtype, Subtype -> failwith "PlaceElement::Subtype not supported"
  | _ -> failwith "Place elements do not match"

(* When this is raised, both variables did not yet have their address taken *)
exception LocalAddressTaken of string (* x0 *) * string (* x1 *)

type place =
  Local of string (* This place is a local variable whose address is never taken in this function *)
| Nonlocal (* A "nonlocal place" is a plcae that is disjoint from all local variables whose address is never taken in this function *)

(* Checks that the place expressions either both evaluate to a local whose address is never taken, or both evaluate to *the same* "nonlocal place" (see definition above). *)
let check_place_refines_place env0 place0 env1 place1 =
  let placeLocalId0 = VfMirRd.Body.Place.local_get place0 in
  let placeLocalName0 = VfMirRd.Body.LocalDeclId.name_get placeLocalId0 in
  let placeLocalId1 = VfMirRd.Body.Place.local_get place1 in
  let placeLocalName1 = VfMirRd.Body.LocalDeclId.name_get placeLocalId1 in
  let placeLocalState0 = List.assoc_opt placeLocalName0 env0 in
  let placeLocalState1 = List.assoc_opt placeLocalName1 env1 in
  let placeProjection0 = VfMirRd.Body.Place.projection_get place0 in
  let placeProjection1 = VfMirRd.Body.Place.projection_get place1 in
  if Capnp.Array.length placeProjection0 <> Capnp.Array.length placeProjection1 then
    failwith "The two place expressions have a different number of projection elements";
  match placeLocalState0, placeLocalState1 with
    Some (Address a1), Some (Address a2) ->
      if not (values_equal a1 a2) then failwith "The addresses of the two places are not equal";
      for i = 0 to Capnp.Array.length placeProjection0 - 1 do
        let projection0 = Capnp.Array.get placeProjection0 i in
        let projection1 = Capnp.Array.get placeProjection1 i in
        check_place_element_refines_place_element projection0 projection1
      done;
      Nonlocal, Nonlocal
  | Some (Address _), _ | _, Some (Address _) -> failwith "Place expressions do not match"
  | _, _ ->
    (* OK, neither local has its address taken *)
    if Capnp.Array.length placeProjection0 <> 0 then
      (* if a local is projected, give up trying to track its value *)
      raise (LocalAddressTaken (placeLocalName0, placeLocalName1));
    Local placeLocalName0, Local placeLocalName1

let check_operand_refines_operand i env0 span0 operand0 env1 span1 operand1 =
  match VfMirRd.Body.BasicBlock.Operand.get operand0, VfMirRd.Body.BasicBlock.Operand.get operand1 with
    (Move placeExpr0, Move placeExpr1) | (Copy placeExpr0, Copy placeExpr1) ->
      begin match check_place_refines_place env0 placeExpr0 env1 placeExpr1 with
        Local x0, Local x1 ->
          begin match List.assoc x0 env0, List.assoc x1 env1 with
            Value v0, Value v1 -> if not (values_equal v0 v1) then failwith (Printf.sprintf "The values of the %d'th operand of %s and %s are not equal" i (string_of_span span0) (string_of_span span1))
          | Address a1, Address a2 -> if not (values_equal a1 a2) then failwith (Printf.sprintf "The addresses of the %d'th operand of %s and %s are not equal" i (string_of_span span0) (string_of_span span1))
          | _ -> failwith "Operand mismatch"
          end
      | Nonlocal, Nonlocal -> ()
        end
  | Constant const_operand_cpn0, Constant const_operand_cpn1 ->
    if eval_const_operand const_operand_cpn0 <> eval_const_operand const_operand_cpn1 then failwith (Printf.sprintf "The constants %s and %s are not equal" (string_of_span span0) (string_of_span span1))

let check_aggregate_refines_aggregate env0 span0 aggregate0 env1 span1 aggregate1 =
  let operands0 = VfMirRd.Body.BasicBlock.Rvalue.AggregateData.operands_get aggregate0 in
  let operands1 = VfMirRd.Body.BasicBlock.Rvalue.AggregateData.operands_get aggregate1 in
  if Capnp.Array.length operands0 <> Capnp.Array.length operands1 then failwith "The two aggregate expressions have a different number of operands";
  let aggregate_kind0 = VfMirRd.Body.BasicBlock.Rvalue.AggregateData.aggregate_kind_get aggregate0 in
  let aggregate_kind1 = VfMirRd.Body.BasicBlock.Rvalue.AggregateData.aggregate_kind_get aggregate1 in
  match VfMirRd.Body.BasicBlock.Rvalue.AggregateData.AggregateKind.get aggregate_kind0, VfMirRd.Body.BasicBlock.Rvalue.AggregateData.AggregateKind.get aggregate_kind1 with
    Array _, Array _ -> failwith "Aggregate::Array not supported"
  | Tuple, Tuple ->
    for i = 0 to Capnp.Array.length operands0 - 1 do
      let operand0 = Capnp.Array.get operands0 i in
      let operand1 = Capnp.Array.get operands1 i in
      check_operand_refines_operand i env0 span0 operand0 env1 span1 operand1
    done
  | Adt _, Adt _ -> failwith "Aggregate::Adt not supported"
  | Closure, Closure -> failwith "Aggregate::Closure not supported"
  | Coroutine, Coroutine -> failwith "Aggregate::Coroutine not supported"
  | CoroutineClosure, CoroutineClosure -> failwith "Aggregate::CoroutineClosure not supported"
  | RawPtr, RawPtr -> failwith "Aggregate::RawPtr not supported"
  | _ -> failwith "Aggregate kinds do not match"

(* Checks that the two rvalues evaluate to the same value *)
let check_rvalue_refines_rvalue env0 span0 rhsRvalue0 env1 span1 rhsRvalue1 =
  match VfMirRd.Body.BasicBlock.Rvalue.get rhsRvalue0, VfMirRd.Body.BasicBlock.Rvalue.get rhsRvalue1 with
  Use operand0, Use operand1 ->
    check_operand_refines_operand 0 env0 span0 operand0 env1 span1 operand1
| Repeat, Repeat -> failwith "Rvalue::Repeat not supported"
| Ref ref_data_cpn0, Ref ref_data_cpn1 ->
  (* We ignore the region because it does not affect the run-time behavior *)
  let borKind0 = VfMirRd.Body.BasicBlock.Rvalue.RefData.bor_kind_get ref_data_cpn0 in
  let borKind1 = VfMirRd.Body.BasicBlock.Rvalue.RefData.bor_kind_get ref_data_cpn1 in
  begin match VfMirRd.Body.BasicBlock.Rvalue.RefData.BorrowKind.get borKind0, VfMirRd.Body.BasicBlock.Rvalue.RefData.BorrowKind.get borKind1 with
    | Shared, Shared -> ()
    | Mut, Mut -> ()
    | _ -> failwith "Rvalue::Ref: borrow kinds do not match"
  end;
  let placeExpr0 = VfMirRd.Body.BasicBlock.Rvalue.RefData.place_get ref_data_cpn0 in
  let placeExpr1 = VfMirRd.Body.BasicBlock.Rvalue.RefData.place_get ref_data_cpn1 in
  begin match check_place_refines_place env0 placeExpr0 env1 placeExpr1 with
    Local x0, Local x1 -> raise (LocalAddressTaken (x0, x1))
  | Nonlocal, Nonlocal -> ()
  end
| ThreadLocalRef, ThreadLocalRef -> failwith "Rvalue::ThreadLocalRef not supported"
| AddressOf address_of_data_cpn0, AddressOf address_of_data_cpn1 -> failwith "Rvalue::AddressOf not supported"
| Len, Len -> failwith "Rvalue::Len not supported"
| Cast cast_data_cpn0, Cast cast_data_cpn1 -> failwith "Rvalue::Cast not supported"
| BinaryOp binary_op_data_cpn0, BinaryOp binary_op_data_cpn1 -> failwith "Rvalue::BinaryOp not supported"
| NullaryOp, NullaryOp -> failwith "Rvalue::NullaryOp not supported"
| UnaryOp unary_op_data_cpn0, UnaryOp unary_op_data_cpn1 -> failwith "Rvalue::UnaryOp not supported"
| Aggregate aggregate_data_cpn0, Aggregate aggregate_data_cpn1 ->
  check_aggregate_refines_aggregate env0 span0 aggregate_data_cpn0 env1 span1 aggregate_data_cpn1
| Discriminant place_cpn0, Discriminant place_cpn1 -> failwith "Rvalue::Discriminant not supported"
| ShallowInitBox, ShallowInitBox -> failwith "Rvalue::ShallowInitBox not supported"

type basic_block_status =
  NotSeen
| Checking of int (* i_bb1 *) * (string * string list) list (* Candidate loop invariant: for each local of the verified program, a list of the locals of the original program that have the same value at each iteration *)
| Checked of int (* i_bb1 *) * (string * string list) list (* Loop invariant that was used to verify this loop. *)

exception RecheckLoop of int (* i_bb0 *) (* When this is raised, the specified basic block's status has already been updated with a weakened candidate loop invariant *)

let string_of_loop_inv loopInv =
  String.concat "; " (List.map (fun (x, ys) -> Printf.sprintf "%s: [%s]" x (String.concat ", " ys)) loopInv)

let local_name locals i = VfMirRd.Body.LocalDeclId.name_get @@ VfMirRd.Body.LocalDecl.id_get (Capnp.Array.get locals i)

let havoc_local_var_state = function
  Value _ -> Value (fresh_symbol ())
| Address _ -> Address (fresh_symbol ())

type unification_variable = {mutable unified_with: unification_variable option; mutable value: local_var_state}

let rec unwrap_unif_var x =
  match x.unified_with with
    None -> x
  | Some y -> unwrap_unif_var y

let unify v v' =
  let v = unwrap_unif_var v in
  let v' = unwrap_unif_var v' in
  if v != v' then v.unified_with <- Some v'

(* Produce an environment for the product program that satisfies only the equalities implied by the loop invariant. *)
let produce_loop_inv env0 env1 loopInv =
  let env0 = List.map (fun (x, v) -> (x, {unified_with=None; value=havoc_local_var_state v})) env0 in
  (* Havoc all locals of the verified crate that are not known to be equal to any locals of the original crate *)
  let env1 = List.map2 (fun (x, v) (x, ys) -> (x, let v = {unified_with=None; value=havoc_local_var_state v} in List.iter (fun y -> unify v (List.assoc y env0)) ys; v)) env1 loopInv in
  let env0 = List.map (fun (x, v) -> (x, (unwrap_unif_var v).value)) env0 in
  let env1 = List.map (fun (x, v) -> (x, (unwrap_unif_var v).value)) env1 in
  env0, env1

(*

Perform a simple dataflow analysis to check refinement. We establish a
one-to-one correspondence between local variables in both programs whose address
is taken. Since the execution of the verified program is angelic, we choose the
addresses of these variables to be the same as in the original program, and
similarly for global and heap-allocated variables. We check that the values
of all corresponding nonlocal (i.e. global or heap-allocated) variables, and the
values of corresponding locals whose address is taken, are equal at all times.
We don't attempt to track the specific values. Only for locals whose address is
not taken, we track the values.

*)

let check_body_refines_body def_path body0 body1 =
  Printf.printf "Checking function body %s\n" def_path;
  let inputs0 = VfMirRd.Body.inputs_get_list body0 in
  let inputs1 = VfMirRd.Body.inputs_get_list body1 in
  let locals0 = VfMirRd.Body.local_decls_get body0 in
  let locals1 = VfMirRd.Body.local_decls_get body1 in
  let bblocks0 = VfMirRd.Body.basic_blocks_get body0 in
  let bblocks1 = VfMirRd.Body.basic_blocks_get body1 in
  let inputs = List.map (fun _ -> fresh_symbol ()) inputs0 in
  (* TODO: Check that inputs0 and inputs1 match *)
  let rec check_body_refines_body_core address_taken =
    let env0 = List.mapi (fun i v -> let x = local_name locals0 (i + 1) in if List.mem_assoc x address_taken then [] else [(x, Value v)]) inputs |> List.flatten in
    let env1 = env0 in
    let address_taken0, address_taken1 = address_taken |> List.map (fun (x0, x1) -> let a = fresh_symbol () in ((x0, Address a), (x1, Address a))) |> List.split in
    let env0 = address_taken0 @ env0 in
    let env1 = address_taken1 @ env1 in
    let bblocks0_statuses = Array.make (Capnp.Array.length bblocks0) NotSeen in
    let rec check_basic_block_refines_basic_block env0 i_bb0 env1 i_bb1 =
      Printf.printf "INFO: In function %s, checking basic block %d against basic block %d, with env0 = [%s] and env1 = [%s]\n" def_path i_bb0 i_bb1 (string_of_env env0) (string_of_env env1);
      match bblocks0_statuses.(i_bb0) with
        NotSeen ->
          let loopInv = env1 |> List.map (fun (x, v1) -> (x, env0 |> List.concat_map (fun (y, v0) -> if v1 = v0 then [y] else []) )) in
          bblocks0_statuses.(i_bb0) <- Checking (i_bb1, loopInv);
          let rec iter loopInv =
            try
              Printf.printf "Loop invariant = [%s]\n" (string_of_loop_inv loopInv);
              (* Havoc all locals of the original crate *)
              let env0, env1 = produce_loop_inv env0 env1 loopInv in
              Printf.printf "INFO: In function %s, checking loop body at basic block %d against basic block %d, with env0 = [%s] and env1 = [%s]\n" def_path i_bb0 i_bb1 (string_of_env env0) (string_of_env env1);
              check_codepos_refines_codepos env0 i_bb0 0 env1 i_bb1 0;
              let Checking (i_bb1, loopInv) = bblocks0_statuses.(i_bb0) in
              bblocks0_statuses.(i_bb0) <- Checked (i_bb1, loopInv)
            with RecheckLoop i_bb0' as e ->
              if i_bb0' <> i_bb0 then begin
                bblocks0_statuses.(i_bb0) <- NotSeen;
                raise e
              end else
                let Checking (i_bb1', loopInv) = bblocks0_statuses.(i_bb0) in
                iter loopInv
          in
          iter loopInv
      | Checking (i_bb1', loopInv) ->
        Printf.printf "INFO: In function %s, loop detected with head = basic block %d\n" def_path i_bb0;
        if i_bb1' <> i_bb1 then failwith (Printf.sprintf "In function %s, loop head %d in the original crate is being checked for refinement against basic block %d in the verified crate, but it is already being checked for refinement against loop head %d in the verified crate" def_path i_bb0 i_bb1 i_bb1');
        if loopInv |> List.for_all @@ fun (x, ys) ->
          let v = List.assoc x env1 in
          ys |> List.for_all @@ fun y -> List.assoc y env0 = v
        then begin
          Printf.printf "Loop with head %d verified, with loop invariant %s!\n" i_bb0 (string_of_loop_inv loopInv);
          () (* Use the induction hypothesis; this path is done. *)
        end else begin
          Printf.printf "Loop with head %d failed to verify; trying again with weaker invariant\n" i_bb0;
          (* Forget about the earlier result; try from scratch *)
          let loopInv = loopInv |> List.map @@ fun (x, ys) ->
            let v = List.assoc x env1 in
            (x, ys |> List.filter @@ fun y -> List.assoc y env0 = v)
          in
          bblocks0_statuses.(i_bb0) <- Checking (i_bb1, loopInv); (* Weaken the candidate loop invariant *)
          raise (RecheckLoop i_bb0)
        end
      | Checked (i_bb1', loopInv) ->
        if i_bb1' = i_bb1 && loopInv |> List.for_all @@ fun (x, ys) ->
          let v = List.assoc x env1 in
          ys |> List.for_all @@ fun y -> List.assoc y env0 = v
        then begin
          Printf.printf "Re-reached loop with head %d, that was already verified; path is done.\n" i_bb0;
          () (* Use the induction hypothesis; this path is done. *)
        end else begin
          (* Forget about the earlier result; try from scratch *)
          bblocks0_statuses.(i_bb0) <- NotSeen;
          check_basic_block_refines_basic_block env0 i_bb0 env1 i_bb1
        end
    (* Checks whether for each behavior of code position (bb0, s0), code position (bb1, s1) has a matching behavior *)
    and check_codepos_refines_codepos env0 i_bb0 i_s0 env1 i_bb1 i_s1 =
      let (env0, i_bb0, i_s0) = process_assignments bblocks0 env0 i_bb0 i_s0 in
      let (env1, i_bb1, i_s1) = process_assignments bblocks1 env1 i_bb1 i_s1 in
      let bb0 = Capnp.Array.get bblocks0 i_bb0 in
      let bb1 = Capnp.Array.get bblocks1 i_bb1 in
      let check_terminator_refines_terminator () =
        let terminator0 = VfMirRd.Body.BasicBlock.terminator_get bb0 in
        let terminator1 = VfMirRd.Body.BasicBlock.terminator_get bb1 in
        let span0 = VfMirRd.Body.SourceInfo.span_get @@ VfMirRd.Body.BasicBlock.Terminator.source_info_get terminator0 in
        let span1 = VfMirRd.Body.SourceInfo.span_get @@ VfMirRd.Body.BasicBlock.Terminator.source_info_get terminator1 in
        Printf.printf "INFO: Checking that terminator at %s refines terminator at %s\n" (string_of_span span0) (string_of_span span1);
        let terminatorKind0 = VfMirRd.Body.BasicBlock.Terminator.kind_get terminator0 in
        let terminatorKind1 = VfMirRd.Body.BasicBlock.Terminator.kind_get terminator1 in
        match (VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.get terminatorKind0, VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.get terminatorKind1) with
          (Goto bb_id0, Goto bb_id1) ->
            let bb_idx0 = Stdint.Uint32.to_int @@ VfMirRd.Body.BasicBlockId.index_get bb_id0 in
            let bb_idx1 = Stdint.Uint32.to_int @@ VfMirRd.Body.BasicBlockId.index_get bb_id1 in
            check_basic_block_refines_basic_block env0 bb_idx0 env1 bb_idx1
        | (Return, Return) ->
            let retVal0 = List.assoc (VfMirRd.Body.LocalDeclId.name_get (VfMirRd.Body.LocalDecl.id_get (Capnp.Array.get locals0 0))) env0 in
            let retVal1 = List.assoc (VfMirRd.Body.LocalDeclId.name_get (VfMirRd.Body.LocalDecl.id_get (Capnp.Array.get locals1 0))) env1 in
            if retVal0 <> retVal1 then
              failwith (Printf.sprintf "In function %s, at basic block %d in the original crate and basic block %d in the verified crate, the return values are not equal" def_path i_bb0 i_bb1)
        | (Call call0, Call call1) ->
          let func0 = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.func_get call0 in
          let func1 = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.func_get call1 in
          check_operand_refines_operand 0 env0 span0 func0 env1 span1 func1;
          let args0 = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.args_get call0 in
          let args1 = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.args_get call1 in
          for i = 0 to Capnp.Array.length args0 - 1 do
            let arg0 = Capnp.Array.get args0 i in
            let arg1 = Capnp.Array.get args1 i in
            check_operand_refines_operand (i + 1) env0 span0 arg0 env1 span1 arg1
          done;
          let dest0 = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.destination_get call0 in
          let dest1 = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.destination_get call1 in
          begin match VfMirRd.Util.Option.get dest0, VfMirRd.Util.Option.get dest1 with
            Nothing, Nothing -> ()
          | Something dest0, Something dest1 ->
            let dest0 = VfMirRd.of_pointer dest0 in
            let dest1 = VfMirRd.of_pointer dest1 in
            let dest0PlaceExpr = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.DestinationData.place_get dest0 in
            let dest1PlaceExpr = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.DestinationData.place_get dest1 in
            let dest0bbid = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.DestinationData.basic_block_id_get dest0 in
            let dest1bbid = VfMirRd.Body.BasicBlock.Terminator.TerminatorKind.FnCallData.DestinationData.basic_block_id_get dest1 in
            let dest0bbidx = Stdint.Uint32.to_int @@ VfMirRd.Body.BasicBlockId.index_get dest0bbid in
            let dest1bbidx = Stdint.Uint32.to_int @@ VfMirRd.Body.BasicBlockId.index_get dest1bbid in
            let result = fresh_symbol () in
            begin match check_place_refines_place env0 dest0PlaceExpr env1 dest1PlaceExpr with
              Local x0, Local x1 ->
              let env0 = update_env x0 (Value result) env0 in
              let env1 = update_env x1 (Value result) env1 in
              check_basic_block_refines_basic_block env0 dest0bbidx env1 dest1bbidx
            | Nonlocal, Nonlocal ->
              check_basic_block_refines_basic_block env0 dest0bbidx env1 dest1bbidx
            end
          end
        | _ -> failwith "Unsupported terminator kind"
      in
      let check_statement_refines_statement () =
        let stmts0 = VfMirRd.Body.BasicBlock.statements_get bb0 in
        let stmts1 = VfMirRd.Body.BasicBlock.statements_get bb1 in
        let stmt0 = Capnp.Array.get stmts0 i_s0 in
        let stmt1 = Capnp.Array.get stmts1 i_s1 in
        let stmtSpan0 = VfMirRd.Body.SourceInfo.span_get @@ VfMirRd.Body.BasicBlock.Statement.source_info_get stmt0 in
        let stmtSpan1 = VfMirRd.Body.SourceInfo.span_get @@ VfMirRd.Body.BasicBlock.Statement.source_info_get stmt1 in
        Printf.printf "INFO: Checking that statement at %s refines statement at %s\n" (string_of_span stmtSpan0) (string_of_span stmtSpan1);
        let stmtKind0 = VfMirRd.Body.BasicBlock.Statement.StatementKind.get (VfMirRd.Body.BasicBlock.Statement.kind_get stmt0) in
        let stmtKind1 = VfMirRd.Body.BasicBlock.Statement.StatementKind.get (VfMirRd.Body.BasicBlock.Statement.kind_get stmt1) in
        match (stmtKind0, stmtKind1) with
          (Assign assign_data0, Assign assign_data1) ->
            let rhsRvalue0 = VfMirRd.Body.BasicBlock.Statement.StatementKind.AssignData.rhs_rvalue_get assign_data0 in
            let rhsRvalue1 = VfMirRd.Body.BasicBlock.Statement.StatementKind.AssignData.rhs_rvalue_get assign_data1 in
            check_rvalue_refines_rvalue env0 stmtSpan0 rhsRvalue0 env1 stmtSpan1 rhsRvalue1;
            let lhsPlace0 = VfMirRd.Body.BasicBlock.Statement.StatementKind.AssignData.lhs_place_get assign_data0 in
            let lhsPlace1 = VfMirRd.Body.BasicBlock.Statement.StatementKind.AssignData.lhs_place_get assign_data1 in
            begin match check_place_refines_place env0 lhsPlace0 env1 lhsPlace1 with
              Local x0, Local x1 ->
              let rhsValue = fresh_symbol () in
              let env0 = update_env x0 (Value rhsValue) env0 in
              let env1 = update_env x1 (Value rhsValue) env1 in
              check_codepos_refines_codepos env0 i_bb0 (i_s0 + 1) env1 i_bb1 (i_s1 + 1)
            | Nonlocal, Nonlocal ->
              check_codepos_refines_codepos env0 i_bb0 (i_s0 + 1) env1 i_bb1 (i_s1 + 1)
            end
      in
      let stmts0 = VfMirRd.Body.BasicBlock.statements_get bb0 in
      let stmts1 = VfMirRd.Body.BasicBlock.statements_get bb1 in
      if i_s0 = Capnp.Array.length stmts0 then
        if i_s1 = Capnp.Array.length stmts1 then
          check_terminator_refines_terminator ()
        else
          failwith (Printf.sprintf "In function %s, cannot prove that the terminator of basic block %d in the original version refines statement %d of basic block %d in the verified version" def_path i_bb0 i_s1 i_bb1)
      else
        if i_s1 = Capnp.Array.length stmts1 then
          failwith (Printf.sprintf "In function %s, cannot prove that statement %d of basic block %d in the original version refines the terminator of basic block %d in the verified version" def_path i_s0 i_bb0 i_bb1)
        else
          check_statement_refines_statement ()
    in
    try
      check_basic_block_refines_basic_block env0 0 env1 0
    with LocalAddressTaken (x0, x1) ->
      let address_taken = (x0, x1) :: address_taken in
      Printf.printf "Caught LocalAddressTaken; restarting with address_taken = %s\n" (String.concat ", " (List.map (fun (x0, x1) -> Printf.sprintf "%s = %s" x0 x1) address_taken));
      check_body_refines_body_core address_taken
  in
  check_body_refines_body_core []
