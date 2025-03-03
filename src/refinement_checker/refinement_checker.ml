open Vf_mir_decoder
type 'a option = 'a Option.t
module VfMir = S
module VfMirRd = VfMir.Reader

let error msg =
  Printf.printf "ERROR: %s\n" msg;
  exit 1

let decode_path (path: source_file) =
  let name = path.name in
  match name with
  | Real real_file_name -> (
      match
        real_file_name
      with
      | LocalPath path -> path
      | Remapped _ -> failwith "Remapped file names are not yet supported")
  | QuoteExpansion _ -> failwith "Quote expansions are not yet supported"

let decode_loc (loc: loc) =
  let path = decode_path @@ loc.file in
  let line = Stdint.Uint64.to_int @@ loc.line in
  let col = Stdint.Uint64.to_int @@ loc.col.pos in
  (path, line, col)

let decode_span span =
  let lo = span.lo in
  let hi = span.hi in
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
| ISizeValue of int (* size, in bytes; typically 8 *) * Stdint.int64
| U8Value of Stdint.uint8
| U16Value of Stdint.uint16
| U32Value of Stdint.uint32
| U64Value of Stdint.uint64
| U128Value of Stdint.uint128
| USizeValue of int (* size, in bytes; typically 8 *) * Stdint.uint64
| CharValue of Stdint.uint32

type const_expr =
  ParamConstExpr of string
| LiteralConstExpr of literal_const_expr

let decode_uint128 uint128_cpn =
  let h = uint128_cpn.h in
  let l = uint128_cpn.l in
  Stdint.Uint128.logor (Stdint.Uint128.shift_left (Stdint.Uint64.to_uint128 h) 64) (Stdint.Uint64.to_uint128 l)

type adt_kind = Struct | Enum | Union

type region = Region of string

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

let decode_scalar_int ty scalar_int_cpn =
  let data = decode_uint128 scalar_int_cpn.data in
  let size = scalar_int_cpn.size in
  match ty, size with
    Bool, 1 -> BoolValue (data <> Stdint.Uint128.zero)
  | Int (FixedWidth 0), 1 -> I8Value (Stdint.Uint128.to_int8 data)
  | Int (FixedWidth 1), 2 -> I16Value (Stdint.Uint128.to_int16 data)
  | Int (FixedWidth 2), 4 -> I32Value (Stdint.Uint128.to_int32 data)
  | Int (FixedWidth 3), 8 -> I64Value (Stdint.Uint128.to_int64 data)
  | Int (FixedWidth 4), 16 -> I128Value (Stdint.Uint128.to_int128 data)
  | Int PtrWidth, _ -> ISizeValue (size, Stdint.Uint128.to_int64 data)
  | UInt (FixedWidth 0), 1 -> U8Value (Stdint.Uint128.to_uint8 data)
  | UInt (FixedWidth 1), 2 -> U16Value (Stdint.Uint128.to_uint16 data)
  | UInt (FixedWidth 2), 4 -> U32Value (Stdint.Uint128.to_uint32 data)
  | UInt (FixedWidth 3), 8 -> U64Value (Stdint.Uint128.to_uint64 data)
  | UInt (FixedWidth 4), 16 -> U128Value data
  | UInt PtrWidth, _ -> USizeValue (size, Stdint.Uint128.to_uint64 data)
  | Char, 4 -> CharValue (Stdint.Uint128.to_uint32 data)

let rec decode_ty (ty_cpn: Vf_mir_decoder.ty) =
  match ty_cpn.kind with
    Bool -> Bool
  | Int int_ty_cpn ->
    begin match int_ty_cpn with
      I8 -> Int (FixedWidth 0)
    | I16 -> Int (FixedWidth 1)
    | I32 -> Int (FixedWidth 2)
    | I64 -> Int (FixedWidth 3)
    | I128 -> Int (FixedWidth 4)
    | ISize -> Int PtrWidth
    end
  | UInt uint_ty_cpn ->
    begin match uint_ty_cpn with
      U8 -> UInt (FixedWidth 0)
    | U16 -> UInt (FixedWidth 1)
    | U32 -> UInt (FixedWidth 2)
    | U64 -> UInt (FixedWidth 3)
    | U128 -> UInt (FixedWidth 4)
    | USize -> UInt PtrWidth
    end
  | Char -> Char
  | Adt adt_ty_cpn ->
    let name = adt_ty_cpn.id.name in
    let kind =
      match adt_ty_cpn.kind with
        StructKind -> Struct
      | EnumKind -> Enum
      | UnionKind -> Union
    in
    let args = List.map decode_gen_arg adt_ty_cpn.substs in
    Adt (name, kind, args)
  | RawPtr raw_ptr_ty_cpn -> RawPtr (decode_ty raw_ptr_ty_cpn.ty)
  | Ref ref_ty_cpn ->
    let region = Region ref_ty_cpn.region.id in
    let ty = ref_ty_cpn.ty in
    let mutability = ref_ty_cpn.mutability in
    Ref (region, decode_ty ty, mutability)
  | FnDef fn_def_ty_cpn ->
    let id = fn_def_ty_cpn.id.name in
    let args = List.map decode_gen_arg fn_def_ty_cpn.substs in
    FnDef (id, args)
  | Never -> Never
  | Tuple tys -> Tuple (List.map decode_ty tys)
  | Param param -> Param param
  | Str -> Str
  | Array array_ty_cpn ->
    let elem_ty = decode_ty array_ty_cpn.elem_ty in
    let size = decode_const_expr array_ty_cpn.size in
    Array (elem_ty, size)
  | Slice ty_cpn -> Slice (decode_ty ty_cpn)
and decode_gen_arg gen_arg_cpn =
  match gen_arg_cpn.kind with
    Lifetime lifetime -> Lifetime (Region lifetime.id)
  | Type ty -> Type (decode_ty ty)
  | Const const -> Const (decode_const_expr const)
and decode_const_expr const_cpn =
  match const_cpn.kind with
    Param param -> ParamConstExpr param.name
  | Value value_cpn ->
    let ty = decode_ty value_cpn.ty in
    let valtree = value_cpn.val_tree in
    match valtree with
      Leaf scalar_int_cpn -> LiteralConstExpr (decode_scalar_int ty scalar_int_cpn)
    | Branch -> failwith "Branch not supported"

type term = Symbol of int | Tuple of term list | FnDef of string * gen_arg list | ScalarInt of literal_const_expr

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

let eval_const_operand const_operand_cpn =
  let mir_const_cpn = const_operand_cpn.const in
  match mir_const_cpn with
    Ty mir_ty_const_cpn -> failwith "Using typesystem constant expressions as MIR constant operands is not yet supported"
  | Val mir_val_const_cpn ->
    let ty = decode_ty mir_val_const_cpn.ty in
    let mir_const_value_cpn = mir_val_const_cpn.const_value in
    begin match mir_const_value_cpn with
      Scalar scalar_cpn ->
      begin match scalar_cpn with
        Int scalar_int_cpn -> ScalarInt (decode_scalar_int ty scalar_int_cpn)
      | Ptr -> failwith "MIR pointer constants are not yet supported"
      end
    | ZeroSized ->
      begin match ty with
        Tuple [] -> Tuple []
      | FnDef (fn, genArgs) -> FnDef (fn, genArgs)
      | _ -> failwith "Zero-sized constants are not yet supported"
      end
    | Slice slice_cpn -> failwith "MIR slice constants are not yet supported"
    end
  | Unevaluated -> failwith "Unevaluated constant operands are not yet supported"

type call_path = basic_block_path option
and basic_block_path = {bb_caller: basic_block_path option; bb_index: int}

let rec string_of_call_path = function
  None -> ""
| Some caller -> Printf.sprintf "%s." (string_of_basic_block_path caller)
and string_of_basic_block_path {bb_caller; bb_index} =
  Printf.sprintf "%s%d" (string_of_call_path bb_caller) bb_index

type local_variable_path = {lv_caller: call_path; lv_name: string}

let string_of_lv_path {lv_caller; lv_name} = Printf.sprintf "%s%s" (string_of_call_path lv_caller) lv_name

type env = (local_variable_path * local_var_state) list

let string_of_env env =
  String.concat "; " (List.map (fun (x, v) -> Printf.sprintf "%s: %s" (string_of_lv_path x) (string_of_local_var_state v)) env)

let update_env x v env = (x, v) :: List.remove_assoc x env

type basic_block_info = <
  id: basic_block_path;
  statements: statement list;
  terminator: terminator;
  to_string: string;
  sibling: int -> basic_block_info;
  caller: (string (* callee result variable *) * place (* destination place *) * basic_block_info (* destination basic block *)) option;
>

let rec basic_block_info_of bbs bb_idx =
  let bb = bbs.(bb_idx) in
  let id = {bb_caller=None; bb_index=bb_idx} in
  object
    method id = id
    method statements = bb.statements
    method terminator = bb.terminator
    method to_string = Printf.sprintf "%s" (string_of_basic_block_path id)
    method sibling i = basic_block_info_of bbs i
    method caller = None
  end

let local_name (locals: local_decl array) i = locals.(i).id.name

let rec process_assignments bodies (env: env) (i_bb: basic_block_info) i_s (ss_i: statement list) =
  match ss_i with
    [] ->
    begin match i_bb#terminator.kind with
      Call ({func=Constant {const=Val {const_value=ZeroSized; ty={kind=FnDef {id={name=funcName}; substs}}}}} as call) when String.ends_with ~suffix:"__VeriFast_wrapper" funcName ->
      let {args; destination; unwind_action} = call in
      let args = args |> List.map @@ fun arg ->
        match arg with
          Move place | Copy place ->
          let placeProjection = place.projection in
          if placeProjection <> [] then
            failwith "Place projections are not yet supported as wrapper call arguments";
          let placeLocalId = place.local in
          let placeLocalName = placeLocalId.name in
          let placeLocalPath = {lv_caller=i_bb#id.bb_caller; lv_name=placeLocalName} in
          begin match List.assoc placeLocalPath env with
            Value v -> v
          | Address v -> failwith "Locals whose address is taken are not yet supported as wrapper call arguments"
          end
        | Constant constant -> failwith "Constants are not yet supported as wrapper call arguments"
      in
      let caller = Some i_bb#id in
      let body: body = List.assoc funcName bodies in
      let bbs = Array.of_list body.basic_blocks in
      let locals = Array.of_list body.local_decls in
      let env = List.mapi (fun i v -> let x = local_name locals (i + 1) in {lv_caller=caller; lv_name=x}, Value v) args @ env in
      let caller_info =
        match destination with
          Nothing -> failwith "Diverging wrapper calls are not yet supported"
        | Something {place; basic_block_id={index}} -> Some (locals.(0).id.name, place, i_bb#sibling (Stdint.Uint32.to_int index))
      in
      let rec bb_info_of i: basic_block_info =
        let callee_bb_id = {bb_caller=caller; bb_index=i} in
        object
        method id = callee_bb_id
        method statements = bbs.(i).statements
        method terminator = bbs.(i).terminator
        method to_string = Printf.sprintf "Basic block %s" (string_of_basic_block_path callee_bb_id)
        method sibling i = bb_info_of i
        method caller = caller_info
      end in
      process_assignments bodies env (bb_info_of 0) 0 (bbs.(0).statements) (* TODO: deal with unwind_action *)
    | Return when i_bb#caller <> None ->
      let Some (returnLocalName, destinationPlace, destinationBb) = i_bb#caller in
      let returnLocalPath = {lv_caller=i_bb#id.bb_caller; lv_name=returnLocalName} in
      if destinationPlace.projection <> [] then failwith "Wrapper calls whose destination place has a projection are not yet supported";
      begin match List.assoc returnLocalPath env with
        Value v ->
          let destinationLocalPath = {lv_caller=destinationBb#id.bb_caller; lv_name=destinationPlace.local.name} in
          let env = update_env destinationLocalPath (Value v) env in
          process_assignments bodies env destinationBb 0 (destinationBb#statements)
      | Address _ -> failwith "Locals whose address is taken are not yet supported as wrapper call destinations"
      end
    | _ -> (env, i_bb, i_s, ss_i)
    end
  | s::ss_i_plus_1 ->
    match s.kind with
      Assign assign_data ->
        let lhsPlace = assign_data.lhs_place in
        let rhsRvalue = assign_data.rhs_rvalue in
        let lhsProjection = lhsPlace.projection in
        if lhsProjection <> [] then
          (env, i_bb, i_s, ss_i)
        else
          let lhsLocalId = lhsPlace.local in
          let lhsLocalName = lhsLocalId.name in
          let lhsLocalPath = {lv_caller=i_bb#id.bb_caller; lv_name=lhsLocalName} in
          begin match rhsRvalue with
            Use operand ->
              begin match operand with
                Move place | Copy place ->
                  let placeProjection = place.projection in
                  if placeProjection <> [] then
                    (env, i_bb, i_s, ss_i)
                  else
                    let placeLocalId = place.local in
                    let placeLocalName = placeLocalId.name in
                    let placeLocalPath = {lv_caller=i_bb#id.bb_caller; lv_name=placeLocalName} in
                    begin match List.assoc placeLocalPath env with
                      Value placeValue ->
                        begin match List.assoc_opt lhsLocalPath env with
                          Some (Address _) -> (env, i_bb, i_s, ss_i)
                        | _ ->
                          let env = update_env lhsLocalPath (Value placeValue) env in
                          process_assignments bodies env i_bb (i_s + 1) (ss_i_plus_1)
                        end
                    | _ -> (env, i_bb, i_s, ss_i)
                      end
              | Constant constant ->
                  (env, i_bb, i_s, ss_i)
              end
            | _ -> (env, i_bb, i_s, ss_i)
            end
    | Nop -> process_assignments bodies env i_bb (i_s + 1) ss_i_plus_1

let values_equal (v0: term) (v1: term) = v0 = v1

let check_place_element_refines_place_element elem0 elem1 =
  match elem0, elem1 with
  | Deref, Deref -> ()
  | Field field0, Field field1 ->
      let fieldIndex0 = field0.index in
      let fieldIndex1 = field1.index in
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

let local_address_taken path0 path1 =
  if path0.lv_caller <> None then
    failwith "Taking the address of a local variable in an inlined function is not yet supported";
  if path1.lv_caller <> None then
    failwith "Taking the address of a local variable in an inlined function is not yet supported";
  raise (LocalAddressTaken (path0.lv_name, path1.lv_name))

type place =
  Local of local_variable_path (* This place is a local variable whose address is never taken in this function *)
| Nonlocal (* A "nonlocal place" is a plcae that is disjoint from all local variables whose address is never taken in this function *)

(* Checks that the place expressions either both evaluate to a local whose address is never taken, or both evaluate to *the same* "nonlocal place" (see definition above). *)
let check_place_refines_place (env0: env) caller0 place0 (env1: env) caller1 place1 =
  let placeLocalId0 = place0.local in
  let placeLocalName0 = placeLocalId0.name in
  let placeLocalPath0 = {lv_caller=caller0; lv_name=placeLocalName0} in
  let placeLocalId1 = place1.local in
  let placeLocalName1 = placeLocalId1.name in
  let placeLocalPath1 = {lv_caller=caller1; lv_name=placeLocalName1} in
  let placeLocalState0 = List.assoc_opt placeLocalPath0 env0 in
  let placeLocalState1 = List.assoc_opt placeLocalPath1 env1 in
  let placeProjection0 = place0.projection in
  let placeProjection1 = place1.projection in
  if List.length placeProjection0 <> List.length placeProjection1 then
    failwith "The two place expressions have a different number of projection elements";
  match placeLocalState0, placeLocalState1 with
    Some (Address a1), Some (Address a2) ->
      if not (values_equal a1 a2) then failwith "The addresses of the two places are not equal";
      List.iter2 check_place_element_refines_place_element placeProjection0 placeProjection1;
      Nonlocal, Nonlocal
  | Some (Address _), _ | _, Some (Address _) -> failwith "Place expressions do not match"
  | _, _ ->
    (* OK, neither local has its address taken *)
    if placeProjection0 <> [] then
      (* if a local is projected, give up trying to track its value *)
      local_address_taken placeLocalPath0 placeLocalPath1;
    Local placeLocalPath0, Local placeLocalPath1

let check_operand_refines_operand i env0 span0 caller0 operand0 env1 span1 caller1 operand1 =
  match operand0, operand1 with
    (Move placeExpr0, Move placeExpr1) | (Copy placeExpr0, Copy placeExpr1) ->
      begin match check_place_refines_place env0 caller0 placeExpr0 env1 caller1 placeExpr1 with
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

let check_aggregate_refines_aggregate env0 span0 caller0 aggregate0 env1 span1 caller1 aggregate1 =
  let operands0 = aggregate0.operands in
  let operands1 = aggregate1.operands in
  if List.length operands0 <> List.length operands1 then failwith "The two aggregate expressions have a different number of operands";
  List.iteri (fun i (operand0, operand1) -> check_operand_refines_operand i env0 span0 caller0 operand0 env1 span1 caller1 operand1) (List.combine operands0 operands1);
  let aggregate_kind0 = aggregate0.aggregate_kind in
  let aggregate_kind1 = aggregate1.aggregate_kind in
  match aggregate_kind0, aggregate_kind1 with
    Array _, Array _ -> failwith "Aggregate::Array not supported"
  | Tuple, Tuple -> ()
  | Adt adt_data0, Adt adt_data1 ->
    let adt_id0 = adt_data0.adt_id in
    let adt_id0 = adt_id0.name in
    let adt_id1 = adt_data1.adt_id in
    let adt_id1 = adt_id1.name in
    if adt_id0 <> adt_id1 then failwith "Aggregate::Adt: ADT names do not match";
    let variant_idx0 = adt_data0.variant_idx in
    let variant_idx1 = adt_data1.variant_idx in
    if variant_idx0 <> variant_idx1 then failwith "Aggregate::Adt: variant indices do not match";
    let genArgs0 = adt_data0.gen_args in
    let genArgs1 = adt_data1.gen_args in
    if List.map decode_gen_arg genArgs0 <> List.map decode_gen_arg genArgs1 then failwith "Aggregate::Adt: generic arguments do not match";
    let union_active_field_idx0 = adt_data0.union_active_field in
    let union_active_field_idx1 = adt_data1.union_active_field in
    if union_active_field_idx0 <> union_active_field_idx1 then failwith "Aggregate::Adt: union active field indices do not match";
    ()
  | Closure, Closure -> failwith "Aggregate::Closure not supported"
  | Coroutine, Coroutine -> failwith "Aggregate::Coroutine not supported"
  | CoroutineClosure, CoroutineClosure -> failwith "Aggregate::CoroutineClosure not supported"
  | RawPtr, RawPtr -> failwith "Aggregate::RawPtr not supported"
  | _ -> failwith "Aggregate kinds do not match"

(* Checks that the two rvalues evaluate to the same value *)
let check_rvalue_refines_rvalue env0 span0 caller0 rhsRvalue0 env1 span1 caller1 rhsRvalue1 =
  match rhsRvalue0, rhsRvalue1 with
  Use operand0, Use operand1 ->
    check_operand_refines_operand 0 env0 span0 caller0 operand0 env1 span1 caller1 operand1
| Repeat, Repeat -> failwith "Rvalue::Repeat not supported"
| Ref ref_data_cpn0, Ref ref_data_cpn1 ->
  (* We ignore the region because it does not affect the run-time behavior *)
  let borKind0 = ref_data_cpn0.bor_kind in
  let borKind1 = ref_data_cpn1.bor_kind in
  begin match borKind0, borKind1 with
    | Shared, Shared -> ()
    | Mut, Mut -> ()
    | _ -> failwith "Rvalue::Ref: borrow kinds do not match"
  end;
  let placeExpr0 = ref_data_cpn0.place in
  let placeExpr1 = ref_data_cpn1.place in
  begin match check_place_refines_place env0 caller0 placeExpr0 env1 caller1 placeExpr1 with
    Local x0, Local x1 -> local_address_taken x0 x1
  | Nonlocal, Nonlocal -> ()
  end
| ThreadLocalRef, ThreadLocalRef -> failwith "Rvalue::ThreadLocalRef not supported"
| AddressOf address_of_data_cpn0, AddressOf address_of_data_cpn1 -> failwith "Rvalue::AddressOf not supported"
| Len, Len -> failwith "Rvalue::Len not supported"
| Cast cast_data_cpn0, Cast cast_data_cpn1 -> failwith "Rvalue::Cast not supported"
| BinaryOp binary_op_data_cpn0, BinaryOp binary_op_data_cpn1 ->
  let op0 = binary_op_data_cpn0.operator in
  let op1 = binary_op_data_cpn1.operator in
  if op0 <> op1 then failwith "Rvalue::BinaryOp: operators do not match";
  let lhs0 = binary_op_data_cpn0.operandl in
  let lhs1 = binary_op_data_cpn1.operandl in
  check_operand_refines_operand 0 env0 span0 caller0 lhs0 env1 span1 caller1 lhs1;
  let rhs0 = binary_op_data_cpn0.operandr in
  let rhs1 = binary_op_data_cpn1.operandr in
  check_operand_refines_operand 1 env0 span0 caller0 rhs0 env1 span1 caller1 rhs1
| NullaryOp, NullaryOp -> failwith "Rvalue::NullaryOp not supported"
| UnaryOp unary_op_data_cpn0, UnaryOp unary_op_data_cpn1 -> failwith "Rvalue::UnaryOp not supported"
| Aggregate aggregate_data_cpn0, Aggregate aggregate_data_cpn1 ->
  check_aggregate_refines_aggregate env0 span0 caller0 aggregate_data_cpn0 env1 span1 caller1 aggregate_data_cpn1
| Discriminant place_cpn0, Discriminant place_cpn1 ->
  begin match check_place_refines_place env0 caller0 place_cpn0 env1 caller1 place_cpn1 with
    Local x0, Local x1 -> if List.assoc x0 env0 <> List.assoc x1 env1 then failwith "The discriminees of the two rvalues are not equal"
  | Nonlocal, Nonlocal -> ()
  end
| ShallowInitBox, ShallowInitBox -> failwith "Rvalue::ShallowInitBox not supported"

type loop_invariant = (local_variable_path * local_variable_path list) list (* For each local of the verified program, a list of the locals of the original program that have the same value at each iteration *)

type basic_block_status =
  Checking of basic_block_path (* i_bb1 *) * loop_invariant (* Candidate loop invariant *)
| Checked of basic_block_path (* i_bb1 *) * loop_invariant (* Loop invariant that was used to verify this loop. *)

exception RecheckLoop of basic_block_path (* i_bb0 *) (* When this is raised, the specified basic block's status has already been updated with a weakened candidate loop invariant *)

let string_of_loop_inv (loopInv: loop_invariant) =
  String.concat "; " (List.map (fun (x, ys) -> Printf.sprintf "%s: [%s]" (string_of_lv_path x) (String.concat ", " (List.map string_of_lv_path ys))) loopInv)

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

type generic_param_kind = Lifetime | Type | Const

type generic_param = string (* name *) * generic_param_kind

let decode_generic_param (generic_param: generic_param_def) =
  let name = generic_param.name in
  let kind =
    match generic_param.kind with
      Lifetime -> Lifetime
    | Type -> Type
    | Const -> Const
  in
  name, kind

let check_predicate_refines_predicate pred0 pred1 =
  match pred0, pred1 with
    Outlives outlives_pred0, Outlives outlives_pred1 ->
      let region1_0 = outlives_pred0.region1 in
      let region1_1 = outlives_pred1.region1 in
      if region1_0 <> region1_1 then failwith "The two outlives predicates have different regions on the left-hand side";
      let region2_0 = outlives_pred0.region2 in
      let region2_1 = outlives_pred1.region2 in
      if region2_0 <> region2_1 then failwith "The two outlives predicates have different regions on the right-hand side"
  | Trait trait_pred0, Trait trait_pred1 ->
      let trait_id0 = trait_pred0.def_id in
      let trait_id1 = trait_pred1.def_id in
      if trait_id0 <> trait_id1 then failwith "The two trait predicates have different trait IDs";
      let generic_args0 = trait_pred0.args in
      let generic_args1 = trait_pred1.args in
      if List.map decode_gen_arg generic_args0 <> List.map decode_gen_arg generic_args1 then failwith "The two trait predicates have different generic arguments"
  | Projection projection_pred0, Projection projection_pred1 ->
      let proj_term0 = projection_pred0.projection_term in
      let proj_term1 = projection_pred1.projection_term in
      let proj_term_def_id0 = proj_term0.def_id in
      let proj_term_def_id1 = proj_term1.def_id in
      if proj_term_def_id0 <> proj_term_def_id1 then failwith "The two projection predicates have different alias identifiers";
      let proj_term_generic_args0 = proj_term0.args in
      let proj_term_generic_args1 = proj_term1.args in
      if List.map decode_gen_arg proj_term_generic_args0 <> List.map decode_gen_arg proj_term_generic_args1 then failwith "The two projection predicates have different alias generic arguments";
      let rhs0 = projection_pred0.term in
      let rhs1 = projection_pred1.term in
      begin match rhs0, rhs1 with
        Ty ty0, Ty ty1 ->
          if decode_ty ty0 <> decode_ty ty1 then failwith "The two projection predicates have different right-hand side types"
      | Const const0, Const const1 ->
          if decode_const_expr const0 <> decode_const_expr const1 then failwith "The two projection predicates have different right-hand side constants"
      end
  | _ -> failwith "The two predicates have different kinds"

let check_body_refines_body verified_bodies def_path body0 body1 =
  Printf.printf "Checking function body %s\n" def_path;
  let visibility0 = body0.visibility in
  let visibility1 = body1.visibility in
  if visibility0 <> visibility1 then failwith "The two functions have different visibilities";
  let unsafety0 = body0.unsafety in
  let unsafety1 = body1.unsafety in
  (* We allow private functions to have different visibility *)
  if visibility0 = Public && unsafety0 = Safe && unsafety1 = Unsafe then failwith "The two functions have different unsafety";
  let generics0 = body0.generics in
  let generics1 = body1.generics in
  if List.length generics0 <> List.length generics1 then failwith "The two functions have a different number of generic parameters";
  let generics0 = List.map decode_generic_param generics0 in
  let generics1 = List.map decode_generic_param generics1 in
  if generics0 <> generics1 then failwith "The two functions have different generic parameters";
  let preds0 = body0.predicates in
  let preds1 = body1.predicates in
  if List.length preds0 <> List.length preds1 then failwith "The two functions have a different number of predicates";
  List.iter2 check_predicate_refines_predicate preds0 preds1;
  let inputs0 = body0.inputs in
  let inputs1 = body1.inputs in
  let inputs0 = List.map decode_ty inputs0 in
  let inputs1 = List.map decode_ty inputs1 in
  if inputs0 <> inputs1 then failwith "The two functions have different input types";
  let locals0 = Array.of_list body0.local_decls in
  let locals1 = Array.of_list body1.local_decls in
  let inputs = List.map (fun _ -> fresh_symbol ()) inputs0 in
  (* We don't support the case where locals in inlined callees have their address taken, so address_taken always refers to locals of the root bodies. *)
  let rec check_body_refines_body_core address_taken =
    let env0 = List.mapi (fun i v -> let x = local_name locals0 (i + 1) in if List.mem_assoc x address_taken then [] else [{lv_caller=None; lv_name=x}, Value v]) inputs |> List.flatten in
    let env1 = List.mapi (fun i v -> let x = local_name locals1 (i + 1) in if List.exists (fun (x0, x1) -> x1 = x) address_taken then [] else [{lv_caller=None; lv_name=x}, Value v]) inputs |> List.flatten in
    let address_taken0, address_taken1 = address_taken |> List.map (fun (x0, x1) -> let a = fresh_symbol () in (({lv_caller=None; lv_name=x0}, Address a), ({lv_caller=None; lv_name=x1}, Address a))) |> List.split in
    let env0 = address_taken0 @ env0 in
    let env1 = address_taken1 @ env1 in
    let bblocks0_statuses: (basic_block_path, basic_block_status) Hashtbl.t = Hashtbl.create 100 in
    let rec check_basic_block_refines_basic_block (env0: env) (i_bb0: basic_block_info) (env1: env) (i_bb1: basic_block_info) =
      Printf.printf "INFO: In function %s, checking basic block %s against basic block %s, with env0 = [%s] and env1 = [%s]\n" def_path i_bb0#to_string i_bb1#to_string (string_of_env env0) (string_of_env env1);
      match Hashtbl.find_opt bblocks0_statuses i_bb0#id with
        None ->
          let loopInv = env1 |> List.map (fun (x, v1) -> (x, env0 |> List.concat_map (fun (y, v0) -> if v1 = v0 then [y] else []) )) in
          Hashtbl.replace bblocks0_statuses i_bb0#id (Checking (i_bb1#id, loopInv));
          let rec iter loopInv =
            try
              Printf.printf "Loop invariant = [%s]\n" (string_of_loop_inv loopInv);
              (* Havoc all locals of the original crate *)
              let env0, env1 = produce_loop_inv env0 env1 loopInv in
              Printf.printf "INFO: In function %s, checking loop body at basic block %s against basic block %s, with env0 = [%s] and env1 = [%s]\n" def_path i_bb0#to_string i_bb1#to_string (string_of_env env0) (string_of_env env1);
              check_codepos_refines_codepos env0 i_bb0 0 i_bb0#statements env1 i_bb1 0 i_bb1#statements;
              let Checking (i_bb1, loopInv) = Hashtbl.find bblocks0_statuses i_bb0#id in
              Hashtbl.replace bblocks0_statuses i_bb0#id (Checked (i_bb1, loopInv))
            with RecheckLoop i_bb0' as e ->
              if i_bb0' <> i_bb0#id then begin
                Hashtbl.remove bblocks0_statuses i_bb0#id;
                raise e
              end else
                let Checking (i_bb1', loopInv) = Hashtbl.find bblocks0_statuses i_bb0#id in
                iter loopInv
          in
          iter loopInv
      | Some (Checking (i_bb1', loopInv)) ->
        Printf.printf "INFO: In function %s, loop detected with head = basic block %s\n" def_path i_bb0#to_string;
        if i_bb1' <> i_bb1#id then failwith (Printf.sprintf "In function %s, loop head %s in the original crate is being checked for refinement against basic block %s in the verified crate, but it is already being checked for refinement against loop head %s in the verified crate" def_path i_bb0#to_string i_bb1#to_string (string_of_basic_block_path i_bb1'));
        if loopInv |> List.for_all @@ fun (x, ys) ->
          let v = List.assoc x env1 in
          ys |> List.for_all @@ fun y -> List.assoc y env0 = v
        then begin
          Printf.printf "Loop with head %s verified, with loop invariant %s!\n" i_bb0#to_string (string_of_loop_inv loopInv);
          () (* Use the induction hypothesis; this path is done. *)
        end else begin
          Printf.printf "Loop with head %s failed to verify; trying again with weaker invariant\n" i_bb0#to_string;
          (* Forget about the earlier result; try from scratch *)
          let loopInv = loopInv |> List.map @@ fun (x, ys) ->
            let v = List.assoc x env1 in
            (x, ys |> List.filter @@ fun y -> List.assoc y env0 = v)
          in
          Hashtbl.replace bblocks0_statuses i_bb0#id (Checking (i_bb1#id, loopInv)); (* Weaken the candidate loop invariant *)
          raise (RecheckLoop i_bb0#id)
        end
      | Some (Checked (i_bb1', loopInv)) ->
        if i_bb1' = i_bb1#id && loopInv |> List.for_all @@ fun (x, ys) ->
          match List.assoc_opt x env1 with None -> false | Some v ->
          ys |> List.for_all @@ fun y -> match List.assoc_opt y env0 with None -> false | Some v' -> v' = v
        then begin
          Printf.printf "Re-reached loop with head %s, that was already verified; path is done.\n" i_bb0#to_string;
          () (* Use the induction hypothesis; this path is done. *)
        end else begin
          (* Forget about the earlier result; try from scratch *)
          Hashtbl.remove bblocks0_statuses i_bb0#id;
          check_basic_block_refines_basic_block env0 i_bb0 env1 i_bb1
        end
    (* Checks whether for each behavior of code position (bb0, s0), code position (bb1, s1) has a matching behavior *)
    and check_codepos_refines_codepos env0 i_bb0 i_s0 ss_i0 env1 i_bb1 i_s1 ss_i1 =
      let (env0, i_bb0, i_s0, ss_i0) = process_assignments [] env0 i_bb0 i_s0 ss_i0 in
      let (env1, i_bb1, i_s1, ss_i1) = process_assignments verified_bodies env1 i_bb1 i_s1 ss_i1 in
      let caller0 = i_bb0#id.bb_caller in
      let caller1 = i_bb1#id.bb_caller in
      let check_terminator_refines_terminator env1 =
        let terminator0 = i_bb0#terminator in
        let terminator1 = i_bb1#terminator in
        let span0 = terminator0.source_info.span in
        let span1 = terminator1.source_info.span in
        Printf.printf "INFO: Checking that terminator at %s refines terminator at %s\n" (string_of_span span0) (string_of_span span1);
        let terminatorKind0 = terminator0.kind in
        let terminatorKind1 = terminator1.kind in
        match (terminatorKind0, terminatorKind1) with
          (Goto bb_id0, Goto bb_id1) ->
            let bb_idx0 = Stdint.Uint32.to_int @@ bb_id0.index in
            let bb_idx1 = Stdint.Uint32.to_int @@ bb_id1.index in
            check_basic_block_refines_basic_block env0 (i_bb0#sibling bb_idx0) env1 (i_bb1#sibling bb_idx1)
        | (SwitchInt switch_int_data0, SwitchInt switch_int_data1) ->
          let discr0 = switch_int_data0.discr in
          let discr1 = switch_int_data1.discr in
          check_operand_refines_operand 0 env0 span0 caller0 discr0 env1 span1 caller1 discr1;
          let targets0 = switch_int_data0.targets in
          let targets1 = switch_int_data1.targets in
          let branches0 = targets0.branches in
          let branches1 = targets1.branches in
          if List.length branches0 <> List.length branches1 then failwith "The two switch statements have a different number of branches";
          List.combine branches0 branches1 |> List.iter (fun (branch0, branch1) ->
            let val0 = decode_uint128 @@ branch0.val_ in
            let val1 = decode_uint128 @@ branch1.val_ in
            if val0 <> val1 then failwith "SwitchInt branch values do not match";
            let target0 = branch0.target in
            let target1 = branch1.target in
            let target0bbid = target0.index in
            let target1bbid = target1.index in
            let target0bbidx = Stdint.Uint32.to_int target0bbid in
            let target1bbidx = Stdint.Uint32.to_int target1bbid in
            check_basic_block_refines_basic_block env0 (i_bb0#sibling target0bbidx) env1 (i_bb1#sibling target1bbidx)
          );
          let otherwise0 = targets0.otherwise in
          let otherwise1 = targets1.otherwise in
          begin match otherwise0, otherwise1 with
            Nothing, Nothing -> ()
          | Something target0, Something target1 ->
            let target0bbidx = Stdint.Uint32.to_int target0.index in
            let target1bbidx = Stdint.Uint32.to_int target1.index in
            check_basic_block_refines_basic_block env0 (i_bb0#sibling target0bbidx) env1 (i_bb1#sibling target1bbidx)
          end
        | UnwindResume, UnwindResume -> ()
        | UnwindTerminate, UnwindTerminate -> ()
        | (Return, Return) ->
            let retVal0 = List.assoc {lv_caller=None; lv_name=locals0.(0).id.name} env0 in
            let retVal1 = List.assoc {lv_caller=None; lv_name=locals1.(0).id.name} env1 in
            if retVal0 <> retVal1 then
              failwith (Printf.sprintf "In function %s, at basic block %s in the original crate and basic block %s in the verified crate, the return values are not equal" def_path i_bb0#to_string i_bb1#to_string)
        | _, Unreachable -> ()
        | (Call call0, Call call1) ->
          let func0 = call0.func in
          let func1 = call1.func in
          check_operand_refines_operand 0 env0 span0 caller0 func0 env1 span1 caller1 func1;
          let args0 = call0.args in
          let args1 = call1.args in
          List.combine args0 args1 |> List.iteri (fun i (arg0, arg1) ->
            check_operand_refines_operand (i + 1) env0 span0 caller0 arg0 env1 span1 caller1 arg1
          );
          let dest0 = call0.destination in
          let dest1 = call1.destination in
          begin match dest0, dest1 with
            Nothing, Nothing -> ()
          | Something dest0, Something dest1 ->
            let dest0PlaceExpr = dest0.place in
            let dest1PlaceExpr = dest1.place in
            let dest0bbid = dest0.basic_block_id in
            let dest1bbid = dest1.basic_block_id in
            let dest0bbidx = Stdint.Uint32.to_int dest0bbid.index in
            let dest1bbidx = Stdint.Uint32.to_int dest1bbid.index in
            let result = fresh_symbol () in
            begin match check_place_refines_place env0 caller0 dest0PlaceExpr env1 caller1 dest1PlaceExpr with
              Local x0, Local x1 ->
              let env0 = update_env x0 (Value result) env0 in
              let env1 = update_env x1 (Value result) env1 in
              check_basic_block_refines_basic_block env0 (i_bb0#sibling dest0bbidx) env1 (i_bb1#sibling dest1bbidx)
            | Nonlocal, Nonlocal ->
              check_basic_block_refines_basic_block env0 (i_bb0#sibling dest0bbidx) env1 (i_bb1#sibling dest1bbidx)
            end
          end
          (* TODO: Check that unwindAction0 refines unwindAction1 *)
        | Drop drop_data0, Drop drop_data1 -> failwith "Drop not supported"
        | TailCall, TailCall -> failwith "TailCall not supported"
        | Assert, Assert -> failwith "Assert not supported"
        | Yield, Yield -> failwith "Yield not supported"
        | CoroutineDrop, CoroutineDrop -> failwith "CoroutineDrop not supported"
        | FalseEdge, FalseEdge -> failwith "FalseEdge not supported"
        | InlineAsm, InlineAsm -> failwith "InlineAsm not supported"
        | _ -> failwith "Terminator kinds do not match"
      in
      let check_statement_refines_statement () =
        let stmt0::ss_i0_plus_1 = ss_i0 in
        let stmt1::ss_i1_plus_1 = ss_i1 in
        let stmtSpan0 = stmt0.source_info.span in
        let stmtSpan1 = stmt1.source_info.span in
        Printf.printf "INFO: Checking that statement at %s refines statement at %s\n" (string_of_span stmtSpan0) (string_of_span stmtSpan1);
        let stmtKind0 = stmt0.kind in
        let stmtKind1 = stmt1.kind in
        match (stmtKind0, stmtKind1) with
          (Assign assign_data0, Assign assign_data1) ->
            let rhsRvalue0 = assign_data0.rhs_rvalue in
            let rhsRvalue1 = assign_data1.rhs_rvalue in
            check_rvalue_refines_rvalue env0 stmtSpan0 caller0 rhsRvalue0 env1 stmtSpan1 caller1 rhsRvalue1;
            let lhsPlace0 = assign_data0.lhs_place in
            let lhsPlace1 = assign_data1.lhs_place in
            begin match check_place_refines_place env0 caller0 lhsPlace0 env1 caller1 lhsPlace1 with
              Local x0, Local x1 ->
              let rhsValue = fresh_symbol () in
              let env0 = update_env x0 (Value rhsValue) env0 in
              let env1 = update_env x1 (Value rhsValue) env1 in
              check_codepos_refines_codepos env0 i_bb0 (i_s0 + 1) ss_i0_plus_1 env1 i_bb1 (i_s1 + 1) ss_i1_plus_1
            | Nonlocal, Nonlocal ->
              check_codepos_refines_codepos env0 i_bb0 (i_s0 + 1) ss_i0_plus_1 env1 i_bb1 (i_s1 + 1) ss_i1_plus_1
            end
      in
      if ss_i0 = [] then
        (* Process assignments of the form `x = &*y;` where x and y are locals whose address is not taken.
          * We are here using the property that inserting such statements can only cause a program to have more UB, so if it verifies, the original program is also safe.
          *)
        match ss_i1 with
          [] -> check_terminator_refines_terminator env1
        | stmt1::ss_i1_plus_1 ->
          let fail () =
            failwith (Printf.sprintf "In function %s, cannot prove that the terminator of basic block %s in the original version refines statement %d of basic block %s in the verified version" def_path i_bb0#to_string i_s1 i_bb1#to_string)
          in
          match stmt1.kind with
            Assign assign_data1 ->
              let rhsRvalue1 = assign_data1.rhs_rvalue in
              begin match rhsRvalue1 with
                Ref ref_data_cpn1 ->
                  let borKind1 = ref_data_cpn1.bor_kind in
                  begin match borKind1 with
                    Shared ->
                      let rhsPlaceExpr1 = ref_data_cpn1.place in
                      let rhsPlaceLocalId1 = rhsPlaceExpr1.local in
                      let rhsPlaceLocalName1 = rhsPlaceLocalId1.name in
                      let rhsPlaceLocalPath1 = {lv_caller=caller1; lv_name=rhsPlaceLocalName1} in
                      let rhsPlaceProjection1 = rhsPlaceExpr1.projection in
                      if List.length rhsPlaceProjection1 <> 1 then fail ();
                      let rhsPlaceProjectionElem1 = List.hd rhsPlaceProjection1 in
                      begin match rhsPlaceProjectionElem1 with
                        Deref ->
                          begin match List.assoc_opt rhsPlaceLocalPath1 env1 with
                            Some (Value rhsValue) ->
                              let lhsPlaceExpr1 = assign_data1.lhs_place in
                              let lhsPlaceLocalId1 = lhsPlaceExpr1.local in
                              let lhsPlaceLocalName1 = lhsPlaceLocalId1.name in
                              let lhsPlaceLocalPath1 = {lv_caller=caller1; lv_name=lhsPlaceLocalName1} in
                              let lhsPlaceProjection1 = lhsPlaceExpr1.projection in
                              if lhsPlaceProjection1 <> [] then fail ();
                              begin match List.assoc_opt lhsPlaceLocalPath1 env1 with
                                Some (Address _) -> fail ()
                              | _ ->
                                let env1 = update_env lhsPlaceLocalPath1 (Value rhsValue) env1 in
                                check_codepos_refines_codepos env0 i_bb0 i_s0 ss_i0 env1 i_bb1 (i_s1 + 1) ss_i1_plus_1
                              end
                          | _ -> fail ()
                          end
                      | _ -> fail ()
                      end
                  | _ -> fail ()
                  end
              | _ -> fail ()
              end
          | _ -> fail ()
      else
        if ss_i1 = [] then
          failwith (Printf.sprintf "In function %s, cannot prove that statement %d of basic block %s in the original version refines the terminator of basic block %s in the verified version" def_path i_s0 i_bb0#to_string i_bb1#to_string)
        else
          check_statement_refines_statement ()
    in
    try
      check_basic_block_refines_basic_block env0 (basic_block_info_of (Array.of_list body0.basic_blocks) 0) env1 (basic_block_info_of (Array.of_list body1.basic_blocks) 0)
    with LocalAddressTaken (x0, x1) ->
      let address_taken = (x0, x1) :: address_taken in
      Printf.printf "Caught LocalAddressTaken; restarting with address_taken = %s\n" (String.concat ", " (List.map (fun (x0, x1) -> Printf.sprintf "%s = %s" x0 x1) address_taken));
      check_body_refines_body_core address_taken
  in
  check_body_refines_body_core []
