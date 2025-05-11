open Vf_mir_decoder

let string_of_ty ty = "<ty>"

let string_of_basic_block_id bb_id =
  Printf.sprintf "bb_%s" (Stdint.Uint32.to_string bb_id.index)

let string_of_place {local; projection} =
  let rec iter inner = function
    | [] -> inner
    | Deref::rest ->
      iter (Printf.sprintf "*(%s)" inner) rest
    | Field {index}::rest ->
      iter (Printf.sprintf "%s.%s" inner (Stdint.Uint32.to_string index)) rest
    | BoxAsPtr _::rest ->
      iter (Printf.sprintf "box_as_ptr(%s)" inner) rest
    | Index::rest ->
      iter (Printf.sprintf "%s[?]" inner) rest
    | ConstantIndex::rest ->
      iter (Printf.sprintf "%s[constant ?]" inner) rest
    | Subslice::rest ->
      iter (Printf.sprintf "subslice(%s)" inner) rest
    | Downcast k::rest ->
      iter (Printf.sprintf "(%s as %s)" inner (Stdint.Uint32.to_string k)) rest
    | OpaqueCast::rest ->
      iter (Printf.sprintf "opaque_cast(%s)" inner) rest
    | Subtype::rest ->
      iter (Printf.sprintf "subtype(%s)" inner) rest
  in
  iter local.name projection

let string_of_uint128 {h; l} =
  let v = Stdint.Uint128.shift_left (Stdint.Uint128.of_uint64 h) 64 in
  let v = Stdint.Uint128.add v (Stdint.Uint128.of_uint64 l) in
  Stdint.Uint128.to_string v

let string_of_const_value ({kind}: ty) = function
  | Scalar (Int {data; size}) -> Printf.sprintf "%su%d" (string_of_uint128 data) size
  | Scalar Ptr -> "ptr"
  | Slice _ -> "slice"
  | ZeroSized ->
    match kind with
      | Tuple _ -> "()"
      | FnDef {id={name}} -> name

let string_of_mir_const = function
| Ty {ty; const} -> Printf.sprintf "TyConst"
| Val {const_value; ty} -> string_of_const_value ty const_value
| Unevaluated -> Printf.sprintf "UnevaluatedConst"

let string_of_operand = function
  | Copy place -> Printf.sprintf "copy %s" (string_of_place place)
  | Move place -> Printf.sprintf "move %s" (string_of_place place)
  | Constant {const} -> string_of_mir_const const

let string_of_rvalue_ref_data {region; bor_kind; place} =
  Printf.sprintf "&%s%s %s" (match bor_kind with Shared -> "" | Mut -> "mut ") region.id (string_of_place place)

let string_of_bin_op = function
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Rem -> "%"
  | BitAnd -> "&"
  | BitOr -> "|"
  | BitXor -> "^"
  | Shl -> "<<"
  | Shr -> ">>"
  | Eq -> "=="
  | Ne -> "!="
  | Lt -> "<"
  | Le -> "<="
  | Gt -> ">"
  | Ge -> ">="
  | Offset -> "offset"

let string_of_aggregate_kind = function
  | Array ty -> Printf.sprintf "array(%s)" (string_of_ty ty)
  | Tuple -> "tuple"
  | Adt {adt_id; adt_kind; variant_id} ->
    begin match adt_kind with
      | StructKind -> Printf.sprintf "%s" adt_id.name
      | EnumKind -> Printf.sprintf "%s::%s" adt_id.name variant_id
      | UnionKind -> Printf.sprintf "%s::%s" adt_id.name variant_id
    end
  | Closure {closure_id} -> Printf.sprintf "closure(%s)" closure_id

let string_of_rvalue = function
  | Use operand -> string_of_operand operand
  | Repeat -> "<repeat>"
  | Ref data -> string_of_rvalue_ref_data data
  | AddressOf {place} -> Printf.sprintf "&raw %s" (string_of_place place)
  | Len -> "len"
  | Cast {operand; ty} ->
    Printf.sprintf "(%s as %s)" (string_of_operand operand) (string_of_ty ty)
  | BinaryOp {operator; operandl; operandr} ->
    Printf.sprintf "%s %s %s" (string_of_operand operandl) (string_of_bin_op operator) (string_of_operand operandr)
  | Aggregate {aggregate_kind; operands} ->
    Printf.sprintf "%s(%s)" (string_of_aggregate_kind aggregate_kind) (String.concat ", " (List.map string_of_operand operands))
  | Discriminant place ->
    Printf.sprintf "discriminant(%s)" (string_of_place place)

let string_of_statement ({source_info; kind}: statement) =
  match kind with
  | Assign {lhs_place; rhs_rvalue} ->
      Printf.sprintf "%s = %s;" (string_of_place lhs_place) (string_of_rvalue rhs_rvalue)
  | Nop -> "nop;"

let string_of_unwind_action = function
  | Continue -> "continue"
  | Unreachable -> "unreachable"
  | Terminate -> "terminate"
  | Cleanup bb_id -> Printf.sprintf "cleanup(%s)" (string_of_basic_block_id bb_id)

let string_of_terminator {source_info; kind} =
  match kind with
  | Goto bb_id -> Printf.sprintf "goto %s;" (string_of_basic_block_id bb_id)
  | SwitchInt {discr; targets={branches; otherwise}} ->
      let otherwise =
        match otherwise with
        | Something bb_id -> [Printf.sprintf "otherwise -> %s" (string_of_basic_block_id bb_id)]
        | Nothing -> []
      in
      let targets = List.map (fun {val_; target} -> Printf.sprintf "%s -> %s" (string_of_uint128 val_) (string_of_basic_block_id target)) branches @ otherwise in
      Printf.sprintf "switch %s {%s}" (string_of_operand discr) (String.concat ", " targets)
  | UnwindResume -> "unwind_resume;"
  | UnwindTerminate -> "unwind_terminate;"
  | Return -> "return;"
  | Unreachable -> "unreachable;"
  | Call {func; args; destination; unwind_action} ->
      let prolog, epilog =
        match destination with
        | Nothing -> "", "unreachable;"
        | Something {place; basic_block_id} ->
            Printf.sprintf "%s = " (string_of_place place), Printf.sprintf "goto %s;" (string_of_basic_block_id basic_block_id)
      in
      let args_str = String.concat ", " (List.map string_of_operand args) in
      Printf.sprintf "%s%s(%s) on_unwind %s; %s" prolog (string_of_operand func) args_str (string_of_unwind_action unwind_action) epilog
  | Drop {place; target; unwind_action} ->
      Printf.sprintf "drop %s on_unwind %s; goto %s;" (string_of_place place) (string_of_unwind_action unwind_action) (string_of_basic_block_id target)
  | Assert -> "assert;"

let string_of_basic_block bb =
  string_of_basic_block_id bb.id ^ ":\n" ^
  String.concat "" (List.map (fun s -> Printf.sprintf "  %s\n" (string_of_statement s)) bb.statements) ^
  Printf.sprintf "  %s" (string_of_terminator bb.terminator)

let string_of_body body =
  Printf.sprintf "fn %s(%s) -> %s {\n%s\n}"
    body.def_path
    (String.concat ", " (List.map string_of_ty body.inputs))
    (string_of_ty body.output)
    ((*String.concat "\n" (List.map string_of_local_decl body.local_decls) ^ *)
     String.concat "\n" (List.map string_of_basic_block body.basic_blocks))
