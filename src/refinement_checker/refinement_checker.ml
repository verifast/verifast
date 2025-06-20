open Vf_mir_decoder
type 'a option = 'a Option.t
module VfMir = S
module VfMirRd = VfMir.Reader

let canonicalize_def_path_re = Str.regexp "'[a-zA-Z_][a-zA-Z0-9_]*"

let canonicalize_def_path def_path =
  (* Use a regex to replace each lifetime (of the form 'abc) in def_path by '_ *)
  Str.global_replace canonicalize_def_path_re "'_" def_path

let popn n xs =
  let rec iter n vs xs =
    if n <= 0 then vs, xs
    else let v::xs = xs in iter (n - 1) (v::vs) xs
  in
  iter n [] xs

let string_of_mutability: mutability -> string = function
  Mut -> "Mut"
| Not -> "Not"

let error msg =
  Printf.printf "ERROR: %s\n" msg;
  exit 1

let decode_path (path: source_file) =
  let name = path.name in
  match name with
  | Real real_file_name ->
      begin match
        real_file_name
      with
      | LocalPath path -> path
      | Remapped {local_path; virtual_name} ->
        "<" ^ virtual_name ^ (match local_path with Nothing -> "" | Something {text} -> "#" ^ text) ^ ">"
      end
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

let string_of_literal_const_expr = function
  BoolValue b -> Printf.sprintf "BoolValue %b" b
| I8Value i -> Printf.sprintf "I8Value %s" (Stdint.Int8.to_string i)
| I16Value i -> Printf.sprintf "I16Value %s" (Stdint.Int16.to_string i)
| I32Value i -> Printf.sprintf "I32Value %s" (Stdint.Int32.to_string i)
| I64Value i -> Printf.sprintf "I64Value %s" (Stdint.Int64.to_string i)
| I128Value i -> Printf.sprintf "I128Value %s" (Stdint.Int128.to_string i)
| ISizeValue (size, i) -> Printf.sprintf "ISizeValue %d %s" size (Stdint.Int64.to_string i)
| U8Value i -> Printf.sprintf "U8Value %s" (Stdint.Uint8.to_string i)
| U16Value i -> Printf.sprintf "U16Value %s" (Stdint.Uint16.to_string i)
| U32Value i -> Printf.sprintf "U32Value %s" (Stdint.Uint32.to_string i)
| U64Value i -> Printf.sprintf "U64Value %s" (Stdint.Uint64.to_string i)
| U128Value i -> Printf.sprintf "U128Value %s" (Stdint.Uint128.to_string i)
| USizeValue (size, i) -> Printf.sprintf "USizeValue %d %s" size (Stdint.Uint64.to_string i)
| CharValue i -> Printf.sprintf "CharValue %s" (Stdint.Uint32.to_string i)

type const_expr =
  ParamConstExpr of string
| LiteralConstExpr of literal_const_expr

let string_of_const_expr = function
  ParamConstExpr param -> Printf.sprintf "ParamConstExpr %s" param
| LiteralConstExpr literal -> string_of_literal_const_expr literal

let decode_uint128 uint128_cpn =
  let h = uint128_cpn.h in
  let l = uint128_cpn.l in
  Stdint.Uint128.logor (Stdint.Uint128.shift_left (Stdint.Uint64.to_uint128 h) 64) (Stdint.Uint64.to_uint128 l)

let encode_uint128 n =
  {h=Stdint.Uint64.of_uint128 (Stdint.Uint128.shift_right n 64); l=Stdint.Uint64.of_uint128 n}

type adt_kind = Struct | Enum | Union

type region = Region of string

let string_of_region = function
  Region s -> s

type ty =
  Bool
| Int of int_width
| UInt of int_width
| Char
| Adt of string * adt_kind * gen_arg list
| RawPtr of ty
| Ref of region * ty * mutability
| FnDef of string * gen_arg list
| FnPtr of ty_kind_fn_ptr_ty
| Closure of string * gen_arg list
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

let rec string_of_ty = function
  Bool -> "Bool"
| Int (FixedWidth n) -> Printf.sprintf "Int (FixedWidth %d)" n
| Int PtrWidth -> "Int PtrWidth"
| UInt (FixedWidth n) -> Printf.sprintf "UInt (FixedWidth %d)" n
| UInt PtrWidth -> "UInt PtrWidth"
| Char -> "Char"
| Adt (name, kind, args) -> Printf.sprintf "Adt %s %s" name (String.concat "; " (List.map string_of_gen_arg args))
| RawPtr ty -> Printf.sprintf "RawPtr %s" (string_of_ty ty)
| Ref (region, ty, mutability) -> Printf.sprintf "Ref %s %s %s" (string_of_region region) (string_of_ty ty) (string_of_mutability mutability)
| FnDef (id, args) -> Printf.sprintf "FnDef %s %s" id (String.concat "; " (List.map string_of_gen_arg args))
| FnPtr _ -> "FnPtr <info elided>"
| Closure (id, args) -> Printf.sprintf "Closure %s %s" id (String.concat "; " (List.map string_of_gen_arg args))
| Never -> "Never"
| Tuple tys -> Printf.sprintf "Tuple [%s]" (String.concat "; " (List.map string_of_ty tys))
| Param param -> Printf.sprintf "Param %s" param
| Str -> "Str"
| Array (ty, size) -> Printf.sprintf "Array %s %s" (string_of_ty ty) (string_of_const_expr size)
| Slice ty -> Printf.sprintf "Slice %s" (string_of_ty ty)
and string_of_gen_arg = function
  Lifetime region -> Printf.sprintf "Lifetime %s" (string_of_region region)
| Type ty -> Printf.sprintf "Type %s" (string_of_ty ty)
| Const const -> Printf.sprintf "Const %s" (string_of_const_expr const)

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

type generic_env = {
  lifetimes: (string * region) list;
  types: (string * ty) list;
  consts: (string * const_expr) list;
}

let string_of_genv genv =
  Printf.sprintf "{lifetimes=[%s]; types=[%s]; consts=[%s]}"
    (String.concat "; " (List.map (fun (name, region) -> Printf.sprintf "%s: %s" name (string_of_region region)) genv.lifetimes))
    (String.concat "; " (List.map (fun (name, ty) -> Printf.sprintf "%s: %s" name (string_of_ty ty)) genv.types))
    (String.concat "; " (List.map (fun (name, const) -> Printf.sprintf "%s: %s" name (string_of_const_expr const)) genv.consts))

let decode_lifetime genv: Vf_mir_decoder.region -> region = function
  {id="'<erased>"} -> Region "'<erased>"
| {id} ->
  try List.assoc id genv.lifetimes
  with Not_found -> failwith (Printf.sprintf "No such lifetime: %s (known lifetimes: %s)" id (String.concat ", " (List.map fst genv.lifetimes)))

let rec decode_ty (genv: generic_env) (ty_cpn: Vf_mir_decoder.ty) =
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
  | Float -> failwith "TODO: Float"
  | Adt adt_ty_cpn ->
    let name = adt_ty_cpn.id.name in
    let kind =
      match adt_ty_cpn.kind with
        StructKind -> Struct
      | EnumKind -> Enum
      | UnionKind -> Union
    in
    let args = List.map (decode_gen_arg genv) adt_ty_cpn.substs in
    Adt (name, kind, args)
  | Foreign -> failwith "TODO: Foreign"
  | RawPtr raw_ptr_ty_cpn -> RawPtr (decode_ty genv raw_ptr_ty_cpn.ty)
  | Ref ref_ty_cpn ->
    let region = decode_lifetime genv ref_ty_cpn.region in
    let ty = ref_ty_cpn.ty in
    let mutability = ref_ty_cpn.mutability in
    Ref (region, decode_ty genv ty, mutability)
  | FnDef fn_def_ty_cpn ->
    let id = fn_def_ty_cpn.id.name in
    let args = List.map (decode_gen_arg genv) fn_def_ty_cpn.substs in
    FnDef (id, args)
  | FnPtr info -> FnPtr info (* FIXME: The MIR exporter throws away some FnPtr info unsoundly *)
  | Dynamic -> failwith "TODO: Dynamic"
  | Closure closure_ty_cpn ->
    let id = closure_ty_cpn.def_id in
    let args = List.map (decode_gen_arg genv) closure_ty_cpn.substs in
    Closure (id, args)
  | CoroutineClosure -> failwith "TODO: CoroutineClosure"
  | Coroutine -> failwith "TODO: Coroutine"
  | CoroutineWitness -> failwith "TODO: CoroutineWitness"
  | Never -> Never
  | Tuple tys -> Tuple (List.map (decode_ty genv) tys)
  | Alias _ -> failwith "TODO: Alias"
  | Param param -> (try List.assoc param genv.types with Not_found -> failwith ("No such type parameter: " ^ param))
  | Bound -> failwith "TODO: Bound"
  | Placeholder -> failwith "TODO: Placeholder"
  | Infer -> failwith "TODO: Infer"
  | Error -> failwith "TODO: Error"
  | Str -> Str
  | Array array_ty_cpn ->
    let elem_ty = decode_ty genv array_ty_cpn.elem_ty in
    let size = decode_const_expr genv array_ty_cpn.size in
    Array (elem_ty, size)
  | Pattern -> failwith "TODO: Pattern"
  | Slice ty_cpn -> Slice (decode_ty genv ty_cpn)
and decode_gen_arg genv gen_arg_cpn =
  match gen_arg_cpn.kind with
    Lifetime lifetime -> Lifetime (decode_lifetime genv lifetime)
  | Type ty -> Type (decode_ty genv ty)
  | Const const -> Const (decode_const_expr genv const)
and decode_const_expr genv const_cpn =
  match const_cpn.kind with
    Param param -> List.assoc param.name genv.consts
  | Value value_cpn ->
    let ty = decode_ty genv value_cpn.ty in
    let valtree = value_cpn.val_tree in
    match valtree with
      Leaf scalar_int_cpn -> LiteralConstExpr (decode_scalar_int ty scalar_int_cpn)
    | Branch -> failwith "Branch not supported"

type call_path = basic_block_path option
and basic_block_path = {bb_caller: basic_block_path option; bb_index: int}

let rec string_of_call_path = function
  None -> ""
| Some caller -> Printf.sprintf "%s." (string_of_basic_block_path caller)
and string_of_basic_block_path {bb_caller; bb_index} =
  Printf.sprintf "%s%d" (string_of_call_path bb_caller) bb_index

type local_variable_path = {lv_caller: call_path; lv_name: string}

let string_of_lv_path {lv_caller; lv_name} = Printf.sprintf "%s%s" (string_of_call_path lv_caller) lv_name

type term =
  Symbol of int
| Tuple of term list
| StructValue of term list
| EnumValue of string * term list
| Closure of term list
| FnDef of string * gen_arg list
| ScalarInt of literal_const_expr
| AddressOfNonMutLocal of < > * local_variable_path (* The object serves to ensure two AddressOfNonMutLocal values do not compare equal even if their variable names happen to match. *)
| FieldTerm of term * int
| ConstTerm of mir_const

let rec string_of_term = function
  Symbol id -> Printf.sprintf "Symbol %d" id
| Tuple ts -> Printf.sprintf "Tuple %s" (string_of_terms ts)
| StructValue ts -> Printf.sprintf "StructValue %s" (string_of_terms ts)
| EnumValue (variant, ts) -> Printf.sprintf "EnumValue %s %s" variant (string_of_terms ts)
| FnDef (fn, genArgs) -> Printf.sprintf "FnDef %s [%s]" fn (String.concat "; " (List.map string_of_gen_arg genArgs))
| ScalarInt literal -> Printf.sprintf "ScalarInt %s" (string_of_literal_const_expr literal)
| Closure ts -> Printf.sprintf "Closure %s" (string_of_terms ts)
| AddressOfNonMutLocal (_, lv_path) -> Printf.sprintf "AddressOfNonMutLocal %s" (string_of_lv_path lv_path)
| FieldTerm (term, i) -> Printf.sprintf "FieldTerm %s %d" (string_of_term term) i
| ConstTerm const -> Printf.sprintf "ConstTerm %s" (Stringifier.string_of_mir_const const)
and string_of_terms ts =
  Printf.sprintf "[%s]" (String.concat "; " (List.map string_of_term ts))

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

let eval_const_operand genv const_operand_cpn =
  let mir_const_cpn = const_operand_cpn.const in
  match mir_const_cpn with
    Ty mir_ty_const_cpn -> failwith "Using typesystem constant expressions as MIR constant operands is not yet supported"
  | Val mir_val_const_cpn ->
    let ty = decode_ty genv mir_val_const_cpn.ty in
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
      | FnDef (fn, genArgs) ->
        let fn =
          if String.starts_with ~prefix:"core::" fn then
            "std::" ^ String.sub fn 6 (String.length fn - 6)
          else
            fn
        in
        FnDef (fn, genArgs)
      | _ -> failwith "Zero-sized constants are not yet supported"
      end
    | Slice slice_cpn -> failwith "MIR slice constants are not yet supported"
    end
  | Unevaluated -> failwith "Unevaluated constant operands are not yet supported"

type env = (local_variable_path * local_var_state) list

let string_of_env env =
  String.concat "; " (List.map (fun (x, v) -> Printf.sprintf "%s: %s" (string_of_lv_path x) (string_of_local_var_state v)) env)

let update_env x v env = (x, v) :: List.remove_assoc x env

type basic_block_info = <
  id: basic_block_path;
  genv: generic_env;
  statements: statement list;
  terminator: terminator;
  to_string: string;
  sibling: int -> basic_block_info;
  caller: (string (* callee result variable *) * place (* destination place *) * basic_block_info (* destination basic block *)) option;
>

let rec basic_block_info_of genv bbs bb_idx =
  let bb = bbs.(bb_idx) in
  let id = {bb_caller=None; bb_index=bb_idx} in
  object
    method id = id
    method genv = genv
    method statements = bb.statements
    method terminator = bb.terminator
    method to_string = string_of_basic_block_path id
    method sibling i = basic_block_info_of genv bbs i
    method caller = None
  end

let local_name (locals: local_decl array) i = locals.(i).id.name

let fns_to_be_inlined: (string * body) list =
  let local x = {local={name=x}; projection=[]; local_is_mutable=false; kind=Other} in
 [
  (
    "std::boxed::Box::<T, A>::into_inner",
    let span =
      {
        lo={file={name=Real (LocalPath "<core>/box.rs:into_inner")}; line=Stdint.Uint64.of_int 1; col={pos=Stdint.Uint64.of_int 1}};
        hi={file={name=Real (LocalPath "<core>/box.rs:into_inner")}; line=Stdint.Uint64.of_int 1; col={pos=Stdint.Uint64.of_int 1}}
      }
    in
    let local_decls: local_decl list =
      [
        {id={name="result"}; ty={kind=Param "T"}; mutability=Not; source_info={span}};
        {id={name="self"}; ty={kind=Adt {id={name="std::boxed::Box"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}; {kind=Type {kind=Param "A"}}]}}; mutability=Not; source_info={span}};
        {id={name="contents_ptr"}; ty={kind=RawPtr {mutability=Not; ty={kind=Param "T"}}}; mutability=Not; source_info={span}};
        {id={name="ref_self"}; ty={kind=Ref {region={id="'<erased>"}; mutability=Mut; ty={kind=Adt {id={name="std::boxed::Box"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}; {kind=Type {kind=Param "A"}}]}}}}; mutability=Not; source_info={span}};
        {id={name="drop_result"}; ty={kind=Tuple []}; mutability=Not; source_info={span}};
      ]
    in
    let basic_blocks: basic_block list =
      [
        {
          id={index=Stdint.Uint32.of_int 0};
          statements=[
            {
              kind=Assign {
                lhs_place=local "contents_ptr";
                rhs_rvalue=Cast {
                  operand=Copy {
                    local={name="self"};
                    projection=[
                      BoxAsNonNull {kind=Param "T"}
                    ];
                    local_is_mutable=false;
                    kind=Other
                  };
                  ty={kind=RawPtr {mutability=Not; ty={kind=Param "T"}}}
                }
              };
              source_info={span}
            };
            {
              kind=Assign {
                lhs_place=local "result";
                rhs_rvalue=Use (Move {
                  local={name="contents_ptr"};
                  projection=[Deref];
                  local_is_mutable=false;
                  kind=Other
                })
              };
              source_info={span}
            };
            {
              kind=Assign {
                lhs_place=local "ref_self";
                rhs_rvalue=Ref {
                  region={id="'<erased>"};
                  bor_kind=Mut;
                  place=local "self";
                  place_ty={kind=Adt {id={name="std::boxed::Box"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}; {kind=Type {kind=Param "A"}}]}};
                  is_implicit=false;
                }
              };
              source_info={span}
            };
          ];
          terminator={
            kind=Call {
              func=Constant {
                const=Val {
                  const_value=ZeroSized;
                  ty={
                    kind=FnDef {
                      id={name="std::ops::Drop::drop"};
                      substs=[
                        {kind=Type {kind=Adt {id={name="std::boxed::Box"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}; {kind=Type {kind=Param "A"}}]}}};
                      ];
                      late_bound_generic_param_count=1;
                    }
                  }
                };
                span
              };
              args=[
                Move (local "ref_self");
              ];
              destination=Something {
                place=local "drop_result";
                basic_block_id={index=Stdint.Uint32.of_int 1}
              };
              unwind_action=Cleanup {index=Stdint.Uint32.of_int 3};
              call_span=span;
              ghost_generic_arg_list=Nothing
            };
            source_info={span}
          };
          is_cleanup=false;
        };
        {
          id={index=Stdint.Uint32.of_int 1};
          statements=[];
          terminator={
            kind=Drop {
              place={
                local={name="self"};
                projection=[Field {index=Stdint.Uint32.of_int 1; name=Something {name="1"}; ty={kind=Param "A"}}];
                local_is_mutable=false;
                kind=Other
              };
              target={index=Stdint.Uint32.of_int 2};
              unwind_action=Cleanup {index=Stdint.Uint32.of_int 4};
            };
            source_info={span}
          };
          is_cleanup=false;
        };
        {
          id={index=Stdint.Uint32.of_int 2};
          statements=[];
          terminator={kind=Return; source_info={span}};
          is_cleanup=false;
        };
        {
          id={index=Stdint.Uint32.of_int 3};
          statements=[];
          terminator={
            kind=Drop {
              place={
                local={name="self"};
                projection=[Field {index=Stdint.Uint32.of_int 1; name=Something {name="1"}; ty={kind=Param "A"}}];
                local_is_mutable=false;
                kind=Other
              };
              target={index=Stdint.Uint32.of_int 4};
              unwind_action=Terminate;
            };
            source_info={span}
          };
          is_cleanup=false;
        };
        {
          id={index=Stdint.Uint32.of_int 4};
          statements=[];
          terminator={kind=UnwindResume; source_info={span}};
          is_cleanup=true;
        }
      ]
    in
    {
      fn_sig_span=span;
      def_kind=Fn;
      def_path="std::boxed::Box::<T, A>::into_inner";
      module_def_path="std::boxed";
      contract={annotations=[]; span};
      output={kind=Param "T"};
      inputs=[
        {kind=Adt {id={name="std::boxed::Box"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}]}};
      ];
      local_decls;
      basic_blocks;
      span;
      imp_span=span;
      var_debug_info=[];
      ghost_stmts=[];
      ghost_decl_blocks=[];
      unsafety=Safe;
      impl_block_hir_generics=Nothing;
      impl_block_generics=[];
      impl_block_predicates=[];
      hir_generics={
        params=[
          {name=Plain {name={name="T"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
          {name=Plain {name={name="A"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
        ];
        where_clause=();
        span
      };
      generics=[
        {name="T"; kind=Type};
        {name="A"; kind=Type};
      ];
      predicates=[];
      is_trait_fn=false;
      is_drop_fn=false;
      visibility=Public;
    }
  );
  (
  "std::boxed::Box::<T, A>::as_ptr",
  let span =
    {
      lo={file={name=Real (LocalPath "<core>/box.rs:as_ptr")}; line=Stdint.Uint64.of_int 1; col={pos=Stdint.Uint64.of_int 1}};
      hi={file={name=Real (LocalPath "<core>/box.rs:as_ptr")}; line=Stdint.Uint64.of_int 1; col={pos=Stdint.Uint64.of_int 1}}
    }
  in
  let local_decls: local_decl list =
    [
      {id={name="result"}; ty={kind=RawPtr {mutability=Not; ty={kind=Param "T"}}}; mutability=Not; source_info={span}};
      {id={name="self"}; ty={kind=Ref {region={id="'<erased>"}; mutability=Not; ty={kind=Adt {id={name="std::boxed::Box"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}]}}}}; mutability=Not; source_info={span}};
      {id={name="b"}; ty={kind=Adt {id={name="std::boxed::Box"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}]}}; mutability=Not; source_info={span}};
    ]
  in
  let basic_blocks: basic_block list =
    [
      {
        id={index=Stdint.Uint32.of_int 0};
        statements=[
          {
            kind=Assign {
              lhs_place=local "b";
              rhs_rvalue=Use (Copy {
                local={name="self"};
                projection=[Deref];
                local_is_mutable=false;
                kind=Other
              })
            };
            source_info={span}
          };
          {
            kind=Assign {
              lhs_place=local "result";
              rhs_rvalue=Cast {
                operand=Copy {
                  local={name="b"};
                  projection=[
                    BoxAsNonNull {kind=Param "T"}
                  ];
                  local_is_mutable=false;
                  kind=Other
                };
                ty={kind=RawPtr {mutability=Not; ty={kind=Param "T"}}}
              }
            };
            source_info={span}
          }
        ];
        terminator={kind=Return; source_info={span}};
        is_cleanup=false;
      }
    ]
  in
  {
    fn_sig_span=span;
    def_kind=Fn;
    def_path="std::boxed::Box::<T, A>::as_ptr";
    module_def_path="std::boxed";
    contract={annotations=[]; span};
    output={kind=RawPtr {mutability=Not; ty={kind=Param "T"}}};
    inputs=[
      {kind=Ref {region={id="'<erased>"}; mutability=Not; ty={kind=Adt {id={name="std::boxed::Box"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}]}}}};
    ];
    local_decls;
    basic_blocks;
    span;
    imp_span=span;
    var_debug_info=[];
    ghost_stmts=[];
    ghost_decl_blocks=[];
    unsafety=Safe;
    impl_block_hir_generics=Nothing;
    impl_block_generics=[];
    impl_block_predicates=[];
    hir_generics={
      params=[
        {name=Plain {name={name="T"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
        {name=Plain {name={name="A"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
      ];
      where_clause=();
      span
    };
    generics=[
      {name="T"; kind=Type};
      {name="A"; kind=Type};
    ];
    predicates=[];
    is_trait_fn=false;
    is_drop_fn=false;
    visibility=Public;
  }
  );
  ("std::option::Option::<T>::map",
  let span =
    {
      lo={file={name=Real (LocalPath "<core>/option.rs:map")}; line=Stdint.Uint64.of_int 1; col={pos=Stdint.Uint64.of_int 1}};
      hi={file={name=Real (LocalPath "<core>/option.rs:map")}; line=Stdint.Uint64.of_int 1; col={pos=Stdint.Uint64.of_int 1}}
    }
  in
  let local_decls: local_decl list =
    [
      {id={name="result"}; ty={kind=Adt {id={name="std::option::Option"}; kind=StructKind; substs=[{kind=Type {kind=Param "U"}}]}}; mutability=Not; source_info={span}};
      {id={name="self"}; ty={kind=Adt {id={name="std::option::Option"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}]}}; mutability=Not; source_info={span}};
      {id={name="f"}; ty={kind=Param "F"}; mutability=Not; source_info={span}};
      {id={name="discr"}; ty={kind=Int ISize}; mutability=Not; source_info={span}};
      {id={name="payload"}; ty={kind=Param "T"}; mutability=Not; source_info={span}};
      (*{id={name="argsTuple"}; ty={kind=Tuple [{kind=Param "T"}]}; mutability=Not; source_info={span}};*)
      {id={name="fResult"}; ty={kind=Param "U"}; mutability=Not; source_info={span}};
    ]
  in
  let basic_blocks: basic_block list =
    [
      {
        id={index=Stdint.Uint32.of_int 0};
        statements=[
          {kind=Assign {lhs_place=local "discr"; rhs_rvalue=Discriminant (local "self")}; source_info={span}}
        ];
        terminator={
          kind=SwitchInt {
            discr=Move (local "discr");
            discr_ty={kind=Int ISize};
            targets={
              branches=[
                {val_=encode_uint128 (Stdint.Uint128.of_int 0); target={index=Stdint.Uint32.of_int 2}};
                {val_=encode_uint128 (Stdint.Uint128.of_int 1); target={index=Stdint.Uint32.of_int 3}};
              ];
              otherwise=Something {index=Stdint.Uint32.of_int 1}
            }
          };
          source_info={span}
        };
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 1};
        statements=[];
        terminator={kind=Unreachable; source_info={span}};
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 2};
        statements=[
          {
            kind=Assign {
              lhs_place=local "result";
              rhs_rvalue=Aggregate {
                aggregate_kind=Adt {
                  adt_id={name="std::option::Option"};
                  variant_idx=Stdint.Uint32.of_int 0;
                  gen_args=[{kind=Type {kind=Param "U"}}];
                  user_type_annotation_index=();
                  union_active_field=Stdint.Uint32.of_int 0;
                  variant_id="None";
                  field_names=[];
                  adt_kind=EnumKind;
                };
                operands=[]
              }
            };
            source_info={span}
          }
        ];
        terminator={kind=Goto {index=Stdint.Uint32.of_int 6}; source_info={span}};
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 3};
        statements=[
          {
            kind=Assign {
              lhs_place=local "payload";
              rhs_rvalue=Use (Copy {
                local={name="self"};
                projection=[
                  Downcast (Stdint.Uint32.of_int 1);
                  Field {
                    index=Stdint.Uint32.of_int 0;
                    ty={kind=Param "T"};
                    name=Nothing;
                  }
                ];
                local_is_mutable=false;
                kind=Other;
              })
            };
            source_info={span}
          };
          (* {
            kind=Assign {
              lhs_place=local "argsTuple";
              rhs_rvalue=Aggregate {
                aggregate_kind=Tuple;
                operands=[Move (local "payload")]
              }
            };
            source_info={span}
          } *)
        ];
        terminator={
          kind=Call {
            func=Constant {
              const=Val {
                const_value=ZeroSized;
                ty={
                  kind=FnDef {
                    id={name="std::ops::FnOnce::call_once--VeriFast"};
                    substs=[
                      {kind=Type {kind=Param "F"}};
                      {kind=Type {kind=Tuple [{kind=Param "T"}]}};
                    ];
                    late_bound_generic_param_count=0;
                  }
                }
              };
              span
            };
            args=[
              Move (local "f");
              Move (local (*"argsTuple"*)"payload")
            ];
            destination=Something {
              place=local "fResult";
              basic_block_id={index=Stdint.Uint32.of_int 4}
            };
            unwind_action=Cleanup {index=Stdint.Uint32.of_int 5};
            call_span=span;
            ghost_generic_arg_list=Nothing
          };
          source_info={span}
        };
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 4};
        statements=[
          {
            kind=Assign {
              lhs_place=local "result";
              rhs_rvalue=Aggregate {
                aggregate_kind=Adt {
                  adt_id={name="std::option::Option"};
                  variant_idx=Stdint.Uint32.of_int 1;
                  gen_args=[{kind=Type {kind=Param "U"}}];
                  user_type_annotation_index=();
                  union_active_field=Stdint.Uint32.of_int 1;
                  variant_id="Some";
                  field_names=[];
                  adt_kind=EnumKind;
                };
                operands=[Move (local "fResult")]
              }
            };
            source_info={span}
          }
        ];
        terminator={kind=Goto {index=Stdint.Uint32.of_int 6}; source_info={span}};
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 5};
        statements=[];
        terminator={kind=UnwindResume; source_info={span}};
        is_cleanup=true;
      };
      {
        id={index=Stdint.Uint32.of_int 6};
        statements=[];
        terminator={kind=Return; source_info={span}};
        is_cleanup=false;
      }
    ]
  in
  {
    fn_sig_span=span;
    def_kind=Fn;
    def_path="std::option::Option::map";
    module_def_path="std::option";
    contract={annotations=[]; span};
    output={kind=Adt {id={name="std::option::Option"}; kind=StructKind; substs=[{kind=Type {kind=Param "U"}}]}};
    inputs=[
      {kind=Adt {id={name="std::option::Option"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}]}};
      {kind=Param "F"};
    ];
    local_decls;
    basic_blocks;
    span;
    imp_span=span;
    var_debug_info=[];
    ghost_stmts=[];
    ghost_decl_blocks=[];
    unsafety=Safe;
    impl_block_hir_generics=Nothing;
    impl_block_generics=[];
    impl_block_predicates=[];
    hir_generics={
      params=[
        {name=Plain {name={name="T"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
        {name=Plain {name={name="U"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
        {name=Plain {name={name="F"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
      ];
      where_clause=();
      span
    };
    generics=[
      {name="T"; kind=Type};
      {name="U"; kind=Type};
      {name="F"; kind=Type};
    ];
    predicates=[];
    is_trait_fn=false;
    is_drop_fn=false;
    visibility=Public;
  });
  "std::option::Option::<T>::unwrap_or_else",
  let span =
    {
      lo={file={name=Real (LocalPath "<core>/option.rs:unwrap_or_else")}; line=Stdint.Uint64.of_int 1; col={pos=Stdint.Uint64.of_int 1}};
      hi={file={name=Real (LocalPath "<core>/option.rs:unwrap_or_else")}; line=Stdint.Uint64.of_int 1; col={pos=Stdint.Uint64.of_int 1}}
    }
  in
  let local_decls: local_decl list =
    [
      {id={name="result"}; ty={kind=Param "T"}; mutability=Not; source_info={span}};
      {id={name="self"}; ty={kind=Adt {id={name="std::option::Option"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}]}}; mutability=Not; source_info={span}};
      {id={name="f"}; ty={kind=Param "F"}; mutability=Not; source_info={span}};
      {id={name="discr"}; ty={kind=Int ISize}; mutability=Not; source_info={span}};
    ]
  in
  let basic_blocks: basic_block list =
    [
      {
        id={index=Stdint.Uint32.of_int 0};
        statements=[
          {kind=Assign {lhs_place=local "discr"; rhs_rvalue=Discriminant (local "self")}; source_info={span}}
        ];
        terminator={
          kind=SwitchInt {
            discr=Move (local "discr");
            discr_ty={kind=Int ISize};
            targets={
              branches=[
                {val_=encode_uint128 (Stdint.Uint128.of_int 0); target={index=Stdint.Uint32.of_int 2}};
                {val_=encode_uint128 (Stdint.Uint128.of_int 1); target={index=Stdint.Uint32.of_int 3}};
              ];
              otherwise=Something {index=Stdint.Uint32.of_int 1}
            }
          };
          source_info={span}
        };
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 1};
        statements=[];
        terminator={kind=Unreachable; source_info={span}};
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 2};
        statements=[];
        terminator={
          kind=Call {
            func=Constant {
              const=Val {
                const_value=ZeroSized;
                ty={
                  kind=FnDef {
                    id={name="std::ops::FnOnce::call_once--VeriFast"};
                    substs=[
                      {kind=Type {kind=Param "F"}};
                      {kind=Type {kind=Tuple []}};
                    ];
                    late_bound_generic_param_count=0;
                  }
                }
              };
              span
            };
            args=[
              Move (local "f")(*;
              Constant {
                const=Val {
                  const_value=ZeroSized;
                  ty={kind=Tuple []}
                };
                span
              }*)
            ];
            destination=Something {
              place=local "result";
              basic_block_id={index=Stdint.Uint32.of_int 6}
            };
            unwind_action=Cleanup {index=Stdint.Uint32.of_int 5};
            call_span=span;
            ghost_generic_arg_list=Nothing
          };
          source_info={span}
        };
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 3};
        statements=[
          {
            kind=Assign {
              lhs_place=local "result";
              rhs_rvalue=Use (Copy {
                local={name="self"};
                projection=[
                  Downcast (Stdint.Uint32.of_int 1);
                  Field {
                    index=Stdint.Uint32.of_int 0;
                    ty={kind=Param "T"};
                    name=Nothing;
                  }
                ];
                local_is_mutable=false;
                kind=Other;
              })
            };
            source_info={span}
          };
          (* {
            kind=Assign {
              lhs_place=local "argsTuple";
              rhs_rvalue=Aggregate {
                aggregate_kind=Tuple;
                operands=[Move (local "payload")]
              }
            };
            source_info={span}
          } *)
        ];
        terminator={
          kind=Goto {index=Stdint.Uint32.of_int 4};
          source_info={span}
        };
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 4};
        statements=[];
        terminator={kind=Return; source_info={span}};
        is_cleanup=false;
      };
      {
        id={index=Stdint.Uint32.of_int 5};
        statements=[];
        terminator={kind=UnwindResume; source_info={span}};
        is_cleanup=true;
      };
      {
        id={index=Stdint.Uint32.of_int 6};
        statements=[];
        terminator={kind=Goto {index=Stdint.Uint32.of_int 4}; source_info={span}};
        is_cleanup=false;
      };
    ]
  in
  {
    fn_sig_span=span;
    def_kind=Fn;
    def_path="std::option::Option::unwrap_or_else";
    module_def_path="std::option";
    contract={annotations=[]; span};
    output={kind=Param "U"};
    inputs=[
      {kind=Adt {id={name="std::option::Option"}; kind=StructKind; substs=[{kind=Type {kind=Param "T"}}]}};
      {kind=Param "F"};
    ];
    local_decls;
    basic_blocks;
    span;
    imp_span=span;
    var_debug_info=[];
    ghost_stmts=[];
    ghost_decl_blocks=[];
    unsafety=Safe;
    impl_block_hir_generics=Nothing;
    impl_block_generics=[];
    impl_block_predicates=[];
    hir_generics={
      params=[
        {name=Plain {name={name="T"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
        {name=Plain {name={name="F"}; span}; bounds=(); span; pure_wrt_drop=false; kind=Type};
      ];
      where_clause=();
      span
    };
    generics=[
      {name="T"; kind=Type};
      {name="F"; kind=Type};
    ];
    predicates=[];
    is_trait_fn=false;
    is_drop_fn=false;
    visibility=Public;
  }
]

(* We translate the MIR basic block to an RCIR basic block, which uses more elementary instructions that interact with an operand stack. *)
type command =
  Store of place (* Pop a value from the top of the operand stack and store it at the specified place *)
| LoadLocal of local_decl_id (* Push the value of the specified local variable onto the operand stack *)
| Deref (* Pop a value from the top of the operand stack, which is an address, and push the value at that address *)
| Field of int (* Pop a value from the top of the operand stack, which is an aggregate value, and push the specified field of the aggregate value *)
| BoxAsPtr (* Pop a value from the top of the operand stack, which is a Box, and push a pointer to the contents of the Box *)
| Downcast of int (* Pop a value from the top of the operand stack, which is an enum value, and push the specified variant of the enum value *)
| Constant of const_operand (* Push a constant operand onto the operand stack *)
| Ref of rvalue_ref_data
| AddressOf of rvalue_address_of_data
| Cast of Vf_mir_decoder.ty (* Pop a value from the top of the operand stack, cast it to the specified type, and push the result *)
| BinaryOp of rvalue_binary_op_data_bin_op (* Pop two values from the top of the operand stack, apply the specified binary operator to them, and push the result *)
| UnaryOp of rvalue_unary_op_data_un_op (* Pop a value from the top of the operand stack, apply the specified unary operator to it, and push the result *)
| Aggregate of aggregate_kind * int (* Pop the specified number of values from the top of the operand stack and push an aggregate value *)
| Discriminant (* Pop a value from the top of the operand stack, which is an enum value, and push the discriminant of the enum value *)
| SourceInfo of source_info

let string_of_command c =
  let open Stringifier in
  match c with
    Store place -> Printf.sprintf "Store %s" (string_of_place place)
  | LoadLocal {name} -> Printf.sprintf "LoadLocal %s" name
  | Deref -> "Deref"
  | Field i -> Printf.sprintf "Field %d" i
  | BoxAsPtr -> "BoxAsPtr"
  | Downcast i -> Printf.sprintf "Downcast %d" i
  | Constant {const} -> Printf.sprintf "Constant %s" (string_of_mir_const const)
  | Ref data -> string_of_rvalue_ref_data data
  | AddressOf {place} -> Printf.sprintf "AddressOf %s" (string_of_place place)
  | Cast ty -> Printf.sprintf "Cast %s" (string_of_ty ty)
  | BinaryOp operator -> Printf.sprintf "BinaryOp %s" (string_of_bin_op operator)
  | Aggregate (aggregate_kind, n) -> Printf.sprintf "Aggregate %s %d" (string_of_aggregate_kind aggregate_kind) n
  | Discriminant -> "Discriminant"
  | SourceInfo {span} -> Printf.sprintf "SourceInfo %s" (string_of_span span)

let commands_for_loading_place {local; projection}: command list =
  let proj_cmds =
    projection |> List.map @@ function
      (Deref: place_elem) -> (Deref: command)
    | Field {index} -> Field (Stdint.Uint32.to_int index)
    | Downcast index -> Downcast (Stdint.Uint32.to_int index)
  in
  LoadLocal local::proj_cmds

let commands_of_operand = function
  Copy place | Move place -> commands_for_loading_place place
| Constant c -> [Constant c]

let commands_of_rvalue = function
  Use operand -> commands_of_operand operand
| Ref rvalue_ref_data -> [Ref rvalue_ref_data]
| AddressOf rvalue_address_of_data -> [AddressOf rvalue_address_of_data]
| Cast {operand=Copy {local; projection=[BoxAsNonNull _]}} -> [LoadLocal local; BoxAsPtr]
| Cast {operand; ty} -> commands_of_operand operand @ [Cast ty]
| BinaryOp {operator; operandl; operandr} -> commands_of_operand operandl @ commands_of_operand operandr @ [BinaryOp operator]
| UnaryOp {operator; operand} -> commands_of_operand operand @ [UnaryOp operator]
| Aggregate {aggregate_kind; operands} -> List.concat_map commands_of_operand operands @ [Aggregate (aggregate_kind, List.length operands)]
| Discriminant place -> commands_for_loading_place place @ [Discriminant]

let commands_of_statement_kind = function
  Assign {lhs_place; rhs_rvalue} ->
  (* ASSUMPTION: It's fine to first evaluate the RHS and then the LHS.
     Evaluating a place expression or an rvalue does not have "physical" side-effects but
     it might have a side-effects on the Tree Borrows state? *)
  commands_of_rvalue rhs_rvalue @ [Store lhs_place]
| Nop -> []

let commands_of_statement ({source_info; kind}: statement) = SourceInfo source_info::commands_of_statement_kind kind

let canonicalize_item_name name =
  if String.starts_with ~prefix:"core::" name then
    "std::" ^ String.sub name 6 (String.length name - 6)
  else
    name

let rec process_commands bodies (env: env) opnds (i_bb: basic_block_info) i_s (ss_i: command list) =
  let load_from_lv_path: 'r. local_variable_path -> (string -> 'r) -> (term -> 'r) -> 'r = fun localPath fallback cont ->
    begin match List.assoc localPath env with
      Value v -> cont v
    | Address v -> fallback "Locals whose address is taken"
    end
  in
  let load_from_local: 'r. local_decl_id -> (string -> 'r) -> (term -> 'r) -> 'r = fun local fallback cont ->
    let localPath = {lv_caller=i_bb#id.bb_caller; lv_name=local.name} in
    load_from_lv_path localPath fallback cont
  in
  let eval_operand: 'r. operand -> (string -> 'r) -> (term -> 'r) -> 'r = fun operand fallback cont ->
    match operand with
      Move place | Copy place ->
      begin match place.projection with
        [] -> load_from_local place.local fallback cont
      | [Deref] ->
        load_from_local place.local fallback @@ fun v ->
        begin match v with
          AddressOfNonMutLocal (_, lv_path) ->
          load_from_lv_path lv_path fallback cont
        | _ -> fallback "Dereferences"
        end
      | [Field {index}] ->
        load_from_local place.local fallback @@ fun v ->
        begin match v with
          Closure vs -> cont (List.nth vs (Stdint.Uint32.to_int index))
        | _ -> fallback "Field projections"
        end
      | _ -> fallback "Place projections"
      end
    | Constant {
        const=Val {
          const_value=ZeroSized;
          ty={kind=Tuple []}
        }
      } ->
      cont (Tuple [])
    | Constant constant -> fallback "Constants"
  in
  let rec eval_operands operands fallback cont =
    match operands with
      [] -> cont []
    | operand::operands ->
      eval_operand operand fallback (fun v -> eval_operands operands fallback (fun vs -> cont (v::vs)))
  in
  let inline_call0 funcName generic_params substs call (body: body) =
    let {args; destination; unwind_action} = call in
    let args = args |> List.map @@ fun arg ->
      eval_operand arg (fun msg -> failwith (msg ^ " are not yet supported as arguments of inlined calls")) (fun v -> v)
    in
    let caller = Some i_bb#id in
    let genv =
      let rec iter lifetimes types consts (generic_params: generic_param_def list) substs =
        match generic_params, substs with
          [], [] -> {lifetimes; types; consts}
        | {name; kind=Lifetime}::generic_params, Lifetime lifetime::substs ->
          iter ((name, lifetime)::lifetimes) types consts generic_params substs
        | {name; kind=Type}::generic_params, Type ty::substs ->
          iter lifetimes ((name, ty)::types) consts generic_params substs
        | {name; kind=Const}::generic_params, Const const::substs ->
          iter lifetimes types ((name, const)::consts) generic_params substs
      in
      iter [] [] [] generic_params substs
    in
    Printf.printf "Entering inlined call of %s with genv=%s\n" funcName (string_of_genv genv);
    let bbs = Array.of_list body.basic_blocks in
    let locals = Array.of_list body.local_decls in
    let env = List.mapi (fun i v -> let x = local_name locals (i + 1) in {lv_caller=caller; lv_name=x}, Value v) args @ env in
    let caller_info =
      match destination with
        Nothing -> failwith "Diverging inlined calls are not yet supported"
      | Something {place; basic_block_id={index}} -> Some (locals.(0).id.name, place, i_bb#sibling (Stdint.Uint32.to_int index))
    in
    let rec bb_info_of i: basic_block_info =
      let callee_bb_id = {bb_caller=caller; bb_index=i} in
      object
      method id = callee_bb_id
      method genv = genv
      method statements = bbs.(i).statements
      method terminator = bbs.(i).terminator
      method to_string = string_of_basic_block_path callee_bb_id
      method sibling i = bb_info_of i
      method caller = caller_info
    end in
    process_commands bodies env [] (bb_info_of 0) 0 (List.concat_map commands_of_statement bbs.(0).statements) (* TODO: deal with unwind_action *)
  in
  let inline_call funcName substs call (body: body) =
    inline_call0 funcName body.generics substs call body
  in
  let done_ () = 
    (env, opnds, i_bb, i_s, ss_i)
  in
  match ss_i with
    [] ->
    assert (opnds = []);
    begin match i_bb#terminator.kind with
      Call ({func=Constant {const=Val {const_value=ZeroSized; ty={kind=FnDef {id={name=funcName}; substs}}}}} as call) ->
      let funcName = canonicalize_item_name funcName in
      let substs = List.map (decode_gen_arg i_bb#genv) substs in
      if funcName = "std::ops::FnOnce::call_once--VeriFast" then
        let [Type (Closure (closureName, closureGenArgs)); Type (Tuple paramTypes)] = substs in
        let body = List.assoc (canonicalize_def_path closureName) bodies in
        Printf.printf "======== Inlined function ========\n%s" (Stringifier.string_of_body body);
        let closureGenArgs = Array.of_list closureGenArgs in
        let closureGenArgs = Array.to_list @@ Array.sub closureGenArgs 0 (Array.length closureGenArgs - 3) in
        let genericParams = closureGenArgs |> List.map @@ fun arg ->
          match arg with
            Lifetime (Region name) -> {name; kind=Lifetime}
          | Type (Param name) -> {name; kind=Type}
          | Const (ParamConstExpr name) -> {name; kind=Const}
        in
        inline_call0 closureName genericParams closureGenArgs call body
      else if String.ends_with ~suffix:"__VeriFast_wrapper" funcName then
        inline_call funcName substs call (List.assoc funcName bodies)
      else begin match List.assoc_opt funcName fns_to_be_inlined with
        Some body -> inline_call funcName substs call body
      | None -> done_ ()
      end
    | Return when i_bb#caller <> None ->
      let Some (returnLocalName, destinationPlace, destinationBb) = i_bb#caller in
      let returnLocalPath = {lv_caller=i_bb#id.bb_caller; lv_name=returnLocalName} in
      if destinationPlace.projection <> [] then failwith "Inlined calls whose destination place has a projection are not yet supported";
      begin match List.assoc returnLocalPath env with
        Value v ->
          let destinationLocalPath = {lv_caller=destinationBb#id.bb_caller; lv_name=destinationPlace.local.name} in
          begin match List.assoc_opt destinationLocalPath env with
            Some (Address _) -> failwith "Locals whose address is taken are not yet supported as return value destinations of inlined calls"
          | _ ->
            let env = update_env destinationLocalPath (Value v) env in
            process_commands bodies env [] destinationBb 0 (List.concat_map commands_of_statement destinationBb#statements)
          end
      | Address _ -> failwith "The scenario where the result variable's address is taken is not yet supported for inlined calls"
      end
    | _ -> done_ ()
    end
  | s::ss_i_plus_1 ->
    let cont env opnds =
      process_commands bodies env opnds i_bb (i_s + 1) ss_i_plus_1
    in
    match s with
      Store lhsPlace ->
        let rhsValue::opnds = opnds in
        let lhsProjection = lhsPlace.projection in
        if lhsProjection <> [] then
          done_ ()
        else
          let lhsLocalId = lhsPlace.local in
          let lhsLocalName = lhsLocalId.name in
          let lhsLocalPath = {lv_caller=i_bb#id.bb_caller; lv_name=lhsLocalName} in
          begin match List.assoc_opt lhsLocalPath env with
            Some (Address _) -> done_ ()
          | _ ->
            let env = update_env lhsLocalPath (Value rhsValue) env in
            cont env opnds
          end
    | LoadLocal localId ->
      load_from_local localId (fun msg -> done_ ()) (fun v -> cont env (v::opnds))
    | Constant {const} -> cont env (ConstTerm const::opnds)
    | Deref ->
      let v::opnds = opnds in
      begin match v with
        AddressOfNonMutLocal (_, lv_path) ->
        load_from_lv_path lv_path (fun msg -> done_ ()) (fun v -> cont env (v::opnds))
      | _ -> done_ ()
      end
    | Field index ->
      let v::opnds = opnds in
      begin match v with
        StructValue vs -> cont env (List.nth vs index::opnds)
      | EnumValue (variant_id, vs) -> cont env (List.nth vs index::opnds)
      | Tuple vs -> cont env (List.nth vs index::opnds)
      | Closure vs -> cont env (List.nth vs index::opnds)
      | _ -> cont env (FieldTerm (v, index)::opnds)
      end
    | Aggregate (Adt {adt_kind=StructKind; adt_id={name}}, n) ->
      let vs, opnds = popn n opnds in
      cont env (StructValue vs::opnds)
    | Aggregate (Adt {adt_kind=EnumKind; variant_id; adt_id={name}}, n) ->
      let vs, opnds = popn n opnds in
      cont env (EnumValue (variant_id, vs)::opnds)
    | Aggregate (Tuple, n) ->
      let vs, opnds = popn n opnds in
      cont env (Tuple vs::opnds)
    | Aggregate (Closure _, n) ->
      let vs, opnds = popn n opnds in
      cont env (Closure vs::opnds)
    | AddressOf addr_of_data ->
      begin match addr_of_data.place.projection with
        [Deref] ->
          let placeLocalPath = {lv_caller=i_bb#id.bb_caller; lv_name=addr_of_data.place.local.name} in
          begin match List.assoc placeLocalPath env with
            Value placeValue ->
            cont env (placeValue::opnds)
          | Address _ -> done_ ()
          end
      | _ -> done_ ()
      end
    | Ref {bor_kind=Shared; place={local; local_is_mutable=false; projection=[]}} ->
      let placeLocalPath = {lv_caller=i_bb#id.bb_caller; lv_name=local.name} in
      cont env (AddressOfNonMutLocal (object end, placeLocalPath)::opnds)
    | Ref {bor_kind=Shared; place={local; local_is_mutable=false; projection=[Deref]}} ->
      load_from_local local (fun msg -> done_ ()) @@ fun v ->
      begin match v with
        AddressOfNonMutLocal (o, lv_path) ->
        cont env (AddressOfNonMutLocal (o, lv_path)::opnds)
      | _ -> done_ ()
      end
    | SourceInfo sourceInfo ->
      Printf.printf "INFO: at %s\n" (string_of_span sourceInfo.span);
      cont env opnds
    | _ -> done_ ()

(* When this is raised, both variables did not yet have their address taken *)
exception LocalAddressTaken of local_variable_path (* x0 *) * local_variable_path (* x1 *)

let local_address_taken path0 path1 =
  raise (LocalAddressTaken (path0, path1))

let rec values_equal (env0: env) (env1: env) (v0: term) (v1: term): bool =
  match v0, v1 with
  | AddressOfNonMutLocal (_, lv_path0), AddressOfNonMutLocal (_, lv_path1) ->
      begin match List.assoc lv_path0 env0, List.assoc lv_path1 env1 with
        Value v0, Value v1 when values_equal env0 env1 v0 v1 ->
          local_address_taken lv_path0 lv_path1
      | Address a1, Address a2 when values_equal env0 env1 a1 a2 -> true
      | _ -> false
      end
  | _, _ -> v0 = v1

let check_place_element_refines_place_element (elem0: place_elem) (elem1: place_elem) =
  match elem0, elem1 with
  | Deref, Deref -> ()
  | Field field0, Field field1 ->
      let fieldIndex0 = field0.index in
      let fieldIndex1 = field1.index in
      if fieldIndex0 <> fieldIndex1 then failwith "Field indices do not match"
  | BoxAsNonNull _, BoxAsNonNull _ -> ()
  | Index, Index -> failwith "PlaceElement::Index not supported"
  | ConstantIndex, ConstantIndex -> failwith "PlaceElement::ConstantIndex not supported"
  | Subslice, Subslice -> failwith "PlaceElement::Subslice not supported"
  | Downcast variant_idx0, Downcast variant_idx1 ->
    if variant_idx0 <> variant_idx1 then failwith "Variant indices do not match"
  | OpaqueCast, OpaqueCast -> failwith "PlaceElement::OpaqueCast not supported"
  | Subtype, Subtype -> failwith "PlaceElement::Subtype not supported"
  | _ -> failwith "Place elements do not match"

type place =
  Local of local_variable_path (* This place is a local variable whose address is never taken in this function *)
| LocalProjection of local_variable_path (* This place is a projection starting from the given local variable *)
| Nonlocal (* A "nonlocal place" is a place that is disjoint from all local variables whose address is never taken in this function *)

(* Checks that the place expressions either both evaluate to a local whose address is never taken,
   or both perform *the same* projection on local variables whose address is never taken,
   or both evaluate to *the same* "nonlocal place" (see definition above). *)
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
  List.iter2 check_place_element_refines_place_element placeProjection0 placeProjection1;
  match placeLocalState0, placeLocalState1 with
    Some (Address a1), Some (Address a2) ->
      if not (values_equal env0 env1 a1 a2) then failwith "The addresses of the two places are not equal";
      Nonlocal, Nonlocal
  | Some (Address _), _ | _, Some (Address _) -> failwith "Place expressions do not match"
  | _, _ ->
    (* OK, neither local has its address taken *)
    match placeProjection0 with
      [] -> Local placeLocalPath0, Local placeLocalPath1
    | es when List.mem (Deref: place_elem) es ->
      begin match placeLocalState0, placeLocalState1 with
        Some (Value v0), Some (Value v1) when values_equal env0 env1 v0 v1 -> ()
      | _ -> failwith "The addresses being dereferenced are not equal"
      end;
      Nonlocal, Nonlocal
    | _ ->
      (* if a local is projected, give up trying to track its value *)
      LocalProjection placeLocalPath0, LocalProjection placeLocalPath1

let check_operand_refines_operand i genv0 env0 span0 caller0 operand0 genv1 env1 span1 caller1 operand1 =
  match operand0, operand1 with
    (Move placeExpr0, Move placeExpr1) | (Copy placeExpr0, Copy placeExpr1) ->
      begin match check_place_refines_place env0 caller0 placeExpr0 env1 caller1 placeExpr1 with
        (Local x0, Local x1) | (LocalProjection x0, LocalProjection x1) ->
          begin match List.assoc x0 env0, List.assoc x1 env1 with
            Value v0, Value v1 -> if not (values_equal env0 env1 v0 v1) then failwith (Printf.sprintf "The values of the %d'th operand of %s and %s are not equal: %s versus %s" i (string_of_span span0) (string_of_span span1) (string_of_term v0) (string_of_term v1))
          | Address a1, Address a2 -> if not (values_equal env0 env1 a1 a2) then failwith (Printf.sprintf "The addresses of the %d'th operand of %s and %s are not equal" i (string_of_span span0) (string_of_span span1))
          | _ -> failwith "Operand mismatch"
          end
      | Nonlocal, Nonlocal -> ()
        end
  | Constant const_operand_cpn0, Constant const_operand_cpn1 ->
    let term0 = eval_const_operand genv0 const_operand_cpn0 in
    let term1 = eval_const_operand genv1 const_operand_cpn1 in
    if term0 <> term1 then failwith (Printf.sprintf "The constants %s at %s and %s at %s are not equal" (string_of_term term0) (string_of_span span0) (string_of_term term1) (string_of_span span1))

let check_aggregate_kind_refines_aggregate_kind genv0 (aggregate_kind0: aggregate_kind) genv1 (aggregate_kind1: aggregate_kind) =
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
    if List.map (decode_gen_arg genv0) genArgs0 <> List.map (decode_gen_arg genv1) genArgs1 then failwith "Aggregate::Adt: generic arguments do not match";
    let union_active_field_idx0 = adt_data0.union_active_field in
    let union_active_field_idx1 = adt_data1.union_active_field in
    if union_active_field_idx0 <> union_active_field_idx1 then failwith "Aggregate::Adt: union active field indices do not match";
    ()
  | Closure _, Closure _ -> failwith "Aggregate::Closure not supported"
  | Coroutine, Coroutine -> failwith "Aggregate::Coroutine not supported"
  | CoroutineClosure, CoroutineClosure -> failwith "Aggregate::CoroutineClosure not supported"
  | RawPtr, RawPtr -> failwith "Aggregate::RawPtr not supported"
  | _ -> failwith "Aggregate kinds do not match"
      
let check_aggregate_refines_aggregate genv0 env0 span0 caller0 aggregate0 genv1 env1 span1 caller1 aggregate1 =
  let operands0 = aggregate0.operands in
  let operands1 = aggregate1.operands in
  if List.length operands0 <> List.length operands1 then failwith "The two aggregate expressions have a different number of operands";
  List.iteri (fun i (operand0, operand1) -> check_operand_refines_operand i genv0 env0 span0 caller0 operand0 genv1 env1 span1 caller1 operand1) (List.combine operands0 operands1);
  let aggregate_kind0 = aggregate0.aggregate_kind in
  let aggregate_kind1 = aggregate1.aggregate_kind in
  check_aggregate_kind_refines_aggregate_kind genv0 aggregate_kind0 genv1 aggregate_kind1

(* Checks that the two rvalues evaluate to the same value *)
let check_rvalue_refines_rvalue genv0 env0 span0 caller0 rhsRvalue0 genv1 env1 span1 caller1 rhsRvalue1 =
  match rhsRvalue0, rhsRvalue1 with
  Use operand0, Use operand1 ->
    check_operand_refines_operand 0 genv0 env0 span0 caller0 operand0 genv1 env1 span1 caller1 operand1
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
    (Local x0, Local x1) | (LocalProjection x0, LocalProjection x1) -> local_address_taken x0 x1
  | Nonlocal, Nonlocal -> ()
  end
| ThreadLocalRef, ThreadLocalRef -> failwith "Rvalue::ThreadLocalRef not supported"
| AddressOf address_of_data_cpn0, AddressOf address_of_data_cpn1 -> failwith "Rvalue::AddressOf not supported"
| Len, Len -> failwith "Rvalue::Len not supported"
| Cast cast_data_cpn0, Cast cast_data_cpn1 ->
  check_operand_refines_operand 0 genv0 env0 span0 caller0 cast_data_cpn0.operand genv1 env1 span1 caller1 cast_data_cpn1.operand;
  if decode_ty genv0 cast_data_cpn0.ty <> decode_ty genv1 cast_data_cpn1.ty then failwith "Rvalue::Cast: types do not match"
| BinaryOp binary_op_data_cpn0, BinaryOp binary_op_data_cpn1 ->
  let op0 = binary_op_data_cpn0.operator in
  let op1 = binary_op_data_cpn1.operator in
  if op0 <> op1 then failwith "Rvalue::BinaryOp: operators do not match";
  let lhs0 = binary_op_data_cpn0.operandl in
  let lhs1 = binary_op_data_cpn1.operandl in
  check_operand_refines_operand 0 genv0 env0 span0 caller0 lhs0 genv1 env1 span1 caller1 lhs1;
  let rhs0 = binary_op_data_cpn0.operandr in
  let rhs1 = binary_op_data_cpn1.operandr in
  check_operand_refines_operand 1 genv0 env0 span0 caller0 rhs0 genv1 env1 span1 caller1 rhs1
| NullaryOp, NullaryOp -> failwith "Rvalue::NullaryOp not supported"
| UnaryOp unary_op_data_cpn0, UnaryOp unary_op_data_cpn1 -> failwith "Rvalue::UnaryOp not supported"
| Aggregate aggregate_data_cpn0, Aggregate aggregate_data_cpn1 ->
  check_aggregate_refines_aggregate genv0 env0 span0 caller0 aggregate_data_cpn0 genv1 env1 span1 caller1 aggregate_data_cpn1
| Discriminant place_cpn0, Discriminant place_cpn1 ->
  begin match check_place_refines_place env0 caller0 place_cpn0 env1 caller1 place_cpn1 with
    (Local x0, Local x1) | (LocalProjection x0, LocalProjection x1) -> if List.assoc x0 env0 <> List.assoc x1 env1 then failwith "The discriminees of the two rvalues are not equal"
  | Nonlocal, Nonlocal -> ()
  end
| ShallowInitBox, ShallowInitBox -> failwith "Rvalue::ShallowInitBox not supported"

type loop_invariant = {
  consts0: (local_variable_path * term) list; (* (lv_path, t) means the value of local `lv_path` of the original program equals t *)
  consts1: (local_variable_path * term) list; (* (lv_path, t) means the value of local `lv_path` of the verified program equals t *)
  eqs: (local_variable_path * local_variable_path list) list (* For each local of the verified program, a list of the locals of the original program that have the same value at each iteration *);
  address_taken: (local_variable_path * local_variable_path) list (* (lv_path0, lv_path1) means the address of local `lv_path0` of the original program equals the address of local `lv_path1` of the verified program *)
}

type basic_block_status =
  Checking of basic_block_path (* i_bb1 *) * loop_invariant (* Candidate loop invariant *)
| Checked of basic_block_path (* i_bb1 *) * loop_invariant (* Loop invariant that was used to verify this loop. *)

exception RecheckLoop of basic_block_path (* i_bb0 *) (* When this is raised, the specified basic block's status has already been updated with a weakened candidate loop invariant *)

let string_of_loop_inv (loopInv: loop_invariant) =
  Printf.sprintf "{consts0: %s; consts1: %s; eqs: %s}"
    (String.concat "; " (List.map (fun (x, t) -> Printf.sprintf "%s: %s" (string_of_lv_path x) (string_of_term t)) loopInv.consts0))
    (String.concat "; " (List.map (fun (x, t) -> Printf.sprintf "%s: %s" (string_of_lv_path x) (string_of_term t)) loopInv.consts1))
    (String.concat "; " (List.map (fun (x, ys) -> Printf.sprintf "%s: [%s]" (string_of_lv_path x) (String.concat ", " (List.map string_of_lv_path ys))) loopInv.eqs))

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
let produce_loop_inv env0 env1 (loopInv: loop_invariant) =
  let env0 = env0 |> List.map @@ fun (x, v) ->
    let value =
      match List.assoc_opt x loopInv.consts0 with
        None ->
          if List.exists (fun (x0, x1) -> x = x0) loopInv.address_taken then
            Address (fresh_symbol ())
          else
            havoc_local_var_state v
      | Some t -> Value t
    in
    (x, {unified_with=None; value})
  in
  (* Havoc all locals of the verified crate that are not known to be equal to any locals of the original crate *)
  let env1 = List.map2 (fun (x, v) (x, ys) ->
      let v =
        match List.assoc_opt x loopInv.consts1 with
          None -> havoc_local_var_state v
        | Some t -> Value t
      in
      (x, let v = {unified_with=None; value=v} in List.iter (fun y -> unify v (List.assoc y env0)) ys; v)
    ) env1 loopInv.eqs
  in
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

let decode_generic_param_def (generic_param_def: generic_param_def) =
  let name = generic_param_def.name in
  let kind =
    match generic_param_def.kind with
      Lifetime -> Lifetime
    | Type -> Type
    | Const -> Const
  in
  name, kind

let decode_hir_generic_param (hir_generic_param: hir_generics_generic_param) =
  let name =
    match hir_generic_param.name with
      Plain ident -> ident.name.name
    | Fresh k -> Printf.sprintf "'__%s" (Stdint.Uint128.to_string (decode_uint128 k))
  in
  let kind =
    match hir_generic_param.kind with
      Lifetime -> Lifetime
    | Type -> Type
    | Const -> Const
  in
  name, kind

let check_predicate_refines_predicate genv0 pred0 genv1 pred1 =
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
      let bound_regions_map =
        match List.combine trait_pred0.bound_regions trait_pred1.bound_regions with
          exception Invalid_argument _ -> failwith "The two trait predicates have different numbers of bound regions"
        | map -> map
      in
      let genv0 = {genv0 with lifetimes=List.map (fun (x, y) -> (x, Region y)) bound_regions_map @ genv0.lifetimes} in
      let genv1 = {genv1 with lifetimes=List.map (fun (_, y) -> (y, Region y)) bound_regions_map @ genv1.lifetimes} in
      let generic_args0 = trait_pred0.args in
      let generic_args1 = trait_pred1.args in
      if List.map (decode_gen_arg genv0) generic_args0 <> List.map (decode_gen_arg genv1) generic_args1 then failwith "The two trait predicates have different generic arguments"
  | Projection projection_pred0, Projection projection_pred1 ->
      let proj_term0 = projection_pred0.projection_term in
      let proj_term1 = projection_pred1.projection_term in
      let proj_term_def_id0 = proj_term0.def_id in
      let proj_term_def_id1 = proj_term1.def_id in
      if proj_term_def_id0 <> proj_term_def_id1 then failwith "The two projection predicates have different alias identifiers";
      let bound_regions_map =
        match List.combine projection_pred0.bound_regions projection_pred1.bound_regions with
          exception Invalid_argument _ -> failwith "The two trait predicates have different numbers of bound regions"
        | map -> map
      in
      let genv0 = {genv0 with lifetimes=List.map (fun (x, y) -> (x, Region y)) bound_regions_map @ genv0.lifetimes} in
      let genv1 = {genv1 with lifetimes=List.map (fun (_, y) -> (y, Region y)) bound_regions_map @ genv1.lifetimes} in
      let proj_term_generic_args0 = proj_term0.args in
      let proj_term_generic_args1 = proj_term1.args in
      if List.map (decode_gen_arg genv0) proj_term_generic_args0 <> List.map (decode_gen_arg genv1) proj_term_generic_args1 then failwith "The two projection predicates have different alias generic arguments";
      let rhs0 = projection_pred0.term in
      let rhs1 = projection_pred1.term in
      begin match rhs0, rhs1 with
        Ty ty0, Ty ty1 ->
          if decode_ty genv0 ty0 <> decode_ty genv1 ty1 then failwith "The two projection predicates have different right-hand side types"
      | Const const0, Const const1 ->
          if decode_const_expr genv0 const0 <> decode_const_expr genv1 const1 then failwith "The two projection predicates have different right-hand side constants"
      end
  | _ -> failwith "The two predicates have different kinds"

let check_body_refines_body bodies0 bodies1 def_path body0 body1 =
  let error msg =
    Printf.printf "ERROR: %s\n" msg;
    Printf.printf "======== Original body ========\n%s\n" (Stringifier.string_of_body body0);
    Printf.printf "======== Verified body ========\n%s\n" (Stringifier.string_of_body body1);
    failwith msg
  in
  Printf.printf "Checking function body %s\n" def_path;
  let visibility0 = body0.visibility in
  let visibility1 = body1.visibility in
  if visibility0 <> visibility1 then failwith "The two functions have different visibilities";
  let unsafety0 = body0.unsafety in
  let unsafety1 = body1.unsafety in
  (* We allow private functions to have different unsafety *)
  if visibility0 = Public && unsafety0 = Safe && unsafety1 = Unsafe then failwith "The two functions have different unsafety";
  let generics0 = List.map decode_generic_param_def body0.impl_block_generics in
  let generics1 = List.map decode_generic_param_def body1.impl_block_generics in
  let generics0 = generics0 @ List.map decode_hir_generic_param body0.hir_generics.params in
  let generics1 = generics1 @ List.map decode_hir_generic_param body1.hir_generics.params in
  if List.length generics0 <> List.length generics1 then failwith "The two functions have a different number of generic parameters";
  let lft_params0, generics0 = List.partition (fun (_, kind) -> kind = Lifetime) generics0 in
  let lft_params1, generics1 = List.partition (fun (_, kind) -> kind = Lifetime) generics1 in
  let root_genv0, root_genv1 =
    let rec iter lifetimes0 lifetimes1 types0 types1 consts0 consts1 generics0 generics1 =
      match generics0, generics1 with
        [], [] -> {lifetimes=lifetimes0; types=types0; consts=consts0}, {lifetimes=lifetimes1; types=types1; consts=consts1}
      | (name0, Lifetime)::generics0, (name1, Lifetime)::generics1 ->
        iter ((name0, Region name0)::lifetimes0) ((name1, Region name0)::lifetimes1) types0 types1 consts0 consts1 generics0 generics1
      | (name0, Type)::generics0, (name1, Type)::generics1 ->
        iter lifetimes0 lifetimes1 ((name0, Param name0)::types0) ((name1, Param name0)::types1) consts0 consts1 generics0 generics1
      | (name0, Const)::generics0, (name1, Const)::generics1 ->
        iter lifetimes0 lifetimes1 types0 types1 ((name0, ParamConstExpr name0)::consts0) ((name1, ParamConstExpr name0)::consts1) generics0 generics1
      | _ -> failwith (Printf.sprintf "The two functions have different kinds of generic parameters: %s and %s" (String.concat ", " (List.map fst generics0)) (String.concat ", " (List.map fst generics1)))
    in
    let {lifetimes=lifetimes0}, {lifetimes=lifetimes1} = iter [] [] [] [] [] [] lft_params0 lft_params1 in
    iter lifetimes0 lifetimes1 [] [] [] [] generics0 generics1
  in
  let preds0 = body0.predicates in
  let preds1 = body1.predicates in
  if List.length preds0 <> List.length preds1 then failwith "The two functions have a different number of predicates";
  let trait_preds0, preds0 = List.partition (function Trait _ -> true | _ -> false) preds0 in
  let trait_preds1, preds1 = List.partition (function Trait _ -> true | _ -> false) preds1 in
  if List.length trait_preds0 <> List.length trait_preds1 then failwith "The two functions have a different number of trait predicates";
  List.iter2 (fun pred0 pred1 -> check_predicate_refines_predicate root_genv0 pred0 root_genv1 pred1) trait_preds0 trait_preds1;
  let outlives_preds0, preds0 = List.partition (function Outlives _ -> true | _ -> false) preds0 in
  let outlives_preds1, preds1 = List.partition (function Outlives _ -> true | _ -> false) preds1 in
  if List.length outlives_preds0 <> List.length outlives_preds1 then failwith "The two functions have a different number of outlives predicates";
  List.iter2 (fun pred0 pred1 -> check_predicate_refines_predicate root_genv0 pred0 root_genv1 pred1) outlives_preds0 outlives_preds1;
  let projection_preds0, preds0 = List.partition (function Projection _ -> true | _ -> false) preds0 in
  let projection_preds1, preds1 = List.partition (function Projection _ -> true | _ -> false) preds1 in
  if List.length projection_preds0 <> List.length projection_preds1 then failwith "The two functions have a different number of projection predicates";
  List.iter2 (fun pred0 pred1 -> check_predicate_refines_predicate root_genv0 pred0 root_genv1 pred1) projection_preds0 projection_preds1;
  if preds0 <> [] || preds1 <> [] then failwith "Predicate kind not supported";
  let inputs0 = body0.inputs in
  let inputs1 = body1.inputs in
  let inputs0 = List.map (decode_ty root_genv0) inputs0 in
  let inputs1 = List.map (decode_ty root_genv1) inputs1 in
  if inputs0 <> inputs1 then failwith "The two functions have different input types";
  let locals0 = Array.of_list body0.local_decls in
  let locals1 = Array.of_list body1.local_decls in
  let inputs = List.map (fun _ -> fresh_symbol ()) inputs0 in
  let rec check_body_refines_body_core address_taken =
    let env0 = List.mapi (fun i v -> let x = {lv_caller=None; lv_name=local_name locals0 (i + 1)} in if List.mem_assoc x address_taken then [] else [x, Value v]) inputs |> List.flatten in
    let env1 = List.mapi (fun i v -> let x = {lv_caller=None; lv_name=local_name locals1 (i + 1)} in if List.exists (fun (x0, x1) -> x1 = x) address_taken then [] else [x, Value v]) inputs |> List.flatten in
    let address_taken0, address_taken1 = address_taken |> List.map (fun (x0, x1) -> let a = fresh_symbol () in ((x0, Address a), (x1, Address a))) |> List.split in
    let env0 = address_taken0 @ env0 in
    let env1 = address_taken1 @ env1 in
    let bblocks0_statuses: (basic_block_path, basic_block_status) Hashtbl.t = Hashtbl.create 100 in
    let rec check_basic_block_refines_basic_block (env0: env) (i_bb0: basic_block_info) (env1: env) (i_bb1: basic_block_info) =
      Printf.printf "INFO: In function %s, checking basic block %s against basic block %s, with env0 = [%s] and env1 = [%s]\n" def_path i_bb0#to_string i_bb1#to_string (string_of_env env0) (string_of_env env1);
      match Hashtbl.find_opt bblocks0_statuses i_bb0#id with
        None ->
          let loopInv = {
            consts0=env0 |> List.map (function (x, Value t) -> [(x, t)] | _ -> []) |> List.flatten;
            consts1=env1 |> List.map (function (x, Value t) -> [(x, t)] | _ -> []) |> List.flatten;
            eqs=env1 |> List.map (fun (x, v1) -> (x, env0 |> List.concat_map (fun (y, v0) -> if v1 = v0 then [y] else []) ));
            address_taken=address_taken
          } in
          Hashtbl.replace bblocks0_statuses i_bb0#id (Checking (i_bb1#id, loopInv));
          let rec iter loopInv =
            try
              Printf.printf "Loop invariant = [%s]\n" (string_of_loop_inv loopInv);
              loopInv.address_taken |> List.iter begin fun (x0, x1) ->
                if List.assoc_opt x0 env0 <> List.assoc_opt x1 env1 then
                  failwith (Printf.sprintf "The states of the two locals %s and %s whose address is taken are not equal" (string_of_lv_path x0) (string_of_lv_path x1))
              end;
              (* Havoc all locals of the original crate *)
              let env0, env1 = produce_loop_inv env0 env1 loopInv in
              Printf.printf "INFO: In function %s, checking loop body at basic block %s against basic block %s, with env0 = [%s] and env1 = [%s]\n" def_path i_bb0#to_string i_bb1#to_string (string_of_env env0) (string_of_env env1);
              let cmds0 = List.concat_map commands_of_statement i_bb0#statements in
              let cmds1 = List.concat_map commands_of_statement i_bb1#statements in
              begin try
                check_codepos_refines_codepos env0 [] i_bb0 0 cmds0 env1 [] i_bb1 0 cmds1
              with
                | Failure msg as e ->
                  Printf.printf "======== Commands of basic block %s of original program ========\n%s\n" i_bb0#to_string (String.concat "\n" (List.mapi (fun i c -> Printf.sprintf "%3d: %s" i (string_of_command c)) cmds0));
                  Printf.printf "======== Commands of basic block %s of verified program ========\n%s\n" i_bb1#to_string (String.concat "\n" (List.mapi (fun i c -> Printf.sprintf "%3d: %s" i (string_of_command c)) cmds1));
                  raise e
              end;
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
        let consts0_hold =
          loopInv.consts0 |> List.for_all @@ fun (x, t) ->
            let v = List.assoc x env0 in
            match v with Value t' -> t = t' | Address _ -> false
        in
        let consts1_hold =
          loopInv.consts1 |> List.for_all @@ fun (x, t) ->
            let v = List.assoc x env1 in
            match v with Value t' -> t = t' | Address _ -> false
        in
        let address_taken_ok =
          (* All variables whose address is taken are in loopInv.address_taken *)
          env0 |> List.for_all @@ fun (x, v) ->
            match v with Address a -> List.exists (fun (x0, x1) -> x = x0) loopInv.address_taken | _ -> true
        in
        if consts0_hold && consts1_hold && address_taken_ok && loopInv.eqs |> List.for_all @@ fun (x, ys) ->
          let v = List.assoc x env1 in
          ys |> List.for_all @@ fun y -> List.assoc y env0 = v
        then begin
          Printf.printf "Loop with head %s verified, with loop invariant %s!\n" i_bb0#to_string (string_of_loop_inv loopInv);
          () (* Use the induction hypothesis; this path is done. *)
        end else begin
          Printf.printf "Loop with head %s failed to verify; trying again with weaker invariant\n" i_bb0#to_string;
          (* Forget about the earlier result; try from scratch *)
          let consts0 = loopInv.consts0 |> List.filter @@ fun (x, t) ->
            let v = List.assoc x env0 in
            match v with Value t' -> t' = t | Address _ -> false
          in
          let consts1 = loopInv.consts1 |> List.filter @@ fun (x, t) ->
            let v = List.assoc x env1 in
            match v with Value t' -> t' = t | Address _ -> false
          in
          let eqs = loopInv.eqs |> List.map @@ fun (x, ys) ->
            let v = List.assoc x env1 in
            (x, ys |> List.filter @@ fun y -> List.assoc y env0 = v)
          in
          let address_taken = env0 |> List.concat_map @@ fun (x0, v0) ->
            match v0 with Address _ ->
              let [x1, _] = env1 |> List.filter (fun (x1, v1) -> v1 = v0) in
              [x0, x1]
            | _ -> []
          in
          Hashtbl.replace bblocks0_statuses i_bb0#id (Checking (i_bb1#id, {consts0; consts1; eqs; address_taken})); (* Weaken the candidate loop invariant *)
          raise (RecheckLoop i_bb0#id)
        end
      | Some (Checked (i_bb1', loopInv)) ->
        if i_bb1' = i_bb1#id && 
          let consts0_hold =
            loopInv.consts0 |> List.for_all @@ fun (x, t) ->
              match List.assoc_opt x env0 with Some (Value t') when t' = t -> true | _ -> false
          in
          let consts1_hold =
            loopInv.consts1 |> List.for_all @@ fun (x, t) ->
              match List.assoc_opt x env1 with Some (Value t') when t' = t -> true | _ -> false
          in
          let address_taken_ok =
            (* All variables whose address is taken are in loopInv.address_taken *)
            env0 |> List.for_all @@ fun (x, v) ->
              match v with Address a -> List.exists (fun (x0, x1) -> x = x0) loopInv.address_taken | _ -> true
          in
          consts0_hold && consts1_hold && address_taken_ok &&
          loopInv.eqs |> List.for_all @@ fun (x, ys) ->
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
    and check_codepos_refines_codepos_core env0 opnds0 (i_bb0 : basic_block_info) i_s0 (ss_i0 : command list) env1 opnds1 (i_bb1 : basic_block_info) i_s1 (ss_i1 : command list) =
      Printf.printf "INFO: In function %s, checking code position %s:%d against code position %s:%d\n" def_path i_bb0#to_string i_s0 i_bb1#to_string i_s1;
      let caller0 = i_bb0#id.bb_caller in
      let caller1 = i_bb1#id.bb_caller in
      let check_terminator_refines_terminator env1 =
        if opnds0 <> [] then failwith "opnds0 <> [] at terminator";
        if opnds1 <> [] then failwith "opnds1 <> [] at terminator";
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
          check_operand_refines_operand 0 i_bb0#genv env0 span0 caller0 discr0 i_bb1#genv env1 span1 caller1 discr1;
          let targets0 = switch_int_data0.targets in
          let targets1 = switch_int_data1.targets in
          let branches0 = targets0.branches in
          let branches1 = targets1.branches in
          if List.length branches0 <> List.length branches1 then error "The two switch statements have a different number of branches";
          List.combine branches0 branches1 |> List.iter (fun (branch0, branch1) ->
            let val0 = decode_uint128 @@ branch0.val_ in
            let val1 = decode_uint128 @@ branch1.val_ in
            if val0 <> val1 then error "SwitchInt branch values do not match";
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
              error (Printf.sprintf "In function %s, at basic block %s in the original crate and basic block %s in the verified crate, the return values %s and %s are not equal" def_path i_bb0#to_string i_bb1#to_string (string_of_local_var_state retVal0) (string_of_local_var_state retVal1))
        | _, Unreachable -> ()
        | (Call call0, Call call1) ->
          let func0 = call0.func in
          let func1 = call1.func in
          check_operand_refines_operand 0 i_bb0#genv env0 span0 caller0 func0 i_bb1#genv env1 span1 caller1 func1;
          let args0 = call0.args in
          let args1 = call1.args in
          List.combine args0 args1 |> List.iteri (fun i (arg0, arg1) ->
            check_operand_refines_operand (i + 1) i_bb0#genv env0 span0 caller0 arg0 i_bb1#genv env1 span1 caller1 arg1
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
            | LocalProjection x0, LocalProjection x1 -> local_address_taken x0 x1
            | Nonlocal, Nonlocal ->
              check_basic_block_refines_basic_block env0 (i_bb0#sibling dest0bbidx) env1 (i_bb1#sibling dest1bbidx)
            end
          end
          (* TODO: Check that unwindAction0 refines unwindAction1 *)
        | Drop drop_data0, Drop drop_data1 ->
          let env0, env1 =
            match check_place_refines_place env0 caller0 drop_data0.place env1 caller1 drop_data1.place with
              Local x0, Local x1 ->
              if List.assoc x0 env0 <> List.assoc x1 env1 then error "The two drop terminators drop different values";
              List.remove_assoc x0 env0, List.remove_assoc x1 env1
            | Nonlocal, Nonlocal -> env0, env1
          in
          let i_bb_target0 = i_bb0#sibling (Stdint.Uint32.to_int drop_data0.target.index) in
          let i_bb_target1 = i_bb1#sibling (Stdint.Uint32.to_int drop_data1.target.index) in
          (* Todo: follow unwind path *)
          check_basic_block_refines_basic_block env0 i_bb_target0 env1 i_bb_target1
        | TailCall, TailCall -> error "TailCall not supported"
        | Assert, Assert -> error "Assert not supported"
        | Yield, Yield -> error "Yield not supported"
        | CoroutineDrop, CoroutineDrop -> error "CoroutineDrop not supported"
        | FalseEdge, FalseEdge -> error "FalseEdge not supported"
        | InlineAsm, InlineAsm -> error "InlineAsm not supported"
        | _ -> error "Terminator kinds do not match"
      in
      let check_command_refines_command () =
        let stmt0::ss_i0_plus_1 = ss_i0 in
        let stmt1::ss_i1_plus_1 = ss_i1 in
        let consume_operand opnds0 opnds1 =
          let v0::opnds0 = opnds0 in
          let v1::opnds1 = opnds1 in
          if not (values_equal env0 env1 v0 v1) then 
            error (Printf.sprintf "In function %s, at command %d of basic block %s in the original crate and command %d of basic block %s in the verified crate, the values %s and %s are not equal" def_path i_s0 i_bb0#to_string i_s1 i_bb1#to_string (string_of_term v0) (string_of_term v1));
          v0, opnds0, opnds1
        in
        let consume_operands n opnds0 opnds1 =
          let vs0, opnds0 = popn n opnds0 in
          let vs1, opnds1 = popn n opnds1 in
          if not (List.for_all2 (values_equal env0 env1) vs0 vs1) then
            error (Printf.sprintf "In function %s, at command %d of basic block %s in the original crate and command %d of basic block %s in the verified crate, the values %s and %s are not equal" def_path i_s0 i_bb0#to_string i_s1 i_bb1#to_string (string_of_terms vs0) (string_of_terms vs1));
          vs0, opnds0, opnds1
        in
        let cont env0 opnds0 env1 opnds1 =
          check_codepos_refines_codepos env0 opnds0 i_bb0 (i_s0 + 1) ss_i0_plus_1 env1 opnds1 i_bb1 (i_s1 + 1) ss_i1_plus_1
        in
        match stmt0, stmt1 with
          Store lhsPlace0, Store lhsPlace1 ->
            let v, opnds0, opnds1 = consume_operand opnds0 opnds1 in
            begin match check_place_refines_place env0 caller0 lhsPlace0 env1 caller1 lhsPlace1 with
              Local x0, Local x1 ->
              let env0 = update_env x0 (Value v) env0 in
              let env1 = update_env x1 (Value v) env1 in
              cont env0 opnds0 env1 opnds1
            | LocalProjection x0, LocalProjection x1 -> local_address_taken x0 x1
            | Nonlocal, Nonlocal ->
              cont env0 opnds0 env1 opnds1
            end
        | LoadLocal {name=local0}, LoadLocal {name=local1} ->
            let localState0 = List.assoc {lv_caller=caller0; lv_name=local0} env0 in
            let localState1 = List.assoc {lv_caller=caller1; lv_name=local1} env1 in
            let v0, v1 =
              match localState0, localState1 with
                Address a1, Address a2 ->
                  if not (values_equal env0 env1 a1 a2) then error "LoadLocal: The addresses of the two locals are not equal";
                  let v = fresh_symbol () in
                  v, v
              | (Address _, _) | (_, Address _) ->
                error "LoadLocal: The address of exactly one of the locals is taken"
              | Value v0, Value v1 ->
                  v0, v1
            in
            cont env0 (v0::opnds0) env1 (v1::opnds1)
        | Deref, Deref ->
            let v, opnds0, opnds1 = consume_operand opnds0 opnds1 in
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | Field i0, Field i1 ->
            if i0 <> i1 then error "Field: The field indices do not match";
            let v, opnds0, opnds1 = consume_operand opnds0 opnds1 in
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | BoxAsPtr, BoxAsPtr ->
            let v, opnds0, opnds1 = consume_operand opnds0 opnds1 in
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | Downcast i0, Downcast i1 ->
            let v, opnds0, opnds1 = consume_operand opnds0 opnds1 in
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | Constant c0, Constant c1 ->
            let v0 = eval_const_operand i_bb0#genv c0 in
            let v1 = eval_const_operand i_bb1#genv c1 in
            if not (values_equal env0 env1 v0 v1) then
              error "Constant: The constant values do not match";
            cont env0 (v0::opnds0) env1 (v1::opnds1)
        | Ref ref0, Ref ref1 ->
            if ref0.bor_kind <> ref1.bor_kind then failwith "Ref: The bor_kinds do not match";
            begin match check_place_refines_place env0 caller0 ref0.place env1 caller1 ref1.place with
              (Local x0, Local x1) | (LocalProjection x0, LocalProjection x1) -> local_address_taken x0 x1
            | Nonlocal, Nonlocal ->
              let v = fresh_symbol () in
              cont env0 (v::opnds0) env1 (v::opnds1)
            end
        | AddressOf addrOfData0, AddressOf addrOfData1 -> error "AddressOf: not yet supported"
        | Cast ty0, Cast ty1 ->
            let v, opnds0, opnds1 = consume_operand opnds0 opnds1 in
            if decode_ty i_bb0#genv ty0 <> decode_ty i_bb1#genv ty1 then
              error "Cast: The types do not match";
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | BinaryOp op0, BinaryOp op1 ->
            let [vlhs; vrhs], opnds0, opnds1 = consume_operands 2 opnds0 opnds1 in
            if op0 <> op1 then error "BinaryOp: The operators do not match";
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | UnaryOp op0, UnaryOp op1 ->
            let v, opnds0, opnds1 = consume_operand opnds0 opnds1 in
            if op0 <> op1 then error "UnaryOp: The operators do not match";
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | Aggregate (kind0, n0), Aggregate (kind1, n1) ->
            if n0 <> n1 then error "Aggregate: The number of elements do not match";
            check_aggregate_kind_refines_aggregate_kind i_bb0#genv kind0 i_bb1#genv kind1;
            let vs, opnds0, opnds1 = consume_operands n0 opnds0 opnds1 in
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | Discriminant, Discriminant ->
            let v, opnds0, opnds1 = consume_operand opnds0 opnds1 in
            let v = fresh_symbol () in
            cont env0 (v::opnds0) env1 (v::opnds1)
        | _ -> error "Command kinds do not match"
      in
      match ss_i0, ss_i1 with
        [], [] -> check_terminator_refines_terminator env1
      | _, [] -> error (Printf.sprintf "In function %s, cannot prove that statement %d of basic block %s in the original version refines the terminator of basic block %s in the verified version" def_path i_s0 i_bb0#to_string i_bb1#to_string)
      | Ref {place={projection=[Deref]}}::_, _ -> check_command_refines_command ()
      | _, Ref {place={projection=[Deref]; local={name=rhsPlaceLocalName1}}}::ss_i1_plus_1 ->
        (* Process assignments of the form `x = &*y;` where x and y are locals whose address is not taken.
          * We are here using the property that inserting such statements can only cause a program to have more UB, so if it verifies, the original program is also safe.
          *)
        let rhsPlaceLocalPath1 = {lv_caller=caller1; lv_name=rhsPlaceLocalName1} in
        let fail () = error (Printf.sprintf "In function %s, cannot prove that code position %d of basic block %s in the original version refines the statement at position %d of basic block %s in the verified version" def_path i_s0 i_bb0#to_string i_s1 i_bb1#to_string) in
        begin match List.assoc_opt rhsPlaceLocalPath1 env1 with
          Some (Value rhsValue) ->
            check_codepos_refines_codepos env0 opnds0 i_bb0 i_s0 ss_i0 env1 (rhsValue::opnds1) i_bb1 (i_s1 + 1) ss_i1_plus_1
        | _ -> fail ()
        end
      | [], _ -> error (Printf.sprintf "In function %s, cannot prove that the terminator of basic block %s in the original version refines statement %d of basic block %s in the verified version" def_path i_bb0#to_string i_s1 i_bb1#to_string)
      | _ -> check_command_refines_command ()
    and check_codepos_refines_codepos env0 opnds0 i_bb0 i_s0 ss_i0 env1 opnds1 i_bb1 i_s1 ss_i1 =
      let (env0, opnds0, i_bb0, i_s0, ss_i0) = process_commands bodies0 env0 opnds0 i_bb0 i_s0 ss_i0 in
      let (env1, opnds1, i_bb1, i_s1, ss_i1) = process_commands bodies1 env1 opnds1 i_bb1 i_s1 ss_i1 in
      let rec iter env0 env1 =
        try
          check_codepos_refines_codepos_core env0 opnds0 i_bb0 i_s0 ss_i0 env1 opnds1 i_bb1 i_s1 ss_i1
        with LocalAddressTaken (x0, x1) ->
          if List.assoc x0 env0 <> List.assoc x1 env1 then failwith (Printf.sprintf "The states of the two locals %s and %s whose address is taken are not equal" (string_of_lv_path x0) (string_of_lv_path x1));
          Printf.printf "Caught LocalAddressTaken (%s, %s); restarting codepos check\n" (string_of_lv_path x0) (string_of_lv_path x1);
          let a = fresh_symbol () in
          let env0 = update_env x0 (Address a) env0 in
          let env1 = update_env x1 (Address a) env1 in
          iter env0 env1
      in
      iter env0 env1
    in
    try
      check_basic_block_refines_basic_block env0 (basic_block_info_of root_genv0 (Array.of_list body0.basic_blocks) 0) env1 (basic_block_info_of root_genv1 (Array.of_list body1.basic_blocks) 0)
    with LocalAddressTaken (x0, x1) ->
      let address_taken = (x0, x1) :: address_taken in
      Printf.printf "Caught LocalAddressTaken; restarting with address_taken = %s\n" (String.concat ", " (List.map (fun (x0, x1) -> Printf.sprintf "%s = %s" (string_of_lv_path x0) (string_of_lv_path x1)) address_taken));
      check_body_refines_body_core address_taken
  in
  check_body_refines_body_core []
