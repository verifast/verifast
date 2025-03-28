open Printf
open Util
open Ast

(** Keeps manifests produced by the compilation phase, for use during the linking phase. Avoids writing manifest files to disk. *)
let manifest_map: (string * string list) list ref = ref []
let jardeps_map: (string * string list) list ref = ref []

(* Region: some auxiliary types and functions *)

let lookup env x = List.assoc x env
let update env x t = (x, t)::env
let string_of_env env = String.concat "; " (List.map (function (x, t) -> x ^ " = " ^ t) env)

let is_lemma k = match k with Lemma(_) -> true | _ -> false

let printff format = kfprintf (fun _ -> flush stdout) stdout format

(** Internal pattern. Either a pattern from the source code, or a term pattern. A term pattern (TermPat t) matches a term t' if t and t' are definitely_equal. *)
type 'termnode pat0 = SrcPat of pat | TermPat of 'termnode
(** A heap chunk. *)
type chunk_info =
  PredicateChunkSize of int (* Size of this chunk with respect to the first chunk of the precondition; used to check lemma termination. *)
type 'termnode chunk =
  Chunk of
    ('termnode (* Predicate name *) * bool (* true if a declared predicate's symbol; false in a scenario where predicate names are passed as values. Used to avoid prover queries. *) ) *
    type_ list *  (* Type arguments *)
    'termnode *  (* Coefficient of fractional permission *)
    'termnode list *  (* Arguments; their prover type is as per the instantiated parameter types, not the generic ones. *)
    chunk_info option
type 'termnode heap = 'termnode chunk list
type 'termnode env = (string * 'termnode) list
(** Execution trace. For error reporting. *)
type branch = LeftBranch | RightBranch
type 'termnode context =
  Assuming of 'termnode
| Executing of 'termnode heap * 'termnode env * loc * string
| PushSubcontext
| PopSubcontext
| Branching of branch
type node_type = ExecNode of string * int list | BranchNode | SuccessNode | ErrorNode
type node = Node of node_type * node list ref

(* Returns the locations of the "call stack" of the current execution step. *)
let get_callers (ctxts: 'termnode context list): loc option list =
  let rec iter lo ls ctxts =
    match ctxts with
      [] -> ls
    | Executing (_, _, l, _)::ctxts -> iter (Some l) ls ctxts
    | PushSubcontext::ctxts -> iter lo (lo::ls) ctxts
    | PopSubcontext::ctxts -> let ls = match ls with [] -> [] | _::ls -> ls in iter None ls ctxts
    | _::ctxts -> iter lo ls ctxts
  in
  iter None [] (List.rev ctxts)

let get_root_caller ctxts = match List.rev (get_callers ctxts) with Some l::_ -> Some l | _ -> None

let tparam_is_uppercase tparam =
  String.length tparam > 0 && match tparam.[0] with 'A'..'Z'|'\'' -> true | _ -> false

let rec c_string_of_type t =
  match t with
    Bool -> "bool"
  | Void -> "void"
  | Int (Signed, CharRank) -> "char"
  | Int (Unsigned, CharRank) -> "unsigned char"
  | Int (Signed, ShortRank) -> "short"
  | Int (Unsigned, ShortRank) -> "unsigned short"
  | Int (Signed, IntRank) -> "int"
  | Int (Unsigned, IntRank) -> "unsigned int"
  | Int (Signed, LongRank) -> "long"
  | Int (Unsigned, LongRank) -> "unsigned long"
  | Int (Signed, LongLongRank) -> "long long"
  | Int (Unsigned, LongLongRank) -> "unsigned long long"
  | Int (Signed, PtrRank) -> "intptr_t"
  | Int (Unsigned, PtrRank) -> "uintptr_t"
  | Int (Signed, FixedWidthRank k) -> "int" ^ string_of_int ((1 lsl k) * 8) ^ "_t"
  | Int (Unsigned, FixedWidthRank k) -> "uint" ^ string_of_int ((1 lsl k) * 8) ^ "_t"
  | Float -> "float"
  | Double -> "double"
  | LongDouble -> "long double"
  | RealType -> "real"
  | InductiveType (i, []) -> i
  | InductiveType (i, targs) -> i ^ "<" ^ String.concat ", " (List.map c_string_of_type targs) ^ ">"
  | ObjType (l, []) -> "class " ^ l
  | ObjType (l, targs) -> "class " ^ l ^ "<" ^ String.concat ", " (List.map c_string_of_type targs) ^ ">"
  | StructType (sn, targs) -> "struct " ^ sn ^ (match targs with [] -> "" | _ -> "<" ^ String.concat ", " (List.map c_string_of_type targs) ^ ">")
  | UnionType un -> "union " ^ un
  | PtrType t -> c_string_of_type t ^ " *"
  | FuncType ft -> ft
  | InlineFuncType rt -> Printf.sprintf "unsafe fn(?) -> %s" (c_string_of_type rt)
  | PredType (tparams, ts, inputParamCount, inductiveness) ->
    let tparamsText = if tparams = [] then "" else "<" ^ String.concat ", " tparams ^ ">" in
    let paramTypesText =
      let typesText ts = String.concat ", " (List.map c_string_of_type ts) in
      match inputParamCount with
        None -> typesText ts
      | Some n ->
        let (ts1, ts2) = take_drop n ts in
        typesText ts1 ^ ";" ^ if ts2 = [] then "" else " " ^ typesText ts2
    in
    let inductivenessText = match inductiveness with Inductiveness_Inductive -> "" | Inductiveness_CoInductive -> "co" in
    Printf.sprintf "%spredicate%s(%s)" inductivenessText tparamsText paramTypesText
  | PureFuncType (t1, t2) ->
    let (pts, rt) =  (* uncurry *)
      let rec iter pts rt =
        match rt with
          PureFuncType (t1, t2) -> iter (t1::pts) t2
        | _ -> (List.rev pts, rt)
      in
      iter [t1] t2
    in
    Printf.sprintf "fixpoint(%s, %s)" (String.concat ", " (List.map c_string_of_type pts)) (c_string_of_type rt)
  | BoxIdType -> "box"
  | HandleIdType -> "handle"
  | AnyType -> "any"
  | RealTypeParam x -> "<" ^ x ^ ">"
  | GhostTypeParam x -> x
  | InferredRealType x -> x ^ "?"
  | InferredType (_, t) -> begin match !t with EqConstraint t -> c_string_of_type t | _ -> "?" end
  | ArrayType(t) -> (c_string_of_type t) ^ "[]"
  | StaticArrayType(t, s) -> c_string_of_type t ^ "[" ^ c_string_of_type s ^ "]" 
  | LiteralConstType n -> string_of_int n
  | ClassOrInterfaceName(n) -> n (* not a real type; used only during type checking *)
  | PackageName(n) -> n (* not a real type; used only during type checking *)
  | RefType(t) -> "ref " ^ (c_string_of_type t)
  | AbstractType x -> x

let rec java_string_of_type t =
  match t with
    Bool -> "boolean"
  | Void -> "void"
  | Int (Signed, CharRank) -> "byte"
  | Int (Unsigned, CharRank) -> "unsigned char"
  | Int (Signed, ShortRank) -> "short"
  | Int (Unsigned, ShortRank) -> "unsigned short"
  | Int (Signed, IntRank) -> "int"
  | Int (Unsigned, IntRank) -> "unsigned int"
  | Int (Signed, LongRank) -> "long"
  | Int (Unsigned, LongRank) -> "unsigned long"
  | Int (Signed, LongLongRank) -> "long long"
  | Int (Unsigned, LongLongRank) -> "unsigned long long"
  | Int (Signed, PtrRank) -> "intptr_t"
  | Int (Unsigned, PtrRank) -> "uintptr_t"
  | Int (Signed, FixedWidthRank k) -> "int" ^ string_of_int ((1 lsl k) * 8) ^ "_t"
  | Int (Unsigned, FixedWidthRank k) -> "uint" ^ string_of_int ((1 lsl k) * 8) ^ "_t"
  | Float -> "float"
  | Double -> "double"
  | LongDouble -> "long double"
  | RealType -> "real"
  | InductiveType (i, []) -> i
  | InductiveType (i, targs) -> i ^ "<" ^ String.concat ", " (List.map java_string_of_type targs) ^ ">"
  | ObjType (l, []) -> "class " ^ l
  | ObjType (l, targs) -> "class " ^ l ^ "<" ^ String.concat ", " (List.map java_string_of_type targs) ^ ">"
  | StructType (sn, targs) -> "struct " ^ sn ^ (match targs with [] -> "" | _ -> "<" ^ String.concat ", " (List.map java_string_of_type targs) ^ ">")
  | UnionType un -> "union " ^ un
  | PtrType t -> java_string_of_type t ^ " *"
  | FuncType ft -> ft
  | InlineFuncType rt -> Printf.sprintf "fn(?) -> %s" (java_string_of_type rt)
  | PredType (tparams, ts, inputParamCount, inductiveness) ->
    let tparamsText = if tparams = [] then "" else "<" ^ String.concat ", " tparams ^ ">" in
    let paramTypesText =
      let typesText ts = String.concat ", " (List.map java_string_of_type ts) in
      match inputParamCount with
        None -> typesText ts
      | Some n ->
        let (ts1, ts2) = take_drop n ts in
        typesText ts1 ^ ";" ^ if ts2 = [] then "" else " " ^ typesText ts2
    in
    let inductivenessText = match inductiveness with Inductiveness_Inductive -> "" | Inductiveness_CoInductive -> "co" in
    Printf.sprintf "%spredicate%s(%s)" inductivenessText tparamsText paramTypesText
  | PureFuncType (t1, t2) ->
    let (pts, rt) =  (* uncurry *)
      let rec iter pts rt =
        match rt with
          PureFuncType (t1, t2) -> iter (t1::pts) t2
        | _ -> (List.rev pts, rt)
      in
      iter [t1] t2
    in
    Printf.sprintf "fixpoint(%s, %s)" (String.concat ", " (List.map java_string_of_type pts)) (java_string_of_type rt)
  | BoxIdType -> "box"
  | HandleIdType -> "handle"
  | AnyType -> "any"
  | RealTypeParam x -> if (String.capitalize_ascii x) = x then x else "<" ^ x ^ ">"
  | GhostTypeParam x -> if (String.capitalize_ascii x) = x then "<" ^ x ^ ">" else x
  | InferredRealType x -> x ^ "?"
  | InferredType (_, t) -> begin match !t with EqConstraint t -> java_string_of_type t | _ -> "?" end
  | ArrayType(t) -> (java_string_of_type t) ^ "[]"
  | StaticArrayType(t, s) -> java_string_of_type t ^ "[" ^ java_string_of_type s ^ "]" 
  | LiteralConstType n -> string_of_int n
  | ClassOrInterfaceName(n) -> n (* not a real type; used only during type checking *)
  | PackageName(n) -> n (* not a real type; used only during type checking *)
  | RefType(t) -> "ref " ^ (java_string_of_type t)
  | AbstractType x -> x

let rec rust_string_of_type t =
  match t with
    Bool -> "bool"
  | Void -> "void"
  | Int (Signed, CharRank) -> "std::ffi::c_char"
  | Int (Unsigned, CharRank) -> "std::ffi::c_uchar"
  | Int (Signed, ShortRank) -> "std::ffi::c_short"
  | Int (Unsigned, ShortRank) -> "std::ffi::c_ushort"
  | Int (Signed, IntRank) -> "std::ffi::c_int"
  | Int (Unsigned, IntRank) -> "std::ffi::c_uint"
  | Int (Signed, LongRank) -> "std::ffi::c_long"
  | Int (Unsigned, LongRank) -> "std::ffi::c_ulong"
  | Int (Signed, LongLongRank) -> "std::ffi::c_longlong"
  | Int (Unsigned, LongLongRank) -> "std::ffi::c_ulonglong"
  | Int (Signed, PtrRank) -> "isize"
  | Int (Unsigned, PtrRank) -> "usize"
  | Int (Signed, FixedWidthRank k) -> "i" ^ string_of_int ((1 lsl k) * 8)
  | Int (Unsigned, FixedWidthRank k) -> "u" ^ string_of_int ((1 lsl k) * 8)
  | RustChar -> "char"
  | Float -> "f32"
  | Double -> "f64"
  | LongDouble -> "std::ffi::c_longdouble"
  | RealType -> "real"
  | InductiveType (i, []) -> i
  | InductiveType (i, targs) -> i ^ "<" ^ String.concat ", " (List.map rust_string_of_type targs) ^ ">"
  | ObjType (l, []) -> "class " ^ l
  | ObjType (l, targs) -> "class " ^ l ^ "<" ^ String.concat ", " (List.map rust_string_of_type targs) ^ ">"
  | StructType (sn, targs) -> sn ^ (match targs with [] -> "" | _ -> "<" ^ String.concat ", " (List.map rust_string_of_type targs) ^ ">")
  | UnionType un -> "union " ^ un
  | PtrType Void -> "*_"
  | PtrType t -> "*" ^ rust_string_of_type t
  | RustRefType (lft, kind, t) -> "&" ^ rust_string_of_type lft ^ (match kind with Mutable -> " mut " | Shared -> " ") ^ rust_string_of_type t
  | FuncType ft -> ft
  | InlineFuncType rt -> Printf.sprintf "fn(?) -> %s" (rust_string_of_type rt)
  | PredType (tparams, ts, inputParamCount, inductiveness) ->
    let tparamsText = if tparams = [] then "" else "<" ^ String.concat ", " tparams ^ ">" in
    let paramTypesText =
      let typesText ts = String.concat ", " (List.map rust_string_of_type ts) in
      match inputParamCount with
        None -> typesText ts
      | Some n ->
        let (ts1, ts2) = take_drop n ts in
        typesText ts1 ^ ";" ^ if ts2 = [] then "" else " " ^ typesText ts2
    in
    let inductivenessText = match inductiveness with Inductiveness_Inductive -> "" | Inductiveness_CoInductive -> "co" in
    Printf.sprintf "%spred%s(%s)" inductivenessText tparamsText paramTypesText
  | PureFuncType (t1, t2) ->
    let (pts, rt) =  (* uncurry *)
      let rec iter pts rt =
        match rt with
          PureFuncType (t1, t2) -> iter (t1::pts) t2
        | _ -> (List.rev pts, rt)
      in
      iter [t1] t2
    in
    Printf.sprintf "fix(%s, %s)" (String.concat ", " (List.map rust_string_of_type pts)) (rust_string_of_type rt)
  | BoxIdType -> "box"
  | HandleIdType -> "handle"
  | AnyType -> "any"
  | RealTypeParam x -> "<" ^ x ^ ">"
  | GhostTypeParam x -> x
  | GhostTypeParamWithEqs (x, eqs) ->
    let string_of_eq ((traitName, traitArgs, assocTypeName), t) =
      Printf.sprintf "%s<%s>" traitName (String.concat ", " (List.map rust_string_of_type traitArgs @ [Printf.sprintf "%s = %s" assocTypeName (rust_string_of_type t)]))
    in
    x ^ ": " ^ String.concat ", " (List.map string_of_eq eqs)
  | InferredRealType x -> x ^ "?"
  | InferredType (_, t) -> begin match !t with EqConstraint t -> rust_string_of_type t | _ -> "?" end
  | ArrayType(t) -> (rust_string_of_type t) ^ "[]"
  | StaticArrayType(t, s) -> Printf.sprintf "[%s; %s]" (rust_string_of_type t) (rust_string_of_type s)
  | LiteralConstType n -> string_of_int n
  | ClassOrInterfaceName(n) -> n (* not a real type; used only during type checking *)
  | PackageName(n) -> n (* not a real type; used only during type checking *)
  | RefType(t) -> "ref " ^ (rust_string_of_type t)
  | AbstractType x -> x
  | StaticLifetime -> "'static"
  | ProjectionType (t, traitName, traitArgs, assocTypeName) -> Printf.sprintf "<%s as %s<%s>>::%s" (rust_string_of_type t) traitName (String.concat ", " (List.map rust_string_of_type traitArgs)) assocTypeName

let string_of_type lang dialect =
  match lang, dialect with
    CLang, Some Rust -> rust_string_of_type
  | CLang, _ -> c_string_of_type
  | Java, _ -> java_string_of_type

module StringOf(StringOfType: sig
  val string_of_type: type_ -> string
end) = struct

  open StringOfType

  let string_of_targs targs =
    if targs = [] then "" else "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">"
  
  (* This assumes the termnodes have already been converted to strings. *)
  let string_of_chunk (Chunk ((g, literal), targs, coef, ts, size): string chunk): string =
    (if coef = "1" then "" else "[" ^ coef ^ "]") ^ g ^ string_of_targs targs ^ "(" ^ String.concat ", " ts ^ ")"
  
  let string_of_heap h = String.concat " * " (List.map string_of_chunk h)
  
  let string_of_context c =
    match c with
      Assuming t -> "Assuming " ^ t
    | Executing (h, env, l, s) -> "Heap: " ^ string_of_heap h ^ "\nEnv: " ^ string_of_env env ^ "\n" ^ string_of_loc l ^ ": " ^ s
    | PushSubcontext -> "Entering subcontext"
    | PopSubcontext -> "Leaving subcontext"
    | Branching LeftBranch -> "Executing first branch"
    | Branching RightBranch -> "Executing second branch"
  
end

exception RustcErrors of loc * string * Json.json list
exception SymbolicExecutionError of string context list * loc * string * error_attribute list option

(* prepends '~' to the given record name *)
let cxx_dtor_name struct_name = "~" ^ struct_name ^ "()"

let bases_constructed_pred_name sn = sn ^ "_bases_constructed"

type _ vfparam =
  Vfparam_disable_overflow_check: bool vfparam
| Vfparam_fwrapv: bool vfparam (* GCC's -fwrapv flag: signed integer arithmetic wraps around *)
| Vfparam_fno_strict_aliasing: bool vfparam (* GCC's -fno-strict-aliasing flag; allows accessing an object of type T1 through a pointer of type T2 even if T1 != T2 *)
| Vfparam_assume_left_to_right_evaluation: bool vfparam
| Vfparam_assume_no_provenance: bool vfparam
| Vfparam_assume_no_subobject_provenance: bool vfparam
| Vfparam_no_simplify_terms: bool vfparam
| Vfparam_runtime: string option vfparam
| Vfparam_include_paths: string list vfparam
| Vfparam_define_macros: string list vfparam
| Vfparam_allow_undeclared_struct_types: bool vfparam
| Vfparam_data_model: data_model option vfparam
| Vfparam_uppercase_type_params_carry_typeid: bool vfparam
| Vfparam_rustc_args: string list vfparam
| Vfparam_extern_specs: string list vfparam
| Vfparam_externs: string list vfparam
| Vfparam_skip_specless_fns: bool vfparam (* Skip verification of functions for which the user did not provide a precondition and postcondition. This is the default behavior for C, C++ and Java but not for Rust. *)
| Vfparam_ignore_ref_creation: bool vfparam
| Vfparam_ignore_unwind_paths: bool vfparam (* In Rust, ignore control flow paths due to stack unwinding after a panic. *)

let cast_vfarg: type t1 t2. t1 vfparam -> t1 -> t2 vfparam -> t2 option = fun p0 a0 p ->
  (* if Obj.magic p0 = Obj.magic p then Some (Obj.magic a0) else None *)
  match p0, p with
    Vfparam_disable_overflow_check, Vfparam_disable_overflow_check -> Some a0
  | Vfparam_fwrapv, Vfparam_fwrapv -> Some a0
  | Vfparam_fno_strict_aliasing, Vfparam_fno_strict_aliasing -> Some a0
  | Vfparam_assume_left_to_right_evaluation, Vfparam_assume_left_to_right_evaluation -> Some a0
  | Vfparam_assume_no_provenance, Vfparam_assume_no_provenance -> Some a0
  | Vfparam_assume_no_subobject_provenance, Vfparam_assume_no_subobject_provenance -> Some a0
  | Vfparam_no_simplify_terms, Vfparam_no_simplify_terms -> Some a0
  | Vfparam_runtime, Vfparam_runtime -> Some a0
  | Vfparam_include_paths, Vfparam_include_paths -> Some a0
  | Vfparam_define_macros, Vfparam_define_macros -> Some a0
  | Vfparam_allow_undeclared_struct_types, Vfparam_allow_undeclared_struct_types -> Some a0
  | Vfparam_data_model, Vfparam_data_model -> Some a0
  | Vfparam_uppercase_type_params_carry_typeid, Vfparam_uppercase_type_params_carry_typeid -> Some a0
  | Vfparam_rustc_args, Vfparam_rustc_args -> Some a0
  | Vfparam_extern_specs, Vfparam_extern_specs -> Some a0
  | Vfparam_externs, Vfparam_externs -> Some a0
  | Vfparam_skip_specless_fns, Vfparam_skip_specless_fns -> Some a0
  | Vfparam_ignore_ref_creation, Vfparam_ignore_ref_creation -> Some a0
  | Vfparam_ignore_unwind_paths, Vfparam_ignore_unwind_paths -> Some a0
  | _ -> None

type _ vfparam_info =
  BoolParam: bool vfparam_info
| ParsedParam: 'a * (?basePath:string -> string -> 'a) * ('a -> 'a -> 'a) -> 'a vfparam_info

let string_opt_param = ParsedParam (None, (fun ?basePath x -> Some x), (fun old new_ -> new_))
let string_list_param = ParsedParam ([], (fun ?basePath x -> [x]), (fun old new_ -> new_ @ old))

let path_opt_param = ParsedParam (None, (fun ?basePath x -> Some (match basePath with None -> x | Some basePath -> compose basePath x)), (fun old new_ -> new_))
let path_list_param = ParsedParam ([], (fun ?basePath x -> [match basePath with None -> x | Some basePath -> compose basePath x]), (fun old new_ -> new_ @ old))

let vfparam_info_of: type a. a vfparam -> a vfparam_info = function
  Vfparam_disable_overflow_check -> BoolParam
| Vfparam_fwrapv -> BoolParam
| Vfparam_fno_strict_aliasing -> BoolParam
| Vfparam_assume_left_to_right_evaluation -> BoolParam
| Vfparam_assume_no_provenance -> BoolParam
| Vfparam_assume_no_subobject_provenance -> BoolParam
| Vfparam_no_simplify_terms -> BoolParam
| Vfparam_runtime -> path_opt_param
| Vfparam_include_paths -> path_list_param
| Vfparam_define_macros -> string_list_param
| Vfparam_allow_undeclared_struct_types -> BoolParam
| Vfparam_data_model -> ParsedParam (None, (fun ?basePath x -> Some (data_model_of_string x)), (fun old new_ -> new_))
| Vfparam_uppercase_type_params_carry_typeid -> BoolParam
| Vfparam_rustc_args -> string_list_param
| Vfparam_extern_specs -> string_list_param
| Vfparam_externs -> string_list_param
| Vfparam_skip_specless_fns -> BoolParam
| Vfparam_ignore_ref_creation -> BoolParam
| Vfparam_ignore_unwind_paths -> BoolParam

let default_vfarg: type ta. ta vfparam -> ta = fun p ->
  match vfparam_info_of p with
    BoolParam -> false
  | ParsedParam (a0, _, _) -> a0

let merge_vfarg: type ta. ta vfparam -> ta -> ta -> ta = fun p a0 a ->
  match vfparam_info_of p with
    BoolParam -> a
  | ParsedParam (_, _, merge) -> merge a0 a

type boxed_vfparam = Vfparam: 'a vfparam -> boxed_vfparam

let vfparams = [
  "disable_overflow_check", (Vfparam Vfparam_disable_overflow_check, " ");
  "fwrapv", (Vfparam Vfparam_fwrapv, "allow truncating signed integer arithmetic (corresponds to GCC's -fwrapv flag)");
  "fno-strict-aliasing", (Vfparam Vfparam_fno_strict_aliasing, "Allow accessing an object of type T1 through an lvalue of type T2 (corresponds to GCC's -fno-strict-aliasing flag)");
  "assume_left_to_right_evaluation", (Vfparam Vfparam_assume_left_to_right_evaluation, "Disable checks related to C's unspecified evaluation order and sequencing rules");
  "assume_no_provenance", (Vfparam Vfparam_assume_no_provenance, "Disregard pointer provenance. This is unsound, even when compiling with -O0!");
  "assume_no_subobject_provenance", (Vfparam Vfparam_assume_no_subobject_provenance, "Assume the compiler's alias analysis ignores subobject provenance. CompCert ignores subobject provenance, and so, it seems, do GCC and Clang (last time I checked)");
  "no_simplify_terms", (Vfparam Vfparam_no_simplify_terms, " ");
  "runtime", (Vfparam Vfparam_runtime, " ");
  "I", (Vfparam Vfparam_include_paths, "Add a directory to the list of directories to be searched for header files.");
  "D", (Vfparam Vfparam_define_macros, "Predefine name as a macro, with definition 1.");
  "allow_undeclared_struct_types", (Vfparam Vfparam_allow_undeclared_struct_types, " ");
  "uppercase_type_params_carry_typeid", (Vfparam Vfparam_uppercase_type_params_carry_typeid, "If true, uppercase type parameters carry a typeid");
  "rustc_arg", (Vfparam Vfparam_rustc_args, "Add a rustc command-line argument");
  "extern_spec", (Vfparam Vfparam_extern_specs, "Format: `foo=path/to/foo.rsspec`. Adds external crate `foo` to the Rust prelude");
  "extern", (Vfparam Vfparam_externs, "`-extern path/to/externCrate` is equivalent to `-rustc_arg --extern -rustc_arg externCrate=path/to/externCrate/target/debug/libexternCrate.rlib -rustc_arg -L -rustc_arg dependency=path/to/externCrate/target/debug/deps -extern_spec externCrate=path/to/externCrate/spec/lib.rsspec`");
  "target", (Vfparam Vfparam_data_model, "Target platform of the program being verified. Determines the size of pointer and integer types. Supported targets: " ^ String.concat ", " (List.map fst data_models));
  "skip_specless_fns", (Vfparam Vfparam_skip_specless_fns, "Skip verification of functions for which the user did not provide a precondition and postcondition. This is the default behavior for C, C++ and Java but not for Rust.");
  "ignore_ref_creation", (Vfparam Vfparam_ignore_ref_creation, "In Rust, treat &E or &mut E like &raw E. This is unsound!");
  "ignore_unwind_paths", (Vfparam Vfparam_ignore_unwind_paths, "In Rust, ignore control flow paths due to stack unwinding after a panic. This is sound only when compiling with -C panic=abort.");
]

type vfbinding = Vfbinding: 'a vfparam * 'a -> vfbinding

module Vfbindings : sig
  type t
  val default: t
  val set: 'ta vfparam -> 'ta -> t -> t
  val reset: 'ta vfparam -> t -> t
  val set_or_reset_bool: bool vfparam -> bool -> t -> t
  val get: 'ta vfparam -> t -> 'ta
  val as_list: t -> vfbinding list
end = struct

  type t = vfbinding list

  let default = []

  let rec set: type ta. ta vfparam -> ta -> t -> t = fun p a bs ->
    match bs with
      [] -> [Vfbinding (p, a)]
    | Vfbinding (p0, a0) as b::bs ->
      match cast_vfarg p0 a0 p with
        Some a0 -> Vfbinding (p, merge_vfarg p a0 a)::bs
      | None -> b::set p a bs

  let rec reset: type ta. ta vfparam -> t -> t = fun p bs ->
    match bs with
      [] -> []
    | Vfbinding (p0, a0) as b::bs ->
      if cast_vfarg p0 a0 p <> None then bs else b::reset p bs

  let set_or_reset_bool: bool vfparam -> bool -> t -> t = fun p b bs ->
    if b then set p true bs else reset p bs

  let rec get: type a. a vfparam -> vfbinding list -> a = fun p bs ->
    match bs with
      [] -> default_vfarg p
    | Vfbinding (p0, a0)::bs ->
      match cast_vfarg p0 a0 p with
        Some a0 -> a0
      | None -> get p bs

  let as_list bs = bs

end
let vtype_pred_name sn = sn ^ "_vtype"

type options = {
  option_verbose: int;
  option_verbose_flags: string list;
  option_vfbindings: Vfbindings.t;
  option_allow_should_fail: bool;
  option_emit_manifest: bool;
  option_check_manifest: bool;
  option_vroots: (string * string) list;
  option_allow_assume: bool;
  option_provides: string list;
  option_keep_provide_files: bool;
  option_safe_mode: bool; (* for invocation through web interface *)
  option_header_whitelist: string list;
  option_use_java_frontend : bool;
  option_enforce_annotations : bool;
  option_report_skipped_stmts: bool; (* Report statements in functions or methods that have no contract. *)
  option_allow_ignore_ref_creation: bool;
} (* ?options *)

(* Region: verify_program_core: the toplevel function *)

(* result of symbolic execution; used instead of unit to detect branches not guarded by push and pop calls *)
type symexec_result = SymExecSuccess

type var_debug_info = { internal_name : string; surf_name : string }
type debug_info_rust_fe = { id : loc; info : var_debug_info list }
type debug_info = DbgInfoRustFe of debug_info_rust_fe list
