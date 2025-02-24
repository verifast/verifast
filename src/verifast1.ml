open Proverapi
open Big_int
open Printf
open Num (* rational numbers *)
open Util
open Stats
open Lexer
open Parser
open Verifast0
open Ast

(* Hide the polymorphic comparison operators; they are error-prone *)

module Polymorphic = struct
  let (<=) = (<=)
  let (<) = (<)
  let (>=) = (>=)
  let (>) = (>)
end

let (<=) (x: int) (y: int) = x <= y
let (<) (x: int) (y: int) = x < y
let (>=) (x: int) (y: int) = x >= y
let (>) (x: int) (y: int) = x > y
let min (x: int) (y: int) = min x y
let max (x: int) (y: int) = max x y

exception NoSuchPredicate of string

type callbacks = {
  reportRange: range_kind -> loc0 -> unit;
  reportUseSite: decl_kind -> loc0 -> loc0 -> unit;
  reportExecutionForest: node list ref -> unit;
  reportStmt: loc0 -> unit;
  reportStmtExec: loc0 -> unit;
  reportDirective: string -> loc0 -> bool;
}

let noop_callbacks = {reportRange = (fun _ _ -> ()); reportUseSite = (fun _ _ _ -> ()); reportExecutionForest = (fun _ -> ()); reportStmt = (fun _ -> ()); reportStmtExec = (fun _ -> ()); reportDirective = (fun _ _ -> false)}

module type VERIFY_PROGRAM_ARGS = sig
  val emitter_callback: string -> string -> package list -> unit
  type typenode
  type symbol
  type termnode
  val ctxt: (typenode, symbol, termnode) Proverapi.context
  val options: options
  val program_path: string
  val callbacks: callbacks
  val breakpoint: (string * int) option
  val focus: (string * int) option (* Only verify the function/method/ctor on the specified source line *)
  val targetPath: int list option
end

module VerifyProgram1(VerifyProgramArgs: VERIFY_PROGRAM_ARGS) = struct

  include VerifyProgramArgs

  let () = Hashtbl.clear typedefs

  let path = program_path
  
  let language, dialect = file_specs path
  let is_rust = dialect = Some Rust

  let string_of_type = string_of_type language dialect
  
  let {
    option_verbose=initial_verbosity;
    option_verbose_flags=verbose_flags;
    option_vfbindings=vfbindings;
    option_allow_should_fail=allow_should_fail;
    option_emit_manifest=emit_manifest;
    option_check_manifest=check_manifest;
    option_use_java_frontend=use_java_frontend;
    option_enforce_annotations=enforce_annotations;
    option_report_skipped_stmts=report_skipped_stmts;
    option_allow_ignore_ref_creation=allow_ignore_ref_creation;
  } = options

  let disable_overflow_check = Vfbindings.get Vfparam_disable_overflow_check vfbindings
  let fwrapv = Vfbindings.get Vfparam_fwrapv vfbindings
  let fno_strict_aliasing = Vfbindings.get Vfparam_fno_strict_aliasing vfbindings || dialect = Some Rust
  let assume_left_to_right_evaluation = Vfbindings.get Vfparam_assume_left_to_right_evaluation vfbindings
  let assume_no_provenance = Vfbindings.get Vfparam_assume_no_provenance vfbindings
  let assume_no_subobject_provenance = Vfbindings.get Vfparam_assume_no_subobject_provenance vfbindings || dialect = Some Rust
  let include_paths = Vfbindings.get Vfparam_include_paths vfbindings
  let option_allow_undeclared_struct_types = Vfbindings.get Vfparam_allow_undeclared_struct_types vfbindings
  let data_model = Vfbindings.get Vfparam_data_model vfbindings
  let define_macros = Vfbindings.get Vfparam_define_macros vfbindings
  let include_paths = Vfbindings.get Vfparam_include_paths vfbindings
  let uppercase_type_params_carry_typeid = Vfbindings.get Vfparam_uppercase_type_params_carry_typeid vfbindings || dialect = Some Rust
  let rustc_args = List.rev @@ Vfbindings.get Vfparam_rustc_args vfbindings
  let extern_specs = List.rev @@ Vfbindings.get Vfparam_extern_specs vfbindings
  let externs = List.rev @@ Vfbindings.get Vfparam_externs vfbindings

  let rustc_args =
    let externs_rustc_args =
      externs |> flatmap @@ fun path ->
        let crateName = Filename.basename path in
        let externArg = Printf.sprintf "%s=%s/target/debug/lib%s.rlib" crateName path crateName in
        let libPathArg = Printf.sprintf "dependency=%s/target/debug/deps" path in
        ["--extern"; externArg; "-L"; libPathArg]
    in
    externs_rustc_args @ rustc_args
  
  let extern_specs =
    let externs_extern_specs =
      externs |> List.map @@ fun path ->
        let crateName = Filename.basename path in
        Printf.sprintf "%s=%s/spec/lib.rsspec" crateName path
    in
    externs_extern_specs @ extern_specs

  let tparam_carries_typeid tparam =
    uppercase_type_params_carry_typeid && tparam_is_uppercase tparam

  let () =
    if assume_no_subobject_provenance && not fno_strict_aliasing then
      static_error (Lexed ((path, 1, 1), (path, 1, 1))) "Command-line option -assume_no_subobject_provenance is allowed only in combination with -fno_strict_aliasing" None;
    if assume_no_provenance && not fno_strict_aliasing then
      static_error (Lexed ((path, 1, 1), (path, 1, 1))) "Command-line option -assume_no_provenance is allowed only in combination with -fno_strict_aliasing" None

  let assume_left_to_right_evaluation = assume_left_to_right_evaluation || language <> CLang || dialect = Some Rust

  let {reportRange; reportUseSite; reportExecutionForest; reportStmt; reportStmtExec; reportDirective} = callbacks

  let item_path_separator = if language = Java then "." else "::"

  let full_name pn n = if pn = "" then n else pn ^ item_path_separator ^ n


  let type_info_name = "std::type_info"
  let type_info_struct_type = StructType (type_info_name, [])
  let type_info_ref_type = match dialect with Some Rust -> PtrType (AbstractType type_info_name) | _ -> RefType type_info_struct_type
  let type_info_ptr_type = PtrType type_info_struct_type

  let reportMacroCall l0u l0d =
    reportUseSite DeclKind_Macro l0d l0u

  let reportUseSite dk ld lu =
    if ld <> DummyLoc && lu <> DummyLoc then
    reportUseSite dk (root_caller_token ld) (lexed_loc lu)

  let reportStmt l = reportStmt (root_caller_token l)
  let reportStmtExec l = reportStmtExec (root_caller_token l)

  let data_model =
    match language with
      Java -> Some data_model_java
    | CLang ->
      match dialect with
        Some Rust ->
        if data_model = None then
          match Vfconfig.platform with
            Windows -> Some data_model_llp64
          | _ -> Some data_model_lp64
        else
          data_model
      | _ -> data_model
  let int_width, long_width, ptr_width = decompose_data_model data_model
  let intType = Int (Signed, IntRank)
  let sizeType = Int (Unsigned, PtrRank)
  let ptrdiff_t = Int (Signed, PtrRank)
  let voidPtrType = PtrType Void

  let char_width = LitWidth 0
  let short_width = LitWidth 1
  let llong_width = LitWidth 3

  let width_of_rank r =
    match r with
      CharRank -> char_width
    | ShortRank -> short_width
    | IntRank -> int_width
    | LongRank -> long_width
    | LongLongRank -> llong_width
    | PtrRank -> ptr_width
    | FixedWidthRank k -> LitWidth k

  let charType = Int (Signed, CharRank)
  let u8Type = Int (Unsigned, FixedWidthRank 0)

  let int_rank_and_signedness tp =
    match tp with
      Int (signedness, rank) -> Some (rank, signedness)
    | PtrType _ -> Some (PtrRank, Unsigned)
    | _ -> None

  let verbosity = ref 0
  
  let set_verbosity v =
    verbosity := v;
    ctxt#set_verbosity (v - 3)
  
  let () = set_verbosity initial_verbosity
  
  let class_counter = ref 0
  let func_counter = ref 0

  (** Maps an identifier to a ref cell containing approximately the number of distinct symbols that have been generated for this identifier.
    * It is an approximation because of clashes such as the clash between the second symbol ('foo0') generated for 'foo'
    * and the first symbol ('foo0') generated for 'foo0'. *)
  let used_ids = Hashtbl.create 10000

  (** Contains all ref cells from used_ids that need to be decremented at the next pop(). *)
  let used_ids_undo_stack = ref []

  (** The terms that represent coefficients of leakable chunks. These come from [_] patterns in the source code. *)
  let dummy_frac_terms = ref []

  (** The terms that represent predicate constructor applications. *)
  let pred_ctor_applications : (termnode * (symbol * termnode * type_ list * (termnode list) * int option)) list ref = ref []

  (** When switching to the next symbolic execution branch, this stack is popped to forget about fresh identifiers generated in the old branch. *)
  let used_ids_stack = ref []
  
  let undoStack = ref []
  
  let push_undo_item f = undoStack := f::!undoStack
  
  let undoStackStack = ref []
  let push_undoStack () = undoStackStack := !undoStack::!undoStackStack; undoStack := []
  let pop_undoStack () = List.iter (fun f -> f ()) !undoStack; let h::t = !undoStackStack in undoStack := h; undoStackStack := t
  
  let executionForest: node list ref = ref [] (* toplevel list of execution trees *)
  let () = reportExecutionForest executionForest
  let currentForest: node list ref ref = ref executionForest
  let currentPath: int list ref = ref []
  let currentBranch: int ref = ref 0
  let targetPath: int list option ref = ref (match targetPath with None -> None | Some bs -> Some (List.rev bs))
  
  let contextStack = ref []
  
  let pprint_context_term t = 
    if not (Vfbindings.get Vfparam_no_simplify_terms vfbindings) then
      match ctxt#simplify t with None -> ctxt#pprint t | Some(t) -> ctxt#pprint t
    else
      ctxt#pprint t

  let print_dbg_info pr (di: debug_info) =
    match di with
    | DbgInfoRustFe dbg_info_rust_fe_list -> begin
      let mmsg_dbg_info_rust_fe ({id; info}: debug_info_rust_fe) = begin
        let msg = "id:" ^ Ast.string_of_loc id ^ "|" in
        List.fold_left (fun msg ({internal_name; surf_name}: var_debug_info) -> msg ^ "{internal_name:" ^ internal_name ^ ", surf_name:" ^ surf_name ^"}") msg info
      end
      in
      let msg = "Debug info for \"" ^ path ^ "\"\n" in
      let msg = List.fold_left (fun msg di_rust_fe -> msg ^ mmsg_dbg_info_rust_fe di_rust_fe ^ "\n") msg dbg_info_rust_fe_list in
      pr ("%s": ('a, out_channel, unit) format) msg
    end

  let filter_map_env_of_ctx var_name_map ctx =
    let is_internal_name n = String.starts_with ~prefix:"$" n in
    let map_env_entry (var_name, term) =
      if not (is_internal_name var_name) then
        Some (var_name, term) (*ghost var*)
      else
        match List.find_opt (fun ({internal_name; surf_name}: var_debug_info) -> internal_name = var_name) var_name_map with
        | None -> None
        | Some entry -> Some (entry.surf_name, term)
    in
    match ctx with
    | Executing (heap, env, loc, msg) -> Executing (heap, List.filter_map map_env_entry env, loc, msg)
    | _ -> ctx

  let filter_redundant_ctxs ctxs =
    let filter_ctx out_ctxs ctx =
      match out_ctxs with
      | [] | [ _ ] -> ctx :: out_ctxs
      | last_ctx :: r_ctxs -> begin
        match ctx with
        | Assuming _ -> if ctx = last_ctx then out_ctxs else ctx :: out_ctxs
        | Executing (heap, env, loc, msg) -> begin
          match last_ctx with
          | Executing (heapl, envl, locl, msgl) ->
            let heap, env = List.sort compare heap, List.sort compare env in
            let heapl, envl = List.sort compare heapl, List.sort compare envl in
            if heap = heapl && env = envl then ctx :: r_ctxs else ctx :: out_ctxs
          | _ -> ctx :: out_ctxs
        end
        | PushSubcontext | PopSubcontext | Branching _ -> ctx :: out_ctxs
      end
    in List.fold_left filter_ctx [] (List.rev ctxs)

  let pprint_context_stack cs dbg_info =
    let cs = List.map
      (function
        | Assuming t -> Assuming (pprint_context_term t)
        | Executing (h, env, l, msg) ->
          let h' =
            List.map
              begin function
              | (Chunk ((g, literal), targs, coef, ts, size)) ->
                Chunk ((ctxt#pprint g, literal), targs, pprint_context_term coef, List.map (fun t -> pprint_context_term t) ts, size)
              end
            h
          in
          let env' = List.map (fun (x, t) -> (x, pprint_context_term t)) env
          in
          Executing (h', env', l, msg)
        | PushSubcontext -> PushSubcontext
        | PopSubcontext -> PopSubcontext
        | Branching branch -> Branching branch) cs in
    let var_name_map =
      match List.hd (List.rev cs), dbg_info with
      | Executing (_, _, current_fid, _), Some(dbg_info) -> begin
        (* print_dbg_info Printf.eprintf dbg_info; *)
        match dbg_info with
        | DbgInfoRustFe dbg_info_rust_fe_list when (language, dialect) = (CLang, Some(Rust)) -> begin
          match List.find_opt (fun ({ id; _}: debug_info_rust_fe) -> id = current_fid) dbg_info_rust_fe_list with
          | None -> None (* its a lemma *)
          | Some f -> Some(f.info)
        end
        | DbgInfoRustFe _ -> failwith "Rust debug info for non Rust language"
      end
      | _ -> None
      (* Todo @Nima @Bart: The first context is not always of the kind `Executing` that makes some tests fail if we write
          `let Executing (_, _, current_fid, _) = List.hd (List.rev cs)`. To circumvent this we do not filter variable names
          in case of other kinds of context as the first one. It should be fixed. *)
    in
    let cs =
      match var_name_map with
      | Some var_name_map -> List.map (filter_map_env_of_ctx var_name_map) cs
      | None -> cs
    in
    if (language, dialect) = (CLang, Some(Rust)) then filter_redundant_ctxs cs else cs

  let register_pred_ctor_application t symbol symbol_term targs ts inputParamCount =
    pred_ctor_applications := (t, (symbol, symbol_term, targs, ts, inputParamCount)) :: !pred_ctor_applications

  let success () = SymExecSuccess

  let major_success () =  (* A major success is a successful completion of a symbolic execution path that shows up as a green node in the execution tree. *)
    push (Node (SuccessNode, ref [])) !currentForest;
    success ()

  let pop_context () = let (h::t) = !contextStack in contextStack := t
  
  let contextStackStack = ref []
  
  let push_contextStack () = push_undoStack(); contextStackStack := !contextStack::!contextStackStack
  let pop_contextStack () = pop_undoStack(); let h::t = !contextStackStack in contextStack := h; contextStackStack := t

  (** Remember the current path condition, set of used IDs, and set of dummy fraction terms. *)  
  let push() =
    used_ids_stack := (!used_ids_undo_stack, !dummy_frac_terms, !pred_ctor_applications)::!used_ids_stack;
    used_ids_undo_stack := [];
    ctxt#push;
    push_contextStack ()
  
  (** Restore the previous path condition, set of used IDs, and set of dummy fraction terms. *)
  let pop() =
    pop_contextStack ();
    List.iter (fun r -> decr r) !used_ids_undo_stack;
    let ((usedIdsUndoStack, dummyFracTerms, predCtorApplications)::t) = !used_ids_stack in
    used_ids_undo_stack := usedIdsUndoStack;
    dummy_frac_terms := dummyFracTerms;
    pred_ctor_applications := predCtorApplications;
    used_ids_stack := t;
    ctxt#pop
  
  (** Execute [cont] in a temporary context. *)
  let in_temporary_context cont =
    push();
    let r = cont() in
    pop();
    r
  
  let execute_branch cont =
    let SymExecSuccess = in_temporary_context cont in
    ()
  
  let get_ident_use_count_cell s =
    try
      Hashtbl.find used_ids s
    with Not_found ->
      let cell = ref 0 in
      Hashtbl.add used_ids s cell;
      cell
  
  (** Generate a fresh ID based on string [s]. *)
  let mk_ident s =
    let count_cell = get_ident_use_count_cell s in
    let rec find_unused_ident count =
      count_cell := count + 1;
      used_ids_undo_stack := count_cell::!used_ids_undo_stack;
      if count = 0 then
        s
      else
        let s = Printf.sprintf "%s%d" s (count - 1) in
        let indexed_count_cell = get_ident_use_count_cell s in
        if !indexed_count_cell > 0 then
          find_unused_ident (count + 1)
        else begin
          indexed_count_cell := 1;
          used_ids_undo_stack := indexed_count_cell::!used_ids_undo_stack;
          s
        end
    in
    find_unused_ident !count_cell

  let () =
    (* Emit axiom forall x: inductive, boxed_bool(unboxed_bool(x)) == x with trigger unboxed_bool(x).
     * This is sound because VeriFast only ever constructs a term unboxed_bool(t) if t denotes a boxed boolean.
     * This assumes that the SMT solver strictly respects triggers, and never instantiates a quantifier for a term that does not match the trigger.
     *)
    ctxt#begin_formal;
    let x = ctxt#mk_bound 0 ctxt#type_inductive in
    let unboxed_x = ctxt#mk_unboxed_bool x in
    let eq = ctxt#mk_eq (ctxt#mk_boxed_bool unboxed_x) x in
    ctxt#end_formal;
    ctxt#assume_forall "boxed_bool_unboxed_bool_x_eq_x" [unboxed_x] [ctxt#type_inductive] eq
  
  (** Convert term [t] from type [proverType] to type [proverType0]. *)  
  let apply_conversion proverType proverType0 t =
    match (proverType, proverType0) with
    | (ProverBool, ProverInductive) -> ctxt#mk_boxed_bool t
    | (ProverInt, ProverInductive) -> ctxt#mk_boxed_int t
    | (ProverReal, ProverInductive) -> ctxt#mk_boxed_real t
    | (ProverInductive, ProverBool) -> ctxt#mk_unboxed_bool t
    | (ProverInductive, ProverInt) -> ctxt#mk_unboxed_int t
    | (ProverInductive, ProverReal) -> ctxt#mk_unboxed_real t
    | (t1, t2) when t1 = t2 -> t
  
  let typenode_of_provertype t =
    match t with
      ProverInt -> ctxt#type_int
    | ProverBool -> ctxt#type_bool
    | ProverReal -> ctxt#type_real
    | ProverInductive -> ctxt#type_inductive
  
  let mk_symbol s domain range kind =
    ctxt#mk_symbol (mk_ident s) domain range kind

  (** For higher-order function application *)
  let apply_symbol = ctxt#mk_symbol "@" [ctxt#type_inductive; ctxt#type_inductive] ctxt#type_inductive Uninterp

  (** Generate a fresh SMT solver symbol based on string [s]. *)  
  let mk_func_symbol s domain range kind =
    let s = mk_ident s in
    let domain_tnodes = List.map typenode_of_provertype domain in
    let fsymb = ctxt#mk_symbol s domain_tnodes (typenode_of_provertype range) kind in
    if domain = [] then
      (fsymb, ctxt#mk_app fsymb [])
    else
      let name = "@" ^ s in
      let vsymb = ctxt#mk_app (ctxt#mk_symbol name [] ctxt#type_inductive Uninterp) [] in
      (* Emit an axiom saying that @(@f, x) == f(x) / @(@(@f, x), y) == f(x, y) / ... *)
      ctxt#begin_formal;
      let bounds = imap (fun k t -> ctxt#mk_bound k t) domain_tnodes in
      let app = List.fold_left2 (fun t1 tp t2 -> ctxt#mk_app apply_symbol [t1; apply_conversion tp ProverInductive t2]) vsymb domain bounds in
      let body = ctxt#mk_eq (apply_conversion ProverInductive range app) (ctxt#mk_app fsymb bounds) in
      ctxt#end_formal;
      ctxt#assume_forall name [app] domain_tnodes body;
      (fsymb, vsymb)
  
  let mk_app (fsymb, vsymb) ts =
    ctxt#mk_app fsymb ts
  
  (* Region: boxing and unboxing *)
  
  let rec provertype_of_type t =
    match t with
      Bool -> ProverBool
    | Int (_, _) -> ProverInt
    | RustChar -> ProverInt
    | Float -> ProverInductive
    | Double -> ProverInductive
    | LongDouble -> ProverInductive
    | RealType -> ProverReal
    | InductiveType _ -> ProverInductive
    | StructType (sn, _) -> ProverInductive
    | UnionType un -> ProverInductive
    | ObjType (n, _) -> ProverInt
    | ArrayType t -> ProverInt
    | StaticArrayType (t, s) -> ProverInductive
    | PtrType _ | RustRefType (_, _, _) -> ProverInductive
    | FuncType _| InlineFuncType _ -> ProverInductive
    | PredType (tparams, ts, inputParamCount, _) -> ProverInductive
    | PureFuncType _ -> ProverInductive
    | BoxIdType -> ProverInt
    | HandleIdType -> ProverInt
    | AnyType -> ProverInductive
    | RealTypeParam _ -> ProverInt
    | GhostTypeParam _ -> ProverInductive
    | GhostTypeParamWithEqs _ -> ProverInductive
    | ProjectionType _ -> ProverInductive
    | Void -> ProverInductive
    | InferredType (_, t) -> begin match !t with EqConstraint t -> provertype_of_type t | _ -> t := EqConstraint (InductiveType ("unit", [])); ProverInductive end
    | AbstractType _ -> ProverInductive
    | RefType t -> ProverInductive
    (* Using expressions of the types below as values is wrong, but we must not crash here because this function is in some cases called by the type checker before it detects that there is a problem and produces a proper error message. *)
    | ClassOrInterfaceName n -> ProverInt
    | PackageName n -> ProverInt
    | StaticLifetime -> ProverInductive
    | t -> failwith ("provertype_of_type: " ^ string_of_type t)
  
  let typenode_of_type t = typenode_of_provertype (provertype_of_type t)
  let type_info_type_node = typenode_of_type type_info_ref_type

  (* Generate some global symbols. *)

  let ancestry_symbol = mk_symbol "ancestry" [ctxt#type_int] ctxt#type_inductive Uninterp
  let ancester_at_symbol = mk_symbol "ancester_at" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp
  let get_class_symbol = mk_symbol "getClass" [ctxt#type_int] ctxt#type_int Uninterp
  let class_serial_number = mk_symbol "class_serial_number" [ctxt#type_int] ctxt#type_int Uninterp
  let class_rank = mk_symbol "class_rank" [ctxt#type_int] ctxt#type_real Uninterp
  let func_rank = mk_symbol "func_rank" [ctxt#type_inductive] ctxt#type_real Uninterp
  let bitwise_or_symbol = mk_symbol "bitor" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp
  let bitwise_xor_symbol = mk_symbol "bitxor" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp
  let bitwise_and_symbol = mk_symbol "bitand" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp
  let bitwise_not_symbol = mk_symbol "bitnot" [ctxt#type_int] ctxt#type_int Uninterp
  let arraylength_symbol = mk_symbol "arraylength" [ctxt#type_int] ctxt#type_int Uninterp
  let shiftleft_symbol = mk_symbol "shiftleft" [ctxt#type_int;ctxt#type_int] ctxt#type_int Uninterp (* shift left on an integer's infinite binary representation. Not truncated. May overflow. *)
  let shiftright_symbol = mk_symbol "shiftright" [ctxt#type_int;ctxt#type_int] ctxt#type_int Uninterp (* shift right with sign extension; Java's ">>" operator. For nonnegative n, "x >> n" is equivalent to floor(x / 2^n). *)

  let () = ctxt#assert_term (ctxt#mk_eq (ctxt#mk_unboxed_bool (ctxt#mk_boxed_int (ctxt#mk_intlit 0))) ctxt#mk_false) (* This allows us to use 0 as a default value for all types; see the treatment of array creation. *)

  let boolt = Bool
  let intt = intType
  let instanceof_symbol = ctxt#mk_symbol "instanceof" [ctxt#type_int; ctxt#type_int] ctxt#type_bool Uninterp
  let array_type_symbol = ctxt#mk_symbol "array_type"  [ctxt#type_int] ctxt#type_int Uninterp
  
  let true_term = ctxt#mk_true
  let false_term = ctxt#mk_false
  let mk_bool b = if b then true_term else false_term

  let two_big_int = big_int_of_int 2
  
  let real_zero = ctxt#mk_reallit 0
  let real_unit = ctxt#mk_reallit 1
  let real_half = ctxt#mk_reallit_of_num (num_of_ints 1 2)

  let int_zero_term = ctxt#mk_intlit 0
  let int_unit_term = ctxt#mk_intlit 1

  let term_of_big_int n = ctxt#mk_intlit_of_string (string_of_big_int n)

  type integer_limits = {max_unsigned_big_int: big_int; min_signed_big_int: big_int; max_signed_big_int: big_int; max_unsigned_term: termnode; min_signed_term: termnode; max_signed_term: termnode}

  let max_width = 4 (* (u)int128 *)

  let width_size_terms_table = Array.init (max_width + 1) (fun k -> ctxt#mk_intlit (1 lsl k))

  let width_size_term_ k = width_size_terms_table.(k)

  let get_unique_var_symb x t = 
    ctxt#mk_app (mk_symbol x [] (typenode_of_type t) Uninterp) []

  let mk_typeid_term name = get_unique_var_symb (name ^ "_typeid") (PtrType Void)
  
  let char_typeid_term = mk_typeid_term (match dialect with Some Rust -> "c_char" | _ -> "char")
  let uchar_typeid_term = mk_typeid_term "unsigned_char"
  let short_typeid_term = mk_typeid_term "short"
  let ushort_typeid_term = mk_typeid_term "ushort"
  let int_typeid_term = mk_typeid_term "int"
  let uint_typeid_term = mk_typeid_term "unsigned_int"
  let long_typeid_term = mk_typeid_term "long"
  let ulong_typeid_term = mk_typeid_term "unsigned_long"
  let llong_typeid_term = mk_typeid_term "long_long"
  let ullong_typeid_term = mk_typeid_term "unsigned_long_long"
  let intptr_typeid_term = mk_typeid_term "intptr_t"
  let uintptr_typeid_term = mk_typeid_term "uintptr_t"
  
  let exact_width_integer_typeid_terms = Array.init (max_width + 1) begin fun k ->
    mk_typeid_term ("uint" ^ string_of_int ((1 lsl k) * 8) ^ "_t"),
    mk_typeid_term ("int" ^ string_of_int ((1 lsl k) * 8) ^ "_t")
  end

  let rust_char_typeid_term = mk_typeid_term (match dialect with Some Rust -> "char" | _ -> "rust_char")

  let pointer_typeid_func_symb = mk_symbol "pointer_typeid" [type_info_type_node] type_info_type_node Uninterp
  let mk_pointer_typeid pointee_typeid = ctxt#mk_app pointer_typeid_func_symb [pointee_typeid]
  let void_pointer_typeid_term = mk_typeid_term "void_ptr"
  let rust_mutable_ref_typeid_func_symb = mk_symbol "ref_mut_typeid" [type_info_type_node; type_info_type_node] type_info_type_node Uninterp
  let rust_shared_ref_typeid_func_symb = mk_symbol "ref_typeid" [type_info_type_node; type_info_type_node] type_info_type_node Uninterp
  let mk_rust_ref_typeid lft_typeid kind pointee_typeid =
    match kind with
      Mutable -> ctxt#mk_app rust_mutable_ref_typeid_func_symb [lft_typeid; pointee_typeid]
    | Shared -> ctxt#mk_app rust_shared_ref_typeid_func_symb [lft_typeid; pointee_typeid]
  let array_typeid_func_symb = mk_symbol "array_typeid" [type_info_type_node; ctxt#type_int] type_info_type_node Uninterp
  let mk_array_typeid elem_typeid size = ctxt#mk_app array_typeid_func_symb [elem_typeid; size]
  let bool_typeid_term = mk_typeid_term "bool"
  let float_typeid_term = mk_typeid_term "float"
  let double_typeid_term = mk_typeid_term "double"
  let long_double_typeid_term = mk_typeid_term "long_double"
  let static_lifetime_typeid_term = mk_typeid_term "'static"

  let sizeof_func_symb = mk_symbol "sizeof" [ctxt#type_inductive] ctxt#type_int Uninterp
  let alignof_func_symb = mk_symbol "alignof" [ctxt#type_inductive] ctxt#type_int Uninterp

  let mk_sizeof typeid_term = ctxt#mk_app sizeof_func_symb [typeid_term]
  let mk_alignof typeid_term = ctxt#mk_app alignof_func_symb [typeid_term]

  let int_size_term, long_size_term, ptr_size_term =
    match data_model with
      Some {int_width; long_width; ptr_width} ->
      width_size_term_ int_width, width_size_term_ long_width, width_size_term_ ptr_width
    | None ->
      let int_size_term = get_unique_var_symb "sizeof_int" intType in
      ctxt#assert_term (ctxt#mk_le (ctxt#mk_intlit 2) int_size_term);
      ctxt#assert_term (ctxt#mk_le int_size_term (ctxt#mk_intlit 4));
      let long_size_term = get_unique_var_symb "sizeof_long" intType in
      ctxt#assert_term (ctxt#mk_le (ctxt#mk_intlit 4) long_size_term);
      ctxt#assert_term (ctxt#mk_le long_size_term (ctxt#mk_intlit 8));
      ctxt#assert_term (ctxt#mk_le int_size_term long_size_term);
      let ptr_size_term = get_unique_var_symb "sizeof_ptr" intType in
      ctxt#assert_term (ctxt#mk_le (ctxt#mk_intlit 2) ptr_size_term);
      ctxt#assert_term (ctxt#mk_le int_size_term ptr_size_term);
      ctxt#assert_term (ctxt#mk_le ptr_size_term (ctxt#mk_intlit 8));
      int_size_term, long_size_term, ptr_size_term

  let width_size_term width =
    match width with
      LitWidth k -> width_size_term_ k
    | IntWidth -> int_size_term
    | LongWidth -> long_size_term
    | PtrWidth -> ptr_size_term

  let rank_size_term k = width_size_term (width_of_rank k)

  let () =
    let assert_sizeof typeid_term size_term =
      ctxt#assert_term (ctxt#mk_eq (mk_sizeof typeid_term) size_term)
    in
    assert_sizeof bool_typeid_term (rank_size_term CharRank);
    assert_sizeof char_typeid_term (rank_size_term CharRank);
    assert_sizeof uchar_typeid_term (rank_size_term CharRank);
    assert_sizeof short_typeid_term (rank_size_term ShortRank);
    assert_sizeof ushort_typeid_term (rank_size_term ShortRank);
    assert_sizeof int_typeid_term (rank_size_term IntRank);
    assert_sizeof uint_typeid_term (rank_size_term IntRank);
    assert_sizeof long_typeid_term (rank_size_term LongRank);
    assert_sizeof ulong_typeid_term (rank_size_term LongRank);
    assert_sizeof llong_typeid_term (rank_size_term LongLongRank);
    assert_sizeof ullong_typeid_term (rank_size_term LongLongRank);
    assert_sizeof intptr_typeid_term (rank_size_term PtrRank);
    assert_sizeof uintptr_typeid_term (rank_size_term PtrRank);
    for k = 0 to max_width do
      assert_sizeof (fst exact_width_integer_typeid_terms.(k)) (width_size_term_ k);
      assert_sizeof (snd exact_width_integer_typeid_terms.(k)) (width_size_term_ k)
    done;
    assert_sizeof float_typeid_term (width_size_term_ 2);
    assert_sizeof double_typeid_term (width_size_term_ 3);
    assert_sizeof void_pointer_typeid_term (width_size_term ptr_width);
    ctxt#begin_formal;
    let t = ctxt#mk_bound 0 type_info_type_node in
    let app = mk_sizeof (mk_pointer_typeid t) in
    let eq = ctxt#mk_eq app (width_size_term ptr_width) in
    ctxt#end_formal;
    ctxt#assume_forall "sizeof_pointer" [app] [type_info_type_node] eq

  let union_size_partial umap l un =
    match try_assoc un umap with
      Some (_, Some (_, s), _) -> s
    | _ -> static_error l (sprintf "Cannot take size of undefined union '%s'" un) None
  
  let integer_limits_table =
    Array.init (max_width + 1) begin fun k ->
      let max_unsigned_big_int = pred_big_int (shift_left_big_int unit_big_int (8 * (1 lsl k))) in
      let max_signed_big_int = shift_right_big_int max_unsigned_big_int 1 in
      let min_signed_big_int = pred_big_int (minus_big_int max_signed_big_int) in
      let max_unsigned_term = term_of_big_int max_unsigned_big_int in
      let max_signed_term = term_of_big_int max_signed_big_int in
      let min_signed_term = term_of_big_int min_signed_big_int in
      {max_unsigned_big_int; max_signed_big_int; min_signed_big_int; max_unsigned_term; max_signed_term; min_signed_term}
    end

  let max_unsigned_big_int k = integer_limits_table.(k).max_unsigned_big_int
  let min_signed_big_int k = integer_limits_table.(k).min_signed_big_int
  let max_signed_big_int k = integer_limits_table.(k).max_signed_big_int
  let max_unsigned_term k = integer_limits_table.(k).max_unsigned_term
  let min_signed_term k = integer_limits_table.(k).min_signed_term
  let max_signed_term k = integer_limits_table.(k).max_signed_term

  let get_fresh_integer_type_limits_symbols name signed_max_lowerBounds signed_max_upperBounds =
    let signed_min_term = get_unique_var_symb (name ^ "_MIN") intType in
    let signed_max_term = get_unique_var_symb (name ^ "_MAX") intType in
    let unsigned_max_term = get_unique_var_symb ("U" ^ name ^ "_MAX") intType in
    ctxt#assert_term (ctxt#mk_eq signed_min_term (ctxt#mk_add (ctxt#mk_mul (ctxt#mk_intlit (-1)) signed_max_term) (ctxt#mk_intlit (-1))));
    ctxt#assert_term (ctxt#mk_eq unsigned_max_term (ctxt#mk_add (ctxt#mk_mul (ctxt#mk_intlit 2) signed_max_term) (ctxt#mk_intlit 1)));
    signed_max_lowerBounds |> List.iter (fun lb -> ctxt#assert_term (ctxt#mk_le lb signed_max_term));
    signed_max_upperBounds |> List.iter (fun ub -> ctxt#assert_term (ctxt#mk_le signed_max_term ub));
    signed_min_term, signed_max_term, unsigned_max_term

  let min_int_term, max_int_term, max_uint_term, min_long_term, max_long_term, max_ulong_term, min_intptr_term, max_intptr_term, max_uintptr_term =
    match data_model with
      Some {int_width; long_width; ptr_width} ->
      min_signed_term int_width,
      max_signed_term int_width,
      max_unsigned_term int_width,
      min_signed_term long_width,
      max_signed_term long_width,
      max_unsigned_term long_width,
      min_signed_term ptr_width,
      max_signed_term ptr_width,
      max_unsigned_term ptr_width
    | None ->
      let min_int_term, max_int_term, max_uint_term = get_fresh_integer_type_limits_symbols "INT" [max_signed_term 1] [max_signed_term 2] in
      let min_long_term, max_long_term, max_ulong_term = get_fresh_integer_type_limits_symbols "LONG" [max_int_term; max_signed_term 2] [max_signed_term 3] in
      let min_intptr_term, max_intptr_term, max_uintptr_term = get_fresh_integer_type_limits_symbols "INTPTR" [max_int_term] [max_signed_term 3] in
      min_int_term, max_int_term, max_uint_term,
      min_long_term, max_long_term, max_ulong_term,
      min_intptr_term, max_intptr_term, max_uintptr_term
  
  let limits_of_type t =
    let Some (k, s) = int_rank_and_signedness t in
    match s, width_of_rank k with
      Signed, LitWidth k -> let {min_signed_term; max_signed_term} = integer_limits_table.(k) in (min_signed_term, max_signed_term)
    | Unsigned, LitWidth k -> let {max_unsigned_term} = integer_limits_table.(k) in (int_zero_term, max_unsigned_term)
    | Unsigned, PtrWidth -> (int_zero_term, max_uintptr_term)
    | Signed, IntWidth -> (min_int_term, max_int_term)
    | Unsigned, IntWidth -> (int_zero_term, max_uint_term)
    | Signed, LongWidth -> (min_long_term, max_long_term)
    | Unsigned, LongWidth -> (int_zero_term, max_ulong_term)
    | Signed, PtrWidth -> (min_intptr_term, max_intptr_term)
  
  let is_within_limits n t =
    match int_rank_and_signedness t with
      Some (k, s) ->
      begin match s, width_of_rank k with
        Signed, LitWidth k -> le_big_int (min_signed_big_int k) n && le_big_int n (max_signed_big_int k)
      | Unsigned, LitWidth k -> le_big_int zero_big_int n && le_big_int n (max_unsigned_big_int k)
      | _ -> false
      end
    | _ -> false

  let get_dummy_frac_term () =
    let t = get_unique_var_symb "dummy" RealType in
    dummy_frac_terms := t::!dummy_frac_terms;
    t
  
  let is_dummy_frac_term t = List.memq t !dummy_frac_terms
  
  let real_unit_pat = TermPat real_unit
  
  let current_module_name =
    match language with
      | Java -> "current_module"
      | CLang -> Filename.chop_extension (Filename.basename path)
  
  let current_module_term = get_unique_var_symb current_module_name intType
  
  let programDir = Filename.dirname path
  let rtpath = match Vfbindings.get Vfparam_runtime vfbindings with None -> concat (rtdir()) "rt.jarspec" | Some path -> path

  (** Records the source lines containing //~, indicating that VeriFast is supposed to detect an error on that line. *)
  let shouldFailLocs: loc0 list ref = ref []
  
  (* Callback function called from the lexer. *)
  let reportShouldFail directive l =
    if not (reportDirective directive l) then
      if allow_should_fail then
        shouldFailLocs := l::!shouldFailLocs
      else
        static_error (Lexed l) "Should fail directives are not allowed; use the -allow_should_fail command-line option to allow them." None

  let check_should_fail default body =
    let locs_match ((path0, line0, _), _) ((path1, line1, _), _) = path0 = path1 && line0 = line1 in
    let should_fail l = let l = root_caller_token l in List.exists (locs_match l) !shouldFailLocs in
    let has_failed l = let l = root_caller_token l in shouldFailLocs := remove (locs_match l) !shouldFailLocs; default in
    let loc_of_ctxts ctxts l = match get_root_caller ctxts with None -> l | Some l -> l in
    try
      body ()
    with
    | StaticError (l, msg, url) when should_fail l -> has_failed l
    | SymbolicExecutionError (ctxts, l, msg, url) when should_fail (loc_of_ctxts ctxts l) -> has_failed (loc_of_ctxts ctxts l)
    | PreprocessorDivergence (l,s) when should_fail (Lexed l) -> has_failed (Lexed l)
    | ParseException (l,s) when should_fail l -> has_failed l
 
  let prototypes_used : (string * loc) list ref = ref []
  
  let extract_specs ps=
    let rec iter (pn,ilist) classes lemmas ds=
      match ds with
      [] -> (classes,lemmas)
    | Class (l, abstract, fin, cn, meths, fds, cons, super, tparams, inames, preds)::rest ->
      let cn = full_name pn cn in
      let meths' = meths |> List.filter begin
        fun x ->
          match x with
            | Meth(lm, gh, t, n, ps, co, ss, fb, v, abstract, mtparams) ->
              match ss with
                | None -> true
                | Some _ -> false
      end in
      let cons' = cons |> List.filter begin
        fun x ->
          match x with
            | Cons (lm, ps, co, ss, v) ->
              match ss with
                | None -> true
                | Some _ -> false
      end in
      iter (pn,ilist) (Class(l, abstract, fin, cn, meths', fds, cons', super, tparams, inames, [])::classes) lemmas rest
    | Func(l,Lemma(_),tparams,rt,fn,arglist,nonghost_callers_only,ftype,contract,terminates,None,_,_) as elem ::rest->
      iter (pn, ilist) classes (elem::lemmas) rest
    | _::rest -> 
      iter (pn, ilist) classes lemmas rest
    in
    let rec iter' (classes,lemmas) ps=
      match ps with
        PackageDecl(l,pn,ilist,ds)::rest-> iter' (iter (pn,ilist) classes lemmas ds) rest
      | [] -> (classes,lemmas)
    in
    iter' ([],[]) ps

  let structures_defined     : (string * loc * loc) list ref = ref [] (* (name, declLoc, bodyLoc) *)
  let unions_defined         : (string * loc * loc) list ref = ref [] (* (name, declLoc, bodyLoc) *)
  let nonabstract_predicates : (string * loc * loc) list ref = ref [] (* (name, familyLoc, instanceLoc) *)
  
  (* Region: check_file *)
  
  module CheckFileTypes = struct
    type 'a map = (string * 'a) list
    type struct_field_info =
        loc
      * ghostness
      * type_
      * symbol option (* offset *)
      * expr option (* init *)
    type cxx_ctor_info =
        loc 
      * type_ map (* params *)
      * asn (* pre *)
      * type_ map (* tenv after pre *)
      * (string (* result variable *) * asn) (* post *)
      * bool (* terminates *)
      * ((string * (expr * bool (* is written *)) option) list (* init list *) * (stmt list * loc)) option option
    type cxx_dtor_info =
        loc 
      * asn (* pre *)
      * type_ map (* tenv after pre *)
      * (string (* result variable *) * asn) (* post *)
      * bool (* terminates *)
      * (stmt list * loc) option option
      * bool (* is_virtual *)
      * string list (* overrides: direct base struct names *)
    type base_spec_info = 
        loc 
      * bool (* virtual *)
      * termnode (* offset *)
    type struct_info =
        loc
      * string list (* type parameters *)
      * (base_spec_info map * struct_field_info map * bool (* has virtual methods *)) option (* None if struct without body *)
      * termnode option (* predicate symbol for struct_padding predicate *)
      * symbol (* type_info_func *)
    type union_field_info =
        loc
      * type_
    type union_info =
        loc
      * ((string * union_field_info) list * termnode (* size *)) option (* None if union without body *) * termnode (* typeid *)
    type enum_info =
        big_int
    type global_info =
        loc
      * type_
      * termnode (* address symbol *)
      * expr option ref (* initializer *)
    type module_info =
        termnode
    type func_symbol =
        symbol
      * termnode (* function as value (for use with "apply") *)
    type pure_func_info =
        loc
      * string list (* type parameters *)
      * type_ (* return type *)
      * (string * type_) list (* parameter names (can be empty string) and types *)
      * func_symbol
    type param_rel =
      IsProperComponentOf (* irreflexive *)
    | IsComponentOf (* reflexive *)
    type pure_func_param_requires_info =
        (int * (loc * int * param_rel * int) list) list (* parameter requires clauses. For example, 'map(f, xs)' has requires clauses [0, [0, Lt, 1]] because it only calls its first argument 'f' with a first argument that is a component of its own second argument 'xs'. *)
    type inductive_ctor_info =
        string (* fully qualified constructor name *)
      * pure_func_info
    type inductive_info =
        loc
      * string list (* type parameters *)
      * (string * inductive_ctor_info) list
      * (string * symbol) list (* getter functions - empty if more than one constructor *)
      * (string * symbol) list (* setter functions - empty if more than one constructor *)
      * string list option (* The type is infinite if any of these type parameters are infinite; if None, it is always infinite. *)
      * int (* 0 = does not contain 'any' or predicate types; 1 = contains 'any' or predicate types, but only in positive positions; 2 = contains 'any' or predicate types in negative positions *)
      * InductiveSubtype.t
      * symbol option (* typeid function, but only if this type does not contain 'any' in negative positions, assuming that type arguments do not contain 'any' in negative positions. *)
    type pred_ctor_info =
      PredCtorInfo of
        loc
      * string list (* type parameters *)
      * (string * type_) list (* constructor parameters *)
      * (string * type_) list (* predicate parameters *)
      * int option (* inputParamCount *)
      * asn (* body *)
      * func_symbol
    type pred_fam_info =
        loc
      * string list (* type parameters *)
      * int (* number of predicate family indices *)
      * type_ list (* parameter types *)
      * termnode
      * int option (* number of input parameters; None if not precise *)
      * inductiveness
    type struct_accessor_info =
        loc
      * symbol                 (* constructor function *)
      * (string * symbol) list (* getter function for each field *)
      * (string * symbol) list (* setter function for each field *)
      * symbol                 (* constructor.opt function *)
    type malloc_block_pred_info =
        string (* predicate name *)
      * pred_fam_info
    type new_block_pred_info =
        string (* predicate name *)
      * pred_fam_info
    type bases_constructed_pred_info =
        string (* predicate name *)
      * pred_fam_info
    type cxx_vtype_pred_info =
        string (* predicate name *)
      * pred_fam_info
    type field_pred_info =
        string (* predicate name *)
      * pred_fam_info
    type pred_inst_info =
        (string * termnode) list (* environment at definition site (for local predicate family instances; see e.g. examples/mcas/mcas.c) *)
      * loc
      * string list (* type parameters *)
      * (string * type_) list (* parameters *)
      * termnode (* predicate family symbol *)
      * int option (* input parameter count *)
      * asn (* body *)
    type pred_inst_map = ((string * string list) (* predicate name and indices *) * pred_inst_info) list
    type func_info =
      FuncInfo of
        (string * termnode) list (* environment at definition site (for local lemma functions) *)
      * termnode (* function pointer *)
      * loc
      * func_kind
      * string list (* type parameters *)
      * type_ option
      * (string * type_) list (* parameters *)
      * bool (* nonghost_callers_only *)
      * asn (* precondition *)
      * (string * type_) list (* type environment after precondition *)
      * (string (* result variable *) * asn) (* postcondition *)
      * bool  (* terminates *)
      * (string * pred_fam_info map * type_ list * (loc * string) list) option (* implemented function type, with function type type arguments and function type arguments *)
      * (stmt list * loc (* closing brace *) ) option option (* body; None if prototype; Some None if ? *)
      * bool (* virtual *)
      * string list (* overrides *)
    type func_type_info =
        loc
      * ghostness
      * string list (* type parameters *)
      * type_ option (* return type *)
      * type_ map (* parameters of the function type *)
      * type_ map (* parameters of the function *)
      * asn (* precondition *)
      * (string (* result variable *) * asn) (* postcondition *)
      * bool (* terminates *)
      * pred_fam_info map (* the is_xyz predicate, if any *)
      * termnode (* typeid *)
    type signature = string * type_ list
    type method_info =
      MethodInfo of
        loc
      * ghostness
      * type_ option
      * type_ map (* parameters *)
      * asn (* precondition *)
      * type_ map (* type environment after precondition *)
      * asn (* postcondition *)
      * (type_ * asn) list (* throws clauses *)
      * asn (* dynamic precondition (= precondition for dynamically bound calls) *)
      * asn (* dynamic postcondition (= postcondition for dynamically bound calls) *)
      * (type_ * asn) list (* dynamic throws clauses *)
      * bool (* terminates *)
      * ((stmt list * loc) * int (*rank for termination check*)) option option (* body *)
      * method_binding
      * visibility
      * bool (* is override *)
      * bool (* is abstract *)
      * string list (* type parameters *)
    type interface_method_info =
      ItfMethodInfo of
        loc
      * ghostness
      * type_ option (* return type *)
      * type_ map (* parameters *)
      * asn (* precondition *)
      * type_ map (* type environment after precondition *)
      * asn (* postcondition *)
      * (type_ * asn) list (* throws clauses *)
      * bool (* terminates *)
      * visibility
      * bool (* is abstract *)
      * string list (* type parameters *)
    type field_info = {
        fl: loc;
        fgh: ghostness;
        ft: type_;
        fvis: visibility;
        fbinding: method_binding;
        ffinal: bool;
        finit: expr option;
        fvalue: constant_value option option ref
      }
    type ctor_info =
      CtorInfo of
        loc
      * type_ map (* parameters *)
      * asn
      * type_ map
      * asn
      * (type_ * asn) list
      * bool (* terminates *)
      * ((stmt list * loc) * int (*rank for termination check*)) option option
      * visibility
    type inst_pred_info =
        loc
      * type_ map
      * string (* family (= class or interface that first declared the predicate) *)
      * termnode
      * asn option
    type interface_inst_pred_info =
        loc
      * type_ map (* parameters *)
      * string (* family (= class or interface that first declared the predicate) *)
      * termnode (* predicate symbol *)
    type interface_info =
      InterfaceInfo of
        loc
      * field_info map
      * (signature * interface_method_info) list
      * interface_inst_pred_info map
      * (string * type_ list) list (* superinterfaces with passed targs *)
      * string list (* type parameters *)
    type class_info = {
      cl: loc;
      cabstract: bool;
      cfinal: class_finality;
      cmeths: (signature * method_info) list;
      cfds: field_info map;
      cctors: (type_ list * ctor_info) list;
      csuper: (string * type_ list);
      cinterfs: (string * type_ list) list;
      cpreds: inst_pred_info map;
      cpn: string; (* package *)
      cilist: import list;
      ctpenv: string list
    }
    type box_action_permission_info =
        termnode (* term representing action permission predicate *)
      * termnode option (* term representing action permission dispenser predicate *)
    type box_action_info =
        loc
      * box_action_permission_info option (* information about permissions required to perform this action, if it is permission-based *)
      * type_ map (* parameters *)
      * expr (* precondition *)
      * expr (* postcondition *)
    type box_handle_predicate_info =
        loc
      * type_ map (* parameters *)
      * string option (* name of extended handle, if any *)
      * asn (* invariant *)
      * preserved_by_clause list
    type box_info = (* shared boxes *)
        loc
      * type_ map (* box parameters *)
      * asn (* invariant *)
      * type_ map (* variables bound by invariant *)
      * box_action_info map
      * box_handle_predicate_info map
    type abstract_type_info = loc
    type type_pred_decl_info =
      loc *
      string * (* self type name*)
      type_ *
      symbol
    type maps =
        struct_info map
      * union_info map
      * enum_info map
      * global_info map
      * module_info map
      * module_info map
      * inductive_info map
      * pure_func_info map
      * pure_func_param_requires_info map
      * pred_ctor_info map
      * struct_accessor_info map
      * malloc_block_pred_info map
      * new_block_pred_info map
      * ((string * string) * (field_pred_info * field_pred_info option)) list
      * pred_fam_info map
      * pred_inst_map
      * (loc * string list * type_) map (* typedefmap *)
      * func_type_info map
      * func_info map
      * box_info map
      * class_info map
      * interface_info map
      * termnode map (* classterms *)
      * termnode map (* interfaceterms *)
      * abstract_type_info map
      * cxx_ctor_info map
      * cxx_dtor_info map
      * bases_constructed_pred_info map
      * cxx_vtype_pred_info map
      * inst_pred_info map map
      * type_pred_decl_info map
    
    type implemented_prototype_info =
        string
      * loc
    type implemented_function_type_info =
        string (* function name *)
      * loc (* function location *)
      * string (* function type name *)
      * string list (* function type arguments; only module names are supported *)
      * bool (* function is declared in an unloadable module *)
    type defined_structure_info =
        string     (* structure name *)
      * loc        (* structure forward declaration location *)
      * loc        (* structure body location *)
    type defined_union_info =
        string     (* union name *)
      * loc        (* union forward declaration location *)
      * loc        (* union body location *)
    type nonabstract_predicate_info =
        string     (* predicate name *)
      * loc        (* predicate forward declaration (= family) location *)
      * loc        (* predicate body (= instance) location *)
    type check_file_output =
        implemented_prototype_info list
      * implemented_function_type_info list
      * defined_structure_info list
      * defined_union_info list
      * nonabstract_predicate_info list
      * module_info map
  end
  
  let javaLangObject = ObjType ("java.lang.Object", [])

  include CheckFileTypes
  
  (* Maps a header file name to the list of header file names that it includes, and the various maps of VeriFast elements that it declares directly. *)
  let headermap: ((loc * (include_kind * string * string) * string list * package list) list * maps) map ref = ref []
  let spec_classes= ref []
  let spec_lemmas= ref []

  let prelude_maps = ref None
  
  (** Verify the .c/.h/.jarsrc/.jarspec file whose headers are given by [headers] and which declares packages [ps].
      As a side-effect, adds all processed headers to the header map.
      Recursively calls itself on headers included by the current file.
      Returns the elements declared directly in the current file.
      May add symbols and global assumptions to the SMT solver.
      
      Paths in [headers] are taken from the source file, which is in [reldir], which is relative to [basedir].
      Note: [basedir] is either the directory of the program being verified (i.e. the file specified on the command line) or
      the directory of the VeriFast built-in header files (= <verifasthome>/bin for C and <verifasthome>/bin/rt for Java).
      
      is_import_spec:
        true if the file being checked specifies a module used by the module being verified
        false if the file being checked specifies the module being verified
    *)
  
  module type CHECK_FILE_ARGS = sig
    val filepath: string
    val is_import_spec: bool
    val include_prelude: bool
    val dir: string
    val headers: (loc * (include_kind * string * string) * string list * package list) list
    val ps: package list

    val dbg_info: debug_info option

    (** For recursive calls. *)
    val check_file: string -> bool -> bool -> string -> (loc * (include_kind * string * string) * string list * package list) list -> package list -> debug_info option -> check_file_output * maps
  end
  
  module CheckFile1(CheckFileArgs: CHECK_FILE_ARGS) = struct
  
  include CheckFileArgs

  let () = emitter_callback filepath dir ps

  let assert_false h env l msg url =
    Util.push (Node (ErrorNode, ref [])) !currentForest;
    raise (SymbolicExecutionError (pprint_context_stack !contextStack dbg_info, l, msg, Option.map (fun topic -> [HelpTopic topic]) url))

  let push_node l msg =
    let oldPath, oldBranch, oldTargetPath = !currentPath, !currentBranch, !targetPath in
    targetPath :=
      begin match oldTargetPath with
        Some (b::bs) ->
          if b = oldBranch then
            if bs = [] then
              assert_false [] [] l "Target branch reached" None
            else
              Some bs
          else
            Some []
        | p -> p
      end;
    currentPath := oldBranch::oldPath;
    currentBranch := 0;
    push_undo_item (fun () -> currentPath := oldPath; currentBranch := oldBranch + 1; targetPath := oldTargetPath);
    let newForest = ref [] in
    let oldForest = !currentForest in
    Util.push (Node (ExecNode (msg, !currentPath), newForest)) oldForest;
    push_undo_item (fun () -> currentForest := oldForest);
    currentForest := newForest

  let push_context ?(verbosity_level = 1) msg =
    contextStack := msg::!contextStack;
    begin match msg with
      Executing (h, env, l, msg) ->
        if !verbosity >= verbosity_level then printff "%10.6fs: %s: %s\n" (Perf.time ()) (string_of_loc l) msg;
        push_node l msg
      | _ -> ()
    end

  let with_context_force msg cont =
    !stats#execStep;
    push_contextStack ();
    push_context msg;
    let result = cont() in
    pop_contextStack ();
    result

  let with_context ?(verbosity_level = 1) msg cont =
    !stats#execStep;
    push_contextStack ();
    push_context ~verbosity_level msg;
    do_finally
      begin fun () ->
        if !targetPath <> Some [] then
          cont ()
        else
          SymExecSuccess
      end
      pop_contextStack

  let is_jarspec = Filename.check_suffix filepath ".jarspec"

  let _ = if options.option_verbose = -1 then Printf.printf "%10.6fs: >> type checking of %s \n" (Perf.time()) filepath

  let
    (
      (structmap0: struct_info map),
      (unionmap0: union_info map),
      (enummap0: enum_info map),
      (globalmap0: global_info map),
      (modulemap0: module_info map),
      (importmodulemap0: module_info map),
      (inductivemap0: inductive_info map),
      (purefuncmap0: pure_func_info map),
      (purefuncparamrequiresmap0: pure_func_param_requires_info map),
      (predctormap0: pred_ctor_info map),
      (struct_accessor_map0: struct_accessor_info map),
      (malloc_block_pred_map0: malloc_block_pred_info map),
      (new_block_pred_map0: new_block_pred_info map),
      (field_pred_map0: ((string * string) * (field_pred_info * field_pred_info option)) list),
      (predfammap0: pred_fam_info map),
      (predinstmap0: pred_inst_map),
      (typedefmap0: (loc * string list * type_) map),
      (functypemap0: func_type_info map),
      (funcmap0: func_info map),
      (boxmap0: box_info map),
      (classmap0: class_info map),
      (interfmap0: interface_info map),
      (classterms0: termnode map),
      (interfaceterms0: termnode map),
      (abstract_types_map0: abstract_type_info map),
      (cxx_ctor_map0: cxx_ctor_info map),
      (cxx_dtor_map0: cxx_dtor_info map),
      (bases_constructed_map0: bases_constructed_pred_info map),
      (cxx_vtype_map0: cxx_vtype_pred_info map),
      (cxx_inst_pred_map0: inst_pred_info map map),
      (typepreddeclmap0: type_pred_decl_info map)
      : maps
    ) =

    let append_nodups xys xys0 string_of_key l elementKind =
      let rec iter xys =
        match xys with
          [] -> xys0
        | ((x, y) as elem)::xys ->
          if List.mem_assoc x xys0 then static_error l ("Duplicate " ^ elementKind ^ " '" ^ string_of_key x ^ "'") None;
          elem::iter xys
      in
      iter xys
    in
    let id x = x in
    let merge_maps l
      (structmap, unionmap, enummap, globalmap, modulemap, importmodulemap, inductivemap, purefuncmap, purefuncparamrequiresmap, predctormap, struct_accessor_map, malloc_block_pred_map, new_block_pred_map, field_pred_map, predfammap, predinstmap, typedefmap, functypemap, funcmap, boxmap, classmap, interfmap, classterms, interfaceterms, abstract_types_map, cxx_ctor_map, cxx_dtor_map, bases_constructed_map, cxx_vtype_map, cxx_inst_pred_map, type_pred_decl_map)
      (structmap0, unionmap0, enummap0, globalmap0, modulemap0, importmodulemap0, inductivemap0, purefuncmap0, purefuncparamrequiresmap0, predctormap0, struct_accessor_map0, malloc_block_pred_map0, new_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, typedefmap0, functypemap0, funcmap0, boxmap0, classmap0, interfmap0, classterms0, interfaceterms0, abstract_types_map0, cxx_ctor_map0, cxx_dtor_map0, bases_constructed_map0, cxx_vtype_map0, cxx_inst_pred_map0, type_pred_decl_map0)
      =
      (
(*     append_nodups structmap structmap0 id l "struct", *)
       structmap @ structmap0,
       append_nodups unionmap unionmap0 id l "union",
       append_nodups enummap enummap0 id l "enum",
       append_nodups globalmap globalmap0 id l "global variable",
       modulemap @ modulemap0,
(*     append_nodups modulemap modulemap0 id l "module", *)
       importmodulemap @ importmodulemap0,
(*     append_nodups importmodulemap importmodulemap0 id l "imported module", *)
       append_nodups inductivemap inductivemap0 id l "inductive datatype",
       append_nodups purefuncmap purefuncmap0 id l "pure function",
       purefuncparamrequiresmap @ purefuncparamrequiresmap0,
       append_nodups predctormap predctormap0 id l "predicate constructor",
       struct_accessor_map @ struct_accessor_map0,
       malloc_block_pred_map @ malloc_block_pred_map0,
       new_block_pred_map @ new_block_pred_map0,
       field_pred_map @ field_pred_map0,
       append_nodups predfammap predfammap0 id l "predicate",
(*     append_nodups predinstmap predinstmap0 (fun (p, is) -> p ^ "(" ^ String.concat ", " is ^ ")") l "predicate instance", *)
       predinstmap @ predinstmap0,
       append_nodups typedefmap typedefmap0 id l "typedef",
       append_nodups functypemap functypemap0 id l "function type",
       append_nodups funcmap funcmap0 id l "function",
       append_nodups boxmap boxmap0 id l "box predicate",
       append_nodups classmap classmap0 id l "class",
       append_nodups interfmap interfmap0 id l "interface",
       classterms @ classterms0, 
       interfaceterms @ interfaceterms0,
       append_nodups abstract_types_map abstract_types_map0 id l "abstract type",
       append_nodups cxx_ctor_map cxx_ctor_map0 id l "constructor",
       append_nodups cxx_dtor_map cxx_dtor_map0 id l "destructor",
       bases_constructed_map @ bases_constructed_map0,
       cxx_vtype_map @ cxx_vtype_map0,
       cxx_inst_pred_map @ cxx_inst_pred_map0,
       append_nodups type_pred_decl_map type_pred_decl_map0 id l "type predicate")
    in

    (* [merge_header_maps maps0 headers] returns [maps0] plus all elements transitively declared in [headers]. *)
    let rec merge_header_maps include_prelude maps0 headers_included dir headers global_headers =
      match headers with
        [] -> (maps0, headers_included)
      | (l, (include_kind, header_path, total_path), hs, header_decls)::headers ->
        if List.mem header_path ["include_ignored_by_verifast.h"; "assert.h"; "limits.h"] then
          merge_header_maps include_prelude maps0 headers_included dir headers global_headers
        else begin
          if (options.option_safe_mode || options.option_header_whitelist <> []) && not (List.mem header_path options.option_header_whitelist) then
            static_error l "This header file is not on the header whitelist." None;
          let includepaths = (match include_kind with DoubleQuoteInclude -> [dir] | AngleBracketInclude -> []) @ include_paths @ [!bindir] in
          let rec find_include_file includepaths =
            match language with
              CLang ->
                total_path
            | Java ->
                match includepaths with
                  [] -> static_error l (Printf.sprintf "No such file: '%s'" header_path) None
                | head::body ->
                  let headerpath = concat head header_path in
                  if Sys.file_exists headerpath then
                    headerpath
                  else
                    (find_include_file body)
          in
          let path = find_include_file includepaths in
          if List.mem path headers_included then
            merge_header_maps include_prelude maps0 headers_included dir headers global_headers
          else begin
            let (headers', maps) =
              match try_assoc path !headermap with
                None ->
                let header_is_import_spec = Filename.remove_extension (Filename.basename header_path) <> Filename.chop_extension (Filename.basename program_path) in
                let (headers', ds) =
                  match language with
                    CLang ->
                      let rec look_up h =
                        try 
                          List.find (fun (l', (_,h',tp'), hs', ps') -> h = tp') global_headers
                        with
                          Not_found -> static_error l (Printf.sprintf "Necessary header %s is not parsed" header_path) None
                      in
                      (List.map (fun h -> look_up h) hs, header_decls)
                  | Java ->
                    let (jars, javaspecs) = parse_jarspec_file_core path in
                    let pathDir = Filename.dirname path in
                    let ds = Java_frontend_bridge.parse_java_files (List.map (fun javaspec -> concat pathDir javaspec) javaspecs) [] 
                                                                   reportRange reportShouldFail initial_verbosity enforce_annotations use_java_frontend
                    in
                    if not header_is_import_spec then begin
                      let (classes, lemmas) = extract_specs ds in
                      spec_classes := classes;
                      spec_lemmas := lemmas
                    end;
                    let l = Lexed (file_loc path) in
                    let spec_include_for_jar jar =
                      let jarspec = (Filename.chop_extension jar) ^ ".jarspec" in
                      (l, (DoubleQuoteInclude, jarspec, concat !bindir jarspec), [], [])
                    in
                    let jarspecs = List.map spec_include_for_jar jars in 
                    (jarspecs, ds)
                in
                reportUseSite DeclKind_HeaderFile (Lexed ((path, 1, 1), (path, 1, 1))) l;
                let (_, maps) = check_file header_path header_is_import_spec include_prelude (Filename.dirname path) headers' ds (*Todo @Nima: dbg_info*) None in
                headermap := (path, (headers', maps))::!headermap;
                (headers', maps)
              | Some (headers', maps) ->
                (headers', maps)
            in
            let path_dir = Filename.dirname path in
            let (maps0, headers_included) = merge_header_maps include_prelude maps0 headers_included path_dir headers' global_headers in
            merge_header_maps include_prelude (merge_maps l maps maps0) (path::headers_included) dir headers global_headers
          end
        end
    in

    let maps0 = ([], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []) in
    
    let (maps0, headers_included) =
      if include_prelude && dialect <> Some Rust then
        match file_type path with
          | Java -> begin
            if rtpath = "nort" then (maps0, []) else
            match try_assoc rtpath !headermap with
              | None -> 
                let ([], javaspecs) = parse_jarspec_file_core rtpath in
                let javaspecs =
                  if options.option_allow_assume then "_assume.javaspec"::javaspecs else javaspecs
                in
                let rtdir = Filename.dirname rtpath in
                let ds = Java_frontend_bridge.parse_java_files (List.map (fun x -> concat rtdir x) javaspecs) [] reportRange
                                                               reportShouldFail initial_verbosity enforce_annotations use_java_frontend in
                let (_, maps0) = check_file rtpath true false !bindir [] ds (*Todo @Nima: dbg_info*) None in
                headermap := (rtpath, ([], maps0))::!headermap;
                (maps0, [])
              | Some ([], maps0) ->
                (maps0, [])
          end
          | CLang ->
            begin match !prelude_maps with
              None ->
              let maps =
                let prelude_name, parse_header_file = 
                  match dialect with 
                  | Some Cxx -> 
                    let open Cxx_frontend in
                    "prelude_cxx.h", fun report_macro_call path report_range report_should_fail verbose include_paths define_macros enforce_annotations data_model -> 
                      let module Translator = Ast_translator.Make(
                        struct 
                          let enforce_annotations = enforce_annotations
                          let data_model_opt = data_model
                          let report_should_fail = report_should_fail
                          let report_range = report_range
                          let dialect_opt = Some Cxx
                          let report_macro_call = report_macro_call
                          let path = path
                          let verbose = verbose
                          let include_paths = include_paths
                          let define_macros = define_macros
                        end
                      )
                      in
                      begin try
                        Translator.parse_cxx_file ()
                      with
                      | Annotation_parser.CxxAnnParseException (l, msg)
                      | Error.CxxAstTranslException (l, msg) -> static_error l msg None
                      end
                  | Some Rust -> "prelude_rust.h", parse_header_file
                  | _ -> "prelude.h", parse_header_file 
                in
                let prelude_path = concat !bindir prelude_name in
                let (prelude_headers, prelude_decls) = parse_header_file reportMacroCall prelude_path reportRange reportShouldFail initial_verbosity [] [] enforce_annotations data_model in
                let prelude_header_names = List.map (fun (_, (_, _, h), _, _) -> h) prelude_headers in
                let prelude_headers = (dummy_loc, (AngleBracketInclude, prelude_name, prelude_path), prelude_header_names, prelude_decls)::prelude_headers in
                merge_header_maps false maps0 [] !bindir prelude_headers prelude_headers
              in
              prelude_maps := Some maps;
              maps
            | Some maps -> maps
            end
      else
        (maps0, [])
    in

    let (maps, _) = merge_header_maps include_prelude maps0 headers_included dir headers headers in
    maps

  (* Region: structdeclmap, enumdeclmap, inductivedeclmap, modulemap *)
  
  let unloadable =
    match language, dialect with
      | CLang, None ->
        let [PackageDecl (_, _, _, ds)] = ps in
        List.exists (function (UnloadableModuleDecl l) -> true | _ -> false) ds
      | _ -> false
  
  let typedefdeclmap =
    let rec iter pn ilist tddm ds cont =
      match ds with
        [] -> cont tddm
      | TypedefDecl (l, LValueRefTypeExpr _, _, _) :: _ ->
        static_error l "Typedefs for lvalue reference types are not supported." None
      | TypedefDecl (l, te, d, tparams)::ds ->
        (* C compiler detects duplicate typedefs *)
        iter pn ilist ((full_name pn d, (pn, ilist, l, tparams, te))::tddm) ds cont
      | _::ds ->
        iter pn ilist tddm ds cont
    in
    if language = Java then [] else
    let rec iter0 tddm ps =
      match ps with
        [] -> List.rev tddm
      | PackageDecl (lp, pn, ilist, ds)::ps ->
        iter pn ilist tddm ds @@ fun tddm ->
        iter0 tddm ps
    in
    iter0 [] ps
  
  let delayed_struct_def sn ldecl ldef =
    structures_defined := (sn, ldecl, ldef)::!structures_defined

  let structdeclmap, cxx_inst_pred_decl_map =
    let rec iter pn ilist sdm pred_map ds cont =
      match ds with
        [] -> cont sdm pred_map
      | Struct (l, sn, tparams, body_opt, attrs)::ds ->
        let sn = full_name pn sn in
        let body_opt, pred_map =
          match body_opt with
          | Some (bases, fields, inst_preds, polymorphic) ->
            if List.exists (fun (CxxBaseSpec (l, _, is_virtual)) -> is_virtual) bases then static_error l "Virtual inheritance is not supported." None;
            let pred_map = 
              match inst_preds with
              | [] -> pred_map
              | _ -> (sn, inst_preds) :: pred_map
            in
            Some (bases, fields, polymorphic), pred_map
          | _ -> None, pred_map
        in
        let earlier_decl =
          match try_assoc sn structmap0 with
            Some (ldecl, tparams0, body, _, _) -> Some (ldecl, tparams0, body <> None)
          | None ->
            match try_assoc sn sdm with
              Some (ldecl, tparams0, body, _) -> Some (ldecl, tparams0, body <> None)
            | None -> None
        in
        begin
          match earlier_decl with
            Some (ldecl, tparams0, has_body) ->
            if has_body then static_error l "Duplicate struct name." None;
            if body_opt = None then static_error l "Duplicate struct declaration." None;
            if List.length tparams0 <> List.length tparams then
              static_error l ("The number of type parameters does not match the earlier declaration of this struct at " ^ string_of_loc ldecl) None;
            delayed_struct_def sn ldecl l
          | None -> ()
        end;
        iter pn ilist ((sn, (l, tparams, body_opt, attrs))::sdm) pred_map ds cont
      | _::ds -> iter pn ilist sdm pred_map ds cont
    in
    let rec iter0 sdm pred_map ps =
      match ps with
        [] -> sdm, List.rev pred_map
      | PackageDecl (lp, pn, ilist, ds)::ps ->
        iter pn ilist sdm pred_map ds @@ fun sdm pred_map ->
        iter0 sdm pred_map ps
    in
    iter0 [] [] ps
  
  let delayed_union_def un ldecl ldef =
    unions_defined := (un, ldecl, ldef)::!unions_defined

  let uniondeclmap =
    let rec iter pn ilist udm ds cont =
      match ds with
        [] -> cont udm
      | Union (l, un, fds_opt)::ds ->
        let un = full_name pn un in
        begin match try_assoc un unionmap0 with
          Some (_, Some _, _) -> static_error l "Duplicate union name." None
        | Some (ldecl, None, _) -> if fds_opt = None then static_error l "Duplicate union declaration." None else delayed_union_def un ldecl l
        | None -> ()
        end;
        begin match try_assoc un udm with
          Some (_, Some _) -> static_error l "Duplicate union name." None
        | Some (ldecl, None) -> if fds_opt = None then static_error l "Duplicate union declaration." None else delayed_union_def un ldecl l
        | None -> ()
        end;
        iter pn ilist ((un, (l, fds_opt))::udm) ds cont
      | _::ds -> iter pn ilist udm ds cont
    in
    let rec iter0 udm ps =
      match ps with
        [] -> udm
      | PackageDecl (lp, pn, ilist, ds)::ps ->
        iter pn ilist udm ds @@ fun udm ->
        iter0 udm ps
    in
    iter0 [] ps

  let enumdeclmap = 
    let rec iter pn ilist edm ds cont = 
      match ds with
        [] -> cont edm
      | EnumDecl(l, en, elems) :: ds ->
        let en = full_name pn en in
        begin 
          match try_assoc en edm with
        | Some((l', elems')) -> static_error l "Duplicate enum name." None
        | None -> iter pn ilist ((en, (l, elems)) :: edm) ds cont
        end
      | _ :: ds -> iter pn ilist edm ds cont
    in
    let rec iter0 edm ps =
      match ps with
        [] -> List.rev edm
      | PackageDecl (lp, pn, ilist, ds)::ps ->
        iter pn ilist edm ds @@ fun edm ->
        iter0 edm ps
    in
    iter0 [] ps
  
  let enummap1 =
    let rec process_decls enummap1 ds =
      match ds with
        [] -> enummap1
      | (_, (l, elems))::ds ->
        let rec process_elems enummap1 nextValue elems =
          match elems with
            [] -> process_decls enummap1 ds
          | (c, expr_opt)::elems ->
            let value =
              match expr_opt with
                None -> nextValue
              | Some e ->
                let rec eval e =
                  match e with
                    IntLit (_, n, _, _, _) -> n
                  | Var (l, x) ->
                    begin match try_assoc2 x enummap1 enummap0 with
                      None -> static_error l "No such enumeration constant" None
                    | Some n -> n
                    end
                  | Operation (l, op, [e1; e2]) ->
                    let n1 = eval e1 in
                    let n2 = eval e2 in
                    begin match op with
                      Add -> add_big_int n1 n2
                    | Sub -> sub_big_int n1 n2
                    | Mul -> mult_big_int n1 n2
                    | Div -> div_big_int n1 n2
                    | _ -> static_error l "This operation is not supported in this position." None
                    end
                  | e -> static_error (expr_loc e) "This expression form is not supported in this position." None
                in
                eval e
            in
            process_elems ((c, value)::enummap1) (succ_big_int value) elems
        in
        process_elems enummap1 zero_big_int elems
    in
    process_decls [] enumdeclmap
  
  let functypenames = 
    ps |> flatmap begin function
      PackageDecl (_, pn, _, ds) ->
      ds |> flatmap begin function
        FuncTypeDecl (l, gh, _, g, tps, ftps, _, _) -> [full_name pn g, (l, gh, tps, ftps)]
      | _ -> []
      end
    end
  
  let inductivedeclmap=
    let rec iter pn idm ds =
      match ds with
        [] -> idm
      | (Inductive (l, i, tparams, ctors))::ds -> let n=full_name pn i in
        if n = "bool" || n = "boolean" || n = "int" || List.mem_assoc n idm || List.mem_assoc n inductivemap0 then
          static_error l "Duplicate datatype name." None
        else
          let subtype = InductiveSubtype.alloc () in
          iter pn ((n, (l, tparams, ctors, subtype))::idm) ds
      | _::ds -> iter pn idm ds
    in
    let rec iter' idm ps=
      match ps with
      PackageDecl(l,pn,ilist,ds)::rest -> iter' (iter pn idm ds) rest
      | [] -> List.rev idm
    in
    iter' [] ps

  let abstract_types_map1 =
    let rec iter pn atm ds =
      match ds with
        [] -> atm
      | (AbstractTypeDecl (l, t))::ds ->
        let n = full_name pn t in
        if List.mem_assoc n atm || List.mem_assoc n abstract_types_map0 then
          static_error l "Duplicate abstract type name." None
        else
          iter pn ((n, l)::atm) ds
      | _::ds -> iter pn atm ds
    in
    let rec iter' atm ps =
      match ps with
        PackageDecl (l, pn, ilist, ds)::rest -> iter' (iter pn atm ds) rest
      | [] -> List.rev atm
    in
    iter' [] ps
   
  (* Region: Java name resolution functions *)
  
  let rec try_assoc' ghost (pn,imports) name map=
    match imports with
      _ when List.mem_assoc (full_name pn name) map -> Some (List.assoc (full_name pn name) map)
    | _ when List.mem_assoc name map-> Some (List.assoc name map)
    | Import(l,_,p,None)::rest when List.mem_assoc (full_name p name) map->  Some (List.assoc (full_name p name) map)
    | Import(l,ghost',p,Some name')::rest when ghost=ghost' && name=name' && List.mem_assoc (full_name p name) map-> Some (List.assoc (full_name p name) map) 
    | _::rest -> try_assoc' ghost (pn,rest) name map
    | [] -> None
  
  let rec try_assoc_pair' ghost (pn,imports) (n,n') map=
    match imports with
      _ when List.mem_assoc (full_name pn n,List.map (fun n-> full_name pn n) n') map -> Some (List.assoc (full_name pn n,List.map (fun n-> full_name pn n) n') map)
    | _ when List.mem_assoc (n,n') map-> Some (List.assoc (n,n') map)
    | Import(l,_,p,None)::rest when List.mem_assoc (full_name p n,List.map (fun n-> full_name p n) n') map->  Some (List.assoc (full_name p n,List.map (fun n-> full_name p n) n') map)
    | Import(l,ghost',p,Some n2)::rest when ghost=ghost' && n=n2 && List.mem_assoc (full_name p n,List.map (fun n-> full_name p n) n') map-> Some (List.assoc (full_name p n,List.map (fun n-> full_name p n) n') map) 
    | _::rest -> try_assoc_pair' ghost (pn,rest) (n,n') map
    | [] -> None

  let try_assoc2' ghost (pn,imports)x xys1 xys2 =
    match try_assoc' ghost (pn,imports) x xys1 with
      None -> try_assoc' ghost (pn,imports) x xys2
    | result -> result
  
  let rec search ghost name (pn,imports) map=
    match imports with
      _ when List.mem_assoc (full_name pn name) map -> true
    | _ when List.mem_assoc name map -> true
    | Import(l,_,p,None)::_ when List.mem_assoc (full_name p name) map-> true
    | Import(l,ghost',p,Some name')::rest when ghost=ghost' && name=name' && List.mem_assoc (full_name p name) map-> true
    | _::rest -> search ghost name (pn,rest) map
    | []->  false
  
  let rec search' ghost name (pn,imports) map=
    match imports with
      _ when List.mem_assoc name map-> Some name
    | _ when List.mem_assoc (full_name pn name) map -> Some (full_name pn name)
    | Import(l,_,p,None)::_ when List.mem_assoc (full_name p name) map-> Some (full_name p name)
    | Import(l,ghost',p,Some name')::rest when ghost=ghost' && name=name' && List.mem_assoc (full_name p name) map ->Some (full_name p name)
    | _::rest -> search' ghost name (pn,rest) map
    | [] -> None
  
  let resolve ghost (pn, imports) l name map =
    match try_assoc0 name map with
      Some xy as result -> result
    | None ->
      if dialect <> Some Rust && String.contains name item_path_separator.[0] then
        None
      else
        match if pn = "" then None else try_assoc0 (pn ^ item_path_separator ^ name) map with
          Some xy as result -> result
        | None ->
          let matches =
            flatmap
              begin function
                Import (l, _, p, None) ->
                begin match try_assoc0 (p ^ item_path_separator ^ name) map with None -> [] | Some xy -> [xy] end
              | Import (l, ghost', p, Some name') when ghost = ghost' && String.starts_with ~prefix:name' name && (name = name' || dialect = Some Rust && String.starts_with ~prefix:(name' ^ item_path_separator) name) ->
                begin match try_assoc0 (p ^ item_path_separator ^ name) map with None -> [] | Some xy -> [xy] end
              | _ -> []
              end
              imports
          in
          match matches with
            [] ->
            if String.starts_with ~prefix:"core::" name then
              try_assoc0 ("std::" ^ String.sub name 6 (String.length name - 6)) map
            else
              None
          | [xy] -> Some xy
          | _ ->
            let fqns = List.map (fun (x, y) -> "'" ^ x ^ "'") matches in
            static_error l ("Ambiguous imports for name '" ^ name ^ "': " ^ String.concat ", " fqns ^ ".") None
  
  let resolve2 (pn, imports) l name map =
    match resolve Real (pn, imports) l name map with 
    | Some f -> Some f 
    | None -> resolve Ghost (pn, imports) l name map

  let resolve2' ghost (pn, imports) l name map0 map1 =
    match resolve ghost (pn, imports) l name map0 with 
    | Some f -> Some f 
    | None -> resolve ghost (pn, imports) l name map1 

  let search2' ghost x (pn,imports) xys1 xys2 =
    match search' ghost x (pn,imports) xys1 with
      None -> search' ghost x (pn,imports) xys2
    | result -> result
  
  let rec erase_type t =
    match t with 
      RealTypeParam t -> javaLangObject
    | ObjType (s, ts) -> ObjType (s, List.map erase_type ts)
    | ArrayType t -> ArrayType (erase_type t)
    | InductiveType (name, ts) -> InductiveType (name, List.map erase_type ts)
    | t -> t

  let rec replace_type loc targenv t = 
    match t with
      RealTypeParam t -> 
        begin try List.assoc t targenv with 
        | Not_found -> static_error loc (Printf.sprintf "Type argument for type param %s not provided." t) None end
    | ArrayType t -> ArrayType (replace_type loc targenv t)
    | ObjType (n,ts) -> ObjType (n, List.map (replace_type loc targenv) ts)
    | t -> t

  let rec replace_inferred_type loc targenv t = 
    match t with
    | InferredRealType t -> begin try List.assoc t targenv with 
        | Not_found -> static_error loc (Printf.sprintf "Type argument for type param %s was not inferred." t) None end
    | ArrayType t -> ArrayType (replace_inferred_type loc targenv t)
    | ObjType (n,ts) -> ObjType (n, List.map (replace_inferred_type loc targenv) ts)
    | t -> t

  let is_primitive_type t = match t with
    Void | Bool | Int _ | RustChar | Float | Double -> true
  | _ -> false

  (* Region: interfdeclmap, classmap1 *)
  
  let (interfmap1,classmap1) =
   let rec iter (ifdm, classlist) ds todo =
     match ds with 
      | [] -> (ifdm, classlist, todo)
      | (pn, ilist, Interface (l, i, interfs, fields, meths, tparams, pred_specs))::rest ->
        let i= full_name pn i in 
        if List.mem_assoc i ifdm then
          static_error l ("There exists already an interface with this name: "^i) None
        else
        if List.mem_assoc i classlist then
          static_error l ("There exists already a class with this name: "^i) None
        else
          begin
            try
              let interfs =
                let rec check_interfs ls=
                  match ls with
                    [] -> []
                  | (n, targs)::ls -> match search2' Real n (pn, ilist) ifdm interfmap0 with 
                              Some i -> (i, targs)::check_interfs ls
                            | None -> raise Not_found
                in
                check_interfs interfs
              in
              iter (((i, (l, fields, meths, pred_specs, interfs, pn, ilist, tparams))::ifdm), classlist) rest todo
            with Not_found ->
              iter (ifdm, classlist) rest ((List.hd ds)::todo)
          end
      | (pn, ilist, Class (l, abstract, fin, i, meths, fields, constr, (super, supertargs), tparams, interfs, preds))::rest ->
        let i= full_name pn i in
        if List.mem_assoc i ifdm then
          static_error l ("There exists already an interface with this name: "^i) None
        else
        if List.mem_assoc i classlist then
          static_error l ("There exists already a class with this name: "^i) None
        else
          begin
            try
              let interfs =
                let rec check_interfs ls=
                    match ls with
                      [] -> []
                    | (n, targs)::ls -> match search2' Real n (pn, ilist) ifdm interfmap0 with 
                                Some i -> (i, targs)::check_interfs ls
                              | None -> raise Not_found
                in
                check_interfs interfs
              in
              let super =
                if i = "java.lang.Object" then "" else
                if super = "java.lang.Object" then super else
                match search2' Real super (pn,ilist) classlist classmap0 with
                  None-> raise Not_found
                | Some super -> super
              in
              iter (ifdm, (i, (l, abstract, fin, meths, fields, constr, (super, supertargs), tparams, interfs, preds, pn, ilist))::classlist) rest todo
            with Not_found ->
              iter (ifdm, classlist) rest ((List.hd ds)::todo)
          end
      | (pn, ilist, _)::rest -> iter (ifdm, classlist) rest todo
    in
    let rec iter' (ifdm, classlist) ds =
      let (ifdm', classlist', ds_rest)  = iter (ifdm, classlist) ds [] in
      if (List.length ds_rest > 0) then
        begin
          if (List.length ds_rest = List.length ds) then
            let rec check_interfs kind i ls (pn,ilist) =
              match ls with
                [] -> kind ^ " " ^ i ^ " is part of an inheritance cycle"
              | (i, targs)::ls -> match search2' Real i (pn,ilist) ifdm interfmap0 with 
                          Some i -> check_interfs kind i ls (pn,ilist)
                        | None -> "Interface " ^ i ^ " not found"
            in
            let (l, message) =
              match ds_rest with
              | (pn, ilist, (Interface (l, i, interfs, fields, meths, pred_specs, tparams)))::_ ->
                  (l, check_interfs "Interface" i interfs (pn,ilist))
              | (pn, ilist, (Class (l, abstract, fin, i, meths, fields, constr, (super, super_targs), tparams, interfs, preds)))::_ ->
                  match search2' Real super (pn, ilist) classlist classmap0 with
                    None-> 
                      if i = "java.lang.Object" || super = "java.lang.Object" then 
                        (l, check_interfs "Class" i interfs (pn,ilist))
                      else
                        (l, "Class " ^ super ^ " not found")
                  | Some super -> (l, check_interfs "Class" i interfs (pn, ilist));
            in
            static_error l message None
          else
            iter' (ifdm', classlist') ds_rest
        end
      else
        (List.rev ifdm', List.rev classlist')
    in
    let rec get_declarations ps =
      match ps with
      | PackageDecl(l,pn,ilist,ds)::rest -> (List.map (fun d -> (pn, ilist, d)) ds) @ (get_declarations rest)
      | [] -> []
    in
    iter' ([],[]) (get_declarations ps)
  
  let inductive_arities =
    List.map (fun (i, (l, tparams, _, subtype)) -> (i, (l, List.length tparams, subtype))) inductivedeclmap
    @ List.map (fun (i, (l, tparams, _, _, _, _, _, subtype, _)) -> (i, (l, List.length tparams, subtype))) inductivemap0
  
  let abstract_types_map = abstract_types_map1 @ abstract_types_map0
  
  let class_arities =
    List.map (fun (cn, (l, _, _, _, _, _, _, tparams, _, _, _, _)) -> (cn, (l, List.length tparams))) classmap1
    @ List.map (fun (cn, {cl=l; ctpenv=tparams}) -> (cn, (l, List.length tparams))) classmap0
    @ List.map (fun (cn, (l, _, _, _, _, _, _, tparams)) -> (cn, (l, List.length tparams))) interfmap1
    @ List.map (fun (cn, InterfaceInfo (l, _, _, _, _, tparams)) -> (cn, (l, List.length tparams))) interfmap0

  let rec instantiate_type tpenv t =
    if tpenv = [] then t else
    match t with
      RealTypeParam x | GhostTypeParam x | GhostTypeParamWithEqs (x, _) -> (try List.assoc x tpenv  with _ -> failwith 
        (Printf.sprintf "not found! looking for %s in env %s" x (String.concat ", " (List.map (fun (a,b) -> a ^ "->" ^ (string_of_type b)) tpenv))))
    | PtrType t -> PtrType (instantiate_type tpenv t)
    | RustRefType (lft, kind, t) -> RustRefType (instantiate_type tpenv lft, kind, instantiate_type tpenv t)
    | InductiveType (i, targs) -> InductiveType (i, List.map (instantiate_type tpenv) targs)
    | PredType ([], pts, inputParamCount, inductiveness) -> PredType ([], List.map (instantiate_type tpenv) pts, inputParamCount, inductiveness)
    | PureFuncType (t1, t2) -> PureFuncType (instantiate_type tpenv t1, instantiate_type tpenv t2)
    | InferredType (_, t) ->
      begin match !t with
      | EqConstraint t -> instantiate_type tpenv t
      | _ -> assert false
      end
    | ArrayType t -> ArrayType (instantiate_type tpenv t)
    | StaticArrayType (t, n) -> StaticArrayType (instantiate_type tpenv t, instantiate_type tpenv n)
    | StructType (sn, targs) -> StructType (sn, List.map (instantiate_type tpenv) targs)
    | InlineFuncType rt -> InlineFuncType (instantiate_type tpenv rt)
    | ProjectionType (t, traitName, traitArgs, assocTypeName) ->
      let t = instantiate_type tpenv t in
      let traitArgs = List.map (instantiate_type tpenv) traitArgs in
      begin match t with
        GhostTypeParamWithEqs (x, eqs) ->
        begin match try_assoc (traitName, traitArgs, assocTypeName) eqs with
          Some t -> t
        | None -> ProjectionType (t, traitName, traitArgs, assocTypeName)
        end
      | _ -> ProjectionType (t, traitName, traitArgs, assocTypeName)
      end
    | _ -> t
  
  let tparam_eqs_table = ref []
  let tparam_eqs_tables_stack = ref []

  let push_tparam_eqs_table () =
    tparam_eqs_tables_stack := !tparam_eqs_table :: !tparam_eqs_tables_stack

  let pop_tparam_eqs_table () =
    let t::ts = !tparam_eqs_tables_stack in
    tparam_eqs_table := t;
    tparam_eqs_tables_stack := ts
  
  let register_tparam_eq x eq =
    tparam_eqs_table := (x, eq)::!tparam_eqs_table
  
  let lookup_tparam_eqs x =
    flatmap (fun (y, eq) -> if y = x then [eq] else []) !tparam_eqs_table
  
  (* Region: check_pure_type: checks validity of type expressions *)
  let check_pure_type_core typedefmap1 (pn,ilist) tpenv te envType =
    let rec create_objects n = if n > 0 then javaLangObject::(create_objects (n-1)) else [] in
    let rec check te =
    match te with
      ManifestTypeExpr (l, t) -> t
    | ArrayTypeExpr (l, t) -> 
        let tp = check t in
        ArrayType(tp)
    | StaticArrayTypeExpr (l, t, s) ->
        let tp = check t in
        let s = check s in
        StaticArrayType(tp, s)
    | LiteralConstTypeExpr (l, n) ->
      if n < 0 then static_error l "Const generic argument must be nonnegative" None;
      begin match ptr_width with
        LitWidth k -> if lt_big_int (max_unsigned_big_int k) (big_int_of_int n) then static_error l "Const generic argument must be within limits of type 'usize'" None
      | _ -> if 65535 < n then static_error l "Const generic argument must be within limits of type 'usize' on all supported targets, i.e. it must be at most 65535" None
      end;
      LiteralConstType n
    | IdentTypeExpr (l, None, id) ->
      begin
      if List.mem id tpenv then begin match envType with
      | Real when language = Java -> RealTypeParam id
      | _ -> let eqs = lookup_tparam_eqs id in if eqs = [] then GhostTypeParam id else GhostTypeParamWithEqs (id, eqs)
      end
      else
      match resolve2' Ghost (pn,ilist) l id typedefmap0 typedefmap1 with
        Some (id, (ld, tparams, t)) ->
        reportUseSite DeclKind_Typedef ld l;
        if tparams <> [] then static_error l "Missing type arguments" None;
        t
      | None ->
      match resolve Ghost (pn,ilist) l id inductive_arities with
        Some (s, (ld, n, _)) ->
        if n > 0 then static_error l "Missing type arguments." None;
        reportUseSite DeclKind_InductiveType ld l;
        InductiveType (s, [])
      | None ->
      match (search2' Real id (pn, ilist) classmap1 classmap0) with
        Some s ->
        let (ld, n) = List.assoc s class_arities in
        reportUseSite DeclKind_Class ld l;
        ObjType (s, create_objects n)
      | None ->  match (search2' Real id (pn, ilist) interfmap1 interfmap0) with
        Some s -> 
        let (ld, n) = List.assoc s class_arities in
        reportUseSite DeclKind_Interface ld l;
        ObjType(s, create_objects n)
      | None ->
      match resolve Real (pn,ilist) l id functypenames with
        Some (id, (ld, _, _, _)) ->
        reportUseSite DeclKind_FuncType ld l;
        FuncType id
      | None ->
      match resolve Real (pn,ilist) l id functypemap0 with
        Some (id, (ld, _, _, _, _, _, _, _, _, _, _)) ->
        reportUseSite DeclKind_FuncType ld l;
        FuncType id
      | None ->
      match resolve Ghost (pn,ilist) l id abstract_types_map with
        Some (n, ld) ->
        reportUseSite DeclKind_AbstractType ld l;
        AbstractType n
      | None ->
      (*** TODO @Nima: Review two following dialect checks regarding Rust after Niels fixed them *)
      (* So we can use class/struct/union names as types in ghost code *)
      match resolve Real (pn,ilist) l id structmap0 with
        Some (id, (ld, tparams, _, _, _)) when dialect = Some Cxx ->
        reportUseSite DeclKind_Struct ld l;
        if tparams <> [] then static_error l "Type arguments required" None;
        StructType (id, [])
      | _ ->
      match resolve Real (pn,ilist) l id structdeclmap with
        Some (id, (ld, tparams, _, _)) when dialect = Some Cxx -> 
        reportUseSite DeclKind_Struct ld l;
        if tparams <> [] then static_error l "Type arguments required" None;
        StructType (id, [])
      | _ ->
      match resolve Real (pn,ilist) l id unionmap0 with
        Some (id, (ld, _, _)) when dialect = Some Cxx ->
        reportUseSite DeclKind_Union ld l;
        UnionType id
      | _ ->
      match resolve Real (pn,ilist) l id uniondeclmap with
        Some (id, (ld, _)) when dialect = Some Cxx ->
        reportUseSite DeclKind_Union ld l;
        UnionType id
      | _ ->
      static_error l ("No such type parameter, inductive datatype, class, interface, or function type: "^id) None
      end
    | IdentTypeExpr (l, Some(pac), id) ->
      let full_name = pac ^ item_path_separator ^ id in
      begin
      match resolve Real (pac, ilist) l id class_arities with
        Some (_, (ld, n)) ->
        reportUseSite DeclKind_Class ld l;
        ObjType(full_name, create_objects n)
      | None -> static_error l ("No such type parameter, inductive datatype, class, interface, or function type: " ^ full_name) None
      end
    | ConstructedTypeExpr (l, id, targs) ->
      begin
      match resolve Ghost (pn,ilist) l id inductive_arities with
        Some (id, (ld, n, _)) ->
        if n <> List.length targs then static_error l "Incorrect number of type arguments." None;
        reportUseSite DeclKind_InductiveType ld l;
        InductiveType (id, List.map check targs)
      | None -> match resolve Real (pn,ilist) l id class_arities with
        Some (id, (ld, n)) ->
        reportUseSite DeclKind_Class ld l;
        if n <> List.length targs then 
          static_error l "Incorrect number of type arguments." None
        else  
          ObjType (id, List.map check targs)
      | None ->
      match resolve2' Ghost (pn,ilist) l id typedefmap0 typedefmap1 with
        Some (id, (ld, tparams, t)) ->
        reportUseSite DeclKind_Typedef ld l;
        let tpenv =
          match zip tparams (List.map check targs) with
            Some tpenv -> tpenv
          | None -> static_error l "Incorrect number of type arguments" None
        in
        instantiate_type tpenv t
      | None -> static_error l ("No such inductive type, class, or interface.") None
      end
    | StructTypeExpr (l, sn, Some _, _, _) ->
      static_error l "A struct type with a body is not supported in this position." None
    | StructTypeExpr (l, Some sn, None, _, targs) ->
      begin match resolve Real (pn,ilist) l sn structmap0 with
        Some (sn, (ld, tparams, _, _, _)) ->
        reportUseSite DeclKind_Struct ld l;
        if List.length targs <> List.length tparams then
          static_error l "Incorrect number of type arguments" None;
        StructType (sn, List.map check targs)
      | None ->
      match resolve Real (pn,ilist) l sn structdeclmap with
        Some (sn, (ld, tparams, _, _)) ->
        reportUseSite DeclKind_Struct ld l;
        if List.length targs <> List.length tparams then
          static_error l "Incorrect number of type arguments" None;
        StructType (sn, List.map check targs)
      | None ->
      if option_allow_undeclared_struct_types && targs = [] then
        StructType (sn, [])
      else
        static_error l ("No such struct: \"" ^ sn ^ "\".") None
      end
    | UnionTypeExpr (l, un, Some _) ->
      static_error l "A union type with a body is not supported in this position." None
    | UnionTypeExpr (l, Some un, None) ->
      begin match try_assoc un unionmap0 with
        Some (ld, _, _) ->
        reportUseSite DeclKind_Union ld l;
        UnionType un
      | None ->
      match try_assoc un uniondeclmap with
        Some (ld, _) ->
        reportUseSite DeclKind_Union ld l;
        UnionType un
      | None ->
      if option_allow_undeclared_struct_types then
        UnionType un
      else
        static_error l ("No such union: \"" ^ un ^ "\".") None
      end
    | EnumTypeExpr (l, en, Some _) ->
      static_error l "An enum type with a body is not supported in this position." None
    | EnumTypeExpr (l, Some en, None) ->
      intType
    | PtrTypeExpr (l, FuncTypeExpr (_, _, _)) -> PtrType Void
    | FuncTypeExpr (l, rt, []) when dialect = Some Rust -> InlineFuncType (check rt)
    | FuncTypeExpr (_, _, _) -> PtrType Void
    | PtrTypeExpr (l, te) -> PtrType (check te)
    | RustRefTypeExpr (l, lft, kind, te) -> RustRefType (check lft, kind, check te)
    | PredTypeExpr (l, tes, inputParamCount) ->
      PredType ([], List.map check tes, inputParamCount, Inductiveness_Inductive)
    | PureFuncTypeExpr (l, ps, requires_opt) ->
      if requires_opt <> None then static_error l "Fixpoint function type requires clauses are not supported here." None;
      let ts = List.map (fun (tp, x_opt) -> check tp) ps in
      let rec iter ts =
        match ts with
          [t1; t2] -> PureFuncType (t1, t2)
        | t1::ts -> PureFuncType (t1, iter ts)
        | _ -> static_error l "A fixpoint function type requires at least two types: a domain type and a range type" None
      in
      iter ts
    | LValueRefTypeExpr (l, te) -> RefType (check te)
    | ConstTypeExpr (l, te) -> check te
    | ProjectionTypeExpr (l, te, traitName, traitArgs, assocTypeName) ->
      let t = check te in
      let traitArgs = List.map check traitArgs in
      ProjectionType (t, traitName, traitArgs, assocTypeName)
    in
    check te
  
  let typedefmap1 =
    let rec iter tdm1 tdds =
      match tdds with
        [] -> tdm1
      | (d, (pn, ilist, l, tparams, te))::tdds ->
        let t = check_pure_type_core tdm1 (pn,ilist) tparams te Real in
        iter ((d,(l, tparams, t))::tdm1) tdds
    in
    iter [] typedefdeclmap
  
  let typedefmap = typedefmap1 @ typedefmap0
  
  (* envType indicates if we are type checking in a ghost or real environment *)
  let check_pure_type (pn,ilist) tpenv envType te = check_pure_type_core typedefmap (pn,ilist) tpenv te envType
  
  let typepreddeclmap1 =
    let rec iter (tpdm1: type_pred_decl_info map) ds =
      match ds with
        [] -> tpdm1
      | TypePredDecl (l, te, selfTypeName, predName)::ds ->
        if List.mem_assoc predName tpdm1 || List.mem_assoc predName typepreddeclmap0 then
          static_error l "Duplicate type predicate declaration" None;
        let tp = check_pure_type ("",[]) [selfTypeName] Ghost te in
        let symb = mk_func_symbol predName [provertype_of_type voidPtrType] (provertype_of_type tp) Uninterp in
        iter ((predName, (l, selfTypeName, tp, fst symb))::tpdm1) ds
      | _::ds ->
        iter tpdm1 ds
    in
    let rec iter' tpdm1 ps =
      match ps with
        [] -> tpdm1
      | PackageDecl (l, pn, ilist, ds)::ps ->
        iter' (iter tpdm1 ds) ps
    in
    iter' [] ps
  
  let typepreddeclmap = typepreddeclmap1 @ typepreddeclmap0

  let split_item_name n =
    match String.rindex_opt n item_path_separator.[0] with
      None -> ("", n)
    | Some i ->
      let pac = String.sub n 0 (i + 1 - String.length item_path_separator) in
      let item = String.sub n (i + 1) (String.length n - i - 1) in
      (pac, item)
  
  let ps =
    let extra_ps =
      ps |> flatmap @@ function PackageDecl (lp, pn, ilist, ds) ->
        ds |> flatmap @@ function
          TypePredDef (l, tparams, te, tpn, Right (ps, inputParamCount, body)) ->
          let tp = check_pure_type (pn,ilist) tparams Ghost te in
          begin match tp with
            StructType (sn, targs) ->
            if targs <> List.map (fun x -> GhostTypeParam x) tparams then
              static_error l "The struct type argument list must match the type parameter list exactly" None;
            begin match List.assoc_opt tpn typepreddeclmap with
              None -> static_error l "No such type predicate" None
            | Some (_, selfTypeName, PredType ([], pts, inputParamCount', inductiveness), _) ->
              let spn, simple_sn = split_item_name sn in
              let sn = if spn = pn then simple_sn else begin assert (pn = ""); sn end in
              let g = Printf.sprintf "%s_%s" sn tpn in
              let tpenv = [selfTypeName, tp] in
              let ps =
                match zip pts ps with
                  None -> static_error l "Incorrect number of parameters" None
                | Some ps -> List.map (fun (tp, x) -> (ManifestTypeExpr (l, instantiate_type tpenv tp), x)) ps
              in
              let extra_ds = 
                [TypePredDef (l, tparams, te, tpn, Left (l, g))] @
                if tparams = [] then
                  [PredFamilyDecl (l, g, tparams, 0, List.map (fun (t, p) -> t) ps, inputParamCount, inductiveness);
                  PredFamilyInstanceDecl (l, g, tparams, [], ps, body)]
                else
                  [PredCtorDecl (l, g, tparams, [], ps, inputParamCount, body)]
              in
              [PackageDecl (l, pn, ilist, extra_ds)]
            | _ -> static_error l "Inline type predicate definitions are supported only when the type of the type predicate is a non-generic predicate type" None
            end
          | _ -> static_error l "Inline type predicate definitions are supported only for struct types" None
          end
        | _ -> []
    in
    extra_ps @ ps

  let classmap1 =
    List.map
      begin fun (sn, (l, abstract, fin, meths, fds, constr, (super, supertargs), tparams, interfs, preds, pn, ilist)) ->
        let supertargs = List.map (check_pure_type (pn,ilist) tparams Real) supertargs in
        let interfs = List.map (fun (i,tes) -> (i,List.map (check_pure_type (pn,ilist) tparams Real) tes)) interfs in
        let rec iter fmap fds =
          match fds with
            [] -> (sn, (l, abstract, fin, meths, List.rev fmap, constr, (super, supertargs), tparams, interfs, preds, pn, ilist))
          | Field (fl, fgh, t, f, fbinding, fvis, ffinal, finit)::fds ->
            if List.mem_assoc f fmap then static_error fl "Duplicate field name." None;
            iter ((f, {fl; fgh; ft=check_pure_type (pn,ilist) tparams Real t; fvis; fbinding; ffinal; finit; fvalue=ref None})::fmap) fds
        in
        iter [] fds
      end
      classmap1
      
  (* Type check type arguments of super types *)
  let interfmap1 = 
    List.map
       begin fun (tn, (li, fields, methods, preds, interfs, pn, ilist, tparams)) ->
        let interfs = List.map (fun (i,tes) -> (i,List.map (check_pure_type (pn,ilist) tparams Real) tes)) interfs in
        (tn, (li, fields, methods, preds, interfs, pn, ilist, tparams))
      end
      interfmap1

  let instantiate_types tpenv ts =
    if tpenv = [] then ts else List.map (instantiate_type tpenv) ts
  
  let terms_of xys =
    xys |> List.map begin fun (x, _) ->
      let t = ctxt#mk_app (mk_symbol x [] ctxt#type_int Uninterp) [] in
      let serialNumber = !class_counter in
      class_counter := !class_counter + 1;
      ctxt#assert_term (ctxt#mk_eq (ctxt#mk_app class_serial_number [t]) (ctxt#mk_intlit serialNumber));
      if is_import_spec then
        ctxt#assert_term (ctxt#mk_lt (ctxt#mk_app class_rank [t]) (ctxt#mk_reallit 0))
      else
        ctxt#assert_term (ctxt#mk_eq (ctxt#mk_app class_rank [t]) (ctxt#mk_reallit serialNumber));
      (x, t)
    end
  let classterms1 =  terms_of classmap1
  let interfaceterms1 = terms_of interfmap1

  let classterms = classterms1 @ classterms0
  let interfaceterms = interfaceterms1 @ interfaceterms0

  (* Region: unionmap1 *)

  let unionmap1 =
    uniondeclmap |> List.map begin fun (un, (l, fds_opt)) ->
      let typeid_symb = get_unique_var_symb ("union_" ^ un ^ "_typeid") (PtrType Void) in
      match fds_opt with
        None -> (un, (l, None, typeid_symb))
      | Some fds ->
        let s = mk_sizeof typeid_symb in
        let fmap =
          let rec iter fmap fds =
            match fds with
              [] -> List.rev fmap
            | Field (lf, gh, t, f, Instance, Public, final, init)::fds ->
              if List.mem_assoc f fmap then static_error lf "Duplicate field name." None;
              if gh = Ghost then static_error lf "Unions cannot have ghost fields." None;
              let t = check_pure_type ("", []) [] gh t in
              iter ((f, (lf, t))::fmap) fds
          in
          iter [] fds
        in
        (un, (l, Some (fmap, s), typeid_symb))
    end

  let unionmap = unionmap1 @ unionmap0

  (* Region: structmap1 *)

  let padding_pred_name sn =
    let package, name = split_item_name sn in
    if package = "" then
      "struct_" ^ name ^ "_padding"
    else
      package ^ item_path_separator ^ "struct_" ^ name ^ "_padding"
  
  let structmap1: struct_info map =
    let rec iter (smap: struct_info map) (smapwith0: struct_info map) remaining =
      match remaining with
      | [] -> smap
      | (sn, (l, tparams, body_opt, attrs)) :: remaining ->
        let type_info_func = mk_symbol (sn ^ "_type_info") (List.map (fun x -> type_info_type_node) tparams) type_info_type_node Uninterp in
        let packed = List.mem Packed attrs in
        let rec iter1 fmap fds has_ghost_fields bases is_polymorphic =
          match fds with
            [] ->
            let padding_predsym_opt =
              if packed || has_ghost_fields then
                None
              else
                Some (get_unique_var_symb (padding_pred_name sn) (PredType ([], [PtrType (StructType (sn, []))], Some 1, Inductiveness_Inductive)))
            in
            let fmap = List.rev fmap in
            let base_map = bases |> List.map @@ fun (CxxBaseSpec (l, base, is_virtual)) -> 
              let base_offset = get_unique_var_symb (sn ^ "_" ^ base ^ "_offset") intType in
                ctxt#assert_term (ctxt#mk_le int_zero_term base_offset);
              base, (l, is_virtual, base_offset) 
            in
            (sn, (l, tparams, Some (base_map, fmap, is_polymorphic), padding_predsym_opt, type_info_func))
          | Field (lf, gh, t, f, Instance, Public, final, init)::fds ->
            if List.mem_assoc f fmap then static_error lf "Duplicate field name." None;
            let t = check_pure_type ("", []) tparams gh t in
            let offset = if gh = Ghost then
              None
            else
              Some (mk_symbol (sn ^ "_" ^ f ^ "_offset") (List.map (fun x -> type_info_type_node) tparams) ctxt#type_int Uninterp)
            in
            let entry = (f, (lf, gh, t, offset, init)) in
            iter1 (entry::fmap) fds (has_ghost_fields || gh = Ghost) bases is_polymorphic
        in
        let new_item = begin
          match body_opt with
            Some (bases, fds, is_polymorphic) -> iter1 [] fds false bases is_polymorphic
          | None -> (sn, (l, tparams, None, None, type_info_func))
        end
        in
        iter (new_item::smap) (new_item::smapwith0) remaining
    in
    iter [] structmap0 (List.rev structdeclmap)

  let structmap = structmap1 @ structmap0

  let union_size = union_size_partial unionmap

  let is_polymorphic_struct sn =
    match List.assoc sn structmap with
    | _, _, (Some (_, _, true)), _, _ -> true
    | _ -> false

  let field_offset l fparent fname =
    let (_, _, Some (_, fmap, _), _, _) = List.assoc fparent structmap in
    let (_, gh, y, offset_opt, _) = List.assoc fname fmap in
    match offset_opt with
      Some term -> term
    | None -> static_error l "Cannot take the address of a ghost field" None

  let enummap = enummap1 @ enummap0
  
  let isfuncs = if file_type path=Java then [] else
    flatmap (fun (ftn, (_, gh, tparams, ftps)) ->
      match (gh, tparams, ftps) with
        (Real, [], []) when dialect <> Some Rust ->
        let isfuncname = "is_" ^ ftn in
        let domain = [provertype_of_type (PtrType Void)] in
        let symb = mk_func_symbol isfuncname domain ProverBool Uninterp in
        [(isfuncname, (dummy_loc, [], Bool, [("", PtrType Void)], symb))]
      | _ -> []
    ) functypenames      
  
  let rec is_subtype_of x y =
    x = y ||
    y = "java.lang.Object" ||
    match try_assoc x classmap1 with
      Some (_, _, _, _, _, _, (super, _), _, interfaces, _, _, _) ->
      is_subtype_of super y || List.exists (fun (itf, _) -> is_subtype_of itf y) interfaces
    | None ->
      match try_assoc x classmap0 with
        Some {csuper=(super, _); cinterfs=interfaces} ->
        is_subtype_of super y || List.exists (fun (itf, _) -> is_subtype_of itf y) interfaces
      | None -> begin match try_assoc x interfmap1 with
          Some (_, _, _, _, interfaces, _, _, _) -> List.exists (fun (itf, _) -> is_subtype_of itf y) interfaces
        | None -> begin match try_assoc x interfmap0 with
            Some (InterfaceInfo (_, _, _, _, interfaces, tparams)) -> List.exists (fun (itf, _) -> is_subtype_of itf y) interfaces
          | None -> false 
          end
        end
  
  let direct_supers (ObjType (cn, targs)) =     
    let toObj (name,targs) = ObjType (name, targs) in
    let (tparams, directSupers_with_tparams) = match try_assoc cn classmap1 with 
      Some (_, _, _, _, _, _, super, tparams, interfaces, _, _, _) -> (tparams, (toObj super)::List.map toObj interfaces)
    | None -> begin match try_assoc cn classmap0 with
        Some {ctpenv; csuper; cinterfs} -> (ctpenv, (toObj csuper)::List.map toObj cinterfs)
      | None -> begin match try_assoc cn interfmap1 with
          Some (_, _, _, _, interfaces, _, _, tparams) -> (tparams, List.map toObj interfaces)
        | None -> begin match try_assoc cn interfmap0 with
            Some (InterfaceInfo (_, _, _, _, interfaces, tparams)) -> (tparams, List.map toObj interfaces)
          end
        end
      end
    in
    let Some tpenv = zip tparams targs in
    if cn = "java.lang.Object" then 
      []
    else
      List.map (replace_type dummy_loc tpenv) directSupers_with_tparams

  let rec is_subtype_of_ x y =
    x = y ||
    y = ObjType("java.lang.Object", []) ||
    match (x, y) with
    | (ObjType (a, atargs), ObjType (b, btargs)) ->
        let directSupers = direct_supers x in
        List.exists (fun st -> st = y || is_subtype_of_ st y) directSupers
    | (ArrayType x, ArrayType y) -> is_subtype_of_ x y
    | _ -> false

  (* A proper type is a type that contains no InferredRealTypeParam *)
  let rec proper_type t = match t with
      ObjType (t, targs) -> List.for_all proper_type targs
    | ArrayType t -> proper_type t
    | Bool | Int _ | RustChar | Double | Float -> true
    | GhostTypeParam _ -> true
    | InferredRealType _ -> false
    | RealTypeParam _ -> true
    | _ -> failwith (Printf.sprintf "no support yet to see if %s is a proper type" (string_of_type t))

  let is_unchecked_exception_type tp = 
    match tp with
     ObjType (cn, _) -> (is_subtype_of cn "java.lang.RuntimeException") || (is_subtype_of cn "java.lang.Error")
    | _ -> false

  (* Region: globaldeclmap *)
  
  let globaldeclmap =
    let rec iter pn ilist gdm ds cont =
      match ds with
        [] -> cont gdm
      | Global(l, te, x, init) :: ds -> (* typecheck the rhs *)
        let x = full_name pn x in
        begin
          match try_assoc x globalmap0 with
            Some(_) -> static_error l "Duplicate global variable name." None
          | None -> ()
        end;
        begin
          match try_assoc x gdm with
            Some (_) -> static_error l "Duplicate global variable name." None
          | None -> 
            let tp = check_pure_type (pn, ilist) [] Real te in
            let global_symb = get_unique_var_symb x (PtrType tp) in
            iter pn ilist ((x, (l, tp, global_symb, ref init)) :: gdm) ds cont
        end
      | _::ds -> iter pn ilist gdm ds cont
    in
    let rec iter0 gdm ps =
      match ps with
        [] -> gdm
      | PackageDecl (lp, pn, ilist, ds)::ps ->
        iter pn ilist gdm ds @@ fun gdm ->
        iter0 gdm ps
    in
    iter0 [] ps

  let globalmap1 = globaldeclmap
  let globalmap = globalmap1 @ globalmap0
 

  (* Region: modulemap *)

  let modulemap1 = [(current_module_name, current_module_term)]

  let modulemap1 = 
    let rec iter mm ds = 
      match ds with
        [] -> List.rev mm
      | RequireModuleDecl(l, name)::ds ->
        begin
          match try_assoc name mm with
          | Some(_) -> iter mm ds (* Ignore duplicate module requirement *)
          | None -> let module_term = get_unique_var_symb name intType in
                    iter ((name, module_term) :: mm) ds
        end
      | _ :: ds -> iter mm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter modulemap1 ds
    | _ when file_type path=Java || dialect <> None -> modulemap1

  let modulemap = modulemap1 @ modulemap0

  (* Region: importmodulemap *)
 
  let importmodulemap1 = 
    let rec iter imm ds = 
      match ds with
        [] -> List.rev imm
      | ImportModuleDecl(l, name)::ds ->
        begin
          match try_assoc name modulemap with
          | None -> static_error l ("Unknown module '" ^ name ^ "'.") None
          | Some(module_term) when module_term == current_module_term -> 
              static_error l ("Cannot import current module.") None
          | Some(module_term) ->
            begin
              match try_assoc name imm with
              | Some(_) -> iter imm ds (* Ignore duplicate module imports *)
              | None -> iter ((name,module_term)::imm) ds
            end
        end
      | _ :: ds -> iter imm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    | _ when file_type path=Java || dialect <> None -> []

  let importmodulemap = importmodulemap1 @ importmodulemap0
  
  (* Region: type-checking of inductive datatypes and fixpoint functions*)
  
  let check_tparams l tparams0 tparams =
    let rec iter tparams =
      match tparams with
        [] -> ()
      | x::xs ->
        if List.mem x tparams0 then static_error l (Printf.sprintf "Type parameter '%s' hides existing type parameter '%s'." x x) None;
        if List.mem x xs then static_error l (Printf.sprintf "Duplicate type parameter '%s'." x) None;
        iter xs
    in
    iter tparams
  
  (* Create function to read a field *)
  let make_getter type_name tt csym subtype fnames f tp =
    (* construct fixpoint function symbol *)
    let id = mk_ident ("get_" ^ type_name ^ "_" ^ f) in
    let get = ctxt#mk_symbol id [typenode_of_type tt] (typenode_of_type tp) (Proverapi.Fixpoint (subtype, 0)) in

    (* construct fixpoint function clause: case C(...,f,...) -> f *)
    let apply _ cvs =
      let Some penv = zip fnames cvs in
      List.assoc f penv
    in
    ctxt#set_fpclauses get 0 [(csym, apply)];
    get

  (* Create function to write a field *)
  let make_setter type_name tt csym subtype getters fnames f tp =
    (* construct fixpoint function symbol *)
    let id = mk_ident ("set_" ^ type_name ^ "_" ^ f) in
    let tt1 = typenode_of_type tt in
    let tp1 = typenode_of_type tp in
    let set = ctxt#mk_symbol id [tt1; tp1] tt1 (Proverapi.Fixpoint (subtype, 0)) in

    (* construct fixpoint function clause: case C(xs,_,ys) -> C(xs,new_value,ys) *)
    let apply [_; new_value] cvs =
      let Some penv = zip fnames cvs in
      let cvs = penv |> List.map (fun (g, cv) -> if g = f then new_value else cv) in
      ctxt#mk_app csym cvs
    in
    ctxt#set_fpclauses set 0 [(csym, apply)];

    (* add auto_lemma about getter/setter relationship:

        auto_lemma(set_T_fi(x, y)) void set_get_for_T_fi(T x, Ti y);
          requires true;
          ensures C(get_T_f1(x), ... get_T_fn(x)) == x;
    *)
    ctxt#begin_formal;
    let desc = "set_get_for_" ^ type_name ^ "_" ^ f in
    let x = ctxt#mk_bound 0 tt1 in
    let y = ctxt#mk_bound 1 tp1 in
    let trigger = ctxt#mk_app set [x; y] in
    let fields = getters |> (List.map (fun (_, getter) -> ctxt#mk_app getter [x])) in
    let lhs = ctxt#mk_app csym fields in
    ctxt#end_formal;
    ctxt#assume_forall desc [trigger] [tt1; tp1] (ctxt#mk_eq lhs x);
    set

  let (inductivemap1, purefuncmap1, purefuncparamrequiresmap1, fixpointmap1) =
    let rec iter (pn,ilist) imap pfm pfprm fpm ds =
      match ds with
        [] -> (imap, pfm, pfprm, fpm)
      | Inductive (l, i, tparams, ctors)::ds -> let i=full_name pn i in
        check_tparams l [] tparams;
        (* Type parameters of inductive types never carry typeids. Rename any uppercase type parameters X to _X. *)
        let tparams' = tparams |> List.map @@ fun x -> if tparam_carries_typeid x then "_" ^ x else x in
        let tpenv = List.map2 (fun x x' -> (x, GhostTypeParam x')) tparams tparams' in
        let (_, _, _, subtype) = List.assoc i inductivedeclmap in
        let tt = InductiveType (i, List.map (fun x -> GhostTypeParam x) tparams') in
        let rec citer j ctormap pfm ctors =
          match ctors with
            [] -> ((pn,ilist), ctormap, pfm)
          | Ctor (lc, cn, name_and_type_exprs)::ctors ->
            let (argument_names, argument_type_expressions) = List.split(name_and_type_exprs) in
            let full_cn = full_name pn cn in
            if List.mem_assoc full_cn pfm || List.mem_assoc full_cn purefuncmap0 then
              static_error lc ("Duplicate pure function name: " ^ full_cn) None
            else begin
              let ts = List.map (fun tp -> instantiate_type tpenv (check_pure_type (pn,ilist) tparams Ghost tp)) argument_type_expressions in
              let csym =
                mk_func_symbol full_cn (List.map provertype_of_type ts) ProverInductive (Proverapi.Ctor (CtorByOrdinal (subtype, j)))
              in
              let purefunc = (full_cn, (lc, tparams', tt, (List.combine argument_names ts), csym)) in
              citer (j + 1) ((cn, purefunc)::ctormap) (purefunc::pfm) ctors
            end
        in
        let (pni, ctormap, pfm) = citer 0 [] pfm ctors in
        (* construct selector functions to read fields of single-constructor types *)
        let getters = match ctors with
        | [Ctor (lc, cn, name_and_type_exprs)] ->
          let (_, (_, _, _, parameter_names_and_types, (csym, _))) = List.assoc cn ctormap in
          let fieldnames = List.map fst parameter_names_and_types in
          name_and_type_exprs |> List.map (fun (f, t) ->
            let tp = List.assoc f parameter_names_and_types in
            (f, make_getter i tt csym subtype fieldnames f tp))
        | _ -> []
        in
        (* construct setter functions to write fields of single-constructor types *)
        let setters = match ctors with
        | [Ctor (lc, cn, name_and_type_exprs)] ->
          let (_, (_, _, _, parameter_names_and_types, (csym, _))) = List.assoc cn ctormap in
          let fieldnames = List.map fst parameter_names_and_types in
          name_and_type_exprs |> List.map (fun (f, t) ->
            let tp = List.assoc f parameter_names_and_types in
            (f, make_setter i tt csym subtype getters fieldnames f tp))
        | _ -> []
        in
        iter pni ((i, (l, tparams', List.rev ctormap, getters, setters, subtype))::imap) pfm pfprm fpm ds
      | Func (l, Fixpoint, tparams, rto, g, ps, nonghost_callers_only, functype, contract, terminates, body_opt, _, _)::ds ->
        let g = full_name pn g in
        if List.mem_assoc g pfm || List.mem_assoc g purefuncmap0 then static_error l ("Duplicate pure function name: "^g) None;
        check_tparams l [] tparams;
        let rt =
          match rto with
            None -> static_error l "Return type of fixpoint functions cannot be void." None
          | Some rt -> (check_pure_type (pn,ilist) tparams Ghost rt)
        in
        if nonghost_callers_only then static_error l "A fixpoint function cannot be marked nonghost_callers_only." None;
        if functype <> None then static_error l "Fixpoint functions cannot implement a function type." None;
        if contract <> None then static_error l "Fixpoint functions cannot have a contract." None;
        if terminates then static_error l "The 'terminates' clause is superfluous for fixpoint functions." None;
        let pmap, param_requires_map =
          let rec iter pmap param_requires_map i ps =
            match ps with
              [] -> List.rev pmap, List.rev param_requires_map
            | (te, p)::ps ->
              let _ = if List.mem_assoc p pmap then static_error l "Duplicate parameter name." None in
              let te, param_requires_map =
                match te with
                  PureFuncTypeExpr (l, ps, Some requires) ->
                  PureFuncTypeExpr (l, ps, None), (i, (List.map snd ps, requires))::param_requires_map
                | _ -> te, param_requires_map
              in
              let t = check_pure_type (pn,ilist) tparams Ghost te in
              iter ((p, t)::pmap) param_requires_map (i + 1) ps
          in
          iter [] [] 0 ps
        in
        let param_requires_map = param_requires_map |> List.map @@ fun (p, (ps, requires)) ->
          let pmap' =
            let rec iter pmap' i = function
            | [_] -> (* Skip return type *) List.rev pmap'
            | Some (l, p)::ps ->
              if List.mem_assoc p pmap' then static_error l "Duplicate parameter name." None;
              if List.mem_assoc p pmap then static_error l "Parameter parameter name hides parameter name." None;
              iter ((p, i)::pmap') (i+1) ps
            | None::ps -> iter pmap' (i+1) ps
            in
            iter [] 0 ps
          in
          let requires =
            let rec iter = function
              Operation (l, And, [x; y]) -> iter x @ iter y
            | Operation (l, ((Lt|Le) as op), [Var (lx, x); Var (ly, y)]) ->
              let x =
                match try_assoc x pmap' with
                  Some i -> i
                | None -> static_error lx "This parameter has no such parameter" None
              in
              let y =
                match try_assoc_i y pmap with
                  None -> static_error ly "No such parameter" None
                | Some (i, _) -> i
              in
              [(l, x, (match op with Lt -> IsProperComponentOf | Le -> IsComponentOf), y)]
            | e -> static_error (expr_loc e) "This expression form is not allowed here." None
            in
            iter requires
          in
          p, requires
        in
        let pfprm =
          match param_requires_map with
            [] -> pfprm
          | _ -> (g, param_requires_map)::pfprm
        in
        let typeid_paramtypes = tparams |> flatmap @@ fun x -> if tparam_carries_typeid x then [ProverInductive] else [] in
        let fsym_paramtypes = typeid_paramtypes @ List.map (fun (p, t) -> provertype_of_type t) pmap in
        begin match body_opt with
          Some ([SwitchStmt (ls, e, cs) as body], _) ->
          let index, subtype = 
            match e with
              Var (lx, x) ->
              begin match try_assoc_i x pmap with
                None -> static_error lx "Fixpoint function must switch on a parameter." None
              | Some (index, tp) ->
                match tp with
                  InductiveType (i, _) ->
                  let (_, _, subtype) = List.assoc i inductive_arities in
                  index, subtype
                | _ -> static_error l "Fixpoint function must switch on a parameter of inductive type." None
              end
            | _ -> static_error l "Fixpoint function must switch on a parameter." None
          in
          let fsym = mk_func_symbol g fsym_paramtypes (provertype_of_type rt) (Proverapi.Fixpoint (subtype, List.length typeid_paramtypes + index)) in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> p, t) pmap, fsym))::pfm) pfprm ((g, (l, tparams, rt, pmap, Some index, body, pn, ilist, fst fsym))::fpm) ds
        | Some ([ReturnStmt (lr, Some e) as body], _) ->
          let fsym = mk_func_symbol g fsym_paramtypes (provertype_of_type rt) Proverapi.Uninterp in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> p, t) pmap, fsym))::pfm) pfprm ((g, (l, tparams, rt, pmap, None, body, pn, ilist, fst fsym))::fpm) ds
        | None ->
          let fsym = mk_func_symbol g fsym_paramtypes (provertype_of_type rt) Proverapi.Uninterp in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> p, t) pmap, fsym))::pfm) pfprm fpm ds
        | _ -> static_error l "Body of fixpoint function must be switch statement or return statement." None
        end
      | _::ds -> iter (pn,ilist) imap pfm pfprm fpm ds
    in
    let rec iter' (imap,pfm,pfprm,fpm) ps=
      match ps with
      PackageDecl(l,pn,il,ds)::rest -> iter' (iter (pn,il) imap pfm pfprm fpm ds) rest
      | [] -> (List.rev imap, List.rev pfm, List.rev pfprm, List.rev fpm)
    in
    iter' ([],isfuncs,[],[]) ps
  
  let purefuncparamrequiresmap = purefuncparamrequiresmap1 @ purefuncparamrequiresmap0

  let inductivemap1 =
    (* Ranks:
       -1 = finished checking; the inductive type is well-defined
        0 = not yet being checked
        n when n > 0 = being checked; n = depth of recursive check
            the inductive at rank n + 1 appears in the definition of the inductive at rank n at a positive or negative position
     *)
    let module EquivalenceClasses = struct
      type
        ec_state = ECState of int * int * ptr list
      and
        ec = ec_state ref
      and
        ptr = ec ref
    end in
    let open EquivalenceClasses in
    let mk_ec () =
      let ec = ref (ECState (0, 0, [])) in
      let ptr = ref ec in
      ec := ECState (0, 0, [ptr]);
      ptr
    in
    let welldefined_map = List.map (fun (i, info) -> (i, (info, mk_ec ()))) inductivemap1 in
    let get_rank ptr = let ECState (rank, containsAny, mems) = !(!ptr) in rank in
    let set_rank ptr rank = let ECState (_, containsAny, mems) = !(!ptr) in !ptr := ECState (rank, containsAny, mems) in
    let get_contains_any ptr = let ECState (rank, containsAny, mems) = !(!ptr) in containsAny in
    let join_contains_any ptr containsAny =
      let ec = !ptr in
      let ECState (rank, containsAny0, mems) = !ec in 
      ec := ECState (rank, max containsAny0 containsAny, mems)
    in
    let ec_contains_any ptr negative = join_contains_any ptr (if negative then 2 else 1) in
    let join_contains_any_neg ptr negative containsAny =
      if containsAny = 0 then () else join_contains_any ptr (if negative then 2 else containsAny)
    in
    let merge_ecs ptr0 ptr1 =
      let ec0 = !ptr0 in
      let ec1 = !ptr1 in
      let ECState (ecrank0, containsAny0, ecmems0) = !ec0 in
      let ECState (ecrank1, containsAny1, ecmems1) = !ec1 in
      if ecrank0 <> ecrank1 then begin
        assert (ecrank0 < ecrank1);
        List.iter (fun ptr -> ptr := ec0) ecmems1;
        ec0 := ECState (ecrank0, max containsAny0 containsAny1, ecmems1 @ ecmems0)
      end
    in
    let rec check_welldefined rank negative_rank pred_ptrs (i, ((l, _, ctors, _, _, _), ptr)) =
      (* Invariant:
         - All nodes reachable from a -1 node are -1
         - There are no cycles through -1 nodes that go through a negative occurrence.
         - The ranks of all nodes are less than the current rank [rank]
         - There are no cycles that go through a negative occurrence in the subgraph that is to the left of the current path.
         - All nodes reachable from a given node in the subgraph that is to the left of the current path, have either the same rank, a higher rank, or rank -1, but never rank 0
         - For any two nodes in the subgraph that is to the left of the current path, they are mutually reachable iff they are in the same equivalence class (and consequently have the same rank)
         - The ranks of the nodes on the current path are always (non-strictly) increasing
       *)
      if get_rank ptr = -1 then
        ()
      else
      begin
        assert (get_rank ptr = 0);
        set_rank ptr rank;
        let pred_ptrs = ptr::pred_ptrs in
        let rec check_ctor (ctorname, (_, (_, _, _, parameter_names_and_types, _))) =
          let rec check_type negative pt =
            match pt with
            | Bool | Void | Int (_, _) | RustChar | RealType | PtrType _ | RustRefType _ | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AbstractType _ | Float | Double | LongDouble -> ()
            | AnyType -> ec_contains_any ptr negative
            | GhostTypeParam _ -> if negative then static_error l "A type parameter may not appear in a negative position in an inductive datatype definition." None
            | InductiveType (i0, tps) ->
              List.iter (fun t -> check_type negative t) tps;
              begin match try_assoc i0 welldefined_map with
                None ->
                let (_, _, _, _, _, _, containsAny0, _, _) = List.assoc i0 inductivemap0 in
                join_contains_any_neg ptr negative containsAny0
              | Some (info0, ptr0) ->
                let ecrank0 = get_rank ptr0 in
                let negative_rank = if negative then rank else negative_rank in
                if ecrank0 > 0 then begin
                  if ecrank0 <= negative_rank then static_error l "This inductive datatype is not well-defined; it occurs recursively in a negative position." None;
                  let rec merge_preds pred_ptrs =
                    match pred_ptrs with
                      [] -> ()
                    | ptr1::pred_ptrs ->
                      if ecrank0 < get_rank ptr1 then begin
                        merge_ecs ptr0 ptr1;
                        merge_preds pred_ptrs
                      end
                  in
                  merge_preds pred_ptrs
                end else begin
                  check_welldefined (rank + 1) negative_rank pred_ptrs (i0, (info0, ptr0));
                  join_contains_any_neg ptr negative (get_contains_any ptr0)
                end
              end
            | PredType (tps, pts, _, _) ->
              assert (tps = []);
              List.iter (fun t -> check_type true t) pts;
              ec_contains_any ptr negative
            | PureFuncType (t1, t2) ->
              check_type true t1; check_type negative t2
            | StructType (_, _) when dialect = Some Rust -> () (* We don't support ghost fields in Rust structs, so these cannot be recursive or contain 'any' or predicate values *)
            | t -> static_error l (Printf.sprintf "Type '%s' is not supported as an inductive constructor parameter type." (string_of_type t)) None
          in
          let (_, parameter_types) = List.split parameter_names_and_types in
          List.iter (check_type false) parameter_types
        in
        List.iter check_ctor ctors;
        (* If this node is the leader of an equivalence class, then this equivalence class has now been proven to be well-defined. *)
        if get_rank ptr = rank then set_rank ptr (-1)
      end
    in
    List.map (fun (i, ((l, tparams, ctors, gets, sets, subtype), ptr) as entry) -> check_welldefined 1 0 [] entry; (i, (l, tparams, ctors, gets, sets, get_contains_any ptr, subtype))) welldefined_map
    (* Postcondition: there are no cycles in the inductive datatype definition graph that go through a negative occurrence. *)
  
  let () =
    let inhabited_map = List.map (fun (i, info) -> (i, (info, ref 0))) inductivemap1 in
    let rec check_inhabited i l ctors status =
      if !status = 2 then
        ()
      else
      begin
        status := 1;
        let rec find_ctor ctors =
          match ctors with
            [] -> static_error l "Inductive datatype is not inhabited." None
          | (_, (_, (_, _, _, pts, _)))::ctors ->
            let (_, pts) = List.split pts in
            let rec type_is_inhabited tp =
              match tp with
                Bool | Int (_, _) | RustChar | RealType | PtrType _ | RustRefType _ | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType | AbstractType _ -> true
              | GhostTypeParam _ -> true  (* Should be checked at instantiation site. *)
              | PredType (tps, pts, _, _) -> true
              | PureFuncType (t1, t2) -> type_is_inhabited t2
              | InductiveType (i0, tps) ->
                List.for_all type_is_inhabited tps &&
                begin match try_assoc i0 inhabited_map with
                  None -> true
                | Some ((l0, _, ctors0, _, _, _, _), status0) ->
                  !status0 <> 1 &&
                  (check_inhabited i0 l0 ctors0 status0; true)
                end
              | StructType (_, _) when dialect = Some Rust -> true (* We don't support ghost fields in Rust *)
              in
            if List.for_all type_is_inhabited pts then () else find_ctor ctors
        in
        find_ctor ctors;
        status := 2
      end
    in
    List.iter (fun (i, ((l, _, ctors, _, _, _, _), status)) -> check_inhabited i l ctors status) inhabited_map
  
  let inductivemap1 =
    let infinite_map = List.map (fun (i, info) -> let status = ref (0, []) in (i, (info, status))) inductivemap1 in
    (* Status: (n, tparams) with n: 0 = not visited; 1 = currently visiting; 2 = infinite if one of tparams is infinite; 3 = unconditionally infinite *)
    (* Infinite = has infinitely many values *)
    let rec determine_type_is_infinite (i, ((l, tparams, ctors, gets, sets, containsAny, _), status)) =
      let (n, _) = !status in
      if n < 2 then begin
        status := (1, []);
        let rec fold_cond cond f xs =
          match xs with
            [] -> Some cond
          | x::xs ->
            begin match f x with
              None -> None
            | Some cond' -> fold_cond (cond' @ cond) f xs
            end
        in
        let ctor_is_infinite (cn, (_, (lc, _, _, pts, _))) =
          let rec type_is_infinite tp =
            match tp with
              Bool -> Some []
            | GhostTypeParam x -> Some [x]
            | Int (_, _) | RustChar | RealType | PtrType _ | RustRefType _ | PredType (_, _, _, _) | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType | AbstractType _ -> None
            | PureFuncType (_, _) -> None (* CAVEAT: This assumes we do *not* have extensionality *)
            | InductiveType (i0, targs) ->
              begin match try_assoc i0 infinite_map with
                Some (info0, status0) ->
                let (n, cond) = !status0 in
                if n = 1 then
                  None
                else begin
                  if n = 0 then determine_type_is_infinite (i0, (info0, status0));
                  let (n, cond) = !status0 in
                  if n = 3 then None else
                  let (_, tparams, _, _, _, _, _) = info0 in
                  let Some tpenv = zip tparams targs in
                  fold_cond [] (fun x -> type_is_infinite (List.assoc x tpenv)) cond
                end
              | None ->
                let (_, tparams, _, _, _, cond, _, _, _) = List.assoc i0 inductivemap0 in
                begin match cond with
                  None -> None
                | Some cond ->
                  let Some tpenv = zip tparams targs in
                  fold_cond [] (fun x -> type_is_infinite (List.assoc x tpenv)) cond
                end
              end
          in
          let (_, pts) = List.split pts in
          fold_cond [] type_is_infinite pts
        in
        match fold_cond [] ctor_is_infinite ctors with
          None -> status := (3, [])
        | Some cond -> status := (2, cond)
      end
    in
    List.iter determine_type_is_infinite infinite_map;
    infinite_map |> List.map
      begin fun (i, ((l, tparams, ctors, gets, sets, containsAny, subtype), status)) ->
        let (n, cond) = !status in
        let cond = if n = 2 then Some cond else None in
        (i, (l, tparams, ctors, gets, sets, cond, containsAny, subtype))
      end
  
  let inductivemap1 = inductivemap1 |> List.map begin fun (i, (l, tparams, ctors, gets, sets, cond, containsAny, subtype)) ->
    (* Since we allow predicate constructor type parameters as predicate constructor parameter types, it is crucial for soundness that
       only types that contain 'any' only in positive positions have typeids.
       Note that we can assume that the type arguments of this inductive type themselves contain 'any' only in positive
       positions, since they themselves must have a typeid for the constructed type to have a typeid.
     *)
    let type_info_func =
      if containsAny < 2 then
        Some (mk_symbol (i ^ "_type_info") (List.map (fun x -> type_info_type_node) tparams) type_info_type_node Uninterp)
      else
        None
    in
    (i, (l, tparams, ctors, gets, sets, cond, containsAny, subtype, type_info_func))
  end

  let inductivemap = inductivemap1 @ inductivemap0

  let rec unfold_inferred_type t =
    match t with
      InferredType (_, t') ->
      begin
        match !t' with
        | EqConstraint t -> unfold_inferred_type t
        | _ -> t
      end
    | _ -> t

  let rec unfold_inferred_type_deep t =
    match unfold_inferred_type t with
      PtrType t -> PtrType (unfold_inferred_type_deep t)
    | RustRefType (lft, mut, t) -> RustRefType (lft, mut, unfold_inferred_type_deep t)
    | t -> t

  let rec type_satisfies_contains_any_constraint assumeTypeParamsContainAnyPositiveOnly allowContainsAnyPositive tp =
    match unfold_inferred_type tp with
      Bool | AbstractType _ | Int (_, _) | RustChar | Float | Double | LongDouble | RealType | FuncType _ | PtrType _ | InlineFuncType _ | RustRefType _ | ObjType _ | ArrayType _ | BoxIdType | HandleIdType -> true
    | RealTypeParam _ | GhostTypeParam _ -> assumeTypeParamsContainAnyPositiveOnly
    | AnyType | PredType (_, _, _, _) -> allowContainsAnyPositive
    | StructType (_, _) -> allowContainsAnyPositive
      (* We don't need to check the struct type type arguments because they are real and real types
         do not contain any in negative positions. *)
    | UnionType _ -> allowContainsAnyPositive
    | StaticArrayType (t, n) -> type_satisfies_contains_any_constraint assumeTypeParamsContainAnyPositiveOnly allowContainsAnyPositive t
    | PureFuncType (t1, t2) -> type_satisfies_contains_any_constraint assumeTypeParamsContainAnyPositiveOnly false t1 && type_satisfies_contains_any_constraint assumeTypeParamsContainAnyPositiveOnly allowContainsAnyPositive t2
    | InductiveType (i, targs) ->
      let (_, _, _, _, _, _, containsAny, _, _) = List.assoc i inductivemap in
      (containsAny <= if allowContainsAnyPositive then 1 else 0) &&
      List.for_all (type_satisfies_contains_any_constraint assumeTypeParamsContainAnyPositiveOnly allowContainsAnyPositive) targs
    | InferredType (_, stateRef) ->
      stateRef := inferred_type_constraint_meet !stateRef (ContainsAnyConstraint allowContainsAnyPositive);
      true
    | t -> failwith ("type_satisfies_contains_any_constraint: " ^ string_of_type t)
  and type_satisfies_inferred_type_constraint cnt tp =
    match cnt with
      Unconstrained -> true
    | ContainsAnyConstraint allowContainsAnyPositive -> type_satisfies_contains_any_constraint false allowContainsAnyPositive tp

  let () =
    structmap1 |> List.iter @@ function
      (sn, (l, tparams, None, _, _)) -> ()
    | (sn, (l, tparams, Some (_, fmap, _), _, _)) ->
      fmap |> List.iter @@ fun (f, (lf, gh, t, offset, init)) ->
        if not (type_satisfies_contains_any_constraint true true t) then
          static_error lf "Struct field types must not contain 'any' or predicate types in negative positions" None
  
  (* Region: type compatibility checker *)

  let rec is_derived_of_base derived_name base_name =
    let check_bases bases = bases |> List.exists @@ fun (name, _) -> is_derived_of_base name base_name in
    derived_name = base_name ||
    match try_assoc derived_name structmap with 
    | Some (_, _, Some (bases, _, _), _, _) -> check_bases bases 
    | None -> false
  
  let rec normalize_pointee_type t =
    match t with
      StaticArrayType (t, _) when not is_rust -> normalize_pointee_type t
    | _ -> t

  let rec compatible_pointees t t0 =
    match (normalize_pointee_type t, normalize_pointee_type t0) with
      (_, Void) -> true
    | (Void, _) -> true
    | ((PtrType t | RustRefType (_, _, t)), (PtrType t0 | RustRefType (_, _, t0))) -> compatible_pointees t t0
    | t, t0 -> unify_relaxed t t0
  
  and unify_relaxed t1 t2 =
    t1 == t2 ||
    match (unfold_inferred_type t1, unfold_inferred_type t2) with
      (InferredType (_, t'), InferredType (_, t0')) ->
      if t' == t0' then true else begin
        if inferred_type_constraint_le !t' !t0' then
          t0' := EqConstraint t1
        else
          t' := EqConstraint t2;
        true
      end
    | (t, InferredType (_, t0)) | (InferredType (_, t0), t) -> type_satisfies_inferred_type_constraint !t0 t && (t0 := EqConstraint t; true)
    | (InductiveType (i1, args1), InductiveType (i2, args2)) ->
      i1=i2 && List.for_all2 unify_relaxed args1 args2
    | (StructType (s1, args1), StructType (s2, args2)) ->
      s1 = s2 && List.for_all2 unify_relaxed args1 args2
    | (PureFuncType (d1, r1), PureFuncType(d2, r2)) -> unify_relaxed d1 d2 && unify_relaxed r1 r2
    | (PredType ([], ts1, inputParamCount1, inductiveness1), PredType ([], ts2, inputParamCount2, inductiveness2)) ->
      for_all2 unify_relaxed ts1 ts2 && inputParamCount1 = inputParamCount2 && inductiveness1 = inductiveness2
    | (ArrayType t1, ArrayType t2) -> unify_relaxed t1 t2
    | (StaticArrayType (t1, n1), StaticArrayType (t2, n2)) -> unify_relaxed t1 t2 && unify_relaxed n1 n2
    | ((PtrType t1 | RustRefType (_, _, t1)), (PtrType t2 | RustRefType (_, _, t2))) -> compatible_pointees t1 t2
    | (InlineFuncType _, PtrType _) -> true
    | (PtrType _, InlineFuncType _) -> true
    | (StaticLifetime, _) | (_, StaticLifetime) -> true
    | (GhostTypeParam x1, GhostTypeParam x2) ->
      (* We ignore lifetimes *)
      if x1 <> "" && x1.[0] = '\'' || x2 <> "" && x2.[0] = '\'' then true else x1 = x2
    | (t1, t2) -> t1 = t2
  
  (* If [unify_strict t1 t2] returns [true], then t1 and t2 must have the same typeid.
   * unify_strict is used to match heap chunk type arguments if uppercase_type_params_carry_typeid. *)
  let rec unify_strict t1 t2 =
    t1 == t2 ||
    match (unfold_inferred_type t1, unfold_inferred_type t2) with
      (InferredType (_, t'), InferredType (_, t0')) ->
      if t' == t0' then true else begin
        if inferred_type_constraint_le !t' !t0' then
          t0' := EqConstraint t1
        else
          t' := EqConstraint t2;
        true
      end
    | (t, InferredType (_, t0)) | (InferredType (_, t0), t) -> type_satisfies_inferred_type_constraint !t0 t && (t0 := EqConstraint t; true)
    | (InductiveType (i1, args1), InductiveType (i2, args2)) ->
      i1=i2 && List.for_all2 unify_strict args1 args2
    | (StructType (s1, args1), StructType (s2, args2)) ->
      s1 = s2 && List.for_all2 unify_strict args1 args2
    | (PureFuncType (d1, r1), PureFuncType(d2, r2)) -> unify_strict d1 d2 && unify_strict r1 r2
    | (PredType ([], ts1, inputParamCount1, inductiveness1), PredType ([], ts2, inputParamCount2, inductiveness2)) ->
      for_all2 unify_strict ts1 ts2 && inputParamCount1 = inputParamCount2 && inductiveness1 = inductiveness2
    | (ArrayType t1, ArrayType t2) -> unify_strict t1 t2
    | (StaticArrayType (t1, n1), StaticArrayType (t2, n2)) -> unify_strict t1 t2 && unify_strict n1 n2
    | (PtrType t1, PtrType t2) -> if fno_strict_aliasing then compatible_pointees t1 t2 else unify_strict t1 t2
    | (RustRefType (lft1, mut1, t1), RustRefType (lft2, mut2, t2)) -> unify_strict lft1 lft2 && mut1 = mut2 && unify_strict t1 t2
    | (InlineFuncType _, PtrType _) -> true
    | (PtrType _, InlineFuncType _) -> true
    | (StaticLifetime, _) | (_, StaticLifetime) -> true
    | (GhostTypeParam x1, GhostTypeParam x2) -> x1 = x2
    | (t1, t2) -> t1 = t2

  let unify t1 t2 = if uppercase_type_params_carry_typeid then unify_strict t1 t2 else unify_relaxed t1 t2

  let width_group w =
    match w with
      PtrWidth -> 1
    | LitWidth 2 | LongWidth -> 2
    | _ -> 0

  let width_ordinal w =
    match w with
      LitWidth 0 -> 0
    | LitWidth 1 -> 1
    | IntWidth -> 2
    | LitWidth 2 -> 3
    | PtrWidth -> 3
    | LongWidth -> 4
    | LitWidth k -> 2 + k

  (* Note: if [width_le w1 w2] returns [false], then either w2 is less than w1 or w1 and w2 are equal. *)
  let width_le l w1 w2 =
    if width_group w1 lor width_group w2 = 3 then
      static_error l "This expression's type depends on the target architecture, which is not supported by VeriFast. Insert casts or specify a target (using the -target command-line option) to eliminate this error." None;
    width_ordinal w1 <= width_ordinal w2

  let definitely_width_le w1 w2 = width_group w1 lor width_group w2 <> 3 && width_ordinal w1 <= width_ordinal w2

  let definitely_width_lt w1 w2 =
    match w1, w2 with
      LitWidth k1, LitWidth k2 -> k1 < k2
    | LitWidth k1, (IntWidth|PtrWidth) -> k1 < 1
    | LitWidth k1, LongWidth -> k1 < 2
    | IntWidth, LitWidth k2 -> 2 < k2
    | (LongWidth|PtrWidth), LitWidth k2 -> 3 < k2
    | _ -> false

  let definitely_is_upcast (Some (r, s)) (Some (r0, s0)) =
    match s, s0 with
      Unsigned, Signed -> definitely_width_lt (width_of_rank r) (width_of_rank r0)
    | Signed, Unsigned -> false
    | _, _ -> definitely_width_le (width_of_rank r) (width_of_rank r0)

  let rec expect_type_core l msg (inAnnotation: bool option) t t0 =
    match (unfold_inferred_type t, unfold_inferred_type t0) with
      (ObjType ("null", _), ObjType _) -> ()
    | (ObjType ("null", _), RealTypeParam _) -> ()
    | (ObjType(_, _), RealTypeParam t) -> ()
    | (ObjType ("null", []), ArrayType _) -> ()
    | (RealTypeParam t, ObjType("java.lang.Object", [])) -> ()
    | (ArrayType _, ObjType ("java.lang.Object", [])) -> ()
    | (RealTypeParam t, t0) -> (* erase t to it's upper bound *) expect_type_core l msg inAnnotation (erase_type (RealTypeParam t)) t0
    (* Note that in Java short[] is not assignable to int[] *)
    | (ArrayType et, ArrayType et0) when et = et0 -> ()
    | (ArrayType (ObjType(t0, ts0)), ArrayType (ObjType(t1, ts1))) -> expect_type_core l msg None (ObjType (t0, ts0)) (ObjType(t1, ts1))
    | (StaticArrayType (elemTp, _), PtrType elemTp0) when not is_rust && compatible_pointees elemTp elemTp0 -> ()
    | (Int (Signed, m), Int (Signed, n)) when definitely_width_le (width_of_rank m) (width_of_rank n) -> ()
    | (Int (Unsigned, m), Int (Unsigned, n)) when definitely_width_le (width_of_rank m) (width_of_rank n) -> ()
    | (Int (Unsigned, m), Int (Signed, n)) when definitely_width_lt (width_of_rank m) (width_of_rank n) -> ()
    | (Int (_, _), Int (_, _)) when inAnnotation = Some true -> ()
    | (Int (_, _), RustChar)| (RustChar, Int (_, _)) -> ()
    | (ObjType (x, _), ObjType (y, _)) when is_subtype_of x y -> ()
    | PtrType (StructType (derived, [])), PtrType (StructType (base, [])) when dialect = Some Cxx && is_derived_of_base derived base -> ()
    | StructType (derived, []), StructType (base, []) when dialect = Some Cxx && is_derived_of_base derived base -> ()
    | (PredType ([], ts, inputParamCount, inductiveness), PredType ([], ts0, inputParamCount0, inductiveness0)) ->
      begin
        match zip ts ts0 with
          Some tpairs when List.for_all (fun (t, t0) -> unify_relaxed t t0) tpairs && (inputParamCount0 = None || inputParamCount = inputParamCount0) -> ()
        | _ -> static_error l (msg ^ "Predicate type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".") None
      end
    | (PureFuncType (t1, t2), PureFuncType (t10, t20)) -> expect_type_core l msg inAnnotation t10 t1; expect_type_core l msg inAnnotation t2 t20
    | (InductiveType (_, _) as tp, AnyType) -> if not (type_satisfies_contains_any_constraint false true tp) then static_error l (msg ^ "Cannot cast type " ^ string_of_type tp ^ " to 'any' because it contains 'any' in a negative position.") None
    | (InductiveType (i1, args1), InductiveType (i2, args2)) when i1 = i2 ->
      List.iter2 (expect_type_core l msg inAnnotation) args1 args2
    | (_, Void) -> ()
    | _ -> if unify_relaxed t t0 then () else static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".") None
  
  let expect_type l (inAnnotation: bool option) t t0 = expect_type_core l "" inAnnotation t t0
  
  let is_assignable_to (inAnnotation: bool option) t t0 =
    try expect_type dummy_loc inAnnotation t t0; true with StaticError (l, msg, url) -> false (* TODO: Consider eliminating this hack *)
  
  let is_assignable_to_sign (inAnnotation: bool option) sign sign0 = for_all2 (is_assignable_to inAnnotation) sign sign0
  
  let convert_provertype_expr e proverType proverType0 =
    if proverType = proverType0 then e else ProverTypeConversion (proverType, proverType0, e)
  
  let box e t t0 =
    match unfold_inferred_type t0 with GhostTypeParam _ -> convert_provertype_expr e (provertype_of_type t) ProverInductive | _ -> e
  
  let unbox e t0 t =
    match unfold_inferred_type t0 with
      GhostTypeParam _ ->
      begin match unfold_inferred_type t with
        InferredType _ -> Unbox (e, t)
      | _ -> convert_provertype_expr e ProverInductive (provertype_of_type t)
      end
    | _ -> e

  (* A universal type is one that is isomorphic to the universe for purposes of type erasure *)
  let rec is_universal_type tp =
    match tp with
      Bool | AbstractType _ -> false
    | GhostTypeParam x | RealTypeParam x -> true
    | Int (_, _) | RustChar | RealType | PtrType _ | RustRefType _ | PredType (_, _, _, _) | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> true
    | PureFuncType (t1, t2) -> is_universal_type t1 && is_universal_type t2
    | InductiveType (i0, targs) ->
      let (_, _, _, _, _, cond, _, _, _) = List.assoc i0 inductivemap in
      cond <> Some [] && List.for_all is_universal_type targs
  
  let functypedeclmap1 =
    let rec iter (pn,ilist) functypedeclmap1 ds =
      match ds with
        [] -> functypedeclmap1
      | FuncTypeDecl (l, gh, rt, ftn, tparams, ftxs, xs, (pre, post, terminates))::ds ->
        if gh = Ghost && terminates then static_error l "A 'terminates' clause on a lemma function type is superfluous." None;
        let ftn0 = ftn in
        let ftn = full_name pn ftn in
        let _ = if List.mem_assoc ftn functypedeclmap1 || List.mem_assoc ftn functypemap0 then static_error l "Duplicate function type name." None in
        let rec check_tparams_distinct tparams =
          match tparams with
            [] -> ()
          | x::xs ->
            if List.mem x xs then static_error l "Duplicate type parameter" None;
            check_tparams_distinct xs
        in
        check_tparams_distinct tparams;
        (* The return type cannot mention type parameters, except in Rust. *)
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) (if dialect = Some Rust then tparams else []) Ghost rt) in
        let ftxmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate function type parameter name." None;
              let t = check_pure_type (pn,ilist) tparams Ghost te in
              iter ((x, t)::xm) xs
          in
          iter [] ftxs
        in
        let xmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm || List.mem_assoc x ftxmap then static_error l "Duplicate parameter name." None;
              let t = check_pure_type (pn,ilist) tparams Ghost te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        iter (pn,ilist) ((ftn, (l, gh, tparams, rt, ftxmap, xmap, ftn0, pn, ilist, pre, post, terminates))::functypedeclmap1) ds
      | _::ds -> iter (pn,ilist) functypedeclmap1 ds
    in
    let rec iter' functypedeclmap1 ps =
      match ps with
        [] -> List.rev functypedeclmap1
      | PackageDecl (_, pn, ilist, ds)::ps -> iter' (iter (pn,ilist) functypedeclmap1 ds) ps
    in
    iter' [] ps
  
  (* Region: predicate families *)
  
  let mk_predfam p l tparams arity ts inputParamCount inductiveness =
    (p, (l, tparams, arity, ts, get_unique_var_symb p (PredType (tparams, ts, inputParamCount, inductiveness)), inputParamCount, inductiveness))

  let tparams_as_targs tparams = List.map (fun x -> GhostTypeParam x) tparams

  let struct_padding_predfams1 =
    flatmap
      (function
         (sn, (l, tparams, body_opt, Some padding_predsymb, _)) ->
          [(padding_pred_name sn, (l, tparams, 0, [PtrType (StructType (sn, tparams_as_targs tparams))], padding_predsymb, Some 1, Inductiveness_Inductive))]
       | _ -> [])
      structmap1
  
  let functypedeclmap1 =
    List.map
      begin fun (g, (l, gh, tparams, rt, ftxmap, xmap, g0, pn, ilist, pre, post, terminates)) ->
        let predfammaps =
          if gh = Ghost || ftxmap <> [] || tparams <> [] || dialect = Some Rust then
            let fun_ptr_type =
              if dialect = Some Rust then InlineFuncType (match rt with None -> Void | Some rt -> rt) else PtrType (FuncType g) in
            let paramtypes = fun_ptr_type::List.map snd ftxmap in
            [mk_predfam (full_name pn ("is_" ^ g0)) l tparams 0 paramtypes (Some (List.length paramtypes)) Inductiveness_Inductive]
          else
            []
        in
        let typeid = mk_typeid_term g in
        (g, (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, terminates, predfammaps, typeid))
      end
      functypedeclmap1
  
  let isparamizedfunctypepreds1 = flatmap (fun (g, (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, terminates, predfammaps, typeid)) -> predfammaps) functypedeclmap1

  let struct_accessor_map1: struct_accessor_info map =
    structmap1 |> flatmap (fun (sn, (l, tparams, body_opt, _, _)) ->
        (* For each struct "s", and each field fi, generate a tuple type and getter/setter functions
             mk_s : T1 * ... * Tn -> struct s
             get_s_fi : struct s -> Ti
             set_s_fi : struct s * Ti -> struct s
        *)
        begin match body_opt with
        | None -> []
        | Some (_, fds, _) ->
          let cname = "mk_" ^ sn in
          let field_gh_types = fds |> List.map (fun (f, (_, gh, t, _, _)) -> (f, gh, t)) in
          let field_names = List.map (fun (f, _, _) -> f) field_gh_types in
          let tt = StructType (sn, tparams_as_targs tparams) in
          let subtype = InductiveSubtype.alloc () in
          let subtype_opt = InductiveSubtype.alloc () in
          let (csym, _) = mk_func_symbol cname (List.map (fun (x, _, t) -> provertype_of_type t) field_gh_types) ProverInductive (Proverapi.Ctor (CtorByOrdinal (subtype, 0))) in
          let (csym_opt, _) = mk_func_symbol (cname ^ ".opt") (field_gh_types |> 
            List.map (function 
              | (f, Ghost, t) -> provertype_of_type t
              | (f, Real, t) -> provertype_of_type (InductiveType ("option", [t])))) 
            ProverInductive (Proverapi.Ctor (CtorByOrdinal (subtype_opt, 0))) 
          in
          let getters = field_gh_types |> List.map (fun (f, _, t) -> (f, make_getter sn tt csym subtype field_names f t)) in
          let setters = field_gh_types |> List.map (fun (f, _, t) -> (f, make_setter sn tt csym subtype getters field_names f t)) in
          (* Axiom: forall s, mk_s (get_f1 s) ... (get_fN s) == s *)
          if field_gh_types <> [] then begin
            ctxt#begin_formal;
            let s = ctxt#mk_bound 0 ctxt#type_inductive in
            let mk_term = ctxt#mk_app csym (List.map (fun (_, getter) -> ctxt#mk_app getter [s]) getters) in
            let fact = ctxt#mk_eq mk_term s in
            ctxt#end_formal;
            ctxt#assume_forall (sn ^ "_injectiveness") [mk_term] [ctxt#type_inductive] fact
          end;
          [(sn, (l, csym, getters, setters, csym_opt))]
        end
    )

  let struct_accessor_map = struct_accessor_map1 @ struct_accessor_map0

  let malloc_block_pred_map1: malloc_block_pred_info map =
    structmap1 |> flatmap begin function
    | (sn, (l, tparams, Some _, _, _)) ->
      [(sn, mk_predfam ("malloc_block_" ^ sn) l tparams 0 [PtrType (StructType (sn, tparams_as_targs tparams))] (Some 1) Inductiveness_Inductive)]
    | _ -> []
    end

  let new_block_pred_map1: new_block_pred_info map =
    match dialect with 
    | Some Cxx ->
      structmap1 |> flatmap begin function
      | (sn, (l, tparams, Some _, _, _)) ->
        let arg = PtrType (StructType (sn, tparams_as_targs tparams)) in
        let args =
          if is_polymorphic_struct sn then [arg; type_info_ptr_type]
          else [arg]
        in
        [sn, mk_predfam ("new_block_" ^ sn) l tparams 0 args (Some 1) Inductiveness_Inductive]
      | _ -> []
    end 
    | _ -> []
  
  let malloc_block_pred_map: malloc_block_pred_info map = malloc_block_pred_map1 @ malloc_block_pred_map0
  let new_block_pred_map: new_block_pred_info map = new_block_pred_map1 @ new_block_pred_map0

  let bases_constructed_map1: bases_constructed_pred_info map =
    let fold acc (sn, (l, tparams, body_opt, _, _)) =
      match body_opt with
      | Some (_ :: _, _, _) -> (sn, mk_predfam (bases_constructed_pred_name sn) l tparams 0 [PtrType (StructType (sn, tparams_as_targs tparams))] (Some 1) Inductiveness_Inductive) :: acc
      | _ -> acc
    in
    structmap1 |> List.fold_left fold [] |> List.rev

  let bases_constructed_map = bases_constructed_map1 @ bases_constructed_map0

  let field_pred_map1 =
    match file_type path with
      Java ->
      classmap1 |> flatmap begin fun (cn, (_,_,_,_, fds,_,_,_,_,_,_,_)) ->
        fds |> List.map begin fun (fn, {fl; ft; fbinding}) ->
          let predfam =
            match fbinding with
              Static -> mk_predfam (cn ^ "_" ^ fn) fl [] 0 [ft] (Some 0) Inductiveness_Inductive
            | Instance -> mk_predfam (cn ^ "_" ^ fn) fl [] 0 [ObjType (cn, []); ft] (Some 1) Inductiveness_Inductive
          in
          ((cn, fn), (predfam, None))
        end
      end
    | _ ->
    flatmap
      (fun (sn, (_, tparams, body_opt, _, _)) ->
         let targs = tparams_as_targs tparams in
         match body_opt with
           None -> []
         | Some (_, fds, _) ->
           List.map
             (fun (fn, (l, gh, t, offset, _)) ->
              ((sn, fn),
               (mk_predfam (sn ^ "_" ^ fn) l tparams 0 [PtrType (StructType (sn, targs)); t] (Some 1) Inductiveness_Inductive,
                match gh with
                  Ghost -> None
                | Real -> Some (mk_predfam (sn ^ "_" ^ fn ^ "_") l tparams 0 [PtrType (StructType (sn, targs)); InductiveType ("option", [t])] (Some 1) Inductiveness_Inductive)
               )
              )
             )
             fds
      )
      structmap1
  
  let field_pred_map = field_pred_map1 @ field_pred_map0
  
  let structpreds1: pred_fam_info map = 
    let map_pred map = map |> List.map @@ fun (_, p) -> p in
    let result = map_pred malloc_block_pred_map1 @ flatmap (function (_, (p, Some p_)) -> [p; p_] | (_, (p, None)) -> [p]) field_pred_map1 @ struct_padding_predfams1 in
    match dialect with
      Some Cxx -> map_pred new_block_pred_map1 @ map_pred bases_constructed_map @ result
    | _ -> result
  
  let predfammap1 =
    let rec iter (pn,ilist) pm ds =
      match ds with
        PredFamilyDecl (l, p, tparams, arity, tes, inputParamCount, inductiveness)::ds -> let p=full_name pn p in
        let ts = List.map (check_pure_type (pn,ilist) tparams Ghost) tes in
        begin
          match try_assoc2' Ghost (pn,ilist) p pm predfammap0 with
            Some (l0, tparams0, arity0, ts0, symb0, inputParamCount0, inductiveness0) ->
            let tpenv =
              match zip tparams0 (List.map (fun tparam -> GhostTypeParam (tparam)) tparams) with
                None -> static_error l "Predicate family redeclarations declares a different number of type parameters." None
              | Some bs -> bs
            in
            let ts0' = List.map (instantiate_type tpenv) ts0 in
            if arity <> arity0 || ts <> ts0' || inputParamCount <> inputParamCount0 || inductiveness <> inductiveness0 then
              static_error l ("Predicate family redeclaration does not match original declaration at '" ^ string_of_loc l0 ^ "'.") None;
            iter (pn,ilist) pm ds
          | None ->
            iter (pn,ilist) (mk_predfam p l tparams arity ts inputParamCount inductiveness::pm) ds
        end
      | _::ds -> iter (pn,ilist) pm ds
      | [] -> List.rev pm
    in
    let rec iter' pm ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest-> iter' (iter (pn,il) pm ds) rest
      | [] -> pm
    in
    iter' (isparamizedfunctypepreds1 @ structpreds1) ps
  
  let (boxmap, predfammap1) =
    let rec iter (pn,ilist) bm pfm ds =
      match ds with
        [] -> (bm, pfm)
      | BoxClassDecl (l, bcn, ps, inv, ads, hpds)::ds -> let bcn= full_name pn bcn in
        if List.mem_assoc bcn pfm || List.mem_assoc bcn purefuncmap0 then static_error l "Box class name clashes with existing predicate name." None;
        let default_hpn = bcn ^ "_handle" in
        if List.mem_assoc default_hpn pfm then static_error l ("Default handle predicate name '" ^ default_hpn ^ "' clashes with existing predicate name.") None;
        let boxpmap =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, x)::ps ->
              if List.mem_assoc x pmap then static_error l "Duplicate parameter name." None;
              if startswith x "old_" then static_error l "Box parameter name cannot start with old_." None;
               if x = "this" then static_error l "Box parameter may not be named \"this\"." None;
              iter ((x, check_pure_type (pn,ilist) [] Ghost te)::pmap) ps
          in
          iter [] ps
        in
        let pfm = mk_predfam bcn l [] 0 (BoxIdType::List.map (fun (x, t) -> t) boxpmap) (Some 1) Inductiveness_Inductive::pfm  in
        let pfm = mk_predfam default_hpn l [] 0 (HandleIdType::BoxIdType::[]) (Some 1) Inductiveness_Inductive::pfm in
        let (pfm, amap) =
          let rec iter pfm amap ads =
            match ads with
              [] -> (pfm, List.rev amap)
            | ActionDecl (l, an, permbased, ps, pre, post)::ads ->
              if List.mem_assoc an amap then static_error l "Duplicate action name." None;
              if permbased && List.length ps > 1 then static_error l "Permission-based actions can have at most one parameter." None; 
              let pmap =
                let rec iter pmap ps =
                  match ps with
                    [] -> List.rev pmap
                  | (te, x)::ps ->
                    if List.mem_assoc x boxpmap then static_error l "Action parameter clashes with box parameter." None;
                    if List.mem_assoc x pmap then static_error l "Duplicate action parameter name." None;
                    if startswith x "old_" then static_error l "Action parameter name cannot start with old_." None;
                    if x = "this" then static_error l "Action parameter may not be named \"this\"." None;
                    iter ((x, check_pure_type (pn,ilist) [] Ghost te)::pmap) ps
                in
                iter [] ps
              in
              let (pfm, action_permission_info) = 
                if not permbased then
                  (pfm, None)
                else begin
                  let nb_action_parameters = List.length ps in
                  let action_permission_pred_name = (bcn ^ "_" ^ an) in
                  if List.mem_assoc action_permission_pred_name pfm || List.mem_assoc action_permission_pred_name purefuncmap0 then static_error l "Action permission name clashes with existing predicate name." None;
                  let action_permission_pred_param_types = BoxIdType :: (List.map (fun (x, t) -> t) pmap) in
                  let action_permission_pred_inputParamCount = Some (1 + nb_action_parameters) in
                  let action_permission_pred = (mk_predfam action_permission_pred_name l [] 0 action_permission_pred_param_types action_permission_pred_inputParamCount) Inductiveness_Inductive in
                  let  (_, (_, _, _, _, action_permission_pred_symb, _, Inductiveness_Inductive)) = action_permission_pred in
                  let (_, _, _, _, is_action_permissionx_symb) = List.assoc ("is_action_permission" ^ (string_of_int nb_action_parameters)) purefuncmap0 in
                  ctxt#assert_term (mk_app is_action_permissionx_symb [action_permission_pred_symb]);
                  if ps = [] then
                    (action_permission_pred :: pfm, Some (action_permission_pred_symb, None))
                  else begin
                    assert (List.length ps = 1);
                    let action_permission_dispenser_pred_name = action_permission_pred_name ^ "_dispenser" in
                    if List.mem_assoc action_permission_dispenser_pred_name pfm || List.mem_assoc action_permission_dispenser_pred_name purefuncmap0 then static_error l "Action permission name clashes with existing predicate name." None;
                    let [(_, action_param_type)] = pmap in 
                    let action_permission_dispenser_pred_param_types = [BoxIdType; InductiveType("list", [action_param_type])] in
                    let action_permission_dispenser_pred_inputParamCount = Some 2 in
                    let action_permission_dispenser_pred = (mk_predfam action_permission_dispenser_pred_name l [] 0  action_permission_dispenser_pred_param_types action_permission_dispenser_pred_inputParamCount Inductiveness_Inductive) in
                    let  (_, (_, _, _, _, action_permission_dispenser_pred_symb, _, _)) = action_permission_dispenser_pred in
                    (* assuming is_action_permission1_dispenser(action_permission_dispenser_pred_symb) *)
                    let (_, _, _, _, is_action_permission1_dispenser_symb) = List.assoc "is_action_permission1_dispenser" purefuncmap0 in
                    ctxt#assert_term (mk_app is_action_permission1_dispenser_symb [action_permission_dispenser_pred_symb]);
                    (* assuming get_action_permission1_for_dispenser(action_permission_dispenser_pred_symb) = action_permission_pred_symb *)
                    let (_, _, _, _, get_action_permission1_for_dispenser_symb) = List.assoc "get_action_permission1_for_dispenser" purefuncmap0 in
                    ctxt#assert_term (ctxt#mk_eq (mk_app get_action_permission1_for_dispenser_symb [action_permission_dispenser_pred_symb]) action_permission_pred_symb);
                    (action_permission_pred :: action_permission_dispenser_pred :: pfm, Some (action_permission_pred_symb, Some action_permission_dispenser_pred_symb))
                  end
                end
              in
              iter pfm ((an, (l, action_permission_info, pmap, pre, post))::amap) ads
          in
          iter pfm [] ads
        in
        let (pfm, hpm) =
          let rec iter pfm hpm hpds =
            match hpds with
              [] -> (pfm, List.rev hpm)
            | HandlePredDecl (l, hpn, ps, extends, inv, pbcs) :: hpds ->
              if List.mem_assoc hpn hpm then static_error l "Duplicate handle predicate name." None;
              if List.mem_assoc hpn pfm then static_error l "Handle predicate name clashes with existing predicate name." None;
              let pmap =
                let rec iter pmap ps =
                  match ps with
                    [] -> List.rev pmap
                  | (te, x)::ps ->
                    if List.mem_assoc x boxpmap then static_error l "Handle predicate parameter clashes with box parameter." None;
                    if List.mem_assoc x pmap then static_error l "Duplicate handle predicate parameter name." None;
                    if startswith x "old_" then static_error l "Handle predicate parameter name cannot start with old_." None;
                    if x = "this" then static_error l "Handle predicate parameter may not be named \"this\"." None;
                    iter ((x, check_pure_type (pn,ilist) [] Ghost te)::pmap) ps
                in
                iter [] ps
              in
              (match extends with 
                None -> ()
              | Some(ehn) -> 
                if not (List.mem_assoc ehn hpm) then static_error l "Extended handle must appear earlier in same box class." None;
                let (el, epmap, extendedInv, einv, epbcs) = List.assoc ehn hpm in
                if (List.length pmap) < (List.length epmap) then static_error l "Extended handle's parameter list must be prefix of extending handle's parameter list." None;
                if not
                (List.for_all2
                  (fun (name1, tp1) (name2, tp2) -> name1 = name2 && tp1 = tp2)
                  (take (List.length epmap) pmap) epmap) 
                then static_error l "Extended handle's parameter list must be prefix of extending handle's parameter list." None;
              );
              iter (mk_predfam hpn l [] 0 (HandleIdType::BoxIdType::List.map (fun (x, t) -> t) pmap) (Some 1) Inductiveness_Inductive::pfm) ((hpn, (l, pmap, extends, inv, pbcs))::hpm) hpds
          in
          iter pfm [] hpds
        in
        iter (pn,ilist) ((bcn, (l, boxpmap, inv, amap, hpm,pn,ilist))::bm) pfm ds
      | _::ds -> iter (pn,ilist) bm pfm ds
    in
    let rec iter' (bm,pfm) ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest-> iter' (iter (pn,il) bm pfm ds) rest
      | [] -> (bm,pfm)
    in
    iter' ([],predfammap1) ps

  let predfammap1, cxx_vtype_map1 =
    match dialect with 
    | Some Cxx ->
      (*
        For each polymorphic struct S create predicate family:
          S_vtype(struct S *; std::type_info *t);  
      *)
      structmap1 |> List.fold_left (fun (pred_fams, vtypes) s ->
        match s with
        | sn, (l, [], Some (_, _, true), _, _) -> 
          let pred = mk_predfam (vtype_pred_name sn) l [] 0 [PtrType (StructType (sn, [])); type_info_ptr_type] (Some 1) Inductiveness_Inductive in
          (pred :: pred_fams), ((sn, pred) :: vtypes)
        | _ -> pred_fams, vtypes
      ) (predfammap1, [])
    | _ -> predfammap1, []
  
  let cxx_vtype_map = cxx_vtype_map1 @ cxx_vtype_map0
  let predfammap = predfammap1 @ predfammap0 (* TODO: Check for name clashes here. *)
  
  let interfmap1 =
    let rec iter_interfs interfmap1_done interfmap1_todo =
      match interfmap1_todo with
        [] -> List.rev interfmap1_done
      | (tn, (li, fields, methods, preds, interfs, pn, ilist, tparams))::interfmap1_todo ->
        let rec iter_preds predmap preds =
          match preds with
            [] -> iter_interfs ((tn, (li, fields, methods, List.rev predmap, interfs, pn, ilist, tparams))::interfmap1_done) interfmap1_todo
          | InstancePredDecl (l, g, ps, body)::preds ->
            if List.mem_assoc g predmap then static_error l "Duplicate predicate name." None;
            let pmap =
              let rec iter pmap ps =
                match ps with
                  [] -> List.rev pmap
                | (tp, x)::ps ->
                  if List.mem_assoc x pmap then static_error l "Duplicate parameter name." None;
                  let tp = check_pure_type (pn,ilist) tparams Real tp in
                  iter ((x, tp)::pmap) ps
              in
              iter [] ps
            in
            let (family, symb) =
              let rec preds_in_itf tn =
                let check_itfmap get_preds_and_itfs itfmap fallback =
                  begin match try_assoc tn itfmap with
                    Some info ->
                    let (preds, itfs) = get_preds_and_itfs info in
                    let itfnames = List.map fst itfs in
                    begin match try_assoc g preds with
                      Some (l, pmap, family, symb) -> [(family, pmap, symb)]
                    | None -> flatmap preds_in_itf itfnames
                    end
                  | None -> fallback ()
                  end
                in
                check_itfmap (function (li, fields, methods, preds, interfs, pn, ilist, tparams) -> (preds, interfs)) interfmap1_done $. fun () ->
                check_itfmap (function InterfaceInfo (li, fields, methods, preds, interfs, tparams) -> (preds, interfs)) interfmap0 $. fun () ->
                []
              in
              match flatmap preds_in_itf (List.map fst interfs) with
                [] -> (tn, get_unique_var_symb (tn ^ "#" ^ g) (PredType ([], [], None, Inductiveness_Inductive)))
              | [(family, pmap0, symb)] ->
                if not (for_all2 (fun (x, t) (x0, t0) -> expect_type_core l "Predicate parameter covariance check" (Some true) t t0; true) pmap pmap0) then
                  static_error l "Predicate override check: parameter count mismatch" None;
                (family, symb)
              | _ -> static_error l "Ambiguous override: multiple overridden predicates" None
            in
            iter_preds ((g, (l, pmap, family, symb))::predmap) preds
        in
        iter_preds [] preds
    in
    iter_interfs [] interfmap1
  
  let classmap1 =
    let rec iter classmap1_done classmap1_todo =
      match classmap1_todo with
        [] -> List.rev classmap1_done
      | (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, tparams, interfs, preds, pn, ilist))::classmap1_todo ->
        let cont predmap = iter ((cn, (lc, abstract, fin, methods, fds_opt, ctors, super, tparams, interfs, List.rev predmap, pn, ilist))::classmap1_done) classmap1_todo in
        let rec iter predmap preds =
          match preds with
            [] -> cont predmap
          | InstancePredDecl (l, g, ps, body)::preds ->
            if List.mem_assoc g predmap then static_error l "Duplicate predicate name." None;
            let pmap =
              let rec iter pmap ps =
                match ps with
                  [] -> List.rev pmap
                | (tp, x)::ps ->
                  if List.mem_assoc x pmap then static_error l "Duplicate parameter name." None;
                  let tp = check_pure_type (pn,ilist) [] Ghost tp in
                  iter ((x, tp)::pmap) ps
              in
              iter [] ps
            in
            let (family, symb) =
              let rec preds_in_itf tn =
                let check_itfmap get_preds_and_itfs itfmap fallback =
                  begin match try_assoc tn itfmap with
                    Some info ->
                    let (preds, itfs) = get_preds_and_itfs info in
                    let itfnames = List.map fst itfs in
                    begin match try_assoc g preds with
                      Some (l, pmap, family, symb) -> [(family, pmap, symb)]
                    | None -> flatmap preds_in_itf itfnames
                    end
                  | None -> fallback ()
                  end
                in
                check_itfmap (function (li, fields, methods, preds, interfs, pn, ilist, tparams) -> (preds, interfs)) interfmap1 $. fun () ->
                check_itfmap (function InterfaceInfo (li, fields, methods, preds, interfs, tparams) -> (preds, interfs)) interfmap0 $. fun () ->
                []
              in
              let rec preds_in_class cn =
                if cn = "" then [] else
                let check_classmap classmap proj fallback =
                  begin match try_assoc cn classmap with
                    Some info ->
                    let ((super, superTargs), interfs, predmap) = proj info in
                    begin match try_assoc g predmap with
                      Some (l, pmap, family, symb, body) -> [(family, pmap, symb)]
                    | None -> preds_in_class super @ flatmap preds_in_itf (List.map fst interfs)
                    end
                  | None -> fallback ()
                  end
                in
                check_classmap classmap1_done
                  (function (lc, abstract, fin, methods, fds_opt, ctors, super, tpenv, interfs, predmap, pn, ilist) -> (super, interfs, predmap))
                  $. fun () ->
                check_classmap classmap0
                  (function {csuper; cinterfs; cpreds} -> (csuper, cinterfs, cpreds))
                  $. fun () ->
                []
              in
              match preds_in_class (fst super) @ flatmap preds_in_itf (List.map fst interfs) with
                (* InstancePredDecl currently does not support coinductive declarations. *)
                [] -> (cn, get_unique_var_symb (cn ^ "#" ^ g) (PredType ([], [], None, Inductiveness_Inductive)))
              | [(family, pmap0, symb)] ->
                if not (for_all2 (fun (x, t) (x0, t0) -> expect_type_core l "Predicate parameter covariance check" (Some true) t t0; true) pmap pmap0) then
                  static_error l "Predicate override check: parameter count mismatch" None;
                (family, symb)
              | _ -> static_error l "Ambiguous override: multiple overridden predicates" None
            in
            iter ((g, (l, pmap, family, symb, body))::predmap) preds
        in
        iter [] preds
    in
    iter [] classmap1

  let cxx_inst_pred_map1_unchecked =
    let rec iter_preds sn ~bases_map ~pred_map ~inst_preds inst_preds_map_done =
      match inst_preds with
      | [] -> List.rev pred_map
      | InstancePredDecl (pred_loc, pred_name, pred_params, pred_body) :: inst_preds ->
        if List.mem_assoc pred_name pred_map then static_error pred_loc "Duplicate predicate name." None;
        let param_map =
          let rec iter param_map params =
            match params with
            | [] -> List.rev param_map
            | (tp, p) :: ps ->
              if List.mem_assoc p param_map then static_error pred_loc "Duplicate parameter name." None;
              let tp = check_pure_type ("", []) [] Ghost tp in
              iter ((p, tp) :: param_map) ps
          in
          iter [] pred_params
        in
        let pred_fam, pred_symb =
          let preds_in_bases bases_map preds_in_struct =
            bases_map |> flatmap @@ fun b -> (b |> fst |> preds_in_struct)
          in
          let rec preds_in_struct sn =
            match try_assoc2 sn cxx_inst_pred_map0 inst_preds_map_done with
            | Some preds ->
              begin match try_assoc pred_name preds with
              | Some (_, params_map, pred_fam, pred_symb, _) ->
                [pred_fam, params_map, pred_symb]
              | None ->
                let _, _, Some (bases_map, _, _), _, _ = List.assoc sn structmap in
                preds_in_bases bases_map preds_in_struct
              end
            | None ->
              []
          in
          match preds_in_bases bases_map preds_in_struct with
          | [] ->
            sn, get_unique_var_symb (sn ^ "#" ^ pred_name) (PredType ([], [], None, Inductiveness_Inductive))
          | [(pred_fam, param_map0, pred_symb)] ->
            if not (for_all2 (fun (x, t) (x0, t0) -> expect_type_core pred_loc "Predicate parameter covariance check." (Some true) t t0; true) param_map param_map0) then
              static_error pred_loc "Predicate override check: parameter count mismatch." None;
            pred_fam, pred_symb
          | _ -> static_error pred_loc "Ambiguous override: multiple overridden predicates." None
        in
        iter_preds sn ~bases_map ~pred_map:((pred_name, (pred_loc, param_map, pred_fam, pred_symb, pred_body)) :: pred_map) ~inst_preds inst_preds_map_done
    in
    let rec iter ~inst_preds inst_preds_map_done =
      match inst_preds with
      | [] -> inst_preds_map_done
      | (sn, inst_preds) :: rest ->
        let _, _, Some (bases_map, _, _), _, _ = List.assoc sn structmap in
        let result = iter_preds sn ~bases_map ~pred_map:[] ~inst_preds inst_preds_map_done in
        iter ~inst_preds:rest ((sn, result) :: inst_preds_map_done)
    in
    iter ~inst_preds:cxx_inst_pred_decl_map []
  
  let (predctormap1, purefuncmap1) =
    let rec iter (pn,ilist) pcm pfm ds =
      match ds with
        PredCtorDecl (l, p, tparams, ps1, ps2, inputParamCount, body)::ds -> let p=full_name pn p in
        begin
          match try_assoc2' Ghost (pn,ilist) p pfm purefuncmap0 with
            Some _ -> static_error l "Predicate constructor name clashes with existing pure function name." None
          | None -> ()
        end;
        begin
          match try_assoc' Ghost (pn,ilist) p predfammap with
            Some _ -> static_error l "Predicate constructor name clashes with existing predicate or predicate family name." None
          | None -> ()
        end;
        check_tparams l [] tparams;
        if List.exists (fun x -> not (tparam_carries_typeid x)) tparams then begin
          if not uppercase_type_params_carry_typeid then
            static_error l "Generic predicate constructor declarations are allowed only if option `uppercase_type_params_carry_typeid` is specified" None
          else
            static_error l "The type parameters of a generic predicate constructor must start with an uppercase letter" None
        end;
        let ps1 =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, x)::ps ->
              begin
                match try_assoc x pmap with
                  Some _ -> static_error l "Duplicate parameter name." None
                | _ -> ()
              end;
              let t = check_pure_type (pn,ilist) tparams Ghost te in
              (* We can assume type parameters contain 'any' in positive positions only because type parameters
                 must carry typeids and therefore must be real Rust types.
                 Real Rust types never contain 'any' in negative positions. *)
              if not (type_satisfies_contains_any_constraint true true t) then static_error (type_expr_loc te) "This type cannot be used as a predicate constructor parameter type because it contains 'any' or a predicate type in a negative position." None;
              iter ((x, t)::pmap) ps
          in
          iter [] ps1
        in
        let ps2 =
          let rec iter psmap pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, x)::ps ->
              begin
                match try_assoc x psmap with
                  Some _ -> static_error l "Duplicate parameter name." None
                | _ -> ()
              end;
              let t = check_pure_type (pn,ilist) tparams Ghost te in
              iter ((x, t)::psmap) ((x, t)::pmap) ps
          in
          iter ps1 [] ps2
        in
        let funcsym = mk_func_symbol p (List.map (fun tparam -> provertype_of_type voidPtrType) tparams @ List.map (fun (x, t) -> provertype_of_type t) ps1) ProverInductive Proverapi.Uninterp in
        (* predicate constructors do not support coinductive predicates yet. *)
        let pf = (p, (l, tparams, PredType ([], List.map (fun (x, t) -> t) ps2, inputParamCount, Inductiveness_Inductive), List.map (fun (x, t) -> (x, t)) ps1, funcsym)) in
        iter (pn,ilist) ((p, (l, tparams, ps1, ps2, inputParamCount, body, funcsym, pn, ilist))::pcm) (pf::pfm) ds
      | [] -> (pcm, pfm)
      | _::ds -> iter (pn,ilist) pcm pfm ds
    in
    let rec iter' (pcm,pfm) ps=
      match ps with
      PackageDecl(l,pn,il,ds)::rest -> iter' (iter (pn,il) pcm pfm ds) rest
      | [] -> (pcm,pfm)
    in
    iter' ([],purefuncmap1) ps
  
  let purefuncmap = purefuncmap1 @ purefuncmap0
  
  (* Region: The type checker *)
  
  let funcnames =
    list_remove_dups
      begin flatmap
        begin fun (PackageDecl (_, pn, _, ds)) ->
          flatmap
            begin function
              (Func (l, (Regular|Lemma(_)), tparams, rt, g, ps, nonghost_callers_only, ft, c, terminates, b, _, _)) -> [full_name pn g]
            | _ -> []
            end
            ds
        end
        ps
      end
  
  let funcnameterms = List.map (fun fn -> (fn, get_unique_var_symb fn (PtrType Void))) funcnames
  let funcnameterms0 = List.map (fun (g, FuncInfo (_, fterm, _, _, _, _, _, _, _, _, _, _, _, _, _, _)) -> (g, fterm)) funcmap0
  let all_funcnameterms = funcnameterms @ funcnameterms0
  
  let check_classname (pn, ilist) (l, c) =
    match search2' Real c (pn,ilist) classmap1 classmap0 with
      None -> static_error l "No such class name." None
    | Some s -> s
  
  let check_classnamelist (pn,ilist) is =
    List.map (check_classname (pn, ilist)) is
  
  let check_funcnamelist is =
    List.map (fun (l, i) -> if not (List.mem i funcnames) then static_error l "No such function name." None; i) is 
  
  let interfmap1 =
    interfmap1 |> List.map begin function (i, (l, fields, meths, preds, supers, pn, ilist, tparams)) ->
      let fieldmap =
        fields |> List.map begin function Field (fl, fgh, ft, f, _, _, _, finit) ->
          let ft = check_pure_type (pn,ilist) [] Real ft in
          (f, {fl; fgh; ft; fvis=Public; fbinding=Static; ffinal=true; finit; fvalue=ref None})
        end
      in
      (i, (l, fieldmap, meths, preds, supers, pn, ilist, tparams))
    end
  
  let rec lookup_class_field (cn, targs) fn =
    let instantiate_type_params {fl; fgh; ft; fvis; fbinding; ffinal; finit; fvalue} tparams = 
      let targenv = zip tparams targs in 
      match targenv with
        None -> {fl; fgh; ft; fvis; fbinding; ffinal; finit; fvalue} (* Can happen in a static context *)
      | Some(targenv) -> {fl; fgh; ft = replace_type dummy_loc targenv ft; fvis; fbinding; ffinal; finit; fvalue}
    in
    let replace_super_targs tparams (super, superTargs) =
      let tpenv = match zip tparams targs with
        None -> [] (* Static field, or no targs. *)
      | Some (tpenv) -> tpenv 
      in
      match tpenv with
        [] -> (super, superTargs)
      | tpenv -> (super, List.map (replace_type dummy_loc tpenv) superTargs) 
    in
    let field_in_super tparams supers = head_flatmap_option (fun super -> lookup_class_field (replace_super_targs tparams super) fn) supers in
    match try_assoc cn classmap1 with
      Some (_, _, _, _, fds, _, super, tparams, itfs, _, _, _) ->
      begin match try_assoc fn fds with
        None when cn = "java.lang.Object" -> None
      | Some f -> Some (instantiate_type_params f tparams, cn)
      | None ->
      match lookup_class_field (replace_super_targs tparams super) fn with
        Some _ as result -> result
      | None ->
      field_in_super tparams itfs
      end
    | None -> 
    match try_assoc cn classmap0 with
      Some {cfds; csuper; cinterfs; ctpenv} ->
      begin match try_assoc fn cfds with
        None when cn = "java.lang.Object" -> None
      | Some f -> Some (instantiate_type_params f ctpenv, cn)
      | None ->
      match lookup_class_field (replace_super_targs ctpenv csuper) fn with
        Some _ as result -> result
      | None ->
      field_in_super ctpenv cinterfs
      end
    | None ->
    match try_assoc cn interfmap1 with
      Some (_, fds, _, _, supers, _, _, tparams) ->
      begin match try_assoc fn fds with
        Some f -> Some (instantiate_type_params f tparams, cn)
      | None ->
      field_in_super tparams supers
      end
    | None ->
    match try_assoc cn interfmap0 with
      Some (InterfaceInfo (_, fds, _, _, supers, tparams)) ->
      begin match try_assoc fn fds with
        Some f -> Some (instantiate_type_params f tparams, cn)
      | None ->
      field_in_super tparams supers
      end
    | None ->
    None

  let is_package x =
    let x = x ^ "." in
    let has_package map = List.exists (fun (cn, _) -> startswith cn x) map in
    has_package classmap1 || has_package classmap0 || has_package interfmap1 || has_package interfmap0
  
  let current_class = "#currentClass"
  
  let string_of_operator op =
    match op with
      Eq -> "eq"
    | Neq -> "neq"
    | Lt -> "lt"
    | Le -> "le"
    | Gt -> "gt"
    | Ge -> "ge"
    | Add -> "add"
    | Sub -> "sub"
    | Mul -> "mul"
    | Div -> "div"
  
  let identifier_string_of_type t =
    match t with
      Float -> "float"
    | Double -> "double"
    | LongDouble -> "long_double"
    | Int (_, FixedWidthRank _) -> string_of_type t
    | RealType -> "real"
  
  let floating_point_fun_call_expr funcmap l t fun_name args =
    let prefix = identifier_string_of_type t in
    if language = Java then
      let className = "verifast.internal.FloatingPoint" in
      let methodName = prefix ^ "_" ^ fun_name in
      let signature = List.map (function (TypedExpr (e, t)) -> t) args in
      begin match try_assoc className classmap0 with
        None -> static_error l ("Internal error: class '" ^ className ^ "' not found") None
      | Some {cmeths} ->
        if not (List.mem_assoc (methodName, signature) cmeths) then
          static_error l (Printf.sprintf "Internal error: no method '%s(%s)' found in class '%s'" methodName (String.concat ", " (List.map string_of_type signature)) className) None
      end;
      WMethodCall (l, className, methodName, signature, args, Static, [])
    else
    let g = "vf__" ^ prefix ^ "_" ^ fun_name in
    if funcmap == [] then static_error l "Cannot perform this floating-point operation in an annotation" None;
    if not (List.mem_assoc g funcmap) then static_error l (Printf.sprintf "Must include header <math.h> when using floating-point operations. (Pseudo-function %s not found.)" g) None;
    WFunCall (l, g, [], args, Static)
  
  let operation_expr funcmap l t operator arg1 arg2 =
    match t with
      Float|Double|LongDouble ->
      floating_point_fun_call_expr funcmap l t (string_of_operator operator) [TypedExpr (arg1, t); TypedExpr (arg2, t)]
    | _ -> WOperation (l, operator, [arg1; arg2], t)
  
  let next_temp_var_name =
    let counter = ref 0 in
    fun () -> let n = !counter in incr counter; Printf.sprintf "#x%d" n
  
  let wintlit l n = WIntLit (l, n)

  let rank_ordinal r =
    match r with
      FixedWidthRank 0 -> 0
    | CharRank -> 1
    | FixedWidthRank 1 -> 2
    | ShortRank -> 3
    | FixedWidthRank 2 -> 4
    | IntRank -> 4
    | PtrRank -> 5
    | LongRank -> 5
    | FixedWidthRank 3 -> 6
    | LongLongRank -> 7
    | FixedWidthRank k -> k + 4

  let integer_promotion l t = (* C11 6.3.1.1 *)
    if dialect = Some Rust then t else
    match t with
    | Int (Signed, k) -> if width_le dummy_loc (width_of_rank k) int_width then intType else t
    | Int (Unsigned, k) -> if definitely_width_lt (width_of_rank k) int_width then intType else if width_le dummy_loc int_width (width_of_rank k) then t else static_error l "Computing the type of this expression involves an integer promotion whose result depends on the target architecture. This is not supported by VeriFast. Insert casts or specify a target (using the -target command-line option) to work around this problem." None

  let usual_arithmetic_conversion inAnnotation l t1 t2 = (* C11 6.3.1.8 *)
    let signed_unsigned t1 t2 n1 n2 =
      if width_le l (width_of_rank n1) (width_of_rank n2) then
        t2
      else if definitely_width_lt (width_of_rank n2) (width_of_rank n1) then
        t1
      else
        static_error l "When computing the type of this expression, the result of the usual arithmetic conversions may depend on the target architecture. This is not supported by VeriFast. Insert casts or specify a target (using the -target command-line option) to work around this problem." None
    in
    match t1, t2 with
      LongDouble, _ | _, LongDouble -> LongDouble
    | Double, _ | _, Double -> Double
    | Float, _ | _, Float -> Float
    | RealType, _ | _, RealType -> RealType
    | t1, t2 ->
      match inAnnotation with Some true -> intType | _ ->
      let t1 = integer_promotion l t1 in
      let t2 = integer_promotion l t2 in
      match t1, t2 with
        Int (Signed, n1), Int (Unsigned, n2) -> signed_unsigned t1 t2 n1 n2
      | Int (Unsigned, n1), Int (Signed, n2) -> signed_unsigned t2 t1 n2 n1
      | Int (s, n1), Int (_, n2) -> Int (s, if width_le l (width_of_rank n1) (width_of_rank n2) then n2 else n1)

  let get_glb_litwidth width =
    match width with
      LitWidth k -> k, true
    | IntWidth|PtrWidth -> 1, false
    | LongWidth -> 2, false

  let rec super_types (ObjType (cn, targs)) =
    let supers =
      if cn = "java.lang.Object" then
        []
      else
        direct_supers (ObjType (cn, targs))
    in
    flatmap (fun s -> s::super_types s) supers

  (* calculates the shared supertype that is more specific than any other shared supertype *)
  let least_upper_bound l tps =
    match tps with
      [t] -> [t]
    | [] -> failwith "calculating least upper bound of no type"
    | tps -> 
      let st_map = List.map (fun tp -> (tp, tp::super_types tp)) tps in
      let filtered_candidate_set = (*intersection of all est sets *)
        let intersection setA setB = List.filter (fun memA -> List.mem memA setB) setA in
        List.fold_left intersection (snd (List.hd st_map)) (List.map snd st_map)
      in
      (* MEC = { V | V in EC, and for all W ≠ V in EC, it is NOT the case that W <: V } *)
      let mec = filtered_candidate_set |> List.filter begin fun v -> (* V in EC *)
        not begin filtered_candidate_set |> List.exists begin fun w ->  (* for every V, select all it's children in EC that are not V *)
            if (w = v) then   
              false
            else
              is_subtype_of_ w v
          end
        end
      end
      in
      mec 

  exception InferenceError of loc * string
  let inference_error l msg = raise (InferenceError (l, msg))

  (* Assigning the assigned types to the inferred types *)
  let infer_type l inferredTypes assignedTypes =
    let rec inference_set set actual expected = 
      match (actual, expected) with 
        (hd::tl, hd0::tl0) -> begin match (hd,hd0) with
        | (ObjType (t, targs), ObjType (t0, targs0)) when t != "null" && t0 != "null" ->
          if proper_type hd && proper_type hd0 then
            inference_set set tl tl0
          else if t != t0 then
            let matchingSuper = (super_types hd0) |> List.filter (fun (ObjType (st, _)) -> st = t) in
            match matchingSuper with
              [] -> inference_error l ("Type mismatch during inference, " ^ t0 ^ " is not a sub type of: " ^ t ^ ".")
            | [(ObjType (st, stargs))] -> inference_set set (targs@tl) (stargs@tl0)
          else if List.length targs != List.length targs0 then
            inference_error l ("Type mismatch during inference, amount of type arguments does not match. Unknown type: " ^ string_of_type hd ^ ". Matching type: " ^ string_of_type hd0 ^ ".")
          else
            inference_set set (targs@tl) (targs0@tl0)
        | (InferredRealType t, ArrayType _) ->
          inference_error l ("No inference for arrays yet.")
        | (InferredRealType t, t0) ->
          if is_primitive_type t0 then
            inference_error l ("Can't infer primitive types yet, no boxing supported.")
          else
            inference_set ((t,t0)::set) tl tl0
        | (ArrayType t, ArrayType t0) ->
          inference_set set (t::tl) (t0::tl0)
        | _ -> inference_set set tl tl0
        end
      | _ -> set
    in
    let binds = inference_set [] inferredTypes assignedTypes in
    let rec infvars binds vs =
      match binds with
        (infvar,tp)::tl ->
          if List.mem infvar vs then
            infvars tl vs
          else
            infvars tl (infvar::vs)
      | [] -> vs
    in
    let setPerInfVar = (infvars binds []) |> List.map begin fun infvar -> 
      (infvar, List.map snd (List.filter (fun (n,tp) -> n = infvar) binds))
    end
    in
    setPerInfVar |> List.map begin fun (infvar, tps) ->
      let inferred = match least_upper_bound l tps with
          [] -> inference_error l "Inference not resolved."
        | [f] -> f
        | s -> inference_error l "Inference would resolve to multiple types. Not supported yet!"
      in
      (infvar, inferred)
    end


  let rec check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (inAnnotation: bool option) e: (expr (* typechecked expression *) * type_ (* expression type *) * big_int option (* constant integer expression => value*)) =
    let (w, t, v) = check_expr_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e in
    let t = unfold_inferred_type t in
    let t =
      match t with
        StaticArrayType (elemTp, s) when not is_rust -> PtrType elemTp
      | _ -> t
    in
    (w, t, v)
  and check_expr_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (inAnnotation: bool option) e: (expr (* typechecked expression *) * type_ (* expression type *) * big_int option (* constant integer expression => value*)) =
    let check e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e in
    let check_with_extra_bindings tenv' e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams (tenv' @ tenv) inAnnotation e in
    let checkcon e = check_condition_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e in
    let checkt e t0 = check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e t0 false in
    let checkt_cast e t0 = 
      (*if (file_type path = Java) then
        let (w, et) = check e in
        (match (t0, et) with
          ((Char | ShortType | IntType), (Char | ShortType | IntType)) -> w
        | (ObjType "object", (ObjType (_) | ArrayType(_))) -> w (* stupid-cast *)
        | ((ObjType (_) | ArrayType(_)), ObjType "object") -> w
        | (ObjType(_), ObjType(_)) -> w
        | _ -> static_error (expr_loc e) (sprintf "illegal cast to %s from %s" (string_of_type t0) (string_of_type et)))
      else *)
        check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e t0 true in
    let rec get_methods tn mn =
      let erase_sign sign = List.map erase_type sign in
      let remove_overrides declared_methods inherited_methods =
        let inherited_method_erased = List.map (fun (sign, info) -> (sign, erase_sign sign, info)) inherited_methods in
        let declared_methods_erased = List.map (fun (sign, info) -> (erase_sign sign, info)) declared_methods in
        List.map (fun (sign, _, info) -> (sign, info))  
          (List.filter (fun (sign, erased_sign, info) -> not (List.mem_assoc erased_sign declared_methods_erased)) inherited_method_erased) in
      if tn = "" then [] else
      match try_assoc tn classmap with
        Some {cmeths; csuper=(csuper, _); cinterfs} ->
        let inherited_methods =
          get_methods csuper mn @ flatmap (fun ifn -> get_methods ifn mn) (List.map fst cinterfs)
        in
        let declared_methods =
          flatmap
            begin fun ((mn', sign), MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, fb, v, is_override, abstract, mtparams)) ->
              if mn' = mn then [(sign, (tn, lm, gh, rt, xmap, pre_dyn, post_dyn, epost_dyn, terminates, fb, v, abstract, mtparams))] else []
            end
            cmeths
        in
        declared_methods @ (remove_overrides declared_methods inherited_methods)
      | None ->
      let InterfaceInfo (_, fields, meths, _, interfs, _) = List.assoc tn interfmap in
      let declared_methods = flatmap
        begin fun ((mn', sign), ItfMethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, terminates, v, abstract, mtparams)) ->
          if mn' = mn then [(sign, (tn, lm, gh, rt, xmap, pre, post, epost, terminates, Instance, v, abstract, mtparams))] else []
        end
        meths
      in
      let inherited_methods = flatmap (fun ifn -> get_methods ifn mn) (List.map fst interfs) in
      declared_methods @ (remove_overrides declared_methods inherited_methods)
    in
    (*
     * Docs: see "promote_checkdone"
     *)
    let promote_numeric_checkdone l e1 e2 check_e1 check_e2 =
      let (w1, t1, _) = check_e1 in
      let (w2, t2, _) = check_e2 in
      match (t1, t2) with
        (t1, t2) when is_arithmetic_type t1 && is_arithmetic_type t2 ->
        let t = usual_arithmetic_conversion inAnnotation l t1 t2 in
        let w1 = if t1 = t then w1 else checkt e1 t in
        let w2 = if t2 = t then w2 else checkt e2 t in
        (w1, w2, t)
      | (t1, t2) ->
        let w2 = checkt e2 t1 in
        (w1, w2, t1)
    in
    (*
     * Precondition: "check e1" has already been executed and its result is
     *   in check_e1. Analogues for check_e2.
     *   This precondition avoids having the implementation call "check e2",
     *   which avoids a quadratic time complexity for typechecking e.g.
     *   "1+1+1+1+1+...+1".
     *
     * If you add support for promoting to unsigned int, be sure to
     * insert a cast to enable overflow/underflow-checking.
     *)
    let promote_checkdone l e1 e2 check_e1 check_e2 =
      match promote_numeric_checkdone l e1 e2 check_e1 check_e2 with
        (w1, w2, PtrType _) as result -> result
      | (w1, w2, t) as result when is_arithmetic_type t -> result
      | _ -> static_error l "Expression of arithmetic or pointer type expected." None
    in
    let promote_numeric l e1 e2 =
      promote_numeric_checkdone l e1 e2 (check e1) (check e2)
    in
    let promote l e1 e2 =
      promote_checkdone l e1 e2 (check e1) (check e2)
    in
    let perform_integral_promotion e =
      let (w, t, _) = check e in
      match t with
        Int (Signed, k) -> if width_le dummy_loc (width_of_rank k) int_width then Upcast (w, t, intType), intType else w, t
      | Int (Unsigned, k) -> if definitely_width_lt (width_of_rank k) int_width then Upcast (w, t, intType), intType else if width_le dummy_loc int_width (width_of_rank k) then w, t else static_error (expr_loc e) "The promoted type of this expression depends on the target architecture. This is not supported by VeriFast. Insert a cast or specify the target (using the -target command-line option) to work around this problem." None
      | _ -> static_error (expr_loc e) "Expression must be of integral type" None
    in
    let check_pure_fun_value_call l w t es =
      if es = [] then static_error l "Zero-argument application of pure function value makes no sense." None;
      let box e t = convert_provertype_expr e (provertype_of_type t) ProverInductive in
      let unbox e t = convert_provertype_expr e ProverInductive (provertype_of_type t) in
      let (ws, tp) =
        let rec apply ws t es =
          match (es, t) with
            ([], t) -> (List.rev ws, t)
          | (e::es, PureFuncType (t1, t2)) -> apply (box (checkt e t1) t1::ws) t2 es
          | (e::es, _) -> static_error l "Too many arguments" None
        in
        apply [] t es
      in
      (unbox (WPureFunValueCall (l, w, ws)) tp, tp, None)
    in
    match e with
      True l -> (e, boolt, None)
    | False l -> (e, boolt, None)
    | Null l -> (e, ObjType ("null", []), None)
    | Var (l, x) ->
      begin
      match try_assoc x tenv with
      | Some(RefType(t)) -> (WDeref (l, WVar (l, x, LocalVar), t), t, None)
      | Some t -> (WVar (l, x, LocalVar), t, None)
      | None ->
      begin fun cont ->
      if language <> Java then cont () else
      let field_of_this =
        match try_assoc "this" tenv with
        | Some ObjType (cn, targs) ->
          begin match lookup_class_field (cn, targs) x with
            None -> None
          | Some ({fgh; ft; fbinding; ffinal; fvalue}, fclass) ->
            let constant_value =
              if ffinal then
                match !fvalue with
                  Some(Some(IntConst(i))) -> Some(i)
                | _ -> None
              else
                None
            in
            Some (WRead (l, WVar (l, "this", LocalVar), fclass, [], x, ft, [], fbinding = Static, fvalue, fgh), ft, constant_value)
          end
        | _ -> None
      in
      match field_of_this with
        Some result -> result
      | None ->
      let field_of_class =
        match try_assoc current_class tenv with
          None -> None
        | Some (ClassOrInterfaceName cn) ->
          match lookup_class_field (cn, []) x with
            None -> None
          | Some ({fgh; ft; fbinding; ffinal; fvalue}, fclass) ->
            if fbinding <> Static then static_error l "Instance field access without target object" None;
            let constant_value =
              if ffinal then
                match !fvalue with
                  Some(Some(IntConst(i))) -> Some(i)
                | _ -> None
              else
                None
            in
            Some (WRead (l, WVar (l, current_class, LocalVar), fclass, [], x, ft, [], true, fvalue, fgh), ft, constant_value)
      in
      match field_of_class with
        Some result -> result
      | None ->
      match resolve Real (pn,ilist) l x classmap1 with
        Some (cn, (ld, _, _, _, _, _, _, _, _, _, _, _)) ->
        reportUseSite DeclKind_Class ld l;
        (WVar (l, x, ClassOrInterfaceNameScope), ClassOrInterfaceName cn, None)
      | None ->
      match resolve Real (pn,ilist) l x interfmap1 with
        Some (cn, (ld, _, _, _, _, _, _, _)) ->
        reportUseSite DeclKind_Interface ld l;
        (WVar (l, x, ClassOrInterfaceNameScope), ClassOrInterfaceName cn, None)
      | None ->
      match resolve Real (pn,ilist) l x classmap0 with
        Some (cn, {cl}) ->
        reportUseSite DeclKind_Class cl l;
        (WVar (l, x, ClassOrInterfaceNameScope), ClassOrInterfaceName cn, None)
      | None ->
      match resolve Real (pn,ilist) l x interfmap0 with
        Some (cn, InterfaceInfo (ld, _, _, _, _, _)) ->
        reportUseSite DeclKind_Interface ld l;
        (WVar (l, x, ClassOrInterfaceNameScope), ClassOrInterfaceName cn, None)
      | None ->
      if is_package x then begin
        (WVar (l, x, PackageNameScope), PackageName x, None)
      end else
        cont ()
      end $. fun () ->
      let check_pure_func_name (x, (ld, tparams, t, param_names_types, _)) =
        reportUseSite DeclKind_PureFunction ld l;
        let (_, pts) = List.split param_names_types in
        let (typeid_types, pts, t) =
          if tparams = [] then
            ([], pts, t)
          else begin
            let tpenv = List.map (fun x -> (x, InferredType (object end, ref Unconstrained))) tparams in
            let typeid_types = tpenv |> flatmap @@ fun (x, tp) -> if tparam_carries_typeid x then [tp] else [] in
            (typeid_types, List.map (instantiate_type tpenv) pts, instantiate_type tpenv t)
          end
        in
        (WVar (l, x, PureFuncName typeid_types), List.fold_right (fun t1 t2 -> PureFuncType (t1, t2)) pts t, None)
      in
      match resolve Ghost (pn,ilist) l x purefuncmap with
      | Some ((x, (ld, tparams, t, [], _)) as entry) -> check_pure_func_name entry
      | _ ->
      match try_assoc x all_funcnameterms with
        Some fterm when language = CLang ->
        (WVar (l, x, FuncName), PtrType Void, None)
      | None ->
      match resolve Ghost (pn,ilist) l x predfammap with
      | Some (x, (ld, tparams, arity, ts, _, inputParamCount, inductiveness)) ->
        reportUseSite DeclKind_Predicate ld l;
        if arity <> 0 then static_error l "Using a predicate family as a value is not supported." None;
        if tparams <> [] then static_error l "Using a predicate with type parameters as a value is not supported." None;
        (WVar (l, x, PredFamName), PredType (tparams, ts, inputParamCount, inductiveness), None)
      | None ->
      match try_assoc x enummap with
      | Some i ->
        (WVar (l, x, EnumElemName i), intType, None)
      | None ->
      match try_assoc' Real (pn, ilist) x globalmap with
      | Some ((ld, tp, symbol, init)) ->
        reportUseSite DeclKind_GlobalVar ld l;
        (WVar (l, x, GlobalName), tp, None)
      | None -> 
      match try_assoc x modulemap with
      | Some _ when language <> Java -> (WVar (l, x, ModuleName), intType, None)
      | _ ->
      match resolve Ghost (pn,ilist) l x purefuncmap with
        Some entry -> check_pure_func_name entry
      | None ->
      if language = Java then
        static_error l ("No such variable, field, class, interface, package, inductive datatype constructor, or predicate: " ^ x) None
      else
        static_error l ("No such variable, constructor, regular function, predicate, enum element, global variable, or module: " ^ x) None
      end
    | PredNameExpr (l, g) ->
      begin
        match resolve Ghost (pn,ilist) l g predfammap with
          Some (g, (ld, tparams, arity, ts, _, inputParamCount, inductiveness)) ->
          reportUseSite DeclKind_Predicate ld l;
          if arity <> 0 then static_error l "Using a predicate family as a value is not supported." None;
          if tparams <> [] then static_error l "Using a predicate with type parameters as a value is not supported." None;
          (PredNameExpr (l, g), PredType (tparams, ts, inputParamCount, inductiveness), None)
        | None -> static_error l "No such predicate." None
      end
    | TruncatingExpr (l, e) ->
      let (w, t, _) = check e in
      begin match t with
        Int (_, _) -> ()
      | _ -> static_error l "Keyword 'truncating' applies only to expressions of integer type" None
      end;
      (TruncatingExpr (l, w), t, None)
    | Operation (l, (MinValue tp | MaxValue tp as operator), []) ->
      (WOperation (l, operator, [], tp), tp, None)
    | Operation (l, (Eq | Neq as operator), [e1; e2]) -> 
      let (w1, w2, t) = promote_numeric l e1 e2 in
      if inAnnotation = Some true then
        (WOperation (l, operator, [w1; w2], t), boolt, None)
      else
        (operation_expr funcmap l t operator w1 w2, boolt, None)
    | Operation (l, (Or | And as operator), [e1; e2]) -> 
      let w1 = checkcon e1 in
      let w2 = checkcon e2 in
      (WOperation (l, operator, [w1; w2], boolt), boolt, None)
    | Operation (l, Not, [e]) -> 
      let w = checkcon e in
      (WOperation (l, Not, [w], boolt), boolt, None)
    | Operation (l, (BitAnd|BitOr|BitXor|Mod as operator), [e1; e2]) ->
      let (w1, w2, t) = promote l e1 e2 in
      begin match t with
        Int (_, _) ->
        (WOperation (l, operator, [w1; w2], t), t, None)
      | _ -> static_error l "Arguments must be of integral type." None
      end
    | Operation (l, BitNot, [e]) ->
      let w, t = perform_integral_promotion e in
      (WOperation (l, BitNot, [w], t), t, None)
    | Operation (l, (Le | Lt | Ge | Gt as operator), [e1; e2]) -> 
      let (w1, w2, t) = promote l e1 e2 in
      (operation_expr funcmap l t operator w1 w2, boolt, None)
    | Operation (l, (Add | Sub as operator), [e1; e2]) ->
      let (w1, t1, value1) = check e1 in
      let (w2, t2, value2) = check e2 in
      begin match t1, t2 with
        PtrType pt1, PtrType pt2 when operator = Sub ->
        if pt1 <> pt2 then static_error l "Pointers must be of same type" None;
        if pt1 <> charType && pt1 <> Void then static_error l "Subtracting non-char pointers is not yet supported" None;
        (WOperation (l, PtrDiff, [w1; w2], t1), ptrdiff_t, None)
      | PtrType pt1, _ ->
        let (w2, t2, _) = check e2 in
        begin match t2 with Int (_, _) -> () | _ -> static_error l "Second operand must be of integer type." None end;
        (WOperation (l, operator, [w1; w2], t1), t1, None)
      | t1, t2 when is_arithmetic_type t1 && is_arithmetic_type t2 ->
        let (w1, w2, t) = promote_checkdone l e1 e2 (w1, t1, value1) (w2, t2, value2) in
        let value =
          match t with
            Int (_, _) ->
            begin match (value1, value2, operator) with
              (Some value1, Some value2, Add) -> Some (add_big_int value1 value2)
            | (Some value1, Some value2, Sub) -> Some (sub_big_int value1 value2)
            | _ -> None
            end
          | _ -> None
        in
        (operation_expr funcmap l t operator w1 w2, t, value)
      | (ObjType ("java.lang.String", []) as t, _) when operator = Add ->
        let w2 = checkt e2 t in
        (WOperation (l, operator, [w1; w2], t), t, None)
      | _ -> static_error l ("Operand of addition or subtraction must be pointer, integer, char, short, or real number. Actual operand types: " ^ string_of_type t1 ^ ", " ^ string_of_type t2) None
      end
    | Operation (l, (Mul|Div as operator), [e1; e2]) ->
      let (w1, w2, t) = promote l e1 e2 in
      begin match t with PtrType _ -> static_error l "Operands should be arithmetic expressions, not pointer expressions" None | _ -> () end;
      (operation_expr funcmap l t operator w1 w2, t, None)
    | Operation (l, (ShiftLeft | ShiftRight as op), [e1; e2]) ->
      let w1, t1 = perform_integral_promotion e1 in
      let w2, _ = perform_integral_promotion e2 in
      (WOperation (l, op, [w1; w2], t1), t1, None)
    | IntLit (l, n, is_decimal, usuffix, lsuffix) ->
      if inAnnotation = Some true then
        (wintlit l n, intt, Some n)
      else if language = Java then
        let type_, value =
          match lsuffix with
            NoLSuffix ->
            intt,
            if is_decimal then
              if le_big_int (min_signed_big_int 2) n && le_big_int n (max_signed_big_int 2) then
                n
              else
                static_error l "Integer literal out of range" None
            else
              if le_big_int n (max_signed_big_int 2) then n else
              if lt_big_int (max_unsigned_big_int 2) n then static_error l "Integer literal too large" None else
              sub_big_int n (succ_big_int (max_unsigned_big_int 2))
          | LSuffix ->
            java_long_type,
            if is_decimal then
              if le_big_int (min_signed_big_int 3) n && le_big_int n (max_signed_big_int 3) then
                n
              else
                static_error l "Integer literal out of range" None
            else
              if le_big_int n (max_signed_big_int 3) then n else
              if lt_big_int (max_unsigned_big_int 3) n then static_error l "Integer literal too large" None else
              sub_big_int n (succ_big_int (max_unsigned_big_int 3))
        in (wintlit l value, type_, Some value)
      else
        let type_ =
          let rec iter ranks =
            match ranks with
              [] -> static_error l "Integer literal out of range" None
            | (rank, k)::ranks ->
              if not usuffix && le_big_int (min_signed_big_int k) n && le_big_int n (max_signed_big_int k) then
                Int (Signed, rank)
              else if (usuffix || not is_decimal) && le_big_int n (max_unsigned_big_int k) then
                Int (Unsigned, rank)
              else
                iter ranks
          in
          let ranks_of int_k long_k =
            match lsuffix with
              NoLSuffix -> [IntRank, int_k; LongRank, long_k; LongLongRank, 3; FixedWidthRank 4, 4]
            | LSuffix -> [LongRank, long_k; LongLongRank, 3; FixedWidthRank 4, 4]
            | LLSuffix -> [LongLongRank, 3; FixedWidthRank 4, 4]
          in
          match data_model with
            Some {int_width; long_width} ->
            iter (ranks_of int_width long_width)
          | None ->
            let rank1 = iter (ranks_of 1 2) in
            let rank2 = iter (ranks_of 2 3) in
            if rank1 <> rank2 then
              static_error l "This expression's type depends on the target architecture. Such expressions are not supported by VeriFast. Add a suffix (U or (U)L or LL) or specify the target architecture (using the -target command-line option) to work around this problem." None
            else
              rank1
        in
          (wintlit l n, type_, Some n)
    | RealLit(l, n, suffix) ->
      if inAnnotation = Some true then
        (e, RealType, None)
      else
        let tp =
          match suffix with
            None -> Double
          | Some FloatFSuffix -> Float
          | Some FloatLSuffix -> LongDouble
        in
        (floating_point_fun_call_expr funcmap l tp "of_real" [TypedExpr (e, RealType)], tp, None)
    | ClassLit (l, s) ->
      let s = check_classname (pn, ilist) (l, s) in
      (ClassLit (l, s), ObjType ("java.lang.Class", []), None)
    | Typeid (l, TypeExpr te) ->
      let t = check_pure_type (pn, ilist) tparams Real te in
      let t = 
        match t with 
        | RefType t -> t
        | _ -> t
      in
      TypeInfo (l, t), type_info_ref_type, None
    | StringLit (l, s) ->
      if inAnnotation = Some true then
        (* TODO: Do the right thing for non-ASCII characters *)
        let cs = chars_of_string s in
        let es = List.map (fun c -> None, IntLit(l, big_int_of_int (Char.code c), true, false, NoLSuffix)) cs in
        check (InitializerList (l, es))
      else
        begin match language with
          Java-> (e, ObjType ("java.lang.String", []), None)
        | _ -> (e, PtrType (if dialect = Some Rust then u8Type else charType), None)
        end
    | CastExpr (l, (StructTypeExpr (_, _, _, _, _) as te), InitializerList (linit, es)) ->
      let t = check_pure_type (pn,ilist) tparams Ghost te in
      let StructType (sn, targs) = t in
      let (_, s_tparams, Some (_, fds, _), _, _) = List.assoc sn structmap in
      let s_tpenv = List.combine s_tparams targs in
      let bs =
        let rec iter fds_todo next_fds es =
          match es with
            [] ->
            begin match fds_todo with
              [] -> []
            | (f, _)::_ -> static_error l (Printf.sprintf "Initializer does not initialize field '%s'" f) None
            end
          | (None, e)::es ->
            begin match next_fds with
              [] -> static_error (expr_loc e) "There is no next field; specify a field name" None
            | ((f, _) as fd)::next_fds ->
              if List.mem_assoc f fds_todo then
                (fd, e)::iter (List.remove_assoc f fds_todo) next_fds es
              else
                static_error (expr_loc e) (Printf.sprintf "Duplicate initializer for field '%s'" f) None
            end
          | (Some (lf, f), e)::es ->
            if List.mem_assoc f fds_todo then
              let next_fds = List.tl (drop_while (fun (f', _) -> f' <> f) fds) in
              ((f, List.assoc f fds_todo), e)::iter (List.remove_assoc f fds_todo) next_fds es
            else if List.mem_assoc f fds then
              static_error lf (Printf.sprintf "Duplicate initializer for field '%s'" f) None
            else
              static_error lf "No such field" None
        in
        iter fds fds es
      in
      let ws = bs |> List.map begin fun ((f, (_, _, tp, _, _)), e) ->
          let tp' = instantiate_type s_tpenv tp in
          (Some (l, f), checkt e tp')
        end
      in
      (CastExpr (l, ManifestTypeExpr (type_expr_loc te, t), InitializerList (linit, ws)), t, None)
    | CastExpr (l, te, e) ->
      let t = check_pure_type (pn,ilist) tparams Ghost te in
      let w = checkt_cast e t in
      (CastExpr (l, ManifestTypeExpr (type_expr_loc te, t), w), t, None)
    | TypedExpr (w, t) ->
      (w, t, None)
    | Read (l, e, f) ->
      check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv e f
    | ActivatingRead (l, e, f) ->
      let (w, t, _) = check e in
      begin match t with
        PtrType (UnionType un) ->
        check_union_member_deref l w un f true
      | _ -> static_error l "Pointer to union expected" None
      end
    | Select (l, ((CxxDerivedToBase (le, _, StructTypeExpr _)) as e), f) ->
      (*
        Select a base object field.
        Objects in C++ are treated as RefType objects, 
        which is why we have to take the address of the expression because it gets dereferenced by default.
      *)
      let e = make_addr_of le e in
      check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv e f
    | Select (l, e, f) ->
      let (w, t, _) = check e in
      begin match w with
      | WVar (_, _, GlobalName) | WDeref (_, _, _) | WReadArray (_, _, _, _) ->
        check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv (AddressOf (l, e)) f
      | _ ->
        begin match t with
        | StructType (sn, targs) ->
          begin match try_assoc sn structmap with
          | Some (_, tparams, Some (_, fds, _), _, _) ->
            begin match try_assoc f fds with
            | None -> static_error l ("No such field in struct '" ^ sn ^ "'.") None
            | Some (_, gh, t, offset, _) ->
              let w = WSelect (l, w, sn, tparams, f, t, targs) in
              (w, instantiate_type (List.combine tparams targs) t, None)
            end
          | _ -> static_error l ("Invalid dereference; struct type '" ^ sn ^ "' has not been defined.") None
          end
        | InductiveType(inductive_name, targs) -> begin
            let (_, _, constructors, _, _, _, _, _, _) = List.assoc inductive_name inductivemap in
            match constructors with
            | [constructor_name, (_, (_, _, _, param_names_types, _))] -> begin
              let params_with_correct_name = List.filter (fun (name,type_) -> name = f) param_names_types in
              match params_with_correct_name with
              | [(name, type_)] -> 
                let (_, _, ctormap, _, _, _, _, _, _) = List.assoc inductive_name inductivemap in
                let [(cn, (_, (_, tparams, _, parameter_names_and_types, (_, _))) : (string * inductive_ctor_info) )] = ctormap in
                let Some tpenv = zip tparams targs in
                let type_instantiated = instantiate_type tpenv type_ in
                (WReadInductiveField(l, w, inductive_name, constructor_name, f, targs, type_, type_instantiated), type_instantiated, None)
              | [] -> static_error l ("The constructor of the inductive data type '" ^ inductive_name ^ "' does not have any field with name '" ^ f ^ "'.") None
              | _ -> static_error l ("The constructor of the inductive data type '" ^ inductive_name ^ "' has multiple fields with name '" ^ f ^ "'.") None
              end
            | _ -> static_error l ("For field access of inductive data type values, the inductive data type must have exactly one constructor, found " ^ (string_of_int (List.length constructors)) ^ ".") None
          end
        | UnionType _ | RefType _ ->
          check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv (AddressOf (l, e)) f
        | _ -> static_error l ("Invalid dereference.") None
        end
      end
    | Deref (l, e) ->
      let (w, t, v) = check e in
      begin
        match t with
          PtrType Void -> static_error l "Cannot dereference a void pointer" None
        | PtrType (FuncType _) -> (w, t, v)
        | PtrType (StaticArrayType (elemTp, elemCount)) when not is_rust -> (w, PtrType elemTp, v)
        | PtrType t0 | RustRefType (_, _, t0) -> (WDeref (l, w, t0), t0, None)
        | _ -> static_error l "Operand must be pointer." None
      end
    | AddressOf (l, Var(l2, x)) when List.mem_assoc x tenv ->
      let pointeeType =
        match List.assoc x tenv with
          RefType t | (StaticArrayType (_, _) as t) -> t
        | _ -> static_error l "Taking the address of this expression is not supported." None
      in
      (WVar (l2, x, LocalVar), PtrType pointeeType, None)
    | AddressOf (la, Deref (ld, e)) ->
      check e
    | CxxLValueToRValue (l, e) -> check e
    | CxxDerivedToBase (l, e, te) ->
      let t = check_pure_type (pn, ilist) tparams Real te in
      let w = checkt_cast e t in
      w, t, None
    | AddressOf (l, e) ->
      let (w, t, v) = check_expr_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e in
      let t = unfold_inferred_type t in
      begin match t, w with
        StaticArrayType (elemTp, _), _ when not is_rust ->
        (w, PtrType elemTp, None)
      | _, WVar (_, x, FuncName) ->
        (w, t, None)
      | RefType t, TypeInfo _ -> (* allow to take the address of a reference to a typeInfo object *)
        w, PtrType t, None
      | _, _ ->
        (AddressOf (l, w), PtrType t, None)
      end
    | CallExpr (l, "getClass", [], [], [LitPat target], Instance) when language = Java ->
      let w = checkt target javaLangObject in
      (WMethodCall (l, "java.lang.Object", "getClass", [], [w], Instance, []), ObjType ("java.lang.Class", []), None)
    | CallExpr (l, "#list", [], [], pats, Static) ->
      let rec to_list_expr pats =
        match pats with
          [] -> CallExpr (l, "nil", [], [], [], Static)
        | LitPat e::pats -> CallExpr (l, "cons", [], [], [LitPat e; LitPat (to_list_expr pats)], Static)
        | _ -> static_error l "List expression must not contain patterns" None
      in
      check (to_list_expr pats)
    | CallExpr (l, "#inductive_ctor_index", [], [], [LitPat e], Static) ->
      let w, t, _ = check e in
      let InductiveType (i, targs) = t in
      (WFunCall (l, "#inductive_ctor_index", [t], [w], Static), Int (Signed, PtrRank), None)
    | CallExpr (l, "#inductive_projection", [], [], [LitPat e; LitPat (WIntLit (_, ctor_index) as i1); LitPat (WIntLit (_, arg_index) as i2)], Static) ->
      let w, t, _ = check e in
      let InductiveType (i, targs) = t in
      let (_, inductive_tparams, ctormap, _, _, _, _, _, _) = List.assoc i inductivemap in
      let tpenv = List.combine inductive_tparams targs in
      let (_, (_, (_, _, _, param_names_types, _))) = List.nth ctormap (int_of_big_int ctor_index) in
      let (x, tp) = List.nth param_names_types (int_of_big_int arg_index) in
      let tp = instantiate_type tpenv tp in
      (WFunCall (l, "#inductive_projection", [t], [w; i1; i2], Static), tp, None)
    | ExprCallExpr (l, e, es) ->
      let es = List.map (function LitPat e -> e | _ -> static_error l "Patterns are not supported here" None) es in
      let (w, t, _) = check e in
      begin match (t, es) with
        (PureFuncType (_, _), _) -> check_pure_fun_value_call l w t es
      | (ClassOrInterfaceName(cn), [e2]) -> check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation (CastExpr(l, IdentTypeExpr(expr_loc e, None, cn), e2))
      | PtrType (FuncType ftn), _ ->
        let (_, gh, tparams, rt, ftxmap, xmap, pre, post, terminates, ft_predfammap, ft_typeid) =
          match try_assoc ftn functypemap with
            None -> static_error l "Function pointer calls are not allowed here." None
          | Some info -> info
        in
        let rt = match rt with None -> Void | Some rt -> rt in (* This depends on the fact that the return type does not mention type parameters. *)
        (WFunPtrCall (l, w, Some ftn, es), rt, None)
      | _ -> static_error l "The callee of a call of this form must be a pure function value." None
      end 
    | CallExpr (l, g, targes, [], pats, fb) ->
      let es = List.map (function LitPat e -> e | _ -> static_error l "Patterns are not allowed in this position" None) pats in
      let process_targes callee_tparams =
        if callee_tparams <> [] && targes = [] then
          let targs = List.map (fun _ -> InferredType (object end, ref Unconstrained)) callee_tparams in
          let Some tpenv = zip callee_tparams targs in
          (targs, tpenv)
        else
          let targs = List.map (check_pure_type (pn,ilist) tparams Ghost) targes in
          let tpenv =
            match zip callee_tparams targs with
              None -> static_error l "Incorrect number of type arguments." None
            | Some bs -> bs
          in
          (targs, tpenv)
      in
      let func_call () =
        match try_assoc g tenv |> Option.map unfold_inferred_type with
          Some (PtrType (FuncType ftn)) ->
          let (_, gh, tparams, rt, ftxmap, xmap, pre, post, terminates, ft_predfammap, ft_typeid) =
            match try_assoc ftn functypemap with
              None -> static_error l "Function pointer calls are not allowed here." None
            | Some info -> info
          in
          let rt = match rt with None -> Void | Some rt -> rt in (* This depends on the fact that the return type does not mention type parameters. *)
          (WFunPtrCall (l, WVar (l, g, LocalVar), Some ftn, es), rt, None)
        | Some (InlineFuncType rt) ->
          (WFunPtrCall (l, WVar (l, g, LocalVar), None, es), rt, None)
        | Some ((PureFuncType (t1, t2) as t)) ->
          if targes <> [] then static_error l "Pure function value does not have type parameters." None;
          check_pure_fun_value_call l (WVar (l, g, LocalVar)) t es
        | _ ->
        match (g, es) with
          ("malloc", [SizeofExpr (ls, TypeExpr te)]) ->
          let t = check_pure_type (pn,ilist) tparams Ghost te in
          (WFunCall (l, g, [], es, Static), PtrType t, None)
        | _ ->
        match resolve2 (pn,ilist) l g funcmap with
          Some (g, FuncInfo (funenv, fterm, lg, k, callee_tparams, tr, ps, nonghost_callers_only, pre, pre_tenv, post, terminates, functype_opt, body, virt, overrides)) ->
          let declKind =
            match k with
              Regular -> DeclKind_RegularFunction
            | Fixpoint -> DeclKind_FixpointFunction
            | Lemma _ -> DeclKind_LemmaFunction
          in
          reportUseSite declKind lg l;
          let (targs, tpenv) = process_targes callee_tparams in
          let wcall = WFunCall (l, g, targs, es, fb) in
          begin match tr with 
          | None -> wcall, Void, None 
          | Some (RefType t) -> WDeref (l, wcall, t), instantiate_type tpenv t, None
          | Some rt -> wcall, instantiate_type tpenv rt, None
          end
        | None ->
        match resolve Ghost (pn,ilist) l g purefuncmap with
          Some (g, (lg, callee_tparams, t0, param_names_types, _)) ->
          reportUseSite DeclKind_PureFunction lg l;
          let (_, ts) = List.split param_names_types in
          let (targs, tpenv) = process_targes callee_tparams in
          let pts =
            match zip es ts with
              None -> static_error l "Incorrect argument count." None
            | Some pts -> pts
          in
          let args = List.map (fun (e, t0) -> let t = instantiate_type tpenv t0 in box (checkt e t) t t0) pts in
          let t = instantiate_type tpenv t0 in
          (unbox (WPureFunCall (l, g, targs, args)) t0 t, t, None)
        | None ->
          static_error l (match language with CLang -> "No such function: " ^ g | Java -> "No such method or function: " ^ g) None
      in
      if language = CLang || classmap = [] then func_call () else
      let try_qualified_call tn es args fb class_targs on_fail =
        let class_tparams = match try_assoc tn classmap with
            Some {ctpenv} -> ctpenv
            | None -> let InterfaceInfo (_, _, _, _, _, tparams) = List.assoc tn interfmap in tparams
        in
        let class_tenv = if inAnnotation <> Some(true) && fb == Instance then
            match zip class_tparams class_targs with
              Some(env) -> env
            | None -> static_error l (Printf.sprintf "The amount of type arguments for the class and the expected number of type parameters does not match.") None
          else
            []
        in
        let ms = get_methods tn g in
        if ms = [] then on_fail () else
        let argtps = List.map (fun e -> let (_, tp, _) = check e in tp) args in
        let targs = targes |> List.map begin fun targ -> 
            let tp = check_pure_type (pn,ilist) tparams Real targ in 
            if is_primitive_type tp then
              static_error l "Type arguments can not be primitive types" None
            else
              tp
          end
        in
        let ms = ms |> List.filter begin fun (_, (_, _, _, _, _, _, _, _, _, _, _, _, mtparams)) ->
          if targs = [] then 
            true
          else (* If type arguments are provided, the amount should match the amount of type parameters in the matching method *)
           match zip mtparams targs with None -> false | Some(_) -> true
        end
        in
        let ms = List.map (fun (sign, (tn', lm, gh, rt, xmap, pre, post, epost, terminates, fb', v, abstract, mtparams)) ->
          (* Replace the type parameters with their concrete type*)
          let methodTargEnv = match zip mtparams targs with
            Some(tenv) -> tenv
          | None ->
            (* Any type parameters still present have to be inferred at this point *)
            let inferTypeParamsEnv = List.map (fun tparam -> (tparam, InferredRealType tparam)) mtparams in
            let xmapTypesToInfer = List.map (fun (name, tp) -> replace_type l inferTypeParamsEnv tp) xmap in
            let inferredTypes = begin try infer_type l xmapTypesToInfer argtps with 
            | InferenceError (l, msg) -> static_error l msg None 
              end 
            in
            List.map (fun tparam ->
              let targt = try List.assoc tparam inferredTypes with Not_found -> static_error l ("couldn't infer type for type parameter: " ^ tparam) None in
              (tparam, targt)) mtparams
          in
          let targenv = methodTargEnv@class_tenv in
          let sign' = if inAnnotation <> Some(true) then
              List.map (replace_type l targenv) sign 
            else
              List.map erase_type sign
          in
          let rt' = match rt with
            Some(rt) -> if inAnnotation <> Some(true) then 
                replace_type l targenv rt
              else
                erase_type rt
          | None -> Void
          in 
          (sign', (tn', lm, gh, rt', xmap, pre, post, epost, terminates, fb', v, abstract, sign, targenv))) ms in
        let ms = List.filter (fun (sign, _) -> is_assignable_to_sign inAnnotation argtps sign) ms in
        let make_well_typed_method m =
          match m with
          (sign', (tn', lm, gh, rt, xmap, pre, post, epost, terminates, fb', v, abstract, sign, targenv)) ->
            reportUseSite DeclKind_Method lm l;
            let (fb, es) = if fb = Instance && fb' = Static then (Static, List.tl es) else (fb, es) in
            if fb <> fb' then static_error l "Instance method requires target object" None
            else (WMethodCall (l, tn', g, sign, es, fb, targenv), rt, None)
        in
        begin match ms with
          [] -> static_error l "No matching method" None
        | [m] -> make_well_typed_method m
        | ms -> 
          begin
            match try_assoc0 argtps ms with
              None -> static_error l "Multiple matching overloads" None
            | Some m -> make_well_typed_method m
          end
        end
      in
      begin match fb with
        Static ->
        begin fun on_fail ->
          match try_assoc "this" tenv with
            Some (ObjType (cn, targs)) ->
            try_qualified_call cn (Var (l, "this")::es) es Instance targs on_fail
          | _ ->
          match try_assoc current_class tenv with
            Some (ClassOrInterfaceName tn) ->
            try_qualified_call tn es es Static [] on_fail
          | _ ->
          on_fail ()
        end $. fun () ->
        func_call ()
      | Instance ->
        let arg0e::args = es in
        let (_, arg0tp, _) = check arg0e in
        let (tn, es, fb, obj_type_arguments) =
          match arg0tp with
            ObjType (tn, targs) -> (tn, es, Instance, targs)
          | ClassOrInterfaceName tn -> (tn, List.tl es, Static, [])
          | _ -> static_error l "Target of method call must be object or class" None
        in
        try_qualified_call tn es args fb obj_type_arguments (fun () -> static_error l "No such method" None)
      end
    | NewObject (l, cn, args, targs) ->
      begin match resolve Real (pn,ilist) l cn classmap with
        Some (cn, {cl; cabstract; ctpenv}) ->
        reportUseSite DeclKind_Class cl l;
        if cabstract then
          static_error l "Cannot create instance of abstract class." None
        else
          let targestps = match targs with 
            Some(targs) -> if targs = [] && ctpenv != [] then
              (* Diamond was used, infer the type arguments later *)
              List.map (fun tparam -> InferredRealType tparam) ctpenv
            else
              targs |> List.map begin fun targ -> 
                let tp = check_pure_type (pn,ilist) tparams Real targ in
                if is_primitive_type tp then 
                  static_error l "Type arguments can not be primitive types." None
                else
                  tp
              end
          | None -> List.map (fun _ -> javaLangObject) ctpenv
          in
          (NewObject (l, cn, args, targs), ObjType (cn,targestps), None)
      | None -> static_error l "No such class" None
      end
    | ReadArray(l, arr, index) ->
      let (w1, arr_t, _) = check arr in
      let (w2, index_t, _) = check index in
      begin match index_t with
        Int (_, _) -> ()
      | _ -> static_error l "Subscript must be of integer type" None
      end;
      begin match arr_t with
        ArrayType tp -> (WReadArray (l, w1, tp, w2), tp, None)
      | StaticArrayType (tp, _) -> (WReadArray (l, w1, tp, w2), tp, None)
      | PtrType (StaticArrayType (tp, _)) -> (WOperation (l, Add, [w1; w2], arr_t), PtrType tp, None)
      | PtrType tp -> (WReadArray (l, w1, tp, w2), tp, None)
      | _ when language = Java -> static_error l "Target of array access is not an array." None
      | _ when language = CLang -> static_error l "Target of array access is not an array or pointer." None
      end
    | NewArray (l, te, len) ->
      let t = check_pure_type (pn,ilist) tparams Real te in
      ignore $. checkt len intType;
      (e, (ArrayType t), None)
    | NewArrayWithInitializer (l, te, es) ->
      let t = check_pure_type (pn,ilist) tparams Real te in
      (e, ArrayType t, None)
    | IfExpr (l, e1, e2, e3) ->
      let w1 = checkcon e1 in
      let (w2, t, _) = check e2 in
      let w3 = checkt e3 t in
      (IfExpr (l, w1, w2, w3), t, None)
    | SwitchExpr (l, e, cs, cdef_opt) ->
      let (w, t, _) = check e in
      begin
        match t with
          InductiveType (i, targs) ->
          begin
            let (_, inductive_tparams, ctormap, _, _, _, _, _, _) = List.assoc i inductivemap in
            let (Some tpenv) = zip inductive_tparams targs in
            let rec iter t0 wcs ctors cs =
              match cs with
                [] ->
                let (t0, wcdef_opt) =
                  match cdef_opt with
                    None ->
                    if ctors <> [] then static_error l ("Missing cases: " ^ String.concat ", " (List.map fst ctors)) None;
                    (t0, None)
                  | Some (lcdef, edef) ->
                    if ctors = [] then static_error lcdef "Superfluous default clause" None;
                    let (wdef, tdef, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation edef in
                    let t0 =
                      match t0 with
                        None -> Some tdef
                      | Some t0 -> expect_type (expr_loc edef) inAnnotation tdef t0; Some t0
                    in
                    (t0, Some (lcdef, wdef))
                in
                begin
                  match t0 with
                    None -> static_error l "Switch expressions with zero clauses are not yet supported." None
                  | Some t0 -> (WSwitchExpr (l, w, i, targs, wcs, wcdef_opt, tenv, t0), t0, None)
                end
              | SwitchExprClause (lc, cn, xs, e)::cs ->
                begin
                  match try_assoc cn ctormap with
                    None ->
                    static_error lc ("Not a constructor of inductive type '" ^ i ^ "'.") None
                  | Some (_, (_, _, _, param_names_types, _)) ->
                    let (_, ts) = List.split param_names_types in
                    if not (List.mem_assoc cn ctors) then static_error lc "Duplicate clause." None;
                    let xenv =
                      let rec iter2 ts xs xenv =
                        match (ts, xs) with
                          ([], []) -> List.rev xenv
                        | (t::ts, []) -> static_error lc "Too few pattern variables." None
                        | ([], _) -> static_error lc "Too many pattern variables." None
                        | (t::ts, x::xs) ->
                          if List.mem_assoc x tenv then static_error lc ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
                          if List.mem_assoc x xenv then static_error lc "Duplicate pattern variable." None;
                          iter2 ts xs ((x, instantiate_type tpenv t)::xenv)
                      in
                      iter2 ts xs []
                    in
                    let (w, t, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams (xenv@tenv) inAnnotation e in
                    let t0 =
                      match t0 with
                        None -> Some t
                      | Some t0 -> expect_type (expr_loc e) inAnnotation t t0; Some t0
                    in
                    let ctors = List.filter (fun (ctorname, _) -> ctorname <> cn) ctors in
                    iter t0 (SwitchExprClause (lc, cn, xs, w)::wcs) ctors cs
                end
            in
            iter None [] ctormap cs
          end
        | _ -> static_error l "Switch expression operand must be inductive value." None
      end
    | SizeofExpr(l, TypeExpr te) ->
      let t = check_pure_type (pn,ilist) tparams Real te in
      (SizeofExpr (l, TypeExpr (ManifestTypeExpr (type_expr_loc te, t))), sizeType, None)
    | SizeofExpr(l, e) ->
      let (w, t, v) = check_expr_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e in
      let t = unfold_inferred_type t in
      begin match t with
        InductiveType ("pointer", []) ->
        (SizeofExpr (l, w), sizeType, None)
      | _ ->
        (SizeofExpr (l, TypeExpr (ManifestTypeExpr (expr_loc e, t))), sizeType, None)
      end
    | AlignofExpr (l, te) ->
      let t = check_pure_type (pn,ilist) tparams Real te in
      (AlignofExpr (l, ManifestTypeExpr (type_expr_loc te, t)), sizeType, None)
    | TypePredExpr (l, te, predName) ->
      let t = check_pure_type (pn,ilist) tparams Real te in
      begin match try_assoc predName typepreddeclmap with
        None -> static_error l "No such type predicate" None
      | Some (ld, selfTypeName, predType, _) ->
        let predType' = instantiate_type [selfTypeName, t] predType in
        (WTypePredExpr (l, t, predName), predType', None)
      end
    | GenericExpr (l, e, cs, d) ->
      let (_, t, _) = check e in
      let matching_cases = cs |> flatmap begin fun (te, e) ->
          let tc = check_pure_type (pn,ilist) tparams Real te in
          if unify_relaxed t tc then [tc, e] else []
        end
      in
      begin match matching_cases with
        [_, e] -> check e
      | [] ->
        begin match d with
          None -> static_error l ("No matching case: " ^ string_of_type t) None
        | Some e -> check e
        end
      | _ -> static_error l ("Multiple matching cases: " ^ string_of_type t ^ " matches cases " ^ String.concat ", " (List.map (fun (t, e) -> string_of_type t) matching_cases)) None
      end
    | InstanceOfExpr(l, e, te) ->
      let t = check_pure_type (pn,ilist) tparams Real te in
      let w = checkt e javaLangObject in
      (InstanceOfExpr (l, w, ManifestTypeExpr (type_expr_loc te, t)), boolt, None)
    | SuperMethodCall(l, mn, args) ->
      let rec get_implemented_instance_method cn mn argtps =
        if cn = "java.lang.Object" then None else
        match try_assoc cn classmap with 
        | Some {cmeths; csuper=(csuper, _)} ->
          begin try
            let m =
              List.find
                begin fun ((mn', sign), MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, fb, v, is_override, abstract, mtparams)) ->
                  mn = mn' &&  is_assignable_to_sign inAnnotation argtps sign && not abstract
                end
                cmeths
            in
            Some m
          with Not_found ->
            get_implemented_instance_method csuper mn argtps
          end
        | None -> None
      in
      let args_checked = List.map (fun a -> let (w, tp, _) = check a in (TypedExpr (w, tp), tp)) args in 
      let argtps = List.map snd args_checked in
      let wargs = List.map fst args_checked in
      let thistype = try_assoc "this" tenv in
      begin match thistype with
        None -> static_error l "super calls not allowed in static context." None
      | Some(ObjType(cn, targs)) -> 
        begin match try_assoc cn classmap with
          None -> static_error l "No matching method." None
        | Some {csuper=(csuper, _)} ->
            begin match get_implemented_instance_method csuper mn argtps with
              None -> static_error l "No matching method." None
            | Some(((mn', sign), MethodInfo (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, terminates, ss, fb, v, is_override, abstract, mtparams))) ->
              reportUseSite DeclKind_Method lm l;
              let tp = match rt with Some(tp) -> tp | _ -> Void in
              let rank = match ss with Some (Some (_, rank)) -> Some rank | None -> None in
              (WSuperMethodCall (l, csuper, mn, Var (l, "this") :: wargs, (lm, gh, rt, xmap, pre, post, epost, terminates, rank, v)), tp, None)
            end
        end
      end 
    | AssignExpr (l, e1, kind, e2) ->
      let (w1, t1, _) = check e1 in
      let w2 = checkt e2 t1 in
      (AssignExpr (l, w1, kind, w2), t1, None)
    | AssignOpExpr (l, e1, op, e2, postOp) ->
      let (w1, t1, _) = check e1 in
      let x = next_temp_var_name () in
      let (w2, t2, _) = check_with_extra_bindings [(x, t1)] (Operation (l, op, [Var (l, x); e2])) in
      let w2', _, _ = check (CastExpr (l, ManifestTypeExpr (l, t1), TypedExpr (w2, t2))) in
      (WAssignOpExpr (l, w1, x, w2', postOp), t1, None)
    | CommaExpr (l, e1, e2) ->
      let (w1, t1, _) = check e1 in
      let (w2, t2, v2) = check e2 in
      (CommaExpr (l, w1, w2), t2, v2)
    | InitializerList (l, es) ->
      let rec to_list_expr es =
        match es with
          [] -> CallExpr (l, "nil", [], [], [], Static)
        | (None, e)::es -> CallExpr (l, "cons", [], [], [LitPat e; LitPat (to_list_expr es)], Static)
        | (Some (lf, f), _)::_ -> static_error lf "Field names are not supported in this position" None
      in
      check (to_list_expr es)
    | CxxNew (l, te, expr_opt) ->
      let t = check_pure_type (pn, ilist) [] Real te in 
      let expr_opt = 
        expr_opt |> option_map @@ fun e ->
          let w, et, _ = check e in
          assert (t = et);
          w
      in
      WCxxNew (l, t, expr_opt), PtrType t, None
    | CxxConstruct (l, name, te, es) ->
      let t = check_pure_type (pn, ilist) [] Real te in 
      WCxxConstruct (l, name, t, es), t, None
    | e -> static_error (expr_loc e) "Expression form not allowed here." None
  and check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (inAnnotation: bool option) e t0 =
    check_expr_t_core_core functypemap funcmap classmap interfmap (pn, ilist) tparams tenv inAnnotation e t0 false
  and check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (inAnnotation: bool option) e t0 isCast =
    match (e, unfold_inferred_type t0) with
      (Operation(l, Div, [IntLit(_, i1, _, _, _); IntLit(_, i2, _, _, _)]), RealType) -> RealLit(l, (num_of_big_int i1) // (num_of_big_int i2), None)
    | (IntLit (l, n, _, _, _), PtrType _) when isCast || eq_big_int n zero_big_int -> WPureFunCall (l, "pointer_ctor", [], [WPureFunCall (l, "null_pointer_provenance", [], []); wintlit l n])
    | (IntLit (l, n, _, _, _), RealType) -> RealLit (l, num_of_big_int n, None)
    | (IntLit (l, n, _, _, _), (Int (Unsigned, rank) as tp)) when isCast || inAnnotation <> Some true ->
      let k, isTight = get_glb_litwidth (width_of_rank rank) in
      if not (le_big_int zero_big_int n && le_big_int n (max_unsigned_big_int k)) then
        if isCast then
          if isTight then
            wintlit l (extract_big_int n 0 (8 * (1 lsl k)))
          else
            static_error l "Truncating cast to target-dependent-sized integer type is not yet supported." None
        else
          static_error l (Printf.sprintf "Integer literal used as %s must be between 0 and %s." (string_of_type tp) (string_of_big_int (max_unsigned_big_int k))) None
      else
        wintlit l n
    | (IntLit (l, n, _, _, _), (Int (Signed, rank) as tp)) when isCast || inAnnotation <> Some true ->
      let k, isTight = get_glb_litwidth (width_of_rank rank) in
      if not (le_big_int (min_signed_big_int k) n && le_big_int n (max_signed_big_int k)) then
        if isCast then begin
          if not isTight then static_error l "Truncating cast to target-dependent-sized integer type is not yet supported." None;
          let n = extract_big_int n 0 (8 * (1 lsl k)) in
          let n = if lt_big_int (max_signed_big_int k) n then sub_big_int n (succ_big_int (max_unsigned_big_int k)) else n in
          wintlit l n
        end else
          static_error l (Printf.sprintf "Integer literal used as %s must be between %s and %s." (string_of_type tp) (string_of_big_int (min_signed_big_int k)) (string_of_big_int (max_signed_big_int k))) None
      else
        wintlit l n
    | _ ->
      (* Note: if you add a cast here, i.e. let the typechecker allow
       * a cast, and that cast can change value (e.g. casting a signed int
       * to an unsigned), be sure to check whether you also have to modify
       * eval_core_cps0 (search for "No other cast allowed by the type
       * checker changes the value").
       *)
      let (w, t, value) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e in
      let check () =
        begin match (t, t0) with
        | _ when t = t0 -> w
        | (ObjType _, ObjType _) when isCast -> w
        | ((PtrType _|RustRefType _), (PtrType _|RustRefType _)) when isCast -> Upcast (w, t, t0)
        | (Int (_, _)), (Int (_, _)) when isCast -> if definitely_is_upcast (int_rank_and_signedness t) (int_rank_and_signedness t0) then Upcast (w, t, t0) else w
        | (PtrType _), (Int (Unsigned, PtrRank)) when isCast -> WReadInductiveField (expr_loc w, w, "pointer", "pointer_ctor", "address", [], PtrType Void, PtrType Void)
        | (PtrType _), (Int (Unsigned, m)) when isCast && definitely_is_upcast (int_rank_and_signedness t) (int_rank_and_signedness t0) -> WReadInductiveField (expr_loc w, w, "pointer", "pointer_ctor", "address", [], PtrType Void, PtrType Void)
        | (Int (_, _)), (PtrType _) when isCast && (inAnnotation = Some true || definitely_is_upcast (int_rank_and_signedness t) (int_rank_and_signedness t0)) -> WPureFunCall (expr_loc w, "pointer_ctor", [], [WPureFunCall (expr_loc w, "null_pointer_provenance", [], []); w])
        | (Int (signedness, _), (Float|Double|LongDouble)) -> floating_point_fun_call_expr funcmap (expr_loc w) t0 ("of_" ^ identifier_string_of_type (Int (signedness, FixedWidthRank max_width))) [TypedExpr (w, t)]
        | ((Float|Double|LongDouble), (Float|Double|LongDouble)) -> floating_point_fun_call_expr funcmap (expr_loc w) t0 ("of_" ^ identifier_string_of_type t) [TypedExpr (w, t)]
        | ((Float|Double|LongDouble), (Int (signedness, _))) when isCast -> floating_point_fun_call_expr funcmap (expr_loc w) (Int (signedness, FixedWidthRank max_width)) ("of_" ^ identifier_string_of_type t) [TypedExpr (w, t)]
        | (ObjType ("java.lang.Object", []), ArrayType _) when isCast -> w
        | ((PtrType _|RustRefType _), InductiveType ("pointer", [])) when isCast -> w
        | (InductiveType ("pointer", []), (PtrType _|RustRefType _)) when isCast -> w
        | (Bool, Int (_, _)) -> IfExpr (expr_loc w, w, WIntLit (expr_loc w, unit_big_int), WIntLit (expr_loc w, zero_big_int))
        | _ ->
          expect_type (expr_loc e) inAnnotation t t0;
          if isCast || try expect_type dummy_loc inAnnotation t0 t; false with StaticError _ -> true then
            Upcast (w, t, t0)
          else
            w
        end
      in
      match (value, t, t0) with
        (Some(value), Int (Signed, r1), Int (Signed, r2)) ->
        begin match width_of_rank r1, width_of_rank r2 with
          LitWidth k1, LitWidth k2 when k2 < k1 && le_big_int (min_signed_big_int k2) value && le_big_int value (max_signed_big_int k2) -> w
        | _ -> check ()
        end
      | _ -> check ()
  and check_condition_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (inAnnotation: bool option) e =
    let (w, t, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e in
    match t with
      Bool -> w
    | Int (_, _) when language = CLang ->
      WOperation (expr_loc e, Neq, [w; wintlit (expr_loc e) (big_int_of_int 0)], t)
    | PtrType _ when language = CLang ->
      WOperation (expr_loc e, Neq, [w; WPureFunCall (expr_loc e, "null_pointer", [], [])], t)
    | _ -> expect_type (expr_loc e) inAnnotation t Bool; w
  and check_union_member_deref l w un f isActivating =
    match try_assoc un unionmap with
      Some (_, Some (fds, _), _) ->
      begin match try_assoc_i f fds with
        None -> static_error l ("No such field in union '" ^ un ^ "'.") None
      | Some (i, (_, tp)) -> (WDeref (l, AddressOf (l, WReadUnionMember (l, w, un, i, f, tp, isActivating)), tp), tp, None)
      end
    | _ -> static_error l ("Invalid dereference; union type '" ^ un ^ "' has not been defined.") None
  and check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv e f =
    let (w, t, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv None e in
    begin
    match unfold_inferred_type_deep t with
    | InductiveType(inductive_name, targs) -> begin
        let (_, _, constructors, _, _, _, _, _, _) = List.assoc inductive_name inductivemap in
        match constructors with
        | [constructor_name, (_, (_, _, _, param_names_types, _))] -> begin
          let params_with_correct_name = List.filter (fun (name,type_) -> name = f) param_names_types in
          match params_with_correct_name with
          | [(name, type_)] -> 
            let (_, _, ctormap, _, _, _, _, _, _) = List.assoc inductive_name inductivemap in
            let [(cn, (_, (_, tparams, _, parameter_names_and_types, (_, _))) : (string * inductive_ctor_info) )] = ctormap in
            let Some tpenv = zip tparams targs in
            let type_instantiated = instantiate_type tpenv type_ in
            (WReadInductiveField(l, w, inductive_name, constructor_name, f, targs, type_, type_instantiated), type_instantiated, None)
          | [] -> static_error l ("The constructor of the inductive data type '" ^ inductive_name ^ "' does not have any field with name '" ^ f ^ "'.") None
          | _ -> static_error l ("The constructor of the inductive data type '" ^ inductive_name ^ "' has multiple fields with name '" ^ f ^ "'.") None
          end
        | _ -> static_error l ("For field access of inductive data type values, the inductive data type must have exactly one constructor, found " ^ (string_of_int (List.length constructors)) ^ ".") None
      end
    | PtrType (StructType (sn, targs))
    | RustRefType (_, _, StructType (sn, targs)) ->
      begin
      match try_assoc sn structmap with
        Some (_, tparams, Some (_, fds, _), _, _) ->
        begin
          match try_assoc f fds with
            None -> static_error l ("No such field in struct '" ^ sn ^ "'.") None
          | Some (_, gh, t, offset, _) ->
            let w = WRead (l, w, sn, tparams, f, t, targs, false, ref (Some None), gh) in
            let t = instantiate_type (List.combine tparams targs) t in
            let w =
              match t with
                StructType _ -> WDeref (l, AddressOf (l, w), t)
              | _ -> w
            in
            (w, t, None)
        end
      | _ -> static_error l ("Invalid dereference; struct type '" ^ sn ^ "' has not been defined.") None
      end
    | PtrType (UnionType un) -> check_union_member_deref l w un f false
    | ObjType (cn, targs) ->
      begin
      match lookup_class_field (cn, targs) f with
        None -> static_error l ("No such field in class '" ^ cn ^ "'.") None
      | Some ({fgh; ft; fbinding; ffinal; fvalue}, fclass) ->
        if fbinding = Static then static_error l "Accessing a static field via an instance is not supported." None;
        let constant_value =
              if ffinal then
                match !fvalue with
                  Some(Some(IntConst(i))) -> Some(i)
                | _ -> None
              else
                None
        in
        (WRead (l, w, fclass, [], f, ft, [], false, ref (Some None), fgh), ft, constant_value)
      end
    | ArrayType _ when f = "length" ->
      (ArrayLengthExpr (l, w), intType, None)
    | ClassOrInterfaceName cn ->
      begin match lookup_class_field (cn, []) f with
        None -> static_error l "No such field" None
      | Some ({fgh; ft; fbinding; ffinal; fvalue}, fclass) ->
        if fbinding = Instance then static_error l "You cannot access an instance field without specifying a target object." None;
        let constant_value =
              if ffinal then
                match !fvalue with
                  Some(Some(IntConst(i))) -> Some(i)
                | _ -> None
              else
                None
         in
        (WRead (l, w, fclass, [], f, ft, [], true, fvalue, fgh), ft, constant_value)
      end
    | PackageName pn ->
      let name = pn ^ "." ^ f in
      if List.mem_assoc name classmap1 || List.mem_assoc name interfmap1 || List.mem_assoc name classmap0 || List.mem_assoc name interfmap0 then
        (e, ClassOrInterfaceName name, None)
      else if is_package name then
        (e, PackageName name, None)
      else
        static_error l "No such type or package" None
    | t -> static_error l (Printf.sprintf "Target expression of field dereference should be of type pointer-to-struct. Instead, found '%s'." (string_of_type t)) None
    end
  
  let check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (inAnnotation: bool option) e =
   let (w, tp, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv inAnnotation e in
   (w, tp)
  
  let check_expr (pn,ilist) tparams tenv (inAnnotation: bool option) e = check_expr_core [] [] [] [] (pn,ilist) tparams tenv inAnnotation e
  let check_condition (pn,ilist) tparams tenv (inAnnotation: bool option) e = check_condition_core [] [] [] [] (pn,ilist) tparams tenv inAnnotation e
  let check_expr_t (pn,ilist) tparams tenv (inAnnotation: bool option) e tp = check_expr_t_core [] [] [] [] (pn,ilist) tparams tenv inAnnotation e tp
  
  (* Region: Type checking of fixpoint function bodies *)

  let fixpointmap1 =
    let rec iter fpm_done fpm_todo =
      match fpm_todo with
        [] -> List.rev fpm_done
      | (g, (l, tparams, rt, pmap, index, body, pn, ilist, fsym))::fpm_todo ->
      let param_requires_map =
        match try_assoc g purefuncparamrequiresmap with
          None -> []
        | Some map ->
          map |> List.map @@ fun (i, reqs) ->
            (fst (List.nth pmap i),
             reqs |> List.map @@ fun (l, j, rel, i) ->
               (l, j, rel, fst (List.nth pmap i)))
      in
      match (index, body) with
        (Some index, SwitchStmt (ls, Var (lx, x), cs)) ->
        let (i, targs) =
          match List.assoc x pmap with
            InductiveType (i, targs) -> (i, targs)
          | _ -> static_error l "Switch operand is not an inductive value." None
        in
        let (_, inductive_tparams, ctormap, _, _, _, _, _, _) = List.assoc i inductivemap in
        let (Some tpenv) = zip inductive_tparams targs in
        let rec check_cs (ctormap : (string * (inductive_ctor_info)) list) wcs cs =
          match cs with
            [] ->
            begin match ctormap with
              [] -> ()
            | (cn, _)::_ ->
              static_error ls ("Missing case: '" ^ cn ^ "'.") None
            end;
            wcs
          | SwitchStmtClause (lc, e, body)::cs ->
            let (cn, xs) =
              match e with
                CallExpr (_, cn, _, _, pats, _) ->
                let xs = List.map (function LitPat (Var (_, x)) -> x | _ -> static_error lc "Constructor arguments must be variable names" None) pats in
                (cn, xs)
              | Var (_, cn) -> (cn, [])
              | _ -> static_error lc "Case expression must be constructor pattern" None
            in
            let ts =
              match try_assoc cn ctormap with
                None -> static_error lc "No such constructor." None
              | Some (_, (_, _, _, param_names_types, _)) -> 
                let (_, types) = List.split param_names_types in
                types
            in
            let xmap =
              let rec iter xmap ts xs =
                match (ts, xs) with
                  ([], []) -> xmap
                | (t::ts, x::xs) ->
                  if List.mem_assoc x pmap then static_error lc "Pattern variable hides parameter." None;
                  let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." None in
                  iter ((x, instantiate_type tpenv t)::xmap) ts xs
                | ([], _) -> static_error lc "Too many pattern variables." None
                | _ -> static_error lc "Too few pattern variables." None
              in
              iter [] ts xs
            in
            let tenv = xmap @ pmap in
            let (lret, body) =
              match body with
                [ReturnStmt (lret, Some e)] -> (lret, e)
              | _ -> static_error lc "Body of switch clause must be a return statement with a result expression." None
            in
            let wbody = check_expr_t (pn,ilist) tparams tenv (Some true) body rt in
            let rec iter0 components e =
              let rec iter () e =
                let iter1 e = iter () e in
                let rec iter2 allowed_reqs e =
                  let is_allowed_req j rel y =
                    allowed_reqs |> List.exists @@ fun (j', rel', y') ->
                      j = j' &&
                      match rel, rel' with
                      | IsProperComponentOf, IsComponentOf -> y = x && List.mem y' components
                      | _, _ -> y' = y || y = x && List.mem y' components
                  in
                  let check_pure_func_call l g' args =
                    if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot mention a fixpoint function that appears later in the program text" None;
                    if g' = g then begin
                      if List.length args > index then begin
                        match List.nth args index with
                          WVar (l'', x, LocalVar) when List.mem x components -> ()
                        | _ -> static_error l "Inductive argument of recursive call must be switch clause pattern variable." None
                      end else begin
                        if not (is_allowed_req (index - List.length args) IsProperComponentOf x) then
                          static_error l "A fixpoint function cannot mention itself unless when passed as an argument for a parameter with an appropriate requires clause" None
                      end
                    end;
                    match try_assoc g' purefuncparamrequiresmap with
                      None -> List.iter iter1 args
                    | Some reqs ->
                      args |> List.iteri @@ fun i arg ->
                        let i_reqs = reqs |> flatmap (fun (i', reqs) -> if i = i' then reqs else []) in
                        let i_reqs = i_reqs |> flatmap @@ fun (_, j, rel, i) ->
                          if i < List.length args then begin
                            match List.nth args i with
                              WVar (_, y, LocalVar) -> [j, rel, y]
                            | _ -> []
                          end else
                            []
                        in
                        iter2 i_reqs arg
                  in
                  let check_local_var_call l g' args =
                    begin match try_assoc g' param_requires_map with
                      None -> ()
                    | Some reqs ->
                      List.iter
                        begin fun (lreq, j, rel, i) ->
                          let satisfies_req =
                            if j < List.length args then begin
                              match List.nth args j with
                                WVar (_, y, LocalVar) ->
                                rel = IsComponentOf && y = i ||
                                i = x && List.mem y components
                              | _ -> false
                            end else
                              is_allowed_req (j - List.length args) rel i
                          in
                          if not satisfies_req then
                            static_error l "Could not prove callee requires clause" None
                        end
                        reqs
                    end;
                    List.iter iter1 args
                  in
                  match e with
                    WPureFunCall (l, g', targs, args) ->
                    check_pure_func_call l g' args
                  | WPureFunValueCall (l, WVar (l', g', PureFuncName _), args) ->
                    check_pure_func_call l g' args
                  | WPureFunValueCall (l, WVar (l', g', LocalVar), args) ->
                    check_local_var_call l g' args
                  | WVar (l, g', PureFuncName _) ->
                    check_pure_func_call l g' []
                  | WVar (l, g', LocalVar) ->
                    check_local_var_call l g' []
                  | WSwitchExpr (l, WVar (_, x, LocalVar), _, _, cs, def_opt, _, _) when List.mem x components ->
                    List.iter (fun (SwitchExprClause (_, _, pats, e)) -> iter0 (pats @ components) e) cs;
                    (match def_opt with None -> () | Some (l, e) -> iter1 e)
                  | _ -> expr_fold_open iter () e
                in
                iter2 [] e
              in
              iter () e
            in
            iter0 (List.map fst xmap) wbody;
            check_cs (List.remove_assoc cn ctormap) (SwitchExprClause (lc, cn, xs, wbody)::wcs) cs
          | SwitchStmtDefaultClause (lc, body)::cs ->
            if cs <> [] then static_error lc "The default clause must be the last clause." None;
            let (lret, body) =
              match body with
                [ReturnStmt (lret, Some e)] -> (lret, e)
              | _ -> static_error lc "Body of switch clause must be a return statement with a result expression." None
            in
            let wbody = check_expr_t (pn,ilist) tparams pmap (Some true) body rt in
            let expr_is_ok e =
              match e with
                WPureFunCall (l, g', targs, args) ->
                if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot call a fixpoint function that appears later in the program text" None;
                if g' = g then static_error l "Recursive calls are not allowed in a default clause." None
              | WVar (l, g', PureFuncName _) ->
                if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot mention a fixpoint function that appears later in the program text" None;
                if g' = g then static_error l "A fixpoint function that mentions itself is not yet supported." None
              | _ -> ()
            in
            expr_iter expr_is_ok wbody;
            let clauses =
              ctormap |> List.map begin fun (cn, (_, (_, _, _, ts, _))) ->
                SwitchExprClause (lc, cn, List.map (fun _ -> "_") ts, wbody)
              end
            in
            clauses @ wcs
        in
        let wcs = check_cs ctormap [] cs in
        iter ((g, (l, tparams, rt, pmap, Some index, SwitchExpr (ls, Var (lx, x), wcs, None), pn, ilist, fsym))::fpm_done) fpm_todo
      | (None, ReturnStmt (lr, Some e)) ->
        let tenv = pmap in
        let w = check_expr_t (pn,ilist) tparams tenv (Some true) e rt in
        let rec iter0 e =
          let rec iter () e =
            let iter1 e = iter () e in
            match e with
              WPureFunCall (l, g', targs, args) ->
              if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot call a fixpoint function that appears later in the program text" None;
              if g' = g then static_error l "A fixpoint function whose body is a return statement cannot call itself." None;
              List.iter iter1 args
            | WVar (l, g', PureFuncName _) ->
              if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot mention a fixpoint function that appears later in the program text" None;
              if g' = g then static_error l "A fixpoint function whose body is a return statement cannot mention itself." None
            | _ -> expr_fold_open iter () e
          in
          iter () e
        in
        iter0 w;
        iter ((g, (l, tparams, rt, pmap, None, w, pn, ilist, fsym))::fpm_done) fpm_todo
    in
    iter [] fixpointmap1
  
  (* Static field initializers cannot have side-effects; otherwise, class initialization would be tricky to verify. *)
  let check_static_field_initializer e =
    let rec iter e =
      match e with
        True _ | False _ | Null _ | WVar _ | WIntLit _ | IntLit _ | RealLit _ | StringLit _ | ClassLit _ -> ()
      | TruncatingExpr (l, e) -> iter e
      | WOperation (l, _, es, _) -> List.iter iter es
      | NewArray (l, t, e) -> iter e
      | NewArrayWithInitializer (l, t, es) -> List.iter iter es
      | CastExpr (l, _, e) -> iter e
      | Upcast (e, _, _) -> iter e
      | TypedExpr (e, _) -> iter e
      | WRead (_, e, _, _, _, _, _, _, _, _) -> iter e
      | WSelect (_, e, _, _, _, _, _) -> iter e
      | _ -> static_error (expr_loc e) "This expression form is not supported in a static field initializer." None
    in
    iter e
  
  (* Region: Type checking of field initializers for static fields *)
  
  let classmap1 =
    List.map
      begin fun (cn, (l, abstract, fin, meths, fds, constr, super, tpenv, interfs, preds, pn, ilist)) ->
        let fds =
          List.map
            begin function
              (f, ({fgh; ft; fbinding=Static; finit=Some e} as fd)) ->
                let e = check_expr_t (pn,ilist) [] [current_class, ClassOrInterfaceName cn] (Some (fgh = Ghost)) e ft in
                if fgh = Real then check_static_field_initializer e;
                (f, {fd with finit=Some e})
            | fd -> fd
            end
            fds
        in
        (cn, (l, abstract, fin, meths, fds, constr, super, tpenv, interfs, preds, pn, ilist))
      end
      classmap1
  
  let interfmap1 =
    interfmap1 |> List.map begin fun (itf, (l, fds, meths, preds, interfs, pn, ilist, tparams)) ->
      let fds = fds |> List.map begin function
          (f, ({fgh; ft; fbinding=Static; finit=Some e} as fd)) ->
          let e = check_expr_t (pn,ilist) [] [current_class, ClassOrInterfaceName itf] (Some (fgh = Ghost)) e ft in
          if fgh = Real then check_static_field_initializer e;
          (f, {fd with finit=Some e})
        | fd -> fd
        end
      in
      (itf, (l, fds, meths, preds, interfs, pn, ilist, tparams))
    end

  let check_c_initializer check_expr_t (pn,ilist) tparams tenv e tp =
    let rec check e tp =
    match tp, e with
    | StaticArrayType (Int (Signed, CharRank), LiteralConstType n), StringLit (ls, s) ->
      if String.length s + 1 > n then static_error ls "String literal does not fit inside character array." None;
      e
    | StaticArrayType (elemTp, LiteralConstType elemCount), InitializerList (ll, es) ->
      let rec iter n es =
        match es with
          [] -> []
        | (_, e)::es ->
          if n = 0 then static_error ll "Initializer list too long." None;
          let e = check e elemTp in
          let es = iter (n - 1) es in
          (None, e)::es
      in
      InitializerList (ll, iter elemCount es)
    | StructType (sn, targs), InitializerList (ll, es) ->
      let tparams, fds =
        match try_assoc sn structmap with
          Some (_, tparams, Some (_, fds, _), _, _) -> tparams, fds
        | _ -> static_error ll (sprintf "Missing definition of struct '%s'" sn) None
      in
      let tpenv = List.combine tparams targs in
      let rec iter fds es =
        match fds, es with
          _, [] -> []
        | (_, (_, Ghost, _, _, _))::fds, es -> iter fds es
        | (_, (_, _, tp, _, _))::fds, (f_opt, e)::es ->
          begin match f_opt with
            None -> ()
          | Some (lf, f) -> static_error lf "Field names are not yet supported in this position" None
          end;
          let e = check e (instantiate_type tpenv tp) in
          let es = iter fds es in
          (None, e)::es
        | _ -> static_error ll "Initializer list too long." None
      in
      InitializerList (ll, iter fds es)
    | tp, e ->
      check_expr_t (pn,ilist) tparams tenv e tp
    in
    check e tp
  
  let () =
    globalmap1 |> List.iter begin fun (x, (lg, tp, symb, ref_init)) ->
      ref_init := option_map (fun e -> check_c_initializer (fun (pn,ilist) tparams tenv e tp -> check_expr_t (pn,ilist) tparams tenv (Some false) e tp) ("", []) [] [] e tp) !ref_init
    end
  
  (* Region: Computing constant field values *)
  
  let truncate_big_int n (Int (Signed, k)) =
    let LitWidth k = width_of_rank k in
    let n = extract_big_int n 0 (8 * (1 lsl k)) in
    if le_big_int n (max_signed_big_int k) then
      n
    else
      sub_big_int n (succ_big_int (max_unsigned_big_int k))

  let () =
    let string_of_const v =
      match v with
        IntConst n -> string_of_big_int n
      | BoolConst b -> if b then "true" else "false"
      | StringConst s -> s
      | NullConst -> "null"
    in
    let rec eval callers e =
      let ev = eval callers in
      match e with
        True l -> BoolConst true
      | False l -> BoolConst false
      | Null l -> NullConst
      | WOperation (l, Add, [e1; e2], tp) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (truncate_big_int (add_big_int n1 n2) tp)
        | (StringConst s1, v) -> StringConst (s1 ^ string_of_const v)
        | (v, StringConst s2) -> StringConst (string_of_const v ^ s2)
        | _ -> raise NotAConstant
        end
      | WOperation (l, Sub, [e1; e2], tp) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (truncate_big_int (sub_big_int n1 n2) tp)
        | _ -> raise NotAConstant
        end
      | WOperation (l, Mul, [e1; e2], tp) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (truncate_big_int (mult_big_int n1 n2) tp)
        | _ -> raise NotAConstant
        end
      | WIntLit (l, n) -> IntConst n
      | StringLit (l, s) -> StringConst s
      | WRead (l, _, fparent, _, fname, _, _, fstatic, _, _) when fstatic -> eval_field callers (fparent, fname)
      | CastExpr (l, ManifestTypeExpr (_, t), e) ->
        let v = ev e in
        begin match (t, v) with
          (Int (Signed, (CharRank|FixedWidthRank 0)), IntConst n) ->
          let n =
            if not (le_big_int (big_int_of_int (-128)) n && le_big_int n (big_int_of_int 127)) then
              let n = int_of_big_int (mod_big_int n (big_int_of_int 256)) in
              let n = if 128 <= n then n - 256 else n in
              big_int_of_int n
            else
              n
          in
          IntConst n
        | (Int (Signed, (ShortRank|FixedWidthRank 1)), IntConst n) ->
          let n =
            if not (le_big_int (big_int_of_int (-32768)) n && le_big_int n (big_int_of_int 32767)) then
              let n = int_of_big_int (mod_big_int n (big_int_of_int 65536)) in
              let n = if 32768 <= n then n - 65536 else n in
              big_int_of_int n
            else
              n
          in
          IntConst n
        | _ -> raise NotAConstant
        end
      | Upcast (e, fromType, toType) -> ev e
      | TypedExpr (e, t) -> ev e
      | WidenedParameterArgument e -> ev e
      | _ -> raise NotAConstant
    and eval_field callers ((cn, fn) as f) =
      if List.mem f callers then raise NotAConstant;
      match try_assoc cn classmap1 with
        Some (l, abstract, fin, meths, fds, const, super, tpenv, interfs, preds, pn, ilist) -> eval_field_body (f::callers) (List.assoc fn fds)
      | None ->
      match try_assoc cn classmap0 with
        Some {cfds} -> eval_field_body (f::callers) (List.assoc fn cfds)
      | None ->
      match try_assoc cn interfmap1 with
        Some (li, fds, meths, preds, interfs, pn, ilist, tparams) -> eval_field_body (f::callers) (List.assoc fn fds)
      | None ->
      match try_assoc cn interfmap0 with
        Some (InterfaceInfo (li, fields, meths, preds, interfs, tparams)) -> eval_field_body (f::callers) (List.assoc fn fields)
      | None ->
      assert false
    and eval_field_body callers {fgh; fbinding; ffinal; finit; fvalue} =
      match !fvalue with
        Some None -> raise NotAConstant
      | Some (Some v) -> v
      | None ->
        match (fbinding, ffinal, finit) with
          (Static, true, Some e) ->
          begin try
            let v = match fgh with Ghost -> GhostConst e | Real -> eval callers e in
            fvalue := Some (Some v);
            v
          with NotAConstant -> fvalue := Some None; raise NotAConstant
          end
        | _ -> fvalue := Some None; raise NotAConstant
    in
    let compute_fields fds is_itf_fields =
      fds |> List.iter (fun (f, fbody) -> try ignore $. eval_field_body [] fbody with NotAConstant -> if is_itf_fields then let {fl} = fbody in static_error fl "Interface field initializer must be constant expression" None)
    in
    classmap1 |> List.iter (fun (cn, (l, abstract, fin, meths, fds, constr, super, tpenv, interfs, preds, pn, ilist)) -> compute_fields fds false);
    interfmap1 |> List.iter (fun (ifn, (li, fds, meths, preds, interfs, pn, ilist, tparams)) -> compute_fields fds true)
  
  (* Region: type checking of assertions *)
  
  let merge_tenvs l tenv1 tenv2 =
    let rec iter tenv1 tenv3 =
      match tenv1 with
        [] -> tenv3
      | ((x, t) as xt)::tenv1 ->
        if List.mem_assoc x tenv2 then static_error l (Printf.sprintf "Variable name clash: '%s'" x) None;
        iter tenv1 (xt::tenv3)
    in
    iter tenv1 tenv2
    
  let rec check_pat_core (pn,ilist) tparams tenv t p =
    match p with
      LitPat (WidenedParameterArgument e) ->
      let (w, tp) = check_expr (pn,ilist) tparams tenv (Some true) e in
      expect_type (expr_loc e) (Some true) t tp;
      (LitPat (WidenedParameterArgument w), [])
    | LitPat e ->
      let fallback () =
        let w = check_expr_t (pn,ilist) tparams tenv (Some true) e t in
        (LitPat w, [])
      in
      begin match e with
        CallExpr (l, g, [], [], pats, Static) ->
        begin match resolve Ghost (pn,ilist) l g purefuncmap with
          Some (g_resolved, (_, _, rt, _, _)) ->
          begin match rt with
            InductiveType (i, _) ->
            let (_, inductive_tparams, ctormap, _, _, _, _, _, _) = List.assoc i inductivemap in
            begin match try_assoc g ctormap with
              Some (_, (ld, _, _, param_names_types, symb)) ->
              reportUseSite DeclKind_InductiveCtor ld l;
              let (_, ts0) = List.split param_names_types in
              let targs = List.map (fun _ -> InferredType (object end, ref Unconstrained)) inductive_tparams in
              let Some tpenv = zip inductive_tparams targs in
              let ts = List.map (instantiate_type tpenv) ts0 in
              let t0 = InductiveType (i, targs) in
              if not (unify t t0) then fallback () else
              let (pats, tenv') = check_pats_core (pn,ilist) l tparams tenv ts pats in
              let args = List.map (fun (LitPat arg | WCtorPat (_, _, _, _, _, _, _, Some arg)) -> arg) pats in
              let args = List.map2 (fun arg (t, t0) -> box arg t t0) args (List.combine ts ts0) in
              let e = WPureFunCall (l, g_resolved, targs, args) in
              (WCtorPat (l, i, targs, g, ts0, ts, pats, Some e), tenv')
            | None ->
              fallback ()
            end
          | _ ->
            fallback ()
          end
        | None ->
          fallback ()
        end
      | _ ->
        fallback()
      end
    | VarPat (l, x) ->
      if List.mem_assoc x tenv then static_error l ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
      (p, [(x, t)])
    | DummyPat|DummyVarPat -> (p, [])
    | CtorPat (l, g, pats) ->
      begin match resolve Ghost (pn,ilist) l g purefuncmap with
        Some (_, (_, _, rt, _, _)) ->
        begin match rt with
          InductiveType (i, _) ->
          let (_, inductive_tparams, ctormap, _, _, _, _, _, _) = List.assoc i inductivemap in
          begin match try_assoc g ctormap with
            Some (_, (ld, _, _, param_names_types, symb)) ->
            reportUseSite DeclKind_InductiveCtor ld l;
            let (_, ts0) = List.split param_names_types in
            let targs = List.map (fun _ -> InferredType (object end, ref Unconstrained)) inductive_tparams in
            let Some tpenv = zip inductive_tparams targs in
            let ts = List.map (instantiate_type tpenv) ts0 in
            let t0 = InductiveType (i, targs) in
            expect_type l (Some true) t t0;
            let (pats, tenv') = check_pats_core (pn,ilist) l tparams tenv ts pats in
            (WCtorPat (l, i, targs, g, ts0, ts, pats, None), tenv')
          | None ->
            static_error l "Not a constructor" None
          end
        | _ -> static_error l "Not a constructor" None
        end
      | None -> static_error l "No such pure function" None
      end
  and check_pats_core (pn,ilist) l tparams tenv ts ps =
    match (ts, ps) with
      ([], []) -> ([], [])
    | (t::ts, p::ps) ->
      let (wpat, tenv') = check_pat_core (pn,ilist) tparams tenv t p in
      let (wpats, tenv'') = check_pats_core (pn,ilist) l tparams tenv ts ps in
      (wpat::wpats, merge_tenvs l tenv' tenv'')
    | ([], _) -> static_error l "Too many patterns" None
    | (_, []) -> static_error l "Too few patterns" None
  
  let check_pat (pn,ilist) tparams tenv t p = let (w, tenv') = check_pat_core (pn,ilist) tparams tenv t p in (w, tenv' @ tenv)
  
  let rec check_pats (pn,ilist) l tparams tenv ts ps =
    match (ts, ps) with
      ([], []) -> ([], tenv)
    | (t::ts, p::ps) ->
      let (wpat, tenv) = check_pat (pn,ilist) tparams tenv t p in
      let (wpats, tenv) = check_pats (pn,ilist) l tparams tenv ts ps in
      (wpat::wpats, tenv)
    | ([], _) -> static_error l "Too many patterns" None
    | (_, []) -> static_error l "Too few patterns" None
  
  let get_class_of_this =
    WMethodCall (dummy_loc, "java.lang.Object", "getClass", [], [WVar (dummy_loc, "this", LocalVar)], Instance, [])
  
  let get_class_finality tn = (* Returns ExtensibleClass if tn is an interface *)
    match try_assoc tn classmap1 with
      Some (lc, abstract, fin, methods, fds_opt, ctors, super, tpenv, interfs, preds, pn, ilist) ->
      fin
    | None ->
      match try_assoc tn classmap0 with
        Some {cfinal} ->
        cfinal
      | None -> ExtensibleClass
  
  let check_inst_pred_asn l tn g check_call error =
    let rec find_in_interf itf =
      let search_interfmap get_interfs_and_preds interfmap fallback =
        match try_assoc itf interfmap with
          Some info ->
          let (interfs, preds) = get_interfs_and_preds info in
          begin match try_assoc g preds with
            Some (_, pmap, family, symb) -> [(family, pmap)]
          | None -> List.flatten (List.map (fun i -> find_in_interf i) (List.map fst interfs))
          end
        | None -> fallback ()
      in
      search_interfmap (function (li, fields, meths, preds, interfs, pn, ilist, tparams) -> (interfs, preds)) interfmap1 $. fun () ->
      search_interfmap (function InterfaceInfo (li, fields, meths, preds, interfs, tparams) -> (interfs, preds)) interfmap0 $. fun () ->
      []
    in
    let rec find_in_class cn =
      let search_classmap classmap proj fallback =
        match try_assoc cn classmap with
          Some info ->
          let ((super, _), interfs, preds) = proj info in
          begin match try_assoc g preds with
            Some (_, pmap, family, symb, body) -> [(family, pmap)]
          | None -> find_in_class super @ flatmap find_in_interf (List.map fst interfs)
          end
        | None -> fallback ()
      in
      search_classmap classmap1
        (function (_, abstract, fin, methods, fds_opt, ctors, super, tpenv, interfs, preds, pn, ilist) -> (super, interfs, preds))
        $. fun () ->
      search_classmap classmap0
        (function {csuper; cinterfs; cpreds} -> (csuper, cinterfs, cpreds))
        $. fun () ->
      []
    in
    let rec find_in_struct sn =
      match try_assoc2 sn cxx_inst_pred_map1_unchecked cxx_inst_pred_map0 with
      | Some preds ->
        begin match try_assoc g preds with
        | Some (_, pmap, family, symb, _) ->
          [family, pmap]
        | None ->
          let _, _, Some (bases, _, _), _, _ = List.assoc sn structmap in
          bases |> List.map fst |> flatmap find_in_struct
        end
      | None -> []
    in
    let candidates =
      match dialect with
      | Some Cxx -> find_in_struct tn
      | _ -> find_in_class tn @ find_in_interf tn
    in
    match candidates with
      [] -> error ()
    | [(family, pmap)] -> check_call family pmap
    | _ -> static_error l (Printf.sprintf "Ambiguous instance predicate assertion: multiple predicates named '%s' in scope" g) None
  
  let get_pred_symb p =
    let (_, _, _, _, symb, _, _) =
      try
        List.assoc p predfammap
      with
        Not_found -> raise (NoSuchPredicate (Printf.sprintf "A declaration for predicate %s is missing from the prelude" p))
    in
    symb
  let get_pure_func_symb g =
    let (_, _, _, _, symb) =
      try
        List.assoc g purefuncmap
      with Not_found -> failwith (Printf.sprintf "Pure function %s missing in the runtime library" g)
    in
    symb
  let get_pred_symb_from_map p m = let _, (_, _, _, _, symb, _, _) = List.assoc p m in symb
  let try_get_pred_symb_from_map p m = try_assoc p m |> option_map @@ fun (_, (_, _, _, _, symb, _, _)) -> symb
  
  let () =
    if Vfbindings.get Vfparam_ignore_unwind_paths vfbindings then
      ctxt#assert_term (mk_app (get_pure_func_symb "ignore_unwind_paths") [])

  let lazy_value f =
    let cell = ref None in
    fun () ->
      match !cell with
        None -> let result = f() in cell := Some result; result
      | Some result -> result
  
  let (!!) f = f ()
  
  let lazy_predfamsymb name = lazy_value (fun () -> get_pred_symb name)
  let lazy_purefuncsymb name = lazy_value (fun () -> get_pure_func_symb name)
  
  let bitand_uintN_symb = lazy_purefuncsymb "bitand_uintN"
  let bitand_intN_symb = lazy_purefuncsymb "bitand_intN"
  let bitor_uintN_symb = lazy_purefuncsymb "bitor_uintN"
  let bitor_intN_symb = lazy_purefuncsymb "bitor_intN"
  let bitxor_uintN_symb = lazy_purefuncsymb "bitxor_uintN"
  let bitxor_intN_symb = lazy_purefuncsymb "bitxor_intN"

  let truncate_unsigned_symb = lazy_purefuncsymb "truncate_unsigned"
  let truncate_signed_symb = lazy_purefuncsymb "truncate_signed"

  let mk_truncate_term tp t =
    match tp with
      Int (Unsigned, rank) ->
      let nbBits =
        match width_of_rank rank with
          LitWidth k -> ctxt#mk_intlit (1 lsl (k + 3))
        | width -> ctxt#mk_mul (ctxt#mk_intlit 8) (width_size_term width)
      in
      mk_app !!truncate_unsigned_symb [t; nbBits]
    | Int (Signed, rank) ->
      let nbBits =
        match width_of_rank rank with
          LitWidth k -> ctxt#mk_intlit (1 lsl (k + 3) - 1)
        | width -> ctxt#mk_sub (ctxt#mk_mul (ctxt#mk_intlit 8) (width_size_term width)) (ctxt#mk_intlit 1)
      in
      mk_app !!truncate_signed_symb [t; nbBits]
  
  let tparam_typeid_varname tn = tn ^ "_typeid"

  let usize_of_const_symb = lazy_purefuncsymb "usize_of_const"
  let const_of_usize_symb = lazy_purefuncsymb "const_of_usize"

  let typeid_of_type_projection traitName traitArg_typeids assocTypeName t0_typeid =
    let g = Printf.sprintf "%s::%s_typeid" traitName assocTypeName in
    mk_app (get_pure_func_symb g) (traitArg_typeids @ [t0_typeid])

  let rec typeid_of_core_core l msg env t =
  match unfold_inferred_type t with
    Int (Signed, CharRank) -> char_typeid_term
  | Int (Signed, ShortRank) -> short_typeid_term
  | Int (Signed, IntRank) -> int_typeid_term
  | Int (Signed, LongRank) -> long_typeid_term
  | Int (Signed, LongLongRank) -> llong_typeid_term
  | Int (Signed, PtrRank) -> intptr_typeid_term
  | Int (Signed, FixedWidthRank k) -> snd exact_width_integer_typeid_terms.(k)
  | Int (Unsigned, CharRank) -> uchar_typeid_term
  | Int (Unsigned, ShortRank) -> ushort_typeid_term
  | Int (Unsigned, IntRank) -> uint_typeid_term
  | Int (Unsigned, LongRank) -> ulong_typeid_term
  | Int (Unsigned, LongLongRank) -> ullong_typeid_term
  | Int (Unsigned, PtrRank) -> uintptr_typeid_term
  | Int (Unsigned, FixedWidthRank k) -> fst exact_width_integer_typeid_terms.(k)
  | RustChar -> rust_char_typeid_term
  | PtrType Void -> void_pointer_typeid_term
  | PtrType _ when fno_strict_aliasing -> void_pointer_typeid_term
  | InlineFuncType _ when fno_strict_aliasing -> void_pointer_typeid_term
  | PtrType t0 -> mk_pointer_typeid (typeid_of_core_core l msg env t0)
  | RustRefType (lft, kind, t0) ->
    let lft_typeid = typeid_of_core_core l msg env lft in
    let t0_typeid = typeid_of_core_core l msg env t0 in
    mk_rust_ref_typeid lft_typeid kind t0_typeid
  | StaticArrayType (elemTp, n) -> mk_array_typeid (typeid_of_core_core l msg env elemTp) (eval_const_type_core l msg env n)
  | LiteralConstType n -> mk_app (const_of_usize_symb ()) [ctxt#mk_intlit n]
  | Bool -> bool_typeid_term
  | Float -> float_typeid_term
  | Double -> double_typeid_term
  | LongDouble -> long_double_typeid_term
  | StructType (sn, targs) ->
    let _, _, _, _, s = List.assoc sn structmap in
    ctxt#mk_app s (List.map (typeid_of_core_core l msg env) targs)
  | InductiveType (i, targs) ->
    let (_, _, _, _, _, _, _, _, type_id_func) = List.assoc i inductivemap in
    begin match type_id_func with
      None -> static_error l (Printf.sprintf "Inductive type '%s' does not have a typeid since it contains 'any' in a negative position" i) None
    | Some type_id_func ->
      ctxt#mk_app type_id_func (List.map (typeid_of_core_core l msg env) targs)
    end;
  | UnionType un ->
    let _, _, s = List.assoc un unionmap in
    s
  | FuncType ftn ->
    begin match try_assoc ftn functypedeclmap1 with
      Some (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, terminates, predfammaps, ft_typeid) ->
      ft_typeid
    | None ->
      let (_, _, _, _, _, _, _, _, _, _, ft_typeid) = List.assoc ftn functypemap0 in
      ft_typeid
    end
  | StaticLifetime -> static_lifetime_typeid_term
  | GhostTypeParam tn | GhostTypeParamWithEqs (tn, _) | RealTypeParam tn  ->
    let x = tparam_typeid_varname tn in
    begin try
      List.assoc x env
    with
      Not_found -> static_error l (Printf.sprintf "%sUnbound variable '%s'" (msg ()) x) None
    end
  | ProjectionType (t0, traitName, traitArgs, assocTypeName) ->
    typeid_of_type_projection traitName (List.map (typeid_of_core_core l msg env) traitArgs) assocTypeName (typeid_of_core_core l msg env t0)
  | InferredType _ -> static_error l (Printf.sprintf "%sA type argument for a type parameter that carries a typeid could not be inferred; specify the type argument explicitly" (msg ())) None
  | tp -> static_error l (Printf.sprintf "%sTaking the typeid of type '%s' is not yet supported" (msg ()) (string_of_type tp)) None
  and eval_const_type_core l msg env t =
    match t with
      LiteralConstType n -> ctxt#mk_intlit n
    | _ -> mk_app (usize_of_const_symb ()) [typeid_of_core_core l msg env t]

  let no_msg _ = ""
  let typeid_of_core l env t = typeid_of_core_core l no_msg env t
  let eval_const_type l env t = eval_const_type_core l no_msg env t
  
  let typeid_of l t = typeid_of_core l [] t

  let rec sizeof_core l env t =
    match t with
      Void -> ctxt#mk_intlit 1
    | Bool -> rank_size_term CharRank
    | Int (_, k) -> rank_size_term k
    | RustChar -> width_size_term_ 2
    (* Assume IEEE-754 *)
    | Float -> width_size_term (LitWidth 2)
    | Double -> width_size_term (LitWidth 3)
    | PtrType _ | RustRefType _ -> width_size_term ptr_width
    | StructType (sn, targs) -> mk_sizeof (typeid_of_core l env t)
    | UnionType un -> union_size_partial unionmap l un
    | StaticArrayType (elemTp, elemCount) -> ctxt#mk_mul (sizeof_core l env elemTp) (eval_const_type l env elemCount)
    | GhostTypeParam x -> mk_sizeof (typeid_of_core l env t)
    | _ -> static_error l ("Taking the size of type " ^ string_of_type t ^ " is not yet supported.") None
  
  let struct_size l env sn targs = sizeof_core l env (StructType (sn, targs))
  
  let sizeof l t = sizeof_core l [] t

  let alignof_core l env t = mk_alignof (typeid_of_core l env t)

  let () = List.combine structmap1 structdeclmap |> List.iter begin fun ((sn, (l, tparams, body_opt, padding_predsym_opt, type_info_func)), (_, (_, _, _, attrs))) ->
    let assume_axiom axiom =
      if tparams = [] then
        let type_info = ctxt#mk_app type_info_func [] in
        let s = mk_sizeof type_info in
        let (name, trigger, fact) = axiom [] [] s in
        ctxt#assert_term fact
      else begin
        ctxt#begin_formal;
        let targs_env = List.mapi (fun i x -> (x ^ "_typeid", ctxt#mk_bound i ctxt#type_inductive)) tparams in
        let targs = List.map snd targs_env in
        let type_info = ctxt#mk_app type_info_func targs in
        let s = mk_sizeof type_info in
        let (name, trigger, fact) = axiom targs_env targs s in
        ctxt#end_formal;
        ctxt#assume_forall name [trigger] (List.map (fun x -> ctxt#type_inductive) tparams) fact
      end
    in
    let packed = List.mem Packed attrs in
    let repr_c = dialect <> Some Rust || List.mem ReprC attrs in
    assume_axiom (fun _ _ s -> (sn ^ "_size_limits", s, ctxt#mk_and (ctxt#mk_lt (ctxt#mk_intlit 0) s) (ctxt#mk_le s max_uintptr_term)));
    match body_opt with
    | Some (_, fmap, _) ->
      let rec offset_iter fields current is_first =
        begin match fields with
        | [] -> if packed then assume_axiom (fun targs_env targs s -> (sn ^ "_packed_size", s, ctxt#mk_eq s (current targs_env)))
        | (f, (lf, Real, t, Some offset_func, init))::fs ->
          if is_first && (fs = [] || repr_c) || packed then
            assume_axiom begin fun targs_env targs s ->
              let offset = ctxt#mk_app offset_func targs in
              (sn ^ "_" ^ f ^ "_packed_offset", offset, ctxt#mk_eq offset (current targs_env))
            end;
          offset_iter fs (fun targs_env -> ctxt#mk_add (current targs_env) (sizeof_core lf targs_env t)) false
        | _::fs -> offset_iter fs current is_first
        end
      in
      offset_iter fmap (fun targs_env -> ctxt#mk_intlit 0) true
    | None -> if packed then static_error l "A struct declaration cannot be packed." None
  end

  let pointer_ctor_symb = lazy_purefuncsymb "pointer_ctor"
  let ptr_add_symb = lazy_purefuncsymb "ptr_add"
  let ptr_add__symb = lazy_purefuncsymb "ptr_add_"
  let field_ptr_symb = lazy_purefuncsymb "field_ptr"
  let union_variant_ptr_symb = lazy_purefuncsymb "union_variant_ptr"
  let null_pointer_provenance_symb = lazy_purefuncsymb "null_pointer_provenance"
  let pointer_within_limits_symb = lazy_purefuncsymb "pointer_within_limits"
  let object_pointer_within_limits_symb = lazy_purefuncsymb "object_pointer_within_limits"
  let field_pointer_within_limits_symb = lazy_purefuncsymb "field_pointer_within_limits"
  let null_pointer_symb = lazy_purefuncsymb "null_pointer"
  let null_pointer_term =
    match language with
      Java -> fun () -> int_zero_term
    | _ -> fun () -> snd (null_pointer_symb ())
  let has_type_symb = lazy_purefuncsymb "has_type"

  let mk_ptr_add p off = mk_app (ptr_add_symb ()) [p; off]
  let rec mk_ptr_add_ l env p off elemType =
    match elemType with
      Void|Int (_, CharRank) ->
      mk_app (ptr_add_symb ()) [p; off]
    | StaticArrayType (elemTp, elemCount) ->
      mk_ptr_add_ l env p (ctxt#mk_mul off (eval_const_type l env elemCount)) elemTp
    | _ ->
      mk_app (ptr_add__symb ()) [p; off; typeid_of_core l env elemType]
  let mk_field_ptr p structTypeid off = mk_app (field_ptr_symb ()) [p; structTypeid; off]
  let mk_field_ptr_ l env p targs structTypeidFunc offsetFunc =
    let targ_typeids = List.map (typeid_of_core l env) targs in
    mk_field_ptr p (ctxt#mk_app structTypeidFunc targ_typeids) (ctxt#mk_app offsetFunc targ_typeids)
  let mk_union_variant_ptr p unionTypeName idx =
    let (_, _, unionTypeid) = List.assoc unionTypeName unionmap in
    mk_app (union_variant_ptr_symb ()) [p; unionTypeid; ctxt#mk_intlit idx]
  let mk_pointer_within_limits p = mk_app (pointer_within_limits_symb ()) [p]
  let mk_object_pointer_within_limits p size = mk_app (object_pointer_within_limits_symb ()) [p; size]
  let mk_field_pointer_within_limits p off = mk_app (field_pointer_within_limits_symb ()) [p; off]
  let mk_has_type p typeid = mk_app (has_type_symb ()) [p; typeid]

  let () =
    if not fno_strict_aliasing && List.mem_assoc "has_type" purefuncmap then begin
      ctxt#begin_formal;
      let p = ctxt#mk_bound 0 ctxt#type_inductive in
      let t = ctxt#mk_bound 1 ctxt#type_inductive in
      let hasType_t_ptr = mk_has_type p (mk_pointer_typeid t) in
      let hasType_void_ptr = mk_has_type p void_pointer_typeid_term in
      let impl = ctxt#mk_implies hasType_t_ptr hasType_void_ptr in
      ctxt#end_formal;
      ctxt#assume_forall "has_type_void_ptr" [hasType_t_ptr] [ctxt#type_inductive; ctxt#type_inductive] impl
      end

  let () =
    structmap1 |> List.iter begin function
      (sn, (_, tparams, Some (_, fmap, _), _, structTypeidFunc)) ->
      fmap |> List.iter begin function (f, (l, Real, t, Some offsetFunc, _)) ->
        ctxt#begin_formal;
        let p = ctxt#mk_bound 0 ctxt#type_inductive in
        let targs_env = List.mapi (fun i x -> (x ^ "_typeid", ctxt#mk_bound (i + 1) ctxt#type_inductive)) tparams in
        let targs = List.map snd targs_env in
        let structTypeid = ctxt#mk_app structTypeidFunc targs in
        let offset = ctxt#mk_app offsetFunc targs in
        let field_has_type = mk_has_type (mk_field_ptr p structTypeid offset) (typeid_of_core l targs_env t) in
        ctxt#end_formal;
        ctxt#assume_forall ("has_type_field_ptr_" ^ sn ^ "_" ^ f) [field_has_type] (ctxt#type_inductive::List.map (fun x -> ctxt#type_inductive) tparams) field_has_type
      | _ -> ()
      end
    | _ -> ()
    end

  let () = if fno_strict_aliasing && List.mem_assoc "has_type" purefuncmap then begin
    ctxt#begin_formal;
    let p = ctxt#mk_bound 0 ctxt#type_inductive in
    let t = ctxt#mk_bound 1 ctxt#type_inductive in
    let hasType = mk_has_type p t in
    ctxt#end_formal;
    ctxt#assume_forall "all_has_type" [hasType] [ctxt#type_inductive; ctxt#type_inductive] hasType
  end

  let () = if assume_no_subobject_provenance && List.mem_assoc "field_ptr" purefuncmap then begin
    begin
    ctxt#begin_formal;
    let pr = ctxt#mk_bound 0 ctxt#type_inductive in
    let structTypeid = ctxt#mk_bound 1 ctxt#type_inductive in
    let addr = ctxt#mk_bound 2 ctxt#type_int in
    let fp = mk_field_ptr pr structTypeid addr in
    let eq = ctxt#mk_eq fp (mk_ptr_add pr addr) in
    ctxt#end_formal;
    ctxt#assume_forall "field_ptr_eq_ptr_add" [fp] [ctxt#type_inductive; ctxt#type_inductive; ctxt#type_int] eq
    end;

    if dialect <> Some Rust then
    begin
    ctxt#begin_formal;
    let p = ctxt#mk_bound 0 ctxt#type_inductive in
    let tid = ctxt#mk_bound 1 ctxt#type_inductive in
    let i = ctxt#mk_bound 2 ctxt#type_int in
    let vp = mk_app (union_variant_ptr_symb ()) [p; tid; i] in
    let eq = ctxt#mk_eq vp p in
    ctxt#end_formal;
    ctxt#assume_forall "union_variant_ptr_eq_ptr" [vp] [ctxt#type_inductive; ctxt#type_inductive; ctxt#type_int] eq
    end
  end

  let pointer_getters = lazy_value (fun () ->
    let (_, _, _, ["provenance", ptr_provenance; "address", ptr_address], _, _, _, _, _) =
      List.assoc "pointer" inductivemap
    in
    ptr_provenance, ptr_address
  )
  
  let ptr_provenance () = fst (pointer_getters ())
  let ptr_address () = snd (pointer_getters ())

  let mk_pointer pr addr = mk_app (pointer_ctor_symb ()) [pr; addr]
  let mk_ptr_provenance p = ctxt#mk_app (ptr_provenance ()) [p]
  let mk_ptr_address p = if language = Java then p else ctxt#mk_app (ptr_address ()) [p]

  let assume_bounds term (tp: type_) = 
    match tp with
      Int (_, _) ->
      let min, max = limits_of_type tp in
      ctxt#assert_term (ctxt#mk_and (ctxt#mk_le min term) (ctxt#mk_le term max))
    | PtrType _ | RustRefType _ when language <> Java ->
      ctxt#assert_term (mk_pointer_within_limits term)
    | _ -> ()
  
  let assert_mk_pointer p =
    ctxt#assert_term (ctxt#mk_eq p (mk_pointer (mk_ptr_provenance p) (mk_ptr_address p)));
    if assume_no_provenance then ctxt#assert_term (ctxt#mk_eq (mk_ptr_provenance p) (snd (null_pointer_provenance_symb ())))

  let get_unique_var_symb_ x t ghost = 
    let result = get_unique_var_symb x t in
    if not ghost then assume_bounds result t;
    begin match language, t with
      CLang, (PtrType _|RustRefType _) -> assert_mk_pointer result
    | _ -> ()
    end;
    result

  let () = 
    globalmap1 |> List.iter (fun (x, (lg, tp, symb, ref_init)) -> assert_mk_pointer symb)

  let get_unique_var_symb_non_ghost x t = 
    get_unique_var_symb_ x t false
  
  let get_unique_var_symbs_ xts ghost = List.map (fun (x, t) -> (x, get_unique_var_symb_ x t ghost)) xts
  let get_unique_var_symbs_non_ghost xts = List.map (fun (x, t) -> (x, get_unique_var_symb_non_ghost x t)) xts
  
  let array_element_symb = lazy_predfamsymb "java.lang.array_element"
  let array_slice_symb = lazy_predfamsymb "java.lang.array_slice"
  let array_slice_deep_symb = lazy_predfamsymb "java.lang.array_slice_deep"
  
  let integer___symb = lazy_predfamsymb "integer__"
  let integers___symb = lazy_predfamsymb "integers__"
  let integer__symb = lazy_predfamsymb "integer_"
  let integers__symb = lazy_predfamsymb "integers_"
  let malloc_block_integers__symb = lazy_predfamsymb "malloc_block_integers_"

  let generic_points_to__symb = lazy_predfamsymb (if dialect = Some Rust then "points_to_" else "generic_points_to_")
  let generic_points_to_symb = lazy_predfamsymb (if dialect = Some Rust then "points_to" else "generic_points_to")
  let array__symb = lazy_predfamsymb "array_"
  let array_symb = lazy_predfamsymb "array"

  let pointee_tuple chunk_pred_name array_pred_name uninit_chunk_pred_name uninit_array_pred_name =
    let ambpn = "malloc_block_" ^ array_pred_name in
    let ambsymb = lazy_predfamsymb ambpn in
    (* no new_block_ in c, but we have to generate a dummy symb so try_pointee_pred_symb0 keeps working (c does not include the prelude of cxx) *)
    let anbpn = match dialect with Some Cxx -> "new_block_" ^ array_pred_name | _ -> "new_block_x unsupported" in
    let anbsymb = match dialect with Some Cxx -> lazy_predfamsymb anbpn | _ -> ambsymb in
    chunk_pred_name, lazy_predfamsymb chunk_pred_name, array_pred_name, lazy_predfamsymb array_pred_name, ambpn, ambsymb, anbpn, anbsymb, uninit_chunk_pred_name, lazy_predfamsymb uninit_chunk_pred_name, uninit_array_pred_name, lazy_predfamsymb uninit_array_pred_name
  
  let _, pointer_pred_symb, _, pointers_pred_symb, _, malloc_block_pointers_pred_symb, _, new_block_pointers_pred_symb, _, pointer__pred_symb, _, pointers__pred_symb as pointer_pointee_tuple = pointee_tuple "pointer" "pointers" "pointer_" "pointers_"
  let _, intptr_pred_symb, _, intptrs_pred_symb, _, malloc_block_intptrs_pred_symb, _, new_block_intptrs_pred_symb, _, intptr__pred_symb, _, intptrs__pred_symb as intptr_pointee_tuple = if dialect <> Some Rust then pointee_tuple "intptr" "intptrs" "intptr_" "intptrs_" else pointee_tuple "isize" "isizes" "isize_" "isizes_"
  let _, uintptr_pred_symb, _, uintptrs_pred_symb, _, malloc_block_uintptrs_pred_symb, _, new_block_uintptrs_pred_symb, _, uintptr__pred_symb, _, uintptrs__pred_symb as uintptr_pointee_tuple = if dialect <> Some Rust then pointee_tuple "uintptr" "uintptrs" "uintptr_" "uintptrs_" else pointee_tuple "usize" "usizes" "usize_" "usizes_"
  let _, llong_pred_symb, _, llongs_pred_symb, _, malloc_block_llongs_pred_symb, _, new_block_llongs_pred_symb, _, llong__pred_symb, _, llongs__pred_symb as llong_pointee_tuple = pointee_tuple "llong_integer" "llongs" "llong_" "llongs_"
  let _, ullong_pred_symb, _, ullongs_pred_symb, _, malloc_block_ullongs_pred_symb, _, new_block_ullongs_pred_symb, _, ullong__pred_symb, _, ullongs__pred_symb as ullong_pointee_tuple = pointee_tuple "u_llong_integer" "ullongs" "ullong_" "ullongs_"
  let _, long_pred_symb, _, longs_pred_symb, _, malloc_block_longs_pred_symb, _, new_block_longs_pred_symb, _, long__pred_symb, _, longs__pred_symb as long_pointee_tuple = pointee_tuple "long_integer" "longs" "long_" "longs_"
  let _, ulong_pred_symb, _, ulongs_pred_symb, _, malloc_block_ulongs_pred_symb, _, new_block_ulongs_pred_symb, _, ulong__pred_symb, _, ulongs__pred_symb as ulong_pointee_tuple = pointee_tuple "ulong_integer" "ulongs" "ulong_" "ulongs_"
  let _, int_pred_symb, _, ints_pred_symb, _, malloc_block_ints_pred_symb, _, new_block_ints_pred_symb, _, int__pred_symb, _, ints__pred_symb as int_pointee_tuple = pointee_tuple "integer" "ints" "int_" "ints_"
  let _, uint_pred_symb, _, uints_pred_symb, _, malloc_block_uints_pred_symb, _, new_block_uints_pred_symb, _, uint__pred_symb, _, uints__pred_symb as uint_pointee_tuple = pointee_tuple "u_integer" "uints" "uint_" "uints_"
  let _, short_pred_symb, _, shorts_pred_symb, _, malloc_block_shorts_pred_symb, _, new_block_shorts_pred_symb, _, short__pred_symb, _, shorts__pred_symb as short_pointee_tuple = pointee_tuple "short_integer" "shorts" "short_" "shorts_"
  let _, ushort_pred_symb, _, ushorts_pred_symb, _, malloc_block_ushorts_pred_symb, _, new_block_ushorts_pred_symb, _, ushort__pred_symb, _, ushorts__pred_symb  as ushort_pointee_tuple = pointee_tuple "u_short_integer" "ushorts" "ushort_" "ushorts_"
  let _, char_pred_symb, _, chars_pred_symb, _, malloc_block_chars_pred_symb, _, new_block_chars_pred_symb, _, char__pred_symb, _, chars__pred_symb  as char_pointee_tuple = pointee_tuple "character" "chars" "char_" "chars_"
  let _, uchar_pred_symb, _, uchars_pred_symb, _, malloc_block_uchars_pred_symb, _, new_block_uchars_pred_symb, _, uchar__pred_symb, _, uchars__pred_symb as uchar_pointee_tuple = pointee_tuple "u_character" "uchars" "uchar_" "uchars_"
  let _, bool_pred_symb, _, bools_pred_symb, _, malloc_block_bools_pred_symb, _, new_block_bools_pred_symb, _, bool__pred_symb, _, bools__pred_symb  as bool_pointee_tuple = pointee_tuple "boolean" "bools" "bool_" "bools_"
  let _, float__pred_symb, _, floats_pred_symb, _, malloc_block_floats_pred_symb, _, new_block_floats_pred_symb, _, float___pred_symb, _, floats__pred_symb  as float_pointee_tuple = pointee_tuple "float_" "floats" "float__" "floats_"
  let _, double__pred_symb, _, doubles_pred_symb, _, malloc_block_doubles_pred_symb, _, new_block_doubles_pred_symb, _, double___pred_symb, _, doubles__pred_symb as double_pointee_tuple = pointee_tuple "double_" "doubles" "double__" "doubles_"
  let _, long_double_pred_symb, _, long_doubles_pred_symb, _, malloc_block_long_doubles_pred_symb, _, new_block_long_doubles_pred_symb, _, long_double__pred_symb, _, long_doubles__pred_symb as long_double_pointee_tuple = pointee_tuple "long_double" "long_doubles" "long_double_" "long_doubles_"
  
  let deref_pointee_tuple (cn, csym, an, asym, mban, mbasym, nban, nbasym, ucn, ucsym, uan, uasym) = (cn, csym(), an, asym(), mban, mbasym, nban, nbasym, ucn, ucsym(), uan, uasym())
  
  let try_pointee_pred_symb0 pointeeType =
    if dialect = Some Rust then None else
    option_map deref_pointee_tuple
    begin match pointeeType with
      PtrType _ -> Some pointer_pointee_tuple
    | Int (Signed, PtrRank) -> Some intptr_pointee_tuple
    | Int (Unsigned, PtrRank) -> Some uintptr_pointee_tuple
    | Int (Signed, CharRank) -> Some char_pointee_tuple
    | Int (Unsigned, CharRank) -> Some uchar_pointee_tuple
    | Int (Signed, ShortRank) -> Some short_pointee_tuple
    | Int (Unsigned, ShortRank) -> Some ushort_pointee_tuple
    | Int (Signed, IntRank) -> Some int_pointee_tuple
    | Int (Unsigned, IntRank) -> Some uint_pointee_tuple
    | Int (Signed, LongRank) -> Some long_pointee_tuple
    | Int (Unsigned, LongRank) -> Some ulong_pointee_tuple
    | Int (Signed, LongLongRank) -> Some llong_pointee_tuple
    | Int (Unsigned, LongLongRank) -> Some ullong_pointee_tuple
    | Bool -> Some bool_pointee_tuple
    | Float -> Some float_pointee_tuple
    | Double -> Some double_pointee_tuple
    | LongDouble -> Some long_double_pointee_tuple
    | _ -> None
    end
  
  let supported_types_text = "int, unsigned int, char, unsigned char, or a pointer type"
  
  let try_pointee_pred_symb pointeeType = option_map (fun (_, x, _, _, _, _, _, _, _, _, _, _) -> x) (try_pointee_pred_symb0 pointeeType)
  
  let list_type elemType = InductiveType ("list", [elemType])
  let option_type elemType = InductiveType ("option", [elemType])

  let integer__chunk_args tp =
    if dialect = Some Rust then None else int_rank_and_signedness tp
  
  let rec check_asn_core (pn,ilist) tparams tenv p =
    let pre_tenv = tenv in
    let rec check_asn tenv p =
      match p with
      | PointsTo (l, ReadArray (lread, earray, SliceExpr (lslice, pstart, pend)), kind, rhs) ->
        let (earray, slices) =
          let rec get_slices = function
            ReadArray (lread0, earray0, SliceExpr (lslice0, pstart0, pend0)) when language = CLang ->
            let (earray, slices) = get_slices earray0 in
            (earray, (lslice0, pstart0, pend0)::slices)
          | earray ->
            (earray, [])
          in
          get_slices earray
        in
        let slices = (lslice, pstart, pend)::slices in
        let (warray, tarray) = check_expr (pn,ilist) tparams tenv (Some true) earray in
        let (wslices, tenv) =
          let rec check_slices tenv = function
            [] -> ([], tenv)
          | (lslice, pstart, pend)::slices ->
            let (wslices, tenv) = check_slices tenv slices in
            let (wstart, tenv) =
              match pstart with
                None -> (None, tenv)
              | Some pstart ->
                let (wstart, tenv) = check_pat (pn,ilist) tparams tenv intType pstart in
                Some wstart, tenv
            in
            let (wend, tenv) =
              match pend with
                None -> (None, tenv)
              | Some pend ->
                let (wend, tenv) = check_pat (pn,ilist) tparams tenv intType pend in
                Some wend, tenv
            in
            ((lslice, wstart, wend)::wslices, tenv)
          in
          check_slices tenv slices
        in
        let (lslice, wstart, wend)::wslices = List.rev wslices in
        begin match language with
        | CLang ->
          let elemtype =
            match tarray with
              PtrType t -> t
            | StaticArrayType (t, _) -> t
            | _ -> static_error lread "Array in array dereference must be of pointer type." None
          in
          let elemtype, multiplier =
            let rec check_slices elemtype wslices =
              match wslices with
                [] -> elemtype, 1
              | (lslice, wstart, wend)::wslices ->
                match elemtype with
                  StaticArrayType (elemtype, LiteralConstType elemCount) ->
                  begin match wstart with
                    None -> ()
                  | Some (LitPat (WIntLit (_, n))) when eq_big_int n zero_big_int -> ()
                  | _ -> static_error lslice "Start of slice, if specified, must be zero" None
                  end;
                  begin match wend with
                    None -> ()
                  | Some (LitPat (WIntLit (_, n))) when eq_big_int n (big_int_of_int elemCount) -> ()
                  | _ -> static_error lslice (Printf.sprintf "End of slice, if specified, must equal array size (%d)" elemCount) None
                  end;
                  let elemtype, multiplier = check_slices elemtype wslices in
                  elemtype, multiplier * elemCount
                | _ ->
                  static_error lslice (Printf.sprintf "Cannot use a slice here to subscript an expression of type %s; array type expected" (string_of_type elemtype)) None
            in
            check_slices elemtype wslices
          in
          let wstart, wend =
            if multiplier = 1 then
              wstart, wend
            else
              let wstart =
                match wstart with
                  None -> None
                | Some (LitPat w) -> Some (LitPat (WOperation (expr_loc w, Mul, [w; WIntLit (expr_loc w, big_int_of_int multiplier)], intType)))
                | _ -> static_error lslice "In this multi-dimensional array assertion, the start pattern of the slice must be an expression" None
              in
              let wend =
                match wend with
                | Some (LitPat w) -> Some (LitPat (WOperation (expr_loc w, Mul, [w; WIntLit (expr_loc w, big_int_of_int multiplier)], intType)))
                | _ -> static_error lslice "In this multi-dimensional array assertion, the end of the slice must be specified as an expression" None
              in
              wstart, wend
          in
          let rhsElemType = match kind with RegularPointsTo -> elemtype | MaybeUninit -> option_type elemtype in
          let (wrhs, tenv) = check_pat (pn,ilist) tparams tenv (list_type rhsElemType) rhs in
          let wfirst, wlength =
            match wstart, wend with
              None, Some wend -> warray, wend
            | Some (LitPat (WIntLit (_, n))), Some wend when eq_big_int n zero_big_int -> warray, wend
            | Some (LitPat wstart), Some (LitPat wend) ->
              WOperation (lslice, Add, [warray; wstart], PtrType elemtype),
              LitPat (WOperation (lslice, Sub, [wend; wstart], intType))
            | _ -> static_error l "Malformed array assertion." None
          in
          begin match try_pointee_pred_symb0 elemtype with
            Some (pointee_pred_name, pointee_pred_symb, array_pred_name, array_pred_symb, _, _, _, _, _, _, uninit_array_pred_name, _) ->
            let array_pred_name = if wrhs = DummyPat || kind = MaybeUninit then uninit_array_pred_name else array_pred_name in
            let p = new predref (PredFam array_pred_name) [PtrType elemtype; intType; list_type rhsElemType] (Some 2) in
            let predAsn = WPredAsn (l, p, true, [], [], [LitPat wfirst; wlength; wrhs]) in
            let asn =
              if fno_strict_aliasing || not (is_ptr_type elemtype) then
                predAsn
              else
                Sep (l, predAsn, ExprAsn (l, WPureFunCall (l, "has_type", [], [wfirst; TypeInfo (l, elemtype)])))
            in
            (asn, tenv, [])
          | None ->
          match integer__chunk_args elemtype with
            Some (k, signedness) ->
            let predname, pred_elemtype = if wrhs = DummyPat || kind = MaybeUninit then "integers__", option_type elemtype else "integers_", elemtype in
            let p = new predref (PredFam predname) [PtrType Void; intType; Bool; intType; list_type pred_elemtype] (Some 4) in
            let predAsn = WPredAsn (l, p, true, [], [], [LitPat wfirst; LitPat (SizeofExpr (l, TypeExpr (ManifestTypeExpr (l, elemtype)))); LitPat (if signedness = Signed then True l else False l); wlength; wrhs]) in
            let asn =
              if fno_strict_aliasing then
                predAsn
              else
                Sep (l, predAsn, ExprAsn (l, WPureFunCall (l, "has_type", [], [wfirst; TypeInfo (l, elemtype)])))
            in
            (asn, tenv, [])
          | None ->
            let array_pred_name, elemtype' = if wrhs = DummyPat || kind = MaybeUninit then "array_", option_type elemtype else "array", elemtype in
            let p = new predref (PredFam array_pred_name) [PtrType elemtype; intType; list_type elemtype'] (Some 2) in
            (WPredAsn (l, p, true, [elemtype], [], [LitPat wfirst; wlength; wrhs]), tenv, [])
          end
        | Java ->
          let elemtype =
            match tarray with
              ArrayType t -> t
            | _ -> static_error lread "Array in array dereference must be of array type." None
          in
          let (wrhs, tenv) = check_pat (pn,ilist) tparams tenv (list_type elemtype) rhs in
          let p = new predref (PredFam "java.lang.array_slice") [ArrayType elemtype; intType; intType; list_type elemtype] (Some 3) in
          let wstart = match wstart with None -> LitPat (wintlit lslice zero_big_int) | Some wstart -> wstart in
          let wend = match wend with None -> LitPat (ArrayLengthExpr (lslice, warray)) | Some wend -> wend in
          let args = [LitPat warray; wstart; wend; wrhs] in
          (WPredAsn (l, p, true, [elemtype], [], args), tenv, [])
        end
      | PointsTo (l, lhs, kind, v) ->
        let (wlhs, t) = check_expr (pn,ilist) tparams tenv (Some true) lhs in
        begin match wlhs with
          WRead (_, _, _, _, _, _, _, _, _, _) | WReadArray (_, _, _, _) -> ()
        | WVar (_, _, GlobalName) -> ()
        | WDeref (_, _, _)  -> ()
        | _ -> static_error l "The left-hand side of a points-to assertion must be a field dereference, a global variable, a pointer variable dereference or an array element expression." None
        end;
        let (wv, tenv') = check_pat (pn,ilist) tparams tenv (match kind with RegularPointsTo -> t | MaybeUninit -> option_type t) v in
        (WPointsTo (l, wlhs, t, kind, wv), tenv', [])
      | PredExprAsn (l, e, args) ->
        let w, tp = check_expr (pn,ilist) tparams tenv (Some true) e in
        let pts, inputParamCount =
          match tp with
            PredType (tparams, pts, inputParamCount, inductiveness) ->
            if tparams <> [] then static_error l "Cannot call a generic predicate here" None;
            pts, inputParamCount
          | _ -> static_error l "The callee of a predicate assertion must be of predicate type" None
        in
        let wargs, tenv' = check_pats (pn,ilist) l tparams tenv pts args in
        (WPredExprAsn (l, w, pts, inputParamCount, wargs), tenv', [])
      | PredAsn (l, p, targs, ps0, ps, binding) ->
        let targs = List.map (check_pure_type (pn, ilist) tparams Ghost) targs in
        begin fun cont ->
          match (try_assoc p tenv |> option_map unfold_inferred_type), binding with
            Some (PredType (callee_tparams, ts, inputParamCount, inductiveness)), (Static|LocalVarPredCall) -> cont ((LocalVar p: pred_name), false, callee_tparams, [], ts, inputParamCount)
          | _ ->
            begin match resolve Ghost (pn,ilist) l p predfammap, binding with
              Some (pname, (lp, callee_tparams, arity, xs, _, inputParamCount, inductiveness)), (Static|PredFamCall) ->
              reportUseSite DeclKind_Predicate lp l;
              let ts0 = match file_type path with
                Java-> list_make arity (ObjType ("java.lang.Class", []))
              | _   -> list_make arity (PtrType Void)
              in
              cont (PredFam pname, true, callee_tparams, ts0, xs, inputParamCount)
            | _ ->
              begin match
                if binding <> Static && binding <> PredCtorCall then None else
                match resolve Ghost (pn,ilist) l p purefuncmap with
                  Some (p, (lp, tparams, PredType ([], ps2, inputParamCount, Inductiveness_Inductive), ps1, funcsym)) ->
                  reportUseSite DeclKind_Predicate lp l;
                  Some (p, tparams, ps1, ps2, inputParamCount)
                | _ -> None
              with
                Some (p, tparams, ps1, ps2, inputParamCount) ->
                cont (PredCtor p, true, tparams, List.map snd ps1, ps2, inputParamCount)
              | None ->
                let error () = 
                  begin match try_assoc p tenv with
                    None ->  static_error l ("No such predicate: " ^ p) None 
                  | Some _ -> static_error l ("Variable " ^ p ^ " is not of predicate type.") None 
                  end
                in
                let check_pats pmap =
                  if targs <> [] then static_error l "Incorrect number of type arguments." None;
                  if ps0 <> [] then static_error l "Incorrect number of indices." None;
                  check_pats (pn, ilist) l [] tenv (List.map snd pmap) ps
                in
                begin match try_assoc "this" tenv with
                  None -> error ()
                | Some (ObjType (cn, _)) ->
                  let check_call family pmap =
                    let wps, tenv = check_pats pmap in
                    let index =
                      if List.mem_assoc cn classmap1 || List.mem_assoc cn classmap0 then
                        ClassLit (l, cn)
                      else
                        get_class_of_this
                    in
                    (WInstPredAsn (l, None, cn, get_class_finality cn, family, p, index, wps), tenv, [])
                  in
                  check_inst_pred_asn l cn p check_call error
                | Some (PtrType (StructType (sn, []))) ->
                  let check_call family pmap =
                    let wps, tenv = check_pats pmap in
                    let index = WVar (l, "thisType", LocalVar) in
                    WInstPredAsn (l, None, sn, ExtensibleClass, family, p, index, wps), tenv, []
                  in
                  check_inst_pred_asn l sn p check_call error
                | Some(_) -> error ()
                end
              end
            end
        end $. fun (p, is_global_predref, callee_tparams, ts0, xs, inputParamCount) ->
        begin
          let (targs, tpenv, inferredTypes) =
            if targs = [] then
              let tpenv = List.map (fun x -> (x, (object end), ref Unconstrained)) callee_tparams in
              (List.map (fun (x, o, r) -> InferredType (o, r)) tpenv,
              List.map (fun (x, o, r) -> (x, InferredType (o, r))) tpenv,
              List.map (fun (x, o, r) -> r) tpenv)
            else
              match zip callee_tparams targs with
                None -> static_error l (Printf.sprintf "Predicate requires %d type arguments." (List.length callee_tparams)) None
              | Some bs -> (targs, bs, [])
          in
          if List.length ps0 <> List.length ts0 then static_error l "Incorrect number of indexes." None;
          let (wps0, tenv) = check_pats (pn,ilist) l tparams tenv ts0 ps0 in
          let xs' = List.map (instantiate_type tpenv) xs in
          let (wps, tenv) = check_pats (pn,ilist) l tparams tenv xs' ps in
          let p = new predref p (ts0 @ xs') inputParamCount in
          (WPredAsn (l, p, is_global_predref, targs, wps0, wps), tenv, inferredTypes)
        end
      | InstPredAsn (l, e, g, index, pats) ->
        let error l tn () = static_error l (Printf.sprintf "Type '%s' does not declare such a predicate." tn) None in
        let (w, t) = check_expr (pn,ilist) tparams tenv (Some true) e in
        begin match t with
        | ObjType (cn, targs) ->
          let check_call family pmap =
            let (wpats, tenv) = check_pats (pn,ilist) l [] tenv (List.map snd pmap) pats in
            let index = check_expr_t (pn,ilist) [] tenv (Some true) index (ObjType ("java.lang.Class", [])) in
            (WInstPredAsn (l, Some w, cn, get_class_finality cn, family, g, index, wpats), tenv, [])
          in
          check_inst_pred_asn l cn g check_call (error l cn)
        | PtrType (StructType (sn, [])) ->
          let check_call family pmap =
            match index with
            | CallExpr (_, "typeid", [], [], [], Instance) when is_polymorphic_struct sn ->
              let target_name w =
                let rec aux = function
                | WVar (_, name, _) -> "#" ^ name
                | AddressOf (_, WDeref (_, w, _)) -> aux w
                in
                aux w
              in
              let vtype_var, index_var = 
                let var_name = target_name w in
                let index_var = Var (l, var_name) in
                if (not (List.mem_assoc var_name pre_tenv)) then
                  VarPat (l, var_name), index_var
                else
                  LitPat (Var (l, var_name)), index_var
              in
              let a, tenv, _ = check_asn tenv (Sep (
                l, 
                CallExpr (l, vtype_pred_name sn, [], [], [LitPat (TypedExpr (w, t)); vtype_var], Static),
                InstPredAsn (l, TypedExpr (w, t), g, index_var, pats)))
              in
              a, tenv, []
            | CallExpr (_, "typeid", [], [], [], Instance) ->
              let wpats, tenv = check_pats (pn, ilist) l [] tenv (List.map snd pmap) pats in
              let index = TypeInfo (l, StructType (sn, [])) in
              WInstPredAsn (l, Some w, sn, ExtensibleClass, family, g, index, wpats), tenv, []
            | _ -> 
              let wpats, tenv = check_pats (pn, ilist) l [] tenv (List.map snd pmap) pats in
              let index = check_expr_t (pn, ilist) [] tenv (Some true) index type_info_ptr_type in
              WInstPredAsn (l, Some w, sn, ExtensibleClass, family, g, index, wpats), tenv, []
          in
          check_inst_pred_asn l sn g check_call (error l sn)
        | _ when dialect = Some Cxx -> static_error l "Target of instance predicate assertion must be of type: pointer to struct." None
        | _ -> static_error l "Target of instance predicate assertion must be of class type." None
        end
      | ExprAsn (l, e) ->
        let w = check_expr_t (pn,ilist) tparams tenv (Some true) e boolt in (ExprAsn (l, w), tenv, [])
      | MatchAsn (l, e1, pat) ->
        let (w1, t) = check_expr (pn,ilist) tparams tenv (Some true) e1 in
        let (wpat, tenv) = check_pat (pn,ilist) tparams tenv t pat in
        (WMatchAsn (l, w1, wpat, t), tenv, [])
      | LetTypeAsn (l, x, t, p) ->
        if List.mem x tparams then static_error l "Duplicate type parameter" None;
        let (p, tenv, infTps) = check_asn_core (pn,ilist) (x::tparams) tenv p in
        let tpenv = (x, t)::List.map (fun x -> (x, GhostTypeParam x)) tparams in
        let tenv = List.map (fun (x, t) -> (x, instantiate_type tpenv t)) tenv in
        (LetTypeAsn (l, x, t, p), tenv, infTps)
      | Sep (l, p1, p2) ->
        let (p1, tenv, infTps1) = check_asn tenv p1 in
        let (p2, tenv, infTps2) = check_asn tenv p2 in
        (Sep (l, p1, p2), tenv, infTps1 @ infTps2)
      | IfExpr (l, e, p1, p2) ->
        let w = check_expr_t (pn,ilist) tparams tenv (Some true) e boolt in
        let (wp1, _, infTps1) = check_asn tenv p1 in
        let (wp2, _, infTps2) = check_asn tenv p2 in
        (IfAsn (l, w, wp1, wp2), tenv, infTps1 @ infTps2)
      | SwitchExpr (l, e, cs, cdef) ->
        let (w, t) = check_expr (pn,ilist) tparams tenv (Some true) e in
        let wcdef = Option.map (fun (l, cdef) -> (l, check_asn tenv cdef)) cdef in
        begin
        match t with
        | InductiveType (i, targs) ->
          begin
          match try_assoc i inductivemap with
            None -> static_error l "Switch operand is not an inductive value." None
          | Some (_, inductive_tparams, ctormap, _, _, _, _, _, _) ->
            let (Some tpenv) = zip inductive_tparams targs in
            let rec iter wcs (ctormap: (string * inductive_ctor_info) list) cs infTps =
              match cs with
                [] ->
                if ctormap = [] && wcdef <> None then static_error l "Superfluous default clause" None;
                let default_wcs = 
                  ctormap |> List.map @@ fun (cn, (full_cn, (_, _, _, param_names_types, _))) ->
                    let (_, ts) = List.split param_names_types in
                    let xsInfo = ts |> List.map (fun t -> match unfold_inferred_type t with GhostTypeParam x -> Some (provertype_of_type (List.assoc x tpenv)) | _ -> None) in
                    match wcdef with
                      None -> static_error l (Printf.sprintf "A clause for constructor '%s' is missing" cn) None
                    | Some (lcdef, (wcdef, _, clauseInfTps)) ->
                      WSwitchAsnClause (lcdef, cn, full_cn, List.map (fun _ -> None) param_names_types, xsInfo, wcdef)
                in
                let cdefInfTps = match wcdef with None -> [] | Some (_, (_, _, cdefInfTps)) -> cdefInfTps in
                (WSwitchAsn (l, w, i, List.rev default_wcs @ wcs), tenv, cdefInfTps @ infTps)
              | SwitchExprClause (lc, cn, xs, body)::cs ->
                begin
                match try_assoc cn ctormap with
                  None -> static_error lc "No such constructor." None
                | Some (full_cn, (_, _, _, param_names_types, _)) ->
                  let (_, ts) = List.split param_names_types in
                  let (xmap, xsInfo) =
                    let rec iter xmap xsInfo ts xs =
                      match (ts, xs) with
                        ([], []) -> (xmap, List.rev xsInfo)
                      | (t::ts, x::xs) ->
                        if List.mem_assoc x tenv then static_error lc ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
                        let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." None in
                        let xInfo = match unfold_inferred_type t with GhostTypeParam x -> Some (provertype_of_type (List.assoc x tpenv)) | _ -> None in
                        iter ((x, instantiate_type tpenv t)::xmap) (xInfo::xsInfo) ts xs
                      | ([], _) -> static_error lc "Too many pattern variables." None
                      | _ -> static_error lc "Too few pattern variables." None
                    in
                    iter [] [] ts xs
                  in
                  let tenv = xmap @ tenv in
                  let (wbody, _, clauseInfTps) = check_asn tenv body in
                  let xs = List.map (fun x -> Some x) xs in
                  iter (WSwitchAsnClause (lc, cn, full_cn, xs, xsInfo, wbody)::wcs) (List.remove_assoc cn ctormap) cs (clauseInfTps @ infTps)
                end
            in
            iter [] ctormap cs []
          end
        | _ -> static_error l "Switch operand is not an inductive value." None
        end
      | EmpAsn l -> (p, tenv, [])
      | ForallAsn (l, te, i, e) -> 
        begin match try_assoc i tenv with
          None -> 
            let t = check_pure_type (pn,ilist) tparams Ghost te in
            let w = check_expr_t (pn,ilist) tparams ((i, t) :: tenv) (Some true) e boolt in
            (ForallAsn(l, ManifestTypeExpr(l, t), i, w), tenv, [])
        | Some _ -> static_error l ("bound variable " ^ i ^ " hides existing local variable " ^ i) None
        end
      | CoefAsn (l, DummyVarPat, _) ->
        static_error l "Dummy variable pattern fractions are not yet supported" None
      | CoefAsn (l, coef, body) ->
        begin match body with
          CoefAsn _ ->
            static_error l ("Consecutive fractional permission coefficients found. Permissions of the form `[f1][f2]p' are not supported.") None
        | _ ->
          let (wcoef, tenv') = check_pat_core (pn,ilist) tparams tenv RealType coef in
          let (wbody, tenv, infTps) = check_asn tenv body in
          (CoefAsn (l, wcoef, wbody), merge_tenvs l tenv' tenv, infTps)
        end
      | EnsuresAsn (l, result_var, body) ->
        begin match try_assoc "#pre" tenv with
          None -> static_error l "Ensures clause not allowed here." None
        | Some rt ->
          let tenv = List.remove_assoc "#pre" tenv in
          let tenv = if rt = Void then tenv else (result_var, rt)::tenv in
          let (wbody, tenv, infTps) = check_asn tenv body in
          (EnsuresAsn (l, result_var, wbody), tenv, infTps)
        end
      | e ->
        let a =
          match e with
          | CallExpr (l, g, targs, pats0, pats, binding) when binding <> Instance -> PredAsn (l, g, targs, pats0, pats, binding)
          | ExprCallExpr (l, e, args) -> PredExprAsn (l, e, args)
          | CallExpr (l, g, [], pats0, LitPat e::pats, Instance) ->
            let index =
              match pats0 with
              | [] when dialect = Some Cxx -> CallExpr (l, "typeid", [], [], [], Instance)
              | [] -> CallExpr (l, "getClass", [], [], [LitPat e], Instance)
              | [LitPat e] -> e
              | _ -> raise (ParseException (l, "Instance predicate call: single index expression expected"))
            in
            InstPredAsn (l, e, g, index, pats)
          | Operation (l, Eq, [e1; e2]) ->
            begin match pat_of_expr e2 with
              LitPat e2 -> ExprAsn (l, e)
            | e2 -> MatchAsn (l, e1, e2)
            end
          | _ -> ExprAsn (expr_loc e, e)
        in
        check_asn tenv a
    in
    check_asn tenv p
  
  let rec fix_inferred_type r =
    match !r with
      EqConstraint t -> fix_inferred_types_in_type t
    | _ -> r := EqConstraint (InductiveType ("unit", []))
  and fix_inferred_types_in_type t =
    match t with
      InferredType (_, r) -> fix_inferred_type r
    | InductiveType (i, targs) -> List.iter fix_inferred_types_in_type targs
    | _ -> ()
  
  let fix_inferred_types rs = List.iter fix_inferred_type rs
  
  let check_asn (pn,ilist) tparams tenv p =
    let (wpred, tenv, infTypes) = check_asn_core (pn,ilist) tparams tenv p in
    fix_inferred_types infTypes;
    (wpred, tenv)
  
  let boxmap =
    List.map
      begin
        fun (bcn, (l, boxpmap, inv, amap, hpmap,pn,ilist)) ->
        let (winv, boxvarmap) = check_asn (pn,ilist) [] (("this", BoxIdType) :: boxpmap)  inv in
        let old_boxvarmap = List.map (fun (x, t) -> ("old_" ^ x, t)) boxvarmap in
        let amap =
        List.map
          (fun (an, (l, action_pred_sym, pmap, pre, post)) ->
             let pre = check_expr_t (pn,ilist) [] ([("actionHandles", list_type HandleIdType)] @ pmap @ boxvarmap) None pre boolt in
             let post = check_expr_t (pn,ilist) [] ([("actionHandles", list_type HandleIdType)] @ pmap @ boxvarmap @ old_boxvarmap) None post boolt in
             (an, (l, action_pred_sym, pmap, pre, post))
          )
          amap
        in
        let hpmap =
        List.map
          (fun (hpn, (l, pmap, einv, inv, pbcs)) ->
             let (winv, _) = check_asn (pn,ilist) [] ([("predicateHandle", HandleIdType)] @ pmap @ boxvarmap) inv in
             (hpn, (l, pmap, einv, winv, pbcs))
          )
          hpmap
        in
        hpmap |> List.iter begin fun (hpn, (l, pmap, einv, inv, pncs)) ->
          match einv with 
            None -> ()
          | Some ehn -> 
            let (el, epmap, extendedInv, einv, epbcs) = List.assoc ehn hpmap in
            match einv with ExprAsn (_, _) -> () | _ -> static_error l "Extended handle's invariant must be pure assertion." None
        end; 
        (bcn, (l, boxpmap, winv, boxvarmap, amap, hpmap))
      end
      boxmap
  
  (* Region: predicate preciseness check *)
  
  let rec vars_used e =
    let rec iter state e =
      match e with
      | WVar (l, x, scope) -> begin match scope with LocalVar -> x::state | _ -> state end
      | WSwitchExpr (l, e, _, _, cs, cdef_opt, _, _) ->
        vars_used e @
        flatmap
          (fun (SwitchExprClause (l, c, xs, e)) ->
           let xs' = vars_used e in
           List.filter (fun x -> not (List.mem x xs)) xs'
          )
          cs @
        (match cdef_opt with None -> [] | Some (l, e) -> vars_used e) @
        state
      | e -> expr_fold_open iter state e
    in
    iter [] e
  
  let assert_expr_fixed fixed e =
    let used = vars_used e in
    let nonfixed = List.filter (fun x -> not (List.mem x fixed)) used in
    if nonfixed <> [] then
      let xs = String.concat ", " (List.map (fun x -> "'" ^ x ^ "'") nonfixed) in
      static_error (expr_loc e) ("Preciseness check failure: non-fixed variable(s) " ^ xs ^ " used in input expression.") None
  
  let rec fixed_pat_fixed_vars pat =
    match pat with
      LitPat (WVar (_, x, LocalVar)) -> [x]
    | LitPat _ -> []
    | VarPat (_, x) -> [x]
    | DummyPat|DummyVarPat -> []
    | WCtorPat (l, i, targs, g, ts0, ts, pats, _) ->
      List.concat (List.map fixed_pat_fixed_vars pats)
  
  let assume_pat_fixed fixed pat =
    fixed_pat_fixed_vars pat @ fixed
  
  let rec assert_pats_fixed l fixed pats =
    List.iter (assert_pat_fixed l fixed) pats
  and assert_pat_fixed l fixed = function
    LitPat e ->
    assert_expr_fixed fixed e
  | WCtorPat (_, _, _, _, _, _, pats, _) ->
    assert_pats_fixed l fixed pats
  | _ ->
    static_error l "Non-fixed pattern used in input position." None
  
  let assume_pats_fixed fixed pats =
    flatmap fixed_pat_fixed_vars pats @ fixed
  
  let expr_is_fixed fixed e =
    let used = vars_used e in
    List.for_all (fun x -> List.mem x fixed) used
  
  let rec check_pred_precise fixed p =
    match p with
      WPointsTo (l, lhs, tp, kind, pv) ->
      begin match lhs with
        WRead (lr, et, _, _, _, _, _, _, _, _) -> assert_expr_fixed fixed et
      | WReadArray (la, ea, tp, ei) -> assert_expr_fixed fixed ea; assert_expr_fixed fixed ei
      | WVar (_, _, GlobalName) -> ()
      | WDeref (_, ed, _) -> assert_expr_fixed fixed ed
      end;
      assume_pat_fixed fixed pv
    | WPredExprAsn (l, e, pts, inputParamCount, pats) ->
      begin match inputParamCount with
        None -> static_error l "Preciseness check failure: callee is not precise." (Some "calleeisnotprecise")
      | Some n ->
        let (inpats, outpats) = take_drop n pats in
        assert_pats_fixed l fixed inpats;
        assume_pats_fixed fixed outpats
      end
    | WPredAsn (l, g, is_global_predref, targs, pats0, pats) ->
      begin
        match g#inputParamCount with
          None -> static_error l "Preciseness check failure: callee is not precise." (Some "calleeisnotprecise")
        | Some n ->
          let (inpats, outpats) = take_drop n pats in
          let inpats = pats0 @ inpats in
          assert_pats_fixed l fixed inpats;
          assume_pats_fixed fixed outpats
      end
    | WInstPredAsn (l, e_opt, st, cfin, tn, g, index, pats) ->
      begin match e_opt with None -> () | Some e -> assert_expr_fixed fixed e end;
      assert_expr_fixed fixed index;
      assume_pats_fixed fixed pats
    | ExprAsn (l, WOperation (_, Eq, [WVar (_, x, LocalVar); e2], _)) ->
      if not (List.mem x fixed) && expr_is_fixed fixed e2 then
        x::fixed
      else
        fixed
    | ExprAsn (_, _) -> fixed
    | WMatchAsn (l, e, pat, tp) ->
      if expr_is_fixed fixed e then
        fixed_pat_fixed_vars pat @ fixed
      else
        fixed
    | LetTypeAsn (_, _, _, p) ->
      check_pred_precise fixed p
    | Sep (l, p1, p2) ->
      let fixed = check_pred_precise fixed p1 in
      check_pred_precise fixed p2
    | IfAsn (l, e, p1, p2) ->
      assert_expr_fixed fixed e;
      let fixed1 = check_pred_precise fixed p1 in
      let fixed2 = check_pred_precise fixed p2 in
      intersect fixed1 fixed2
    | WSwitchAsn (l, e, i, cs) ->
      assert_expr_fixed fixed e;
      let rec iter fixed' cs =
        match cs with
          [] -> get fixed'
        | WSwitchAsnClause (l, c, full_cn, xs, _, p)::cs ->
          let xs = flatmap (function None -> [] | Some x -> [x]) xs in
          let fixed = check_pred_precise (xs@fixed) p in
          iter (Some (match fixed' with None -> fixed | Some fixed' -> intersect fixed' fixed)) cs
      in
      iter None cs
    | EmpAsn l -> fixed
    | ForallAsn (l, _, i, e) -> fixed
    | CoefAsn (l, coefpat, p) ->
      begin
        match coefpat with
          LitPat e -> assert_expr_fixed fixed e
        | VarPat (_, x) -> static_error l "Precision check failure: variable patterns not supported as coefficients." None
        | DummyPat|DummyVarPat -> ()
      end;
      check_pred_precise fixed p
  
  (* Region: Predicate instances *)
  
  let predinstmap1 =
    flatmap
      begin
        function
          (sn, (lsn, tparams, Some (_, fmap, _), padding_symb_opt, _)) ->
          let targs = tparams_as_targs tparams in
          begin match padding_symb_opt, fmap with
          | Some symb, [_] ->
            (* Single-field structs have no padding *)
            [(padding_pred_name sn, []),
             ([], lsn, tparams, [sn, PtrType (StructType (sn, targs))], symb, Some 1,
              EmpAsn lsn)]
          | _ -> []
          end
          @
          flatmap
            begin
              function
                (f, (l, Real, t, offset, _)) ->
                begin
                let ((g, (_, _, _, _, symb, _, _)), g__opt) = List.assoc (sn, f) field_pred_map in
                let predinst___ p p_ domain0 t args =
                  let p = new predref (PredFam p) (domain0 @ [t]) (Some (1 + List.length args)) in
                  let p_ = new predref (PredFam p_) (domain0 @ [InductiveType ("option", [t])]) (Some (1 + List.length args)) in
                  let inst =
                  ((g, []),
                   ([], l, tparams, [sn, PtrType (StructType (sn, targs)); "value", t], symb, Some 1,
                    let r = WRead (l, WVar (l, sn, LocalVar), sn, tparams, f, t, targs, false, ref (Some None), Real) in
                    WPredAsn (l, p, true, [], [], ([LitPat (AddressOf (l, r))] @ List.map (fun e -> LitPat e) args @ [LitPat (WVar (l, "value", LocalVar))]))
                   )
                  )
                  in
                  match g__opt with
                    None -> [inst]
                  | Some (g_, (_, _, _, _, symb_, _, _)) ->
                    [
                      inst
                    ;
                      ((g_, []),
                       ([], l, tparams, [sn, PtrType (StructType (sn, targs)); "value", InductiveType ("option", [t])], symb_, Some 1,
                        let r = WRead (l, WVar (l, sn, LocalVar), sn, tparams, f, t, targs, false, ref (Some None), Real) in
                        WPredAsn (l, p_, true, [], [], ([LitPat (AddressOf (l, r))] @ List.map (fun e -> LitPat e) args @ [LitPat (WVar (l, "value", LocalVar))]))
                       )
                      )
                    ]
                in
                let points_to_predinst () =
                  let r = WRead (l, WVar (l, sn, LocalVar), sn, tparams, f, t, targs, false, ref (Some None), Real) in
                  let body = WPointsTo (l, WDeref (l, AddressOf (l, r), t), t, RegularPointsTo, LitPat (WVar (l, "value", LocalVar))) in
                  let inst =
                    (g, []),
                    ([], l, tparams, [sn, PtrType (StructType (sn, targs)); "value", t], symb, Some 1, body)
                  in
                  match g__opt with
                    None -> [inst]
                  | Some (g_, (_, _, _, _, symb_, _, _)) ->
                    [
                      inst
                    ;
                      let body = WPointsTo (l, WDeref (l, AddressOf (l, r), t), t, MaybeUninit, LitPat (WVar (l, "value", LocalVar))) in
                      ((g_, []),
                       ([], l, tparams, [sn, PtrType (StructType (sn, targs)); "value", InductiveType ("option", [t])], symb_, Some 1, body)
                      )
                    ]
                in
                let predinst__ p p_ domain t = predinst___ p p_ domain t [] in
                let predinst_ p p_ t = predinst__ p p_ [PtrType t] t in
                let predinst p p_ = predinst_ p p_ t in
                match t with
                  _ when dialect = Some Rust -> points_to_predinst ()
                | PtrType _ -> points_to_predinst ()
                | Int (Signed, PtrRank) -> predinst "intptr" "intptr_"
                | Int (Unsigned, PtrRank) -> predinst "uintptr" "uintptr_"
                | Int (Signed, CharRank) -> predinst "character" "char_"
                | Int (Unsigned, CharRank) -> predinst "u_character" "uchar_"
                | Int (Signed, ShortRank) -> predinst "short_integer" "short_"
                | Int (Unsigned, ShortRank) -> predinst "u_short_integer" "ushort_"
                | Int (Signed, IntRank) -> predinst "integer" "int_"
                | Int (Unsigned, IntRank) -> predinst "u_integer" "uint_"
                | Int (Signed, LongRank) -> predinst "long_integer" "long_"
                | Int (Unsigned, LongRank) -> predinst "ulong_integer" "ulong_"
                | Int (Signed, LongLongRank) -> predinst "llong_integer" "llong_"
                | Int (Unsigned, LongLongRank) -> predinst "u_llong_integer" "ullong_"
                | Int (s, _) -> predinst___ "integer_" "integer__" [PtrType Void; intType; Bool] intType [SizeofExpr (l, TypeExpr (ManifestTypeExpr (l, t))); if s = Signed then True l else False l]
                | Bool -> predinst_ "boolean" "bool_" Bool
                | GhostTypeParam tparam -> points_to_predinst ()
                | _ -> []
                end
              | _ -> []
            end
            fmap
        | _ -> []
      end
      structmap1
  
  let check_predinst0 predfam_tparams arity ps psymb inputParamCount (pn, ilist) tparams tenv env l p predinst_tparams fns xs body =
    check_tparams l tparams predinst_tparams;
    let tpenv =
      match zip predfam_tparams (List.map (fun x -> GhostTypeParam x) predinst_tparams) with
        None -> static_error l "Number of type parameters does not match predicate family." None
      | Some bs -> bs
    in
    if List.length fns <> arity then static_error l "Incorrect number of indexes." None;
    let pxs =
      match zip ps xs with
        None -> static_error l "Incorrect number of parameters." None
      | Some pxs -> pxs
    in
    let tparams' = predinst_tparams @ tparams in
    let xs =
      let rec iter2 xm pxs =
        match pxs with
          [] -> List.rev xm
        | (t0, (te, x))::xs -> 
          let t = check_pure_type (pn,ilist) tparams' Ghost te in
          expect_type l (Some true) t (instantiate_type tpenv t0);
          if List.mem_assoc x tenv then static_error l ("Parameter '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
          if List.mem_assoc x xm then static_error l "Duplicate parameter name." None;
          iter2 ((x, t)::xm) xs
      in
      iter2 [] pxs
    in
    let (wbody, _) = check_asn (pn,ilist) tparams' (xs @ tenv) body in
    begin
      match inputParamCount with
        None -> ()
      | Some n ->
        let (inps, outps) = take_drop n (List.map (fun (x, t) -> x) xs) in
        let inps = inps @ List.map (fun (x, t) -> x) tenv in
        let fixed = check_pred_precise inps wbody in
        List.iter
          (fun x ->
           if not (List.mem x fixed) then
             static_error l ("Preciseness check failure: body does not fix output parameter '" ^ x ^ "'.") None)
          outps
    end;
    ((p, fns), (env, l, predinst_tparams, xs, psymb, inputParamCount, wbody))
  
  let check_predinst (pn, ilist) tparams tenv env l p predinst_tparams fns xs body =
    let (p, predfam_tparams, arity, ps, psymb, inputParamCount) =
      match resolve Ghost (pn,ilist) l p predfammap with
        None -> static_error l ("No such predicate family: "^p) None
      | Some (p, (lfam, predfam_tparams, arity, ps, psymb, inputParamCount, inductiveness)) ->
        if fns = [] && language = CLang && l != lfam then begin
          nonabstract_predicates := (p, lfam, l)::!nonabstract_predicates
        end;
        (p, predfam_tparams, arity, ps, psymb, inputParamCount)
    in
    check_predinst0 predfam_tparams arity ps psymb inputParamCount (pn, ilist) tparams tenv env l p predinst_tparams fns xs body

  let check_structnamelist is =
    is |> List.map (fun (l, sn) -> if List.mem_assoc sn structmap then sn else static_error l "No such struct" None)

  let mk_pred_inst l (pn, ilist) pred tparams is params body =
    let fns = match language, dialect with
      Java, _-> check_classnamelist (pn,ilist) is
    | CLang, Some Rust -> check_structnamelist is
    | _ -> check_funcnamelist is 
    in
    check_predinst (pn, ilist) [] [] [] l pred tparams fns params body
  
  let predinstmap1 =
    match dialect with 
    | Some Cxx ->
      (* 
        For each polymorphic struct S with polymorphic bases [B0; ...; Bn] and n > 0 create:
          predicate S_vtype(struct S *s, std::type_info *t) =
            B0_vtype(s, t) &*& ... &*& Bn_vtype(s, t)
      *)
      let mk_pred_inst l sn body = 
        let params = [(PtrTypeExpr (l, (StructTypeExpr (l, Some sn, None, [], []))), "s"); (PtrTypeExpr (l, (StructTypeExpr (l, Some type_info_name, None, [], []))), "t")] in
        mk_pred_inst l ("", []) (vtype_pred_name sn) [] [] params body 
      in
      let base_vtype l base = CallExpr (l, (vtype_pred_name base), [], [], [LitPat (Var (l, "s")); LitPat (Var (l, "t"))], Static) in
      structmap1 |> List.fold_left (fun acc s ->
        match s with
        | sn, (l, [], Some (bases, _, true), _, _) ->
          let bases = bases |> List.filter @@ fun (b, _) -> is_polymorphic_struct b in
          begin match bases with
          | [] -> acc
          | [(base, _)] -> 
            let body = base_vtype l base in
            let pred_inst = mk_pred_inst l sn body in
            pred_inst :: acc
          | (base, _) :: bases ->
            let fold acc (base, _) = Sep (l, base_vtype l base, acc) in
            let body = bases |> List.fold_left fold (base_vtype l base) in
            let pred_inst = mk_pred_inst l sn body in
            pred_inst :: acc
          end
        | _ -> acc
      ) predinstmap1
    | _ -> predinstmap1
  
  let predinstmap1 = 
    let rec iter (pn,ilist) pm ds =
      match ds with
        PredFamilyInstanceDecl (l, p, tparams, is, xs, body)::ds ->
        let (pfns, info) as entry = mk_pred_inst l (pn, ilist) p tparams is xs body in 
        let _ = if List.mem_assoc pfns pm || List.mem_assoc pfns predinstmap0 then static_error l "Duplicate predicate family instance." None in
        iter (pn,ilist) (entry::pm) ds
      | _::ds -> iter (pn,ilist) pm ds
      | [] -> List.rev pm
    in
    let rec iter' pm ps=
      match ps with
        PackageDecl(l,pn,il,ds)::rest -> iter' (iter (pn,il) pm ds) rest
      | [] -> pm
    in
    iter' predinstmap1 ps
  
  let predinstmap = predinstmap1 @ predinstmap0
  
  let predctormap1 =
    List.map
      (
        function
          (g, (l, tparams, ps1, ps2, inputParamCount, body, funcsym,pn,ilist)) ->
          let (wbody, _) = check_asn (pn,ilist) tparams (ps1 @ ps2) body in
          begin match inputParamCount with
            None -> ()
          | Some(n) -> 
            let (inps, outps) = take_drop n (List.map (fun (x, t) -> x) ps2) in
            let inps = (List.map (fun (x, t) -> x) ps1) @ inps in
            let fixed = check_pred_precise inps wbody in
            List.iter
              (fun x ->
                if not (List.mem x fixed) then
                  static_error l ("Preciseness check failure: body does not fix output parameter '" ^ x ^ "'.") None)
              outps
          end;
          (g, PredCtorInfo (l, tparams, ps1, ps2, inputParamCount, wbody, funcsym))
      )
      predctormap1
  
  let predctormap = predctormap1 @ predctormap0

  let () = (* Process type predicate definitions. *)
    let rec iter pn ilist defs ds cont =
      match ds with
        [] -> cont defs
      | TypePredDef (l, tparams, te, predName, Left (lrhs, rhs))::ds ->
        check_tparams l [] tparams;
        let tp = check_pure_type (pn,ilist) tparams Ghost te in
        let (_, selfTypeName, predType, symb) =
          match try_assoc predName typepreddeclmap with
            None -> static_error l "No such type predicate" None
          | Some info -> info
        in
        (* It is tricky to guard against duplicate definitions for the same typeid (especially in the presence of type parameters).
           For now, we do not attempt to prevent it at all, which is unsound if the user can introduce arbitrary type predicate
           definitions. Therefore, we allow this construct to be used only by the Rust translator. *)
        if dialect <> Some Rust then static_error l "Type predicate definitions are allowed only in Rust programs" None;
        let defs =
          match tp with
            StructType (sn, _) ->
            if List.mem_assoc sn structmap0 then static_error l "A type predicate definition for a struct type is allowed only in the file that declares the struct" None;
            if List.mem (sn, predName) defs then static_error l (Printf.sprintf "Duplicate definition of type predicate %s for struct %s" predName sn) None;
            (sn, predName)::defs
          | _ -> defs (* TODO: Prevent duplicate type predicate definitions for non-struct types, probably by not allowing definitions for these types at all. *)
        in
        let predType' = instantiate_type [selfTypeName, tp] predType in
        if tparams = [] then
          let typeid = typeid_of_core l [] tp in
          let type_pred_term = ctxt#mk_app symb [typeid] in
          match resolve Ghost (pn,ilist) lrhs rhs predfammap with
            Some (rhs, (_, pred_tparams, nbIndices, pts, predSymb, inputParamCount, inductiveness)) ->
            if pred_tparams <> [] then static_error lrhs "The right-hand side predicate has type parameters" None;
            if nbIndices <> 0 then static_error lrhs "The right-hand side predicate is a predicate family" None;
            expect_type lrhs (Some true) (PredType ([], pts, inputParamCount, inductiveness)) predType';
            ctxt#assert_term (ctxt#mk_eq type_pred_term predSymb);
            iter pn ilist defs ds cont
          | None ->
          match resolve Ghost (pn,ilist) lrhs rhs purefuncmap with
            Some (rhs, (_, ctor_tparams, PredType ([], ctor_ps', inputParamCount, _), ctor_ps, ctorSymb)) ->
            if ctor_tparams <> [] then static_error l "The right-hand side predicate constructor has type parameters" None;
            let pred_type = PredType ([], ctor_ps', inputParamCount, Inductiveness_Inductive) in
            let rhs_type = List.fold_right (fun (_, pt) ctp -> PureFuncType (pt, ctp)) ctor_ps pred_type in
            expect_type l (Some true) rhs_type predType';
            ctxt#assert_term (ctxt#mk_eq type_pred_term (snd ctorSymb));
            iter pn ilist defs ds cont
          | None ->
            static_error l ("No such predicate or predicate constructor: " ^ rhs) None
        else
          begin match resolve Ghost (pn,ilist) lrhs rhs purefuncmap with
            Some (rhs, (_, ctor_tparams, PredType ([], ctor_ps', inputParamCount, Inductiveness_Inductive), ctor_ps, ctorSymb)) ->
            let tpenv =
              match zip ctor_tparams (List.map (fun x -> GhostTypeParam x) tparams) with
                None -> static_error lrhs "Incorrect number of type arguments" None
              | Some bs -> bs
            in
            let ctor_pts = instantiate_types tpenv (List.map snd ctor_ps) in
            let ctor_pts' = instantiate_types tpenv ctor_ps' in
            let pred_type = PredType ([], ctor_pts', inputParamCount, Inductiveness_Inductive) in
            let rhs_type = List.fold_right (fun pt ctp -> PureFuncType (pt, ctp)) ctor_pts pred_type in
            expect_type lrhs (Some true) rhs_type predType';
            ctxt#begin_formal;
            let targs_env = List.mapi (fun i x -> (x ^ "_typeid", ctxt#mk_bound i ctxt#type_inductive)) tparams in
            let targs = List.map snd targs_env in
            let typeid = typeid_of_core l targs_env tp in
            let typePredTerm = ctxt#mk_app symb [typeid] in
            let ctorApp = List.fold_left (fun f arg -> ctxt#mk_app apply_symbol [f; arg]) (snd ctorSymb) targs in
            let eq = ctxt#mk_eq typePredTerm ctorApp in
            ctxt#end_formal;
            ctxt#assume_forall (Printf.sprintf "type_pred_def_%s_%s" predName rhs) [typePredTerm] (List.map (fun x -> ctxt#type_inductive) tparams) eq;
            iter pn ilist defs ds cont
          | None ->
            static_error lrhs "No such predicate constructor" None
          end
      | _::ds ->
        iter pn ilist defs ds cont
    in
    let rec iter' defs ps =
      match ps with
        [] -> ()
      | PackageDecl (l, pn, ilist, ds)::ps ->
        iter pn ilist defs ds @@ fun defs ->
        iter' defs ps
    in
    iter' [] ps
  
  let classmap1 =
    classmap1 |> List.map
      begin fun (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, tpenv, interfs, preds, pn, ilist)) ->
        let preds =
          preds |> List.map
            begin function
              (g, (l, pmap, family, symb, Some body)) ->
              let tenv = (current_class, ClassOrInterfaceName cn)::("this", ObjType (cn, []))::pmap in
              let (wbody, _) = check_asn (pn,ilist) [] tenv body in
              let fixed = check_pred_precise ["this"] wbody in
              List.iter
                begin fun (x, t) ->
                  if not (List.mem x fixed) then static_error l ("Preciseness check failure: predicate body does not fix parameter '" ^ x ^ "'.") None
                end
                pmap;
              (g, (l, pmap, family, symb, Some wbody))
            | pred -> pred
            end
        in
        (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, tpenv, interfs, preds, pn, ilist))
      end

  let cxx_inst_pred_map1 =
    cxx_inst_pred_map1_unchecked |> List.map (fun (sn, inst_preds) ->
      let winst_preds = inst_preds |> List.map (function
        | g, (loc, pmap, family, symb, Some body) ->
          let tenv = ("this", PtrType (StructType (sn, []))) :: pmap in
          let wbody, _ = check_asn ("", []) [] tenv body in
          let fixed = check_pred_precise ["this"] wbody in
          pmap |> List.iter (fun (x, t) ->
            if not (List.mem x fixed) then static_error loc ("Preciseness check failure: predicate body does not fix parameter '" ^ x ^ "'.") None
          );
          g, (loc, pmap, family, symb, Some wbody)
        | pred ->
          pred
        )
      in
      sn, winst_preds
    )

  let cxx_inst_pred_map = cxx_inst_pred_map1 @ cxx_inst_pred_map0
  
  (* Region: evaluation helpers; pushing and popping assumptions and execution trace elements *)
  
  let check_ghost_nonrec ghostenv e =
    match e with
      Var (l, x) | WVar (l, x, LocalVar) -> if List.mem x ghostenv then static_error l "Cannot read a ghost variable in a non-pure context." None
    | _ -> ()

  let check_ghost ghostenv e =
    expr_iter (check_ghost_nonrec ghostenv) e
  
  let () =
    unionmap1 |> List.iter begin fun (un, (l, body_opt, unionTypeid)) ->
      match body_opt with
        None -> ()
      | Some (fds, s) ->
        fds |> List.iteri begin fun i (f, (lf, tp)) ->
          ctxt#assert_term (ctxt#mk_le (sizeof l tp) s);
          ctxt#begin_formal;
          let p = ctxt#mk_bound 0 ctxt#type_inductive in
          let member_has_type = mk_has_type (mk_app (union_variant_ptr_symb ()) [p; unionTypeid; ctxt#mk_intlit i]) (typeid_of lf tp) in
          let union_has_type = mk_has_type p unionTypeid in
          ctxt#end_formal;
          ctxt#assume_forall ("has_type_union_variant_" ^ un ^ "_" ^ f) [member_has_type] [ctxt#type_inductive] (ctxt#mk_eq union_has_type member_has_type)
        end
    end

  let field_address l env t fparent targs fname =
    let (_, tparams, Some (_, fmap, _), _, structTypeidFunc) = List.assoc fparent structmap in
    let (_, gh, y, offsetFunc_opt, _) = List.assoc fname fmap in
    let offsetFunc =
       match offsetFunc_opt with
        Some symbol -> symbol
      | None -> static_error l "Cannot take the address of a ghost field" None
    in
    mk_field_ptr_ l env t targs structTypeidFunc offsetFunc

  let direct_base_addr (derived_name, derived_addr) base_name =
    let _, _, Some (bases, _, _), _, derivedTypeid = List.assoc derived_name structmap in
    let _, _, base_offset = List.assoc base_name bases in
    mk_field_ptr derived_addr (ctxt#mk_app derivedTypeid []) base_offset

  let base_addr l (derived_name, derived_addr) base_name =
    if derived_name = base_name then 
      derived_addr
    else
      let rec iter derived_name offsets =
        let _, _, Some (bases, _, _), _, derivedTypeidFunc = List.assoc derived_name structmap in
        let derivedTypeid = ctxt#mk_app derivedTypeidFunc [] in
        let other_paths = bases |> List.fold_left begin fun acc (name, (_, _, offset)) -> 
          match iter name ((derivedTypeid, offset) :: offsets) with
          | Some p -> p :: acc
          | None -> acc
        end [] in
        match try_assoc base_name bases, other_paths with 
        | Some _,  _ :: _
        | None, _ :: (_ :: _) -> static_error l (Printf.sprintf "Derived '%s' to base '%s' is ambiguous: multiple '%s' base candidates exist." derived_name base_name base_name) None
        | Some (_, _, base_offset), [] -> Some ((derivedTypeid, base_offset) :: offsets)
        | None, [p] -> Some p
        | _ -> None
      in 
      let Some offsets = iter derived_name [] in 
      List.rev offsets |> List.fold_left (fun addr (structTypeid, offset) -> mk_field_ptr addr structTypeid offset) derived_addr

  let convert_provertype term proverType proverType0 =
    if proverType = proverType0 then term else apply_conversion proverType proverType0 term
  
  let prover_convert_term term t t0 =
    if t = t0 then term else convert_provertype term (provertype_of_type t) (provertype_of_type t0)

  let nil_symb = lazy_purefuncsymb "nil"
  
  let mk_nil () = mk_app !!nil_symb []
  
  let cons_symb = lazy_purefuncsymb "cons"

  let mk_cons elem_tp head tail = mk_app !!cons_symb [apply_conversion (provertype_of_type elem_tp) ProverInductive head; tail]

  let some_symb = lazy_purefuncsymb "some"

  let mk_some elem_tp value = mk_app !!some_symb [apply_conversion (provertype_of_type elem_tp) ProverInductive value]
  
  let all_eq_symb = lazy_purefuncsymb "all_eq"

  let mk_all_eq elem_tp xs x = mk_app !!all_eq_symb [xs; apply_conversion (provertype_of_type elem_tp) ProverInductive x]
  
  let head_symb = lazy_purefuncsymb "head"
  
  let mk_head elem_tp xs = apply_conversion ProverInductive (provertype_of_type elem_tp) (mk_app !!head_symb [xs])
  
  let nth_symb = lazy_purefuncsymb "nth"
  
  let mk_nth elem_tp n xs = apply_conversion ProverInductive (provertype_of_type elem_tp) (mk_app !!nth_symb [n; xs])
  
  let tail_symb = lazy_purefuncsymb "tail"
  
  let mk_tail xs = mk_app !!tail_symb [xs]
  
  let rec mk_list elem_tp elems =
    match elems with
      [] -> mk_nil()
    | e::es -> mk_cons elem_tp e (mk_list elem_tp es)
  
  let take_symb = lazy_purefuncsymb "take"
  
  let mk_take n xs = mk_app !!take_symb [n; xs]
  
  let drop_symb = lazy_purefuncsymb "drop"
  
  let mk_drop n xs = mk_app !!drop_symb [n; xs]
  
  let append_symb = lazy_purefuncsymb "append"
  
  let mk_append l1 l2 = mk_app !!append_symb [l1; l2]
  
  let length_symb = lazy_purefuncsymb "length"
  
  let mk_length l = mk_app !!length_symb [l]
  
  let distinct_symb = lazy_purefuncsymb "distinct"
  
  let mk_distinct l = mk_app !!distinct_symb [l]
  
  let mem_symb = lazy_purefuncsymb "mem"
  
  let mk_mem elem_tp e xs = (mk_app !!mem_symb [apply_conversion (provertype_of_type elem_tp) ProverInductive e; xs])
  
  let rec mk_zero_list n =
    assert (0 <= n);
    if n = 0 then
      mk_nil ()
    else
      mk_cons charType (ctxt#mk_intlit 0) (mk_zero_list (n - 1))
  
  let mk_char_list_of_c_string size s =
    let n = String.length s in
    let as_signed_char n = if 127 < n then n - 256 else n in
    let rec iter k =
      if k = n then
        mk_zero_list (size - n)
      else
        mk_cons charType (ctxt#mk_intlit (as_signed_char (Char.code s.[k]))) (iter (k + 1))
    in
    iter 0
  
  let mk_u8_list_of_rust_string s =
    let n = String.length s in
    let rec iter k =
      if k = n then
        mk_nil ()
      else
        mk_cons charType (ctxt#mk_intlit (Char.code s.[k])) (iter (k + 1))
    in
    iter 0
    
  (* data type to represent ancestries *)
  type ancestry_dt =
    | Class_anc of
        bool * (* is_final *)
        (string list) * (* ancesters *)
        (string list) (* class hierarchy *)

    | Intrf_anc of
        string list (* ancesters *)

(*
  (* useful for printing ancestries for debugging purposes *)

  let list_to_string lst f =
    let rec list_to_string_helper tmp l =
      match l with
        | [] -> tmp
        | [a] -> tmp ^ (f a)
        | h :: t -> list_to_string_helper (tmp ^ (f h) ^ "; ") t
    in
    "[" ^ (list_to_string_helper "" lst) ^ "]"

  let ancestry_to_string anc =
    match anc with
      | Class_anc (isfin, anc, hier) ->
          "class_ancestry(" ^ (if isfin then "final" else "non-final") ^ ", " ^ (list_to_string anc (fun n -> n)) ^ ", " ^ (list_to_string hier (fun n -> n)) ^ ")"
      | Intrf_anc anc -> "interface_ancestry(" ^ (list_to_string anc (fun n -> n)) ^ ")"
*)

  (*calculating class/interface ancestries*)
  (*we assume that there are no cycles in the class/interface diagram.
    note that if it is not the case, program will enter an infinite loop (we won't get stack overflow as the function is tail-recursive)
   *)
  (* clmap0 and intfmap0 are respectively the class map and interface map for the library *)
  let calculate_ancestries () =
    let merge_ancesters_of_direct_ancesters already_calculated_ancestries direct_ancesters =
      let rec merge_ancesters_of_direct_ancesters_helper (tmp_anc, tmp_hier) l =
        match l with
          | [] ->
              Some (tmp_anc, tmp_hier)
          | h :: t ->
            try
              let new_tmp_anc_tmp_hier = 
                match List.assoc h already_calculated_ancestries with
                  | Class_anc (isfin, anc, hier) -> (tmp_anc @ anc, tmp_hier @ hier)
                  | Intrf_anc anc -> (tmp_anc @ anc, tmp_hier)
              in
              merge_ancesters_of_direct_ancesters_helper new_tmp_anc_tmp_hier t
            with
              Not_found -> None (* assert false (* As class and interface maps are sorted by inheritance order. *) *)
      in
      merge_ancesters_of_direct_ancesters_helper ([], []) direct_ancesters
    in
    let calculate_ancestry_from_direct_ancesters_info already_calculated_ancestries clinfname direct_anc_info =
      let (direct_ancesters, is_a_class, is_a_final_class) =
        direct_anc_info
      in
      match merge_ancesters_of_direct_ancesters already_calculated_ancestries direct_ancesters with
        | Some (direct_ancesters_ancestry, direct_ancesters_hierarchy) ->
          begin
            let (anc, hier) =
              ((clinfname :: direct_ancesters_ancestry), (if is_a_class then (clinfname :: direct_ancesters_hierarchy) else direct_ancesters_hierarchy))
            in
            if(is_a_class) then
              Some (clinfname, Class_anc (is_a_final_class, anc, hier))
            else
              Some (clinfname, Intrf_anc anc)
          end
        | None -> None
    in
    let calculate_ancestry_intfmap0 already_calculated_ancestries (clinfname, info) =
      let super_clintf =
        match info with
          InterfaceInfo (_, _, _, _, intfs, _) ->
            (List.map fst intfs, false, false)
      in
      calculate_ancestry_from_direct_ancesters_info already_calculated_ancestries clinfname super_clintf
    in
    let calculate_ancestry_intfmap1 already_calculated_ancestries (clinfname, info) =
      let super_clintf =
        match info with
          (_, _, _, _, intfs, _, _, _) ->
            (List.map fst intfs, false, false)
      in
      calculate_ancestry_from_direct_ancesters_info already_calculated_ancestries clinfname super_clintf
    in
    let calculate_ancestry_classmap0 already_calculated_ancestries (clinfname, info) =
      let super_clintf =
        let iafc =
          if info.cfinal = FinalClass then true else false
        in
        let (csuper, superTargs) = info.csuper in
        if csuper = "" then (List.map fst info.cinterfs, true, iafc) else ((csuper :: (List.map fst info.cinterfs)), true, iafc) (* super class of Java.lang.Object is registered as "" *)
      in
      calculate_ancestry_from_direct_ancesters_info already_calculated_ancestries clinfname super_clintf
    in
    let calculate_ancestry_classmap1 already_calculated_ancestries (clinfname, info) =
      let super_clintf =
        match info with
          (_, _, fin, _, _, _, (spr, superTargs), _, intfs, _, _, _) ->
            let intfs = List.map fst intfs in
            let iafc =
              if fin = FinalClass then true else false
            in
            if spr = "" then (intfs, true, iafc) else ((spr :: intfs), true, iafc) (* super class of Java.lang.Object is registered as "" *)
      in
      calculate_ancestry_from_direct_ancesters_info already_calculated_ancestries clinfname super_clintf
    in
    let calculate_all_ancestries already_calculated_anc lst calculator =
      let rec calculate_all_ancestries_helper num_started_with tmp postponed l =
        match l with
          | [] ->
              begin
              if postponed = [] then
                tmp
              else
                if (List.length postponed) >= num_started_with then (* This check is to prevent infinite loops in case any of the situations below takes place due to a bug. *)
                  assert false (* This can only happen if there are classes/interfaces with ancesters that are not in the maps or
                                   if there is a cycle in the inheritence graph! which is impossible according to java's semantics. *)
                else
                  calculate_all_ancestries_helper (List.length postponed) tmp [] (List.rev postponed)
              end
          | h :: t ->
              begin
                match calculator tmp h with
                  | Some new_anc -> calculate_all_ancestries_helper num_started_with (new_anc :: tmp) postponed t
                  | None ->
                      if (t = [] && postponed = []) then
                        assert false (* h has ancesters that are neither processed yet nor are postponed! This should be impossible *)
                      else
                        (* Class/interface h appears in the class/interface map in an incorrect order! This should technically not happen.
                           Yet, it occurs when we have a program that uses a java library (other than the standard library), e.g.,
                           examples/reduced_annotations/java_language/main.jarsrc *)
                        (* In this case, we simply postpone processing of h! *)
                        (* In case no postponing happens, this function is linear in the length of the input list, i.e., lst.
                           In the worst case, i.e., when the given list is sorted in the inverse order of inheritance,
                           this function is quadratic in the length of the input list, i.e., lst *)
                        calculate_all_ancestries_helper num_started_with tmp (h :: postponed) t
              end
      in
      calculate_all_ancestries_helper (List.length lst) already_calculated_anc [] lst
    in
    let ancestries =
      let anc_intfmap0 =
        calculate_all_ancestries [] interfmap0 calculate_ancestry_intfmap0
      in
      let anc_intfmap0_intfmap1 =
        calculate_all_ancestries anc_intfmap0 interfmap1 calculate_ancestry_intfmap1
      in
      let anc_intfmap0_intfmap1_classmap0 =
        calculate_all_ancestries anc_intfmap0_intfmap1 classmap0 calculate_ancestry_classmap0
      in
      let anc_intfmap0_intfmap1_classmap0_classmap1 =
        calculate_all_ancestries anc_intfmap0_intfmap1_classmap0 classmap1 calculate_ancestry_classmap1
      in
      anc_intfmap0_intfmap1_classmap0_classmap1
    in
(*    (* printing ancestries: *)
    let () =
       List.iter (fun (cn, anc) -> print_string ("\n(" ^ cn ^ ", " ^ (ancestry_to_string anc) ^ ")\n")) ancestries; flush stdout
    in *)
    ancestries

(* adding asserions for ancestries to the prover theory *)
let add_ancestries_to_prover ancestries =
  let make_prover_ancestry anc =
    let resolve_class_interface nm =
      try
        List.assoc nm classterms
      with
        Not_found ->
          try
            List.assoc nm interfaceterms
          with
            Not_found ->
              assert false (* should be impossible as each class/interface must have an representative term for prover *)
    in
    let add_ancestry cintf lst = 
      let prover_ancestry_list =
        mk_list intType (List.map resolve_class_interface lst)
      in
      let eq_assertion =
        ctxt#mk_eq (ctxt#mk_app ancestry_symbol [cintf]) prover_ancestry_list
      in
      ctxt#assert_term eq_assertion
    in
    let add_hierarchy_and_instance_of_ancestry cintf ancestry hierarchy =
      let ancester_at_of length var offset i a =
        (* hierarchy is claculated in reverse order of inheritance (i.e., java.lang.Object is at the end). Therefore, we encode i^{th} element of the hierarchy as ancester_at(_, (length - i -1)).
           Where length is the length of the hierarchy *)
        ctxt#mk_eq (ctxt#mk_app ancester_at_symbol [var; (ctxt#mk_intlit (length - offset - i - 1))]) (resolve_class_interface a)
      in
      ctxt#begin_formal;
      let x =
        ctxt#mk_bound 0 ctxt#type_int
      in
      let mk_x_instanceof y =
        ctxt#mk_app instanceof_symbol [x; (resolve_class_interface y)]
      in
      let x_instanceof_cintf =
        ctxt#mk_app instanceof_symbol [x; cintf]
      in
      let encoded_hierarchy =
        match hierarchy with
          | [] -> None (* it must be an interface with no class hierarchy *)
          | [a] -> Some (ancester_at_of 1 x 0 0 a)
          | h :: tl -> let len = List.length hierarchy in Some (List.fold_left (fun x y -> ctxt#mk_and x y) (ancester_at_of len x 0 0 h) (imap (ancester_at_of len x 1) tl))
      in
      let instanceof_ancestry =
        match ancestry with
          | [] -> assert false (* the class ancestry can never be empty as it shoul always contain the class itself *)
          | [a] -> None (* it must be the class/interface itself *)
          | h :: tl -> Some (List.fold_left (fun x y -> ctxt#mk_and x y) (mk_x_instanceof h) (List.map mk_x_instanceof tl))
      in
      let x_instanceof_cintf_implies_encoded_hierarchy_and_instance_of_ancestry =
        match (encoded_hierarchy, instanceof_ancestry) with
          | (None, None) ->
              None
          | (None, Some ianc) ->
              Some (ctxt#mk_implies x_instanceof_cintf ianc)
          | (Some eh, None) ->
              Some (ctxt#mk_implies x_instanceof_cintf eh)
          | (Some eh, Some ianc) ->
              Some (ctxt#mk_implies x_instanceof_cintf (ctxt#mk_and eh ianc))
      in
      ctxt#end_formal;
      match x_instanceof_cintf_implies_encoded_hierarchy_and_instance_of_ancestry with
        | None -> ()
        | Some body ->
            begin
              (*
              (* Printing the body of lemmas being emmited. Used for debugging purposes. *)
              let () =
                print_string ("\n" ^ (ctxt#pprint body) ^ "\n"); flush stdout;
              in *)
              ctxt#assume_forall ("x_instanceof_cintf_implies_encoded_hierarchy_and_instance_of_ancestry_for" ^ (ctxt#pprint cintf)) [x_instanceof_cintf] [ctxt#type_int] body
            end
    in
    let add_finality cintf =
      ctxt#begin_formal;
      let a =
        ctxt#mk_bound 0 ctxt#type_int
      in
      let a_instanceof_cintf =
        ctxt#mk_app instanceof_symbol [a; cintf]
      in
      let a_getClass_eq_cintf =
        ctxt#mk_eq (ctxt#mk_app get_class_symbol [a]) cintf
      in
      let a_instanceof_cintf_iff_a_getClass_eq_cintf =
        ctxt#mk_iff a_instanceof_cintf a_getClass_eq_cintf
      in
      ctxt#end_formal;
      ctxt#assume_forall ("a_instanceof_cintf_iff_a_getClass_eq_cintf_for" ^ (ctxt#pprint cintf)) [a_instanceof_cintf] [ctxt#type_int] a_instanceof_cintf_iff_a_getClass_eq_cintf
    in
    match anc with
      | (nm, Class_anc (isfin, ancestry, hierarchy)) ->
          let cintf =
            resolve_class_interface nm
          in
          add_ancestry cintf ancestry;
          add_hierarchy_and_instance_of_ancestry cintf ancestry hierarchy;
          if isfin then add_finality cintf else ()
      | (nm, Intrf_anc ancestry) ->
          let cintf =
            resolve_class_interface nm
          in
          add_ancestry cintf ancestry;
          add_hierarchy_and_instance_of_ancestry cintf ancestry []
  in
  List.iter make_prover_ancestry ancestries

(* adding to the SMT solver that: forall a c, (a instance of c) <=> (mem(c, ancestry(a.getClass()))) *)
let add__forall_a_c__a_instanceof_c__iff__mem_c__ancestry_getClass_a () =
  ctxt#begin_formal;
  let a =
    ctxt#mk_bound 0 ctxt#type_int
  in
  let c =
    ctxt#mk_bound 1 ctxt#type_int
  in
  let a_instanceof_c =
    ctxt#mk_app instanceof_symbol [a; c]
  in
  let ancestry_getClass_a =
    ctxt#mk_app ancestry_symbol [(ctxt#mk_app get_class_symbol [a])]
  in
  let mem_c__ancestry_getClass_a =
    mk_mem intType c ancestry_getClass_a
  in
  let a_instanceof_c__iff__mem_c__ancestry_getClass_a =
    ctxt#mk_iff a_instanceof_c mem_c__ancestry_getClass_a
  in
  ctxt#end_formal;
  ctxt#assume_forall "a_instanceof_c__iff__mem_c__ancestry_getClass_a" [a_instanceof_c] [ctxt#type_int; ctxt#type_int] a_instanceof_c__iff__mem_c__ancestry_getClass_a


let check_if_list_is_defined () =
  try 
    let () =
      ignore (!!nil_symb)
    in
    let () =
      ignore (!!cons_symb)
    in
    let () =
      ignore (!!mem_symb)
    in
    true
  with
    Not_found -> false

(* if the language is java, enable reasoning about instanceof *)
  let () =
    match language with
      | Java ->
          if check_if_list_is_defined () then
            begin
              let ancestries =
                 calculate_ancestries ()
              in
              add_ancestries_to_prover ancestries;
              add__forall_a_c__a_instanceof_c__iff__mem_c__ancestry_getClass_a ()
            end
          else
            output_string stderr "Definition of the inductive data type list was not found. Support for instanceof is not enabled!\n"
      | CLang -> ()
  
  (* TODO: To improve performance, push only when branching, i.e. not at every assume. *)
  
  let assume t cont =
    !stats#proverAssume;
    push_context (Assuming t);
    ctxt#push;
    let result =
      match ctxt#assume t with
        Unknown -> cont()
      | Unsat -> major_success ()
    in
    pop_context();
    ctxt#pop;
    result
  
  let assume_opt t cont =
    match t with
      None -> cont ()
    | Some(t) -> assume t cont
  
  let assume_eq t1 t2 cont = assume (ctxt#mk_eq t1 t2) cont
  let assume_neq t1 t2 cont = assume (ctxt#mk_not (ctxt#mk_eq t1 t2)) cont
  
  let query_term t = 
    !stats#proverOtherQuery;
    (ctxt#query t)
  
  let assert_term t h env l msg url = 
    !stats#proverOtherQuery;
    if not (ctxt#query t) then
      assert_false h env l (Printf.sprintf "%s (Cannot prove %s.)" msg (ctxt#pprint t)) url

  let assume_has_type l typeid_env addr tp cont =
    if fno_strict_aliasing then
      cont ()
    else
      assume (mk_has_type addr (typeid_of_core l typeid_env tp)) cont

  let assume_has_type_if cond l typeid_env addr tp cont =
    if cond then
      assume_has_type l typeid_env addr tp cont
    else
      cont ()
  
  let assert_has_type typeid_env addr tp h env l msg url =
    if not fno_strict_aliasing then
      assert_term (mk_has_type addr (typeid_of_core l typeid_env tp)) h env l msg url

  let rec prover_type_term l tp = 
    match tp with
      ObjType(n, _) -> 
      begin match try_assoc n classterms with
        None -> (match try_assoc n interfaceterms with None -> static_error l ("unknown prover_type_expr for: " ^ (string_of_type tp)) None | Some(t) -> t)
      | Some(t) -> t
      end
    | ArrayType(tp) -> (ctxt#mk_app array_type_symbol [prover_type_term l tp])
    | _ -> static_error l ("unknown prover_type_expr for: " ^ (string_of_type tp)) None

  (* Region: evaluation *)
  
  let check_overflow l min t max assert_term =
    if not disable_overflow_check then begin
      assert_term l (ctxt#mk_le min t) "Potential arithmetic underflow." (Some "potentialarithmeticunderflow");
      assert_term l (ctxt#mk_le t max) "Potential arithmetic overflow." (Some "potentialarithmeticoverflow")
    end

  let woperation_type_result_type op t =
    match op with
      Le|Ge|Lt|Gt|Eq|Neq -> Bool 
    | PtrDiff -> ptrdiff_t
    | _ -> t

  let woperation_result_type (WOperation (l, op, es, t)) =
    woperation_type_result_type op t

  let check_shift_amount ass_term l t v =
    match language, ass_term with
      CLang, Some assert_term ->
      let width =
        match t with
          Int (Signed, k) -> ctxt#mk_sub (ctxt#mk_mul (ctxt#mk_intlit 8) (rank_size_term k)) (ctxt#mk_intlit 1)
        | Int (Unsigned, k) -> ctxt#mk_mul (ctxt#mk_intlit 8) (rank_size_term k)
      in
      assert_term l (ctxt#mk_le (ctxt#mk_intlit 0) v) "Shifting by a negative amount has undefined behavior." None;
      assert_term l (ctxt#mk_lt v width) "Shifting by an amount greater than or equal to the width of the operand has undefined behavior." None
    | _ -> ()
  
  let check_pointer_within_limits ass_term l v =
    begin match ass_term with
      Some assert_term when not disable_overflow_check ->
      assert_term l (mk_pointer_within_limits v) "Pointer may be out of bounds" None
    | _ -> ()
    end;
    v

  let eval_op l env truncating op e1 v1 e2 v2 t ass_term =
    let check_overflow0 v =
      begin match ass_term with
        Some assert_term ->
        let min, max = limits_of_type (woperation_type_result_type op t) in
        check_overflow l min v max assert_term
      | _ -> ()
      end;
      v
    in
    let check_overflow v =
      match truncating, t with
        true, Int (Signed, _) when language <> Java && not fwrapv -> static_error l "Signed integer arithmetic overflow is undefined behavior unless the -fwrapv flag is specified" None
      | true, _ -> mk_truncate_term (woperation_type_result_type op t) v
      | false, _ -> check_overflow0 v
    in
    begin match op with
      And -> ctxt#mk_and v1 v2
    | Or -> ctxt#mk_or v1 v2
    | Eq ->
      begin match t with
        Bool -> ctxt#mk_iff v1 v2
      | (PtrType _|RustRefType _) ->
        if ass_term = None then
          ctxt#mk_eq v1 v2
        else
          static_error l "A pointer comparison is not supported in this context." None
      | _ -> ctxt#mk_eq v1 v2
      end
    | Neq -> ctxt#mk_not (ctxt#mk_eq v1 v2)
    | Add ->
      begin match t with
      | Int (_, _) ->
        check_overflow (ctxt#mk_add v1 v2)
      | PtrType t ->
        check_pointer_within_limits ass_term l (mk_ptr_add_ l env v1 v2 t)
      | RealType ->
        ctxt#mk_real_add v1 v2
      end
    | Sub ->
      begin match t with
        Int (_, _) ->
        check_overflow (ctxt#mk_sub v1 v2)
      | PtrType t ->
        check_pointer_within_limits ass_term l (mk_ptr_add_ l env v1 (ctxt#mk_sub int_zero_term v2) t)
      | RealType ->
        ctxt#mk_real_sub v1 v2
      end
    | PtrDiff -> check_overflow (ctxt#mk_sub (mk_ptr_address v1) (mk_ptr_address v2))
    | Mul ->
      begin match t with
        Int (_, _) ->
        check_overflow (ctxt#mk_mul v1 v2)
      | RealType ->
        ctxt#mk_real_mul v1 v2
      end
    | Le|Lt|Ge|Gt ->
      let v1, v2 =
        match t with
          PtrType _ -> mk_ptr_address v1, mk_ptr_address v2
        | _ -> v1, v2
      in
      begin match t with
        Int (_, _) | PtrType _ ->
        begin match op with
          Le -> ctxt#mk_le v1 v2
        | Lt -> ctxt#mk_lt v1 v2
        | Ge -> ctxt#mk_le v2 v1
        | Gt -> ctxt#mk_lt v2 v1
        end
      | RealType ->
        begin match op with
          Le -> ctxt#mk_real_le v1 v2
        | Lt -> ctxt#mk_real_lt v1 v2
        | Ge -> ctxt#mk_real_le v2 v1
        | Gt -> ctxt#mk_real_lt v2 v1
        end
      end
    | Div ->
      begin match t with
        RealType -> static_error l "Realdiv not supported yet in /=." None
      | Int (_, _) ->
        begin match ass_term with
          Some assert_term -> begin
            let min, _ = limits_of_type (woperation_type_result_type op t) in
            assert_term l (ctxt#mk_not (ctxt#mk_eq v2 (ctxt#mk_intlit 0))) "Denominator might be 0." None;
            if not disable_overflow_check then begin
              assert_term l
                (ctxt#mk_not (ctxt#mk_and (ctxt#mk_eq v1 min) (ctxt#mk_eq v2 (ctxt#mk_intlit (-1)))))
                "Division may overflow." None;
            end
          end
        | None -> ()
        end;
        (ctxt#mk_div v1 v2)
      end
    | Mod ->
      begin match ass_term with
        Some assert_term -> begin
          let min, _ = limits_of_type (woperation_type_result_type op t) in
          assert_term l (ctxt#mk_not (ctxt#mk_eq v2 (ctxt#mk_intlit 0))) "Denominator might be 0." None;
          if not disable_overflow_check then begin
            assert_term l
              (ctxt#mk_not (ctxt#mk_and (ctxt#mk_eq v1 min) (ctxt#mk_eq v2 (ctxt#mk_intlit (-1)))))
              "Operation may overflow." None;
          end
        end
      | None -> ()
      end;
      ctxt#mk_mod v1 v2
    | ShiftLeft ->
      begin match language, t, ass_term with
        CLang, Int (Signed, _), Some assert_term ->
        assert_term l (ctxt#mk_le (ctxt#mk_intlit 0) v1) "Left-shifting a negative value has undefined behavior." None
      | _ -> ()
      end;
      check_shift_amount ass_term l t v2;
      let v = ctxt#mk_app shiftleft_symbol [v1;v2] in
      begin match e2 with
        WIntLit (_, n) | Upcast (WIntLit (_, n), _, _) when le_big_int zero_big_int n && le_big_int n (big_int_of_int 64) ->
        ctxt#assert_term (ctxt#mk_eq v (ctxt#mk_mul v1 (ctxt#mk_intlit_of_string (string_of_big_int (power_int_positive_big_int 2 n)))))
      | _ -> ()
      end;
      check_overflow v
    | _ -> static_error l "This operator is not supported in this position." None
    end

  let rec eval_core_cps0 eval_core ev state ass_term read_field env e cont =
     let evs state es cont =
      let rec iter state vs es =
        match es with
          [] -> cont state (List.rev vs)
        | e::es -> ev state e $. fun state v -> iter state (v::vs) es
      in
      iter state [] es
    in
    let check_overflow l min t max =
      begin
      match ass_term with
        Some assert_term -> check_overflow l min t max assert_term
      | _ -> ()
      end;
      t
    in
    match e with
      True l -> cont state ctxt#mk_true
    | False l -> cont state ctxt#mk_false
    | Null l -> cont state (ctxt#mk_intlit 0)
    | WVar (l, x, scope) ->
      cont state
      begin
        match scope with
          LocalVar -> (try List.assoc x env with Not_found -> assert_false [] env l (Printf.sprintf "Unbound variable '%s'" x) None)
        | FuncName -> List.assoc x all_funcnameterms
        | PredFamName -> let Some (_, _, _, _, symb, _, _) = try_assoc x predfammap in symb
        | EnumElemName n -> ctxt#mk_intlit_of_string (string_of_big_int n)
        | GlobalName ->
          let Some((_, tp, symbol, init)) = try_assoc x globalmap in 
          begin match tp with
            StaticArrayType (_, _) -> symbol
          | _ -> 
          begin
            match read_field with
              None -> static_error l "Cannot mention global variables in this context." None
            | Some (read_field, read_static_field, deref_pointer, read_array) ->
              deref_pointer l symbol tp
          end
          end
        | ModuleName -> List.assoc x modulemap
        | PureFuncName typeid_types ->
          let (lg, tparams, t, tps, (fsymb, vsymb)) = List.assoc x purefuncmap in
          List.fold_left (fun f arg -> ctxt#mk_app apply_symbol [f; arg]) vsymb (List.map (typeid_of_core l env) typeid_types)
      end
    | PredNameExpr (l, g) -> let Some (_, _, _, _, symb, _, _) = try_assoc g predfammap in cont state symb
    | CastExpr (l, ManifestTypeExpr (_, StructType (sn, targs)), InitializerList (linit, ws)) ->
      begin fun cont ->
        let rec iter state vs ws =
          match ws with
            [] -> cont state (List.rev vs)
          | (Some (_, f), w)::ws ->
            ev state w @@ fun state v ->
            iter state ((f, v)::vs) ws
        in
        iter state [] ws
      end @@ fun state vs ->
      let (_, s_tparams, Some (_, fds, _), _, _) = List.assoc sn structmap in
      let s_tpenv = List.combine s_tparams targs in
      let vs_boxed = fds |> List.map begin fun (f, (_, _, tp, _, _)) ->
          let v = List.assoc f vs in
          let tp' = instantiate_type s_tpenv tp in
          prover_convert_term v tp' tp
        end
      in
      let (_, csym, _, _, _) = List.assoc sn struct_accessor_map in
      cont state (ctxt#mk_app csym vs_boxed)
    | TruncatingExpr (l, CastExpr (lc, ManifestTypeExpr (_, t), e)) ->
      begin
        match (e, t) with
        | (e, (Int (_, _) as tp)) ->
          ev state e $. fun state t ->
          cont state (mk_truncate_term tp t)
        | _ ->
          static_error l "Unsupported truncating cast" None
      end
    | CastExpr (l, ManifestTypeExpr (_, t0), (Upcast (e, t, t0') as upcast)) when t0 == t0' -> ev state upcast cont
    | CastExpr (l, ManifestTypeExpr (_, t), e) ->
      begin
        match (e, t) with
          (e, (Int (_, _) as tp)) ->
          ev state e $. fun state t ->
          let min, max = limits_of_type tp in
          cont state (check_overflow l min t max)
        | (_, (ObjType _|ArrayType _)) when ass_term = None -> static_error l "Class casts are not allowed in annotations." None
        | _ -> ev state e cont (* No other cast allowed by the type checker changes the value *)
      end
    | Upcast (e, PtrType (StructType (derived, [])), PtrType (StructType (base, []))) when dialect = Some Cxx && is_derived_of_base derived base ->
      ev state e @@ fun state v ->
      base_addr (expr_loc e) (derived, v) base |> cont state
    | Upcast (e, fromType, toType) -> ev state e cont
    | TypedExpr (e, t) -> ev state e cont
    | WidenedParameterArgument e -> ev state e cont
    | RealLit(l, n, _) ->
      cont state begin 
        if eq_num n (num_of_big_int unit_big_int) then
        real_unit
            else
        ctxt#mk_reallit_of_num n
      end
    | WIntLit (l, n) ->
      let v =
        match int_of_big_int n with
          exception Failure _ -> ctxt#mk_intlit_of_string (string_of_big_int n)
        | n -> ctxt#mk_intlit n
      in
      cont state v
    | ClassLit (l,s) -> cont state (List.assoc s classterms)
    | TypeInfo (l, tp) ->
      cont state (typeid_of_core l env tp)
    | StringLit (l, s) ->
      if ass_term = None then static_error l "String literals are not allowed in ghost code." None;
      cont state
        begin match file_type path with
          Java -> get_unique_var_symb "stringLiteral" (ObjType ("java.lang.String", []))
        | _ -> get_unique_var_symb "stringLiteral" (PtrType charType)
        end
    | WMethodCall (l, "java.lang.Object", "getClass", [], [target], Instance, _) ->
      ev state target $. fun state t ->
      cont state (ctxt#mk_app get_class_symbol [t])
    | WPureFunCall (l, g, targs, args) ->
      begin match try_assoc g predctormap with
        Some (PredCtorInfo(lg, tparams, ps1, ps2, inputParamCount, body, (s, st))) ->
          let targs_typeids = List.map (typeid_of_core l env) targs in
          evs state args $. fun state vs ->
          
          let fun_app = (mk_app (s, st) (targs_typeids @ vs)) in
          (if((List.length ps1) = (List.length vs)) then
            register_pred_ctor_application fun_app s st targs vs inputParamCount);
          cont state fun_app
      | None ->
        begin match try_assoc g purefuncmap with
          None -> static_error l ("No such pure function: "^g) None
        | Some (lg, tparams, t, pts, s) ->
          evs state args $. fun state vs ->
          let Some tpenv = zip tparams targs in
          let targs_typeids = tpenv |> flatmap @@ fun (x, tp) -> if tparam_carries_typeid x then [typeid_of_core l env tp] else [] in
          cont state (mk_app s (targs_typeids @ vs))
        end
      end
    | WPureFunValueCall (l, e, es) ->
      evs state (e::es) $. fun state (f::args) ->
      cont state (List.fold_left (fun f arg -> ctxt#mk_app apply_symbol [f; arg]) f args)
    | IfExpr (l, e1, e2, e3) ->
      ev state e1 $. fun state v1 ->
      ctxt#begin_formal;
      evs state [e2; e3] $. fun state [v2; v3] ->
      ctxt#end_formal;
      cont state (ctxt#mk_ifthenelse v1 v2 v3) (* Only sound if e2 and e3 are side-effect-free *)
    | WOperation (l, MinValue tp, [], _) -> cont state (fst (limits_of_type tp))
    | WOperation (l, MaxValue tp, [], _) -> cont state (snd (limits_of_type tp))
    | WOperation (l, BitAnd, [e1; WOperation (_, BitNot, [e2], _)], _) ->
      ev state e1 $. fun state v1 -> ev state e2 $. fun state v2 ->
      cont state (ctxt#mk_app bitwise_and_symbol [v1; ctxt#mk_app bitwise_not_symbol [v2]])
    | WOperation (l, Not, [e], _) -> ev state e $. fun state v -> cont state (ctxt#mk_not v)
    | WOperation (l, BitNot, [e], t) ->
      (* If we interpret bitwise_not_symbol as operating on arbitrary-size integers interpreted as infinite bitstrings through infinite sign-extension,
         then bitwise_not_symbol maps signed n-bit integers to signed n-bit integers (of the opposite sign),
         but it maps unsigned integers to negative integers.
       *)
      let is_signed_int = match t with Int (Signed, n) -> true | _ -> false in
      if is_signed_int || ass_term = None then
        ev state e $. fun state v -> cont state (ctxt#mk_app bitwise_not_symbol [v])
      else
        static_error l "VeriFast does not currently support taking the bitwise complement (~) of an unsigned integer except as part of a bitwise AND (x & ~y)." None
    | WOperation (l, Div, [e1; e2], RealType) ->
      begin match (e1, e2) with
        (RealLit (_, n, _), WIntLit (_, d)) when eq_num n (num_of_big_int unit_big_int) && eq_big_int d two_big_int -> cont state real_half
      | (WIntLit (_, n), WIntLit (_, d)) when eq_big_int n unit_big_int && eq_big_int d two_big_int -> cont state real_half
      | _ -> 
        let rec eval_reallit e =
            match e with
            WIntLit (l, n) -> num_of_big_int n
          | RealLit (l, n, _) -> n
          | _ -> static_error (expr_loc e) "The denominator of a division must be a literal." None
        in
        ev state e1 $. fun state v1 -> cont state (ctxt#mk_real_mul v1 (ctxt#mk_reallit_of_num (div_num (num_of_int 1) (eval_reallit e2)))) 
      end
    | WOperation (l, (BitAnd|BitOr|BitXor as op), [e1; e2], t) ->
      let operands_bounds =
        if ass_term = None then (* in ghost code, where integer types do not imply limits *) None else
        match e1, e2 with
          Upcast (_, t1, _), Upcast (_, t2, _) ->
          begin match t1, t2 with
            Int (s1, r1), Int (s2, r2) ->
            begin match s1, width_of_rank r1, s2, width_of_rank r2 with
              Signed, LitWidth n1, Signed, LitWidth n2 -> Some (Int (Signed, FixedWidthRank (max n1 n2)))
            | Unsigned, LitWidth n1, Unsigned, LitWidth n2 -> Some (Int (Unsigned, FixedWidthRank (max n1 n2)))
            | Signed, LitWidth n1, Unsigned, LitWidth n2 when n2 < n1 -> Some t1
            | Unsigned, LitWidth n1, Signed, LitWidth n2 when n1 < n2 -> Some t2
            | _ -> None
            end
          | _ -> None
          end
        | Upcast (_, t1, _), WIntLit (_, n) when is_within_limits n t1 -> Some t1
        | WIntLit (_, n), Upcast (_, t2, _) when is_within_limits n t2 -> Some t2
        | _ -> None
      in
      evs state [e1; e2] $. fun state [v1; v2] ->
      let symb, uintN_symb, intN_symb = match op with
          BitAnd -> bitwise_and_symbol, !!bitand_uintN_symb, !!bitand_intN_symb
        | BitXor -> bitwise_xor_symbol, !!bitxor_uintN_symb, !!bitxor_intN_symb
        | BitOr -> bitwise_or_symbol, !!bitor_uintN_symb, !!bitor_intN_symb
      in
      let v = ctxt#mk_app symb [v1; v2] in
      let assume_eq_bounded_op t =
        match t with
          Int (s, r) ->
          begin match s, width_of_rank r with
            Unsigned, LitWidth k -> ctxt#assert_term (ctxt#mk_eq v (mk_app uintN_symb [v1; v2; ctxt#mk_intlit ((1 lsl k) * 8)]))
          | Signed, LitWidth k -> ctxt#assert_term (ctxt#mk_eq v (mk_app intN_symb [v1; v2; ctxt#mk_intlit ((1 lsl k) * 8 - 1)]))
          | _ -> ()
          end
        | _ -> ()
      in
      let t =
        match operands_bounds with
          None -> t
        | Some t ->
          (* BitAnd, BitOr, and BitXor are bitwise nonexpansive (the bitwidth of the result equals the bitwidth of the operands). *)
          assume_bounds v t;
          t
      in
      if ass_term <> None then begin
        assume_eq_bounded_op t;
        begin match e2, op with
          WIntLit (_, i), BitAnd when le_big_int zero_big_int i ->
          ctxt#assert_term (ctxt#mk_and (ctxt#mk_le int_zero_term v) (ctxt#mk_le v v2));
          if eq_big_int i unit_big_int then
            ctxt#assert_term (ctxt#mk_eq (ctxt#mk_mod v1 (ctxt#mk_intlit 2)) v)
        | _ -> ()
        end
      end;
      cont state v
    | WOperation (l, ShiftRight, [e1; e2], t) ->
      evs state [e1; e2] $. fun state [v1; v2] ->
      check_shift_amount ass_term l t v2;
      begin match language, t, ass_term with
        CLang, Int (Signed, _), Some assert_term ->
        begin match e1 with
          Upcast (_, Int (Unsigned, _), _) -> ()
        | _ ->
          assert_term l (ctxt#mk_le (ctxt#mk_intlit 0) v1) "Right-shifting a negative number has implementation-defined behavior." None
        end
      | _ -> ()
      end;
      let v = ctxt#mk_app shiftright_symbol [v1; v2] in
      begin match e1 with
        Upcast (_, tfrom, _) when ass_term <> None -> assume_bounds v tfrom
      | _ when ass_term <> None -> assume_bounds v t
      | _ -> ()
      end;
      cont state v
    | TruncatingExpr (l, WOperation (lo, op, ([e1; e2] as es), t)) ->
      evs state es $. fun state [v1; v2] -> cont state (eval_op l env true op e1 v1 e2 v2 t ass_term)
    | WOperation (l, op, ([e1; e2] as es), t) ->
      evs state es $. fun state [v1; v2] -> cont state (eval_op l env false op e1 v1 e2 v2 t ass_term)
    | ArrayLengthExpr (l, e) ->
      ev state e $. fun state t ->
      begin match ass_term with
        Some assert_term -> assert_term l (ctxt#mk_not (ctxt#mk_eq t (ctxt#mk_intlit 0))) "Target of array length expression might be null" None
      | None -> ()
      end;
      cont state (ctxt#mk_app arraylength_symbol [t])
    | WRead(l, e, fparent, tparams, fname, frange, targs, fstatic, fvalue, fghost) ->
      if fstatic then
        begin match !fvalue with
          Some (Some v) ->
          begin match v with
            IntConst n -> cont state (ctxt#mk_intlit_of_string (string_of_big_int n))
          | BoolConst b -> cont state (if b then ctxt#mk_true else ctxt#mk_false)
          | StringConst s -> static_error l "String constants are not yet supported." None
          | NullConst -> cont state (ctxt#mk_intlit 0)
          | GhostConst e -> ev state e $. cont
          end
        | _ ->
          match read_field with
            None -> static_error l "Cannot use field read expression in this context." None
          | Some (read_field, read_static_field, deref_pointer, read_array) -> cont state (read_static_field l fparent fname)
        end
      else
        ev state e $. fun state v ->
        begin
          match frange with
            StaticArrayType (elemTp, elemCount) ->
            cont state (check_pointer_within_limits ass_term l (field_address l env v fparent targs fname))
          | _ ->
          match read_field with
            None -> static_error l "Cannot use field dereference in this context." None
          | Some (read_field, read_static_field, deref_pointer, read_array) -> cont state (read_field l v fparent targs fname)
        end
    | WSelect(l, e, fparent, tparams, fname, frange, targs) ->
      let tpenv = List.combine tparams targs in
      let frange' = instantiate_type tpenv frange in
      let (_, _, getters, _, _) = List.assoc fparent struct_accessor_map in
      let getter = List.assoc fname getters in
      ev state e $. fun state v ->
      cont state (prover_convert_term (ctxt#mk_app getter [v]) frange frange')
    | WReadInductiveField(l, e, data_type_name, constructor_name, field_name, targs, type_, type_instantiated) ->
      let (_, _, _, getters, _, _, _, _, _) = List.assoc data_type_name inductivemap in
      let getter = List.assoc field_name getters in
      ev state e $. fun state v ->
      cont state (prover_convert_term (ctxt#mk_app getter [v]) type_ type_instantiated)
    | WReadArray(l, arr, tp, i) ->
      evs state [arr; i] $. fun state [arr; i] ->
      begin
        match read_field with
          None -> static_error l "Cannot use array indexing in this context." None
        | Some (read_field, read_static_field, deref_pointer, read_array) -> cont state (read_array l arr i tp)
      end
    | WDeref (l, e, t) ->
      ev state e $. fun state v ->
      begin
        match read_field with
          None -> static_error l "Cannot perform dereference in this context." None
        | Some (read_field, read_static_field, deref_pointer, read_array) ->
          cont state (deref_pointer l v t)
      end
    | AddressOf (l, e) ->
      begin
        match e with
          WRead (le, e, fparent, tparams, fname, frange, targs, fstatic, fvalue, fghost) -> 
          (* MS Visual C++ behavior: http://msdn.microsoft.com/en-us/library/hx1b6kkd.aspx (= depends on command-line switches and pragmas) *)
          (* GCC documentation is not clear about it. *)
          ev state e $. fun state v ->
          cont state (check_pointer_within_limits ass_term l (field_address l env v fparent targs fname))
        | WReadArray (le, w1, tp, w2) ->
          ev state w1 $. fun state arr ->
          ev state w2 $. fun state index ->
          cont state (check_pointer_within_limits ass_term le (mk_ptr_add_ le env arr index tp))
        | WVar (l, x, GlobalName) ->
          let Some (l, tp, symbol, init) = try_assoc x globalmap in cont state symbol
        (* The address of a function symbol is commonly used in the
           assignment of function pointers. We tread (&function) in the
           same way as (function), which is what most compilers do: *)
        | WVar (l, x, FuncName) ->
            cont state (List.assoc x all_funcnameterms)
        | WDeref (l, w, tp) ->
          ev state w cont
        | WReadUnionMember (l, w, unionName, memberIndex, memberName, memberType, isActivating) ->
          ev state w $. fun state v ->
          cont state (mk_union_variant_ptr v unionName memberIndex)
        | _ -> static_error l "Taking the address of this expression is not supported." None
      end
    | WSwitchExpr (l, e, i, targs, cs, cdef_opt, tenv, tp) ->
      let tt = InductiveType (i, targs) in
      let g = mk_ident "switch_expression" in
      ev state e $. fun state t ->
      let env =
        let rec iter env0 env =
          match env with
            [] -> env0
          | (x, t)::env ->
            if List.mem_assoc x env0 then iter env0 env else iter ((x, t)::env0) env
        in
        iter [] env
      in
      let (_, _, ctormap, _, _, _, _, subtype, _) = List.assoc i inductivemap in
      let symbol = ctxt#mk_symbol g (typenode_of_type tt :: List.map (fun (x, _) -> typenode_of_type (List.assoc x tenv)) env) (typenode_of_type tp) (Proverapi.Fixpoint (subtype, 0)) in
      let case_clauses = List.map (fun (SwitchExprClause (_, cn, ps, e)) -> (cn, (ps, e))) cs in
      let (_, _, ctormap, _, _, _, _, _, _) = List.assoc i inductivemap in
      let fpclauses =
        List.map
          begin fun (cn, (_, (_, tparams, _, parameter_names_and_types, (csym, _)))) ->
            let (_, pts) = List.split parameter_names_and_types in
            match try_assoc cn case_clauses with
              Some (ps, e) ->
              let apply (_::gvs) cvs =
                let Some genv = zip (List.map fst env) gvs in
                let Some penv = zip ps cvs in
                let penv =
                  if tparams = [] then penv else
                  let Some penv = zip penv pts in
                  let Some tpenv = zip tparams targs in
                  List.map
                    (fun ((pat, term), typ) ->
                     match unfold_inferred_type typ with
                       GhostTypeParam x -> (pat, convert_provertype term ProverInductive (provertype_of_type (List.assoc x tpenv)))
                     | _ -> (pat, term)
                    )
                    penv
                in
                let env = penv@genv in
                eval_core None None env e
              in
              (csym, apply)
            | None ->
              let (Some (_, e)) = cdef_opt in
              let apply (_::gvs) cvs =
                let Some genv = zip (List.map fst env) gvs in
                eval_core None None genv e
              in
              (csym, apply)
          end
          ctormap
      in
      ctxt#set_fpclauses symbol 0 fpclauses;
      cont state (ctxt#mk_app symbol (t::List.map (fun (x, t) -> t) env))
    | ProverTypeConversion (tfrom, tto, e) -> ev state e $. fun state v -> cont state (convert_provertype v tfrom tto)
    | Unbox (e, t) ->
      ev state e $. fun state v ->
      cont state (convert_provertype v ProverInductive (provertype_of_type t))
    | SizeofExpr (l, TypeExpr (ManifestTypeExpr (_, t))) ->
      cont state (sizeof_core l env t)
    | AlignofExpr (l, ManifestTypeExpr (_, t)) ->
      cont state (alignof_core l env t)
    | SizeofExpr (l, w) ->
      ev state w $. fun state v ->
      cont state (mk_sizeof v)
    | WTypePredExpr (l, t, predName) ->
      let (_, _, _, symb) = List.assoc predName typepreddeclmap in
      cont state (ctxt#mk_app symb [typeid_of_core l env t])
    | InstanceOfExpr(l, e, ManifestTypeExpr (l2, tp)) ->
      ev state e $. fun state v -> cont state (ctxt#mk_app instanceof_symbol [v; prover_type_term l2 tp])
    | _ -> static_error (expr_loc e) "Construct not supported in this position." None
  
  let rec eval_core ass_term read_field env e =
    let rec ev () e cont = eval_core_cps0 eval_core ev () ass_term read_field env e cont in
    ev () e $. fun () v -> v
  
  let eval_core_cps ev state ass_term read_field env e cont = eval_core_cps0 eval_core ev state ass_term read_field env e cont
  
  let eval read_field env e = eval_core None read_field env e

  let _ =
    List.iter
    begin function
       (g, (l, tparams, t, pmap, Some index, SwitchExpr (_, Var (_, x), cs, _), pn, ilist, fsym)) ->
       let typeid_pmap = tparams |> flatmap @@ fun x -> if tparam_carries_typeid x then [x ^ "_typeid", voidPtrType] else [] in
       let rec index_of_param i x0 ps =
         match ps with
           [] -> assert false
         | (x, tp)::ps -> if x = x0 then (i, tp) else index_of_param (i + 1) x0 ps
       in
       let (i, InductiveType (_, targs)) = index_of_param 0 x pmap in
       let clauses =
         List.map
           (function SwitchExprClause (_, cn, pats, e) ->
              let (_, tparams, _, ts, (ctorsym, _)) = match try_assoc' Ghost (pn,ilist) cn purefuncmap with Some x -> x in
              let eval_body gts cts =
                let Some pts = zip (typeid_pmap @ pmap) gts in
                let penv = List.map (fun ((p, tp), t) -> (p, t)) pts in
                let Some patenv = zip pats cts in
                let patenv = List.filter (fun (x, t) -> x <> "_") patenv in
                let patenv =
                  if tparams = [] then patenv else
                  let Some tpenv = zip tparams targs in
                  let Some patenv = zip patenv ts in
                  List.map
                    (fun ((x, term), (name, typ)) ->
                     let term =
                     match unfold_inferred_type typ with
                       GhostTypeParam x -> convert_provertype term ProverInductive (provertype_of_type (List.assoc x tpenv))
                     | _ -> term
                     in
                     (x, term)
                    )
                    patenv
                in
                eval None (patenv @ penv) e
              in
              (ctorsym, eval_body)
           )
           cs
       in
       ctxt#set_fpclauses fsym (List.length typeid_pmap + i) clauses
     | (g, (l, tparams, t, pmap, None, w, pn, ilist, fsym)) ->
       let typeid_pmap = tparams |> flatmap @@ fun x -> if tparam_carries_typeid x then [x ^ "_typeid", voidPtrType] else [] in
       ctxt#begin_formal;
       let env = imap (fun i (x, tp) -> let pt = typenode_of_type tp in (pt, (x, ctxt#mk_bound i pt))) (typeid_pmap @ pmap) in
       let tps = List.map fst env in
       let env = List.map snd env in
       let rhs = eval None env w in
       let lhs = ctxt#mk_app fsym (List.map snd env) in
       ctxt#end_formal;
       ctxt#assume_forall g [lhs] tps (ctxt#mk_eq lhs rhs)
    end
    fixpointmap1
  
  end

end
