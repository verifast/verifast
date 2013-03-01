open Proverapi
open Big_int
open Printf
open Num (* rational numbers *)
open Util
open Stats
open Lexer
open Ast
open Parser
open Verifast0

module type VERIFY_PROGRAM_ARGS = sig
  val emitter_callback: package list -> unit
  type typenode
  type symbol
  type termnode
  val ctxt: (typenode, symbol, termnode) Proverapi.context
  val options: options
  val program_path: string
  val reportRange: range_kind -> loc -> unit
  val reportUseSite: decl_kind -> loc -> loc -> unit
  val reportExecutionForest: node list ref -> unit
  val breakpoint: (string * int) option
  val targetPath: int list option
end

module VerifyProgram1(VerifyProgramArgs: VERIFY_PROGRAM_ARGS) = struct

  include VerifyProgramArgs

  let path = program_path
  
  let language = file_type path
  
  let {
    option_verbose=initial_verbosity;
    option_disable_overflow_check=disable_overflow_check;
    option_allow_should_fail=allow_should_fail;
    option_emit_manifest=emit_manifest;
    option_include_paths=include_paths
  } = options
  
  let verbosity = ref 0
  
  let set_verbosity v =
    verbosity := v;
    ctxt#set_verbosity (v - 3)
  
  let () = set_verbosity initial_verbosity
  
  let class_counter = ref 0

  (** Maps an identifier to a ref cell containing approximately the number of distinct symbols that have been generated for this identifier.
    * It is an approximation because of clashes such as the clash between the second symbol ('foo0') generated for 'foo'
    * and the first symbol ('foo0') generated for 'foo0'. *)
  let used_ids = Hashtbl.create 10000
  (** Contains all ref cells from used_ids that need to be decremented at the next pop(). *)
  let used_ids_undo_stack = ref []
  (** The terms that represent coefficients of leakable chunks. These come from [_] patterns in the source code. *)
  let dummy_frac_terms = ref []
  (** The terms that represent predicate constructor applications. *)
  let pred_ctor_applications : (termnode * (symbol * termnode * (termnode list) * int option)) list ref = ref []
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
    if options.option_simplify_terms then
      match ctxt#simplify t with None -> ctxt#pprint t | Some(t) -> ctxt#pprint t
    else
      ctxt#pprint t
  
  let globalPluginMap = ref []
  
  let pprint_context_stack cs =
    List.map
      (function
         Assuming t -> Assuming (pprint_context_term t)
       | Executing (h, env, l, msg) ->
         let h' =
           List.map
             begin function
               (Chunk ((g, literal), targs, coef, ts, Some (PluginChunkInfo info))) ->
               let [_, ((_, plugin), _)] = !globalPluginMap in
               Chunk ((ctxt#pprint g, literal), targs, pprint_context_term coef, [plugin#string_of_state info], None)
             | (Chunk ((g, literal), targs, coef, ts, size)) ->
               Chunk ((ctxt#pprint g, literal), targs, pprint_context_term coef, List.map (fun t -> pprint_context_term t) ts, size)
             end
             h
         in
         let env' = List.map (fun (x, t) -> (x, pprint_context_term t)) env in
         Executing (h', env', l, msg)
       | PushSubcontext -> PushSubcontext
       | PopSubcontext -> PopSubcontext)
      cs

  let register_pred_ctor_application t symbol symbol_term ts inputParamCount =
    pred_ctor_applications := (t, (symbol, symbol_term, ts, inputParamCount)) :: !pred_ctor_applications

  let assert_false h env l msg url =
    raise (SymbolicExecutionError (pprint_context_stack !contextStack, "false", l, msg, url))
  
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
    oldForest := Node (msg, !currentPath, newForest)::!oldForest;
    push_undo_item (fun () -> currentForest := oldForest);
    currentForest := newForest
  
  let push_context msg =
    contextStack := msg::!contextStack;
    begin match msg with
      Executing (h, env, l, msg) ->
      push_node l msg
    | _ -> ()
    end
  let pop_context () = let (h::t) = !contextStack in contextStack := t
  
  let contextStackStack = ref []
  
  let push_contextStack () = push_undoStack(); contextStackStack := !contextStack::!contextStackStack
  let pop_contextStack () = pop_undoStack(); let h::t = !contextStackStack in contextStack := h; contextStackStack := t
  
  let with_context_force msg cont =
    stats#execStep;
    push_contextStack ();
    push_context msg;
    let result = cont() in
    pop_contextStack ();
    result
  
  let with_context msg cont =
    stats#execStep;
    push_contextStack ();
    push_context msg;
    let result =
      if !targetPath <> Some [] then
        cont()
      else
        SymExecSuccess
    in
    pop_contextStack ();
    result
  
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
    | IntType -> ProverInt
    | UShortType -> ProverInt
    | ShortType -> ProverInt
    | UintPtrType -> ProverInt
    | RealType -> ProverReal
    | UChar -> ProverInt
    | Char -> ProverInt
    | InductiveType _ -> ProverInductive
    | StructType sn -> assert false
    | ObjType n -> ProverInt
    | ArrayType t -> ProverInt
    | StaticArrayType (t, s) -> ProverInt
    | PtrType t -> ProverInt
    | FuncType _ -> ProverInt
    | PredType (tparams, ts, inputParamCount) -> ProverInductive
    | PureFuncType _ -> ProverInductive
    | BoxIdType -> ProverInt
    | HandleIdType -> ProverInt
    | AnyType -> ProverInductive
    | TypeParam _ -> ProverInductive
    | Void -> ProverInductive
    | InferredType t -> begin match !t with None -> t := Some (InductiveType ("unit", [])); ProverInductive | Some t -> provertype_of_type t end
  
  let typenode_of_type t = typenode_of_provertype (provertype_of_type t)
   
  (* Generate some global symbols. *)
  
  let get_class_symbol = mk_symbol "getClass" [ctxt#type_int] ctxt#type_int Uninterp
  let class_serial_number = mk_symbol "class_serial_number" [ctxt#type_int] ctxt#type_int Uninterp
  let bitwise_or_symbol = mk_symbol "bitor" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp
  let bitwise_xor_symbol = mk_symbol "bitxor" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp
  let bitwise_and_symbol = mk_symbol "bitand" [ctxt#type_int; ctxt#type_int] ctxt#type_int Uninterp
  let bitwise_not_symbol = mk_symbol "bitnot" [ctxt#type_int] ctxt#type_int Uninterp
  let arraylength_symbol = mk_symbol "arraylength" [ctxt#type_int] ctxt#type_int Uninterp
  let shiftleft_int32_symbol = mk_symbol "shiftleft_int32" [ctxt#type_int;ctxt#type_int] ctxt#type_int Uninterp (* shift left and truncate to 32-bit signed integer; Java's "<<" operator on two ints *)
  let shiftright_symbol = mk_symbol "shiftright" [ctxt#type_int;ctxt#type_int] ctxt#type_int Uninterp (* shift right with sign extension; Java's ">>" operator. For nonnegative n, "x >> n" is equivalent to floor(x / 2^n). *)
  let truncate_int8_symbol = mk_symbol "truncate_int8" [ctxt#type_int] ctxt#type_int Uninterp
  let truncate_uint8_symbol = mk_symbol "truncate_uint8" [ctxt#type_int] ctxt#type_int Uninterp
  let truncate_int16_symbol = mk_symbol "truncate_int16" [ctxt#type_int] ctxt#type_int Uninterp
  
  let () = ignore $. ctxt#assume (ctxt#mk_eq (ctxt#mk_unboxed_bool (ctxt#mk_boxed_int (ctxt#mk_intlit 0))) ctxt#mk_false) (* This allows us to use 0 as a default value for all types; see the treatment of array creation. *)

  let boolt = Bool
  let intt = IntType
  let instanceof_symbol = ctxt#mk_symbol "instanceof" [ctxt#type_int; ctxt#type_int] ctxt#type_bool Uninterp
  let array_type_symbol = ctxt#mk_symbol "array_type"  [ctxt#type_int] ctxt#type_int Uninterp
  
  let two_big_int = big_int_of_int 2
  
  let real_zero = ctxt#mk_reallit 0
  let real_unit = ctxt#mk_reallit 1
  let real_half = ctxt#mk_reallit_of_num (num_of_ints 1 2)

  let int_zero_term = ctxt#mk_intlit 0

  (* unsigned int & pointer types *)
  let min_uint_term = ctxt#mk_intlit_of_string "0"
  let max_uint_term = ctxt#mk_intlit_of_string "4294967295"
  let min_ptr_big_int = big_int_of_string "0"
  let max_ptr_big_int = big_int_of_string "4294967295"
  let max_ptr_term = ctxt#mk_intlit_of_string "4294967295"

  (* signed int *)
  let min_int_big_int = big_int_of_string "-2147483648"
  let min_int_term = ctxt#mk_intlit_of_string "-2147483648"
  let max_int_big_int = big_int_of_string "2147483647"
  let max_int_term = ctxt#mk_intlit_of_string "2147483647"

  (* unsigned short *)
  let min_ushort_big_int = big_int_of_string "0"
  let min_ushort_term = ctxt#mk_intlit_of_string "0"
  let max_ushort_big_int = big_int_of_string "65535"
  let max_ushort_term = ctxt#mk_intlit_of_string "65535"

  (* signed short *)
  let min_short_big_int = big_int_of_string "-32768"
  let min_short_term = ctxt#mk_intlit_of_string "-32768"
  let max_short_big_int = big_int_of_string "32767"
  let max_short_term = ctxt#mk_intlit_of_string "32767"

  (* unsigned char *)
  let min_uchar_big_int = big_int_of_string "0"
  let min_uchar_term = ctxt#mk_intlit_of_string "0"
  let max_uchar_big_int = big_int_of_string "255"
  let max_uchar_term = ctxt#mk_intlit_of_string "255"

  (* signed char *)
  let min_char_big_int = big_int_of_string "-128"
  let min_char_term = ctxt#mk_intlit_of_string "-128"
  let max_char_big_int = big_int_of_string "127"
  let max_char_term = ctxt#mk_intlit_of_string "127"
  
  let get_unique_var_symb x t = 
    ctxt#mk_app (mk_symbol x [] (typenode_of_type t) Uninterp) []
  
  let assume_bounds term tp = 
    match tp with
      Char -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le min_char_term term) (ctxt#mk_le term max_char_term));
    | UChar -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le min_uchar_term term) (ctxt#mk_le term max_uchar_term));
    | ShortType -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le min_short_term term) (ctxt#mk_le term max_short_term));
    | UShortType -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le min_ushort_term term) (ctxt#mk_le term max_ushort_term));
    | IntType -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le min_int_term term) (ctxt#mk_le term max_int_term));
    | PtrType _ | UintPtrType -> ignore $. ctxt#assume (ctxt#mk_and (ctxt#mk_le (ctxt#mk_intlit 0) term) (ctxt#mk_le term max_ptr_term));
    | _ -> ()
  
  let get_unique_var_symb_non_ghost x t = 
    let res = get_unique_var_symb x t in
    assume_bounds res t;
    res
  
  let get_unique_var_symb_ x t ghost = 
    if ghost then
      get_unique_var_symb x t
    else
      get_unique_var_symb_non_ghost x t
  
  let get_dummy_frac_term () =
    let t = get_unique_var_symb "dummy" RealType in
    dummy_frac_terms := t::!dummy_frac_terms;
    t
  
  let is_dummy_frac_term t = List.memq t !dummy_frac_terms
  
  let get_unique_var_symbs_ xts ghost = List.map (fun (x, t) -> (x, get_unique_var_symb_ x t ghost)) xts
  let get_unique_var_symbs_non_ghost xts = List.map (fun (x, t) -> (x, get_unique_var_symb_non_ghost x t)) xts
  
  let real_unit_pat = TermPat real_unit
  
  let plugin_context = object
    method mk_symbol x tp = get_unique_var_symb x (match tp with Plugins.PointerTerm -> PtrType Void | Plugins.IntTerm -> IntType | Plugins.CharListTerm -> InductiveType ("list", [IntType]))
    method query_formula t1 r t2 = ctxt#query (match r with Plugins.Eq -> ctxt#mk_eq t1 t2 | Plugins.Neq -> ctxt#mk_not (ctxt#mk_eq t1 t2) | Plugins.Lt -> ctxt#mk_lt t1 t2)
    method push = ctxt#push
    method assert_formula t1 r t2 = ctxt#assume (match r with Plugins.Eq -> ctxt#mk_eq t1 t2 | Plugins.Neq -> ctxt#mk_not (ctxt#mk_eq t1 t2) | Plugins.Lt -> ctxt#mk_lt t1 t2) = Unsat
    method pop = ctxt#pop
  end
  
  let current_module_name =
    match language with
      | Java -> "current_module"
      | CLang -> Filename.chop_extension (Filename.basename path)
  
  let current_module_term = get_unique_var_symb current_module_name IntType
  
  let programDir = Filename.dirname path
  let rtpath = match options.option_runtime with None -> concat rtdir "rt.jarspec" | Some path -> path
  (** Records the source lines containing //~, indicating that VeriFast is supposed to detect an error on that line. *)
  let shouldFailLocs = ref []
  
  (* Callback function called from the lexer. *)
  let reportShouldFail l =
    if allow_should_fail then
      shouldFailLocs := l::!shouldFailLocs
    else
      static_error l "Should fail directives are not allowed; use the -allow_should_fail command-line option to allow them." None
  
  let check_should_fail default body =
    let locs_match ((path0, line0, _), _) ((path1, line1, _), _) = path0 = path1 && line0 = line1 in
    let should_fail l = List.exists (locs_match l) !shouldFailLocs in
    let has_failed l = shouldFailLocs := remove (locs_match l) !shouldFailLocs; default in
    let loc_of_ctxts ctxts l = match get_root_caller ctxts with None -> l | Some l -> l in
    try
      body ()
    with
    | StaticError (l, msg, url) when should_fail l -> has_failed l
    | SymbolicExecutionError (ctxts, phi, l, msg, url) when should_fail (loc_of_ctxts ctxts l) -> has_failed (loc_of_ctxts ctxts l)
    | PreprocessorDivergence (l,s) when should_fail l -> has_failed l
 
  let prototypes_used : (string * loc) list ref = ref []
  
  let register_prototype_used l g =
    if not (List.mem (g, l) !prototypes_used) then
      prototypes_used := (g, l)::!prototypes_used
  
  let extract_specs ps=
    let rec iter (pn,ilist) classes lemmas ds=
      match ds with
      [] -> (classes,lemmas)
    | Class (l, abstract, fin, cn, meths, fds, cons, super, inames, preds)::rest ->
      let cn = full_name pn cn in
      let meths' = meths |> List.filter begin
        fun x ->
          match x with
            | Meth(lm, gh, t, n, ps, co, ss,fb,v,abstract) ->
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
      iter (pn,ilist) (Class(l,abstract,fin,cn,meths',fds,cons',super,inames,[])::classes) lemmas rest
    | Func(l,Lemma(_),tparams,rt,fn,arglist,nonghost_callers_only,ftype,contract,None,fb,vis) as elem ::rest->
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
  
  (* Region: check_file *)
  
  module CheckFileTypes = struct
    type 'a map = (string * 'a) list
    type struct_field_info =
        loc
      * ghostness
      * type_
    type struct_info =
        loc
      * (string * struct_field_info) list option (* None if struct without body *)
      * termnode option (* predicate symbol for struct_padding predicate *)
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
      * type_ list (* parameter types *)
      * func_symbol
    type inductive_ctor_info =
        string (* fully qualified constructor name *)
      * pure_func_info
    type inductive_info =
        loc
      * string list (* type parameters *)
      * (string * inductive_ctor_info) list
      * string list option (* The type is infinite if any of these type parameters are infinite; if None, it is always infinite. *)
    type pred_ctor_info =
      PredCtorInfo of
        loc
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
    type malloc_block_pred_info =
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
      * termnode option (* function pointer; None if ? *)
      * loc
      * func_kind
      * string list (* type parameters *)
      * type_ option
      * (string * type_) list (* parameters *)
      * bool (* nonghost_callers_only *)
      * asn (* precondition *)
      * (string * type_) list (* type environment after precondition *)
      * asn (* postcondition *)
      * (string * pred_fam_info map * type_ list * (loc * string) list) option (* implemented function type, with function type type arguments and function type arguments *)
      * (stmt list * loc (* closing brace *) ) option option (* body; None if prototype; Some None if ? *)
      * method_binding (* always Static; TODO: remove *)
      * visibility (* always Public; TODO: remove *)
    type func_type_info =
        loc
      * ghostness
      * string list (* type parameters *)
      * type_ option (* return type *)
      * type_ map (* parameters of the function type *)
      * type_ map (* parameters of the function *)
      * asn (* precondition *)
      * asn (* postcondition *)
      * pred_fam_info map (* the is_xyz predicate, if any *)
    type signature = string * type_ list
    type method_info =
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
      * (stmt list * loc) option option (* body *)
      * method_binding
      * visibility
      * bool (* is override *)
      * bool (* is abstract *)
    type interface_method_info =
        loc
      * ghostness
      * type_ option (* return type *)
      * type_ map (* parameters *)
      * asn (* precondition *)
      * type_ map (* type environment after precondition *)
      * asn (* postcondition *)
      * (type_ * asn) list (* throws clauses *)
      * visibility
      * bool (* is abstract *)
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
        loc
      * type_ map (* parameters *)
      * asn
      * type_ map
      * asn
      * (type_ * asn) list
      * (stmt list * loc) option option
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
      * string list (* superinterfaces *)
    type class_info = {
      cl: loc;
      cabstract: bool;
      cfinal: class_finality;
      cmeths: (signature * method_info) list;
      cfds: field_info map;
      cctors: (type_ list * ctor_info) list;
      csuper: string;
      cinterfs: string list;
      cpreds: inst_pred_info map;
      cpn: string; (* package *)
      cilist: import list
    }
    type plugin_info = (* logic plugins, e.g. to enable the use of Philippa Gardner's context logic for reasoning about tree data structures *)
        (  Plugins.plugin
         * termnode Plugins.plugin_instance)
      * termnode (* predicate symbol for plugin chunk *)
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
    type maps =
        struct_info map
      * enum_info map
      * global_info map
      * module_info map
      * module_info map
      * inductive_info map
      * pure_func_info map
      * pred_ctor_info map
      * malloc_block_pred_info map
      * ((string * string) * field_pred_info) list
      * pred_fam_info map
      * pred_inst_map
      * type_ map (* typedefmap *)
      * func_type_info map
      * func_info map
      * box_info map
      * class_info map
      * interface_info map
      * termnode map (* classterms *)
      * termnode map (* interfaceterms *)
      * plugin_info map
    
    type implemented_prototype_info =
        string
      * loc
    type implemented_function_type_info =
        string (* function name *)
      * loc (* function location *)
      * string (* function type name *)
      * string list (* function type arguments; only module names are supported *)
      * bool (* function is declared in an unloadable module *)
    type check_file_output =
        implemented_prototype_info list
      * implemented_function_type_info list
      * module_info map
  end
  
  include CheckFileTypes
  
  (* Maps a header file name to the list of header file names that it includes, and the various maps of VeriFast elements that it declares directly. *)
  let headermap: ((loc * (string * string) * string list * package list) list * maps) map ref = ref []
  let spec_classes= ref []
  let spec_lemmas= ref []
  
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
    val basedir: string
    val reldir: string
    val headers: (loc * (string * string) * string list * package list) list
    val ps: package list
    
    (** For recursive calls. *)
    val check_file: string -> bool -> bool -> string -> string -> (loc * (string * string) * string list * package list) list -> package list -> check_file_output * maps
  end
  
  module CheckFile1(CheckFileArgs: CHECK_FILE_ARGS) = struct
  
  include CheckFileArgs
  
  let is_jarspec = Filename.check_suffix filepath ".jarspec"
  
  let
    (
      (structmap0: struct_info map),
      (enummap0: enum_info map),
      (globalmap0: global_info map),
      (modulemap0: module_info map),
      (importmodulemap0: module_info map),
      (inductivemap0: inductive_info map),
      (purefuncmap0: pure_func_info map),
      (predctormap0: pred_ctor_info map),
      (malloc_block_pred_map0: malloc_block_pred_info map),
      (field_pred_map0: ((string * string) * field_pred_info) list),
      (predfammap0: pred_fam_info map),
      (predinstmap0: pred_inst_map),
      (typedefmap0: type_ map),
      (functypemap0: func_type_info map),
      (funcmap0: func_info map),
      (boxmap0: box_info map),
      (classmap0: class_info map),
      (interfmap0: interface_info map),
      (classterms0: termnode map),
      (interfaceterms0: termnode map),
      (pluginmap0: plugin_info map)
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
      (structmap, enummap, globalmap, modulemap, importmodulemap, inductivemap, purefuncmap, predctormap, malloc_block_pred_map, field_pred_map, predfammap, predinstmap, typedefmap, functypemap, funcmap, boxmap, classmap, interfmap, classterms, interfaceterms, pluginmap)
      (structmap0, enummap0, globalmap0, modulemap0, importmodulemap0, inductivemap0, purefuncmap0, predctormap0, malloc_block_pred_map0, field_pred_map0, predfammap0, predinstmap0, typedefmap0, functypemap0, funcmap0, boxmap0, classmap0, interfmap0, classterms0, interfaceterms0, pluginmap0)
      =
      (append_nodups structmap structmap0 id l "struct",
       append_nodups enummap enummap0 id l "enum",
       append_nodups globalmap globalmap0 id l "global variable",
       modulemap @ modulemap0,
(*       append_nodups modulemap modulemap0 id l "module", *)
       importmodulemap @ importmodulemap0,
(*     append_nodups importmodulemap importmodulemap0 id l "imported module", *)
       append_nodups inductivemap inductivemap0 id l "inductive datatype",
       append_nodups purefuncmap purefuncmap0 id l "pure function",
       append_nodups predctormap predctormap0 id l "predicate constructor",
       malloc_block_pred_map @ malloc_block_pred_map0,
       field_pred_map @ field_pred_map0,
       append_nodups predfammap predfammap0 id l "predicate",
       append_nodups predinstmap predinstmap0 (fun (p, is) -> p ^ "(" ^ String.concat ", " is ^ ")") l "predicate instance",
       append_nodups typedefmap typedefmap0 id l "typedef",
       append_nodups functypemap functypemap0 id l "function type",
       append_nodups funcmap funcmap0 id l "function",
       append_nodups boxmap boxmap0 id l "box predicate",
       append_nodups classmap classmap0 id l "class",
       append_nodups interfmap interfmap0 id l "interface",
       classterms @ classterms0, 
       interfaceterms @ interfaceterms0,
       if pluginmap0 <> [] && pluginmap <> [] then static_error l "VeriFast does not yet support loading multiple plugins" None else
       append_nodups pluginmap pluginmap0 id l "plugin")
    in

    (** [merge_header_maps maps0 headers] returns [maps0] plus all elements transitively declared in [headers]. *)
    let rec merge_header_maps include_prelude maps0 headers_included basedir reldir headers =
      match headers with
        [] -> (maps0, headers_included)
      | (l, (header_path, total_path), hs, header_decls)::headers ->
        if List.mem header_path ["bool.h"; "assert.h"; "limits.h"] then
          merge_header_maps include_prelude maps0 headers_included basedir reldir headers
        else begin
          if (options.option_safe_mode || options.option_header_whitelist <> []) && not (List.mem header_path options.option_header_whitelist) then
            static_error l "This header file is not on the header whitelist." None;
          let rellocalpath = concat reldir header_path in
          let includepaths = List.append include_paths [basedir; bindir] in
          let rec find_include_file includepaths =
            match includepaths with
              [] -> static_error l (Printf.sprintf "No such file: '%s'" rellocalpath) None
            | head::body ->
              let headerpath = concat head rellocalpath in
              if Sys.file_exists headerpath then
                (head, rellocalpath)
              else
                (find_include_file body)
          in
          let (basedir1, relpath) = find_include_file includepaths in
          let relpath = reduce_path relpath in
          let path = if (options.option_run_preprocessor) then total_path else concat basedir1 relpath in
          if List.mem path headers_included then
            merge_header_maps include_prelude maps0 headers_included basedir reldir headers
          else begin
            let reldir1 = Filename.dirname relpath in
            let (headers', maps) =
              match try_assoc path !headermap with
                None ->
                let header_is_import_spec = Filename.chop_extension (Filename.basename header_path) <> Filename.chop_extension (Filename.basename program_path) in
                let (headers', ds) =
                  match language with
                    CLang ->
                      if (options.option_run_preprocessor) then begin
                        let rec look_up hs headers =
                          match headers with
                            (l', (h',tp'), hs', ps')::rest -> 
                              if (List.mem tp' hs && tp' <> total_path) then 
                                (l', (h',tp'), hs', ps')::(look_up (List.append hs hs') rest)
                              else 
                                look_up hs rest
                          | [] -> []
                        in
                        look_up hs headers, header_decls
                      end
                      else
                        parse_header_file basedir1 relpath reportRange reportShouldFail false []
                  | Java ->
                    let (jars, javaspecs) = parse_jarspec_file_core path in
                    let pathDir = Filename.dirname path in
                    let ds = List.map (fun javaspec -> parse_java_file (concat pathDir javaspec) reportRange reportShouldFail) javaspecs in
                    if not header_is_import_spec then begin
                      let (classes, lemmas) = extract_specs ds in
                      spec_classes := classes;
                      spec_lemmas := lemmas
                    end;
                    let l = file_loc path in
                    let jarspecs = List.map (fun path -> (l, (path ^ "spec", concat bindir (path ^ "spec")), [], [])) jars in
                    (jarspecs, ds)
                in
                let (_, maps) = check_file header_path header_is_import_spec include_prelude basedir1 reldir1 headers' ds in
                headermap := (path, (headers', maps))::!headermap;
                (headers', maps)
              | Some (headers', maps) ->
                (headers', maps)
            in
            let (maps0, headers_included) = merge_header_maps include_prelude maps0 headers_included basedir1 reldir1 headers' in
            merge_header_maps include_prelude (merge_maps l maps maps0) (path::headers_included) basedir reldir headers
          end
        end
    in

    let maps0 = ([], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []) in
    
    let (maps0, headers_included) =
      if include_prelude then
        match file_type path with
          | Java -> begin
            if rtpath = "nort" then (maps0, []) else
            match try_assoc rtpath !headermap with
              | None -> 
                let ([], javaspecs) = parse_jarspec_file_core rtpath in
                let javaspecs =
                  if options.option_allow_assume then "_assume.javaspec"::javaspecs else javaspecs
                in
                let ds = List.map (fun x -> parse_java_file (concat rtdir x) reportRange reportShouldFail) javaspecs in
                let (_, maps0) = check_file rtpath true false bindir "" [] ds in
                headermap := (rtpath, ([], maps0))::!headermap;
                (maps0, [])
              | Some ([], maps0) ->
                (maps0, [])
          end
          | CLang ->
            if (options.option_run_preprocessor) then begin
              let (headers, prelude_decls) = parse_header_file bindir "prelude.h" reportRange reportShouldFail options.option_run_preprocessor [] in
              let header_names = List.map (fun (_,(_,h),_,_) -> h) headers in
              merge_header_maps false maps0 [] bindir "" ((dummy_loc, ("prelude.h",concat bindir "prelude.h"), header_names, prelude_decls)::headers)
            end
            else
              merge_header_maps false maps0 [] bindir "" [(dummy_loc, ("prelude.h",""), [], [])]
      else
        (maps0, [])
    in

    let (maps, _) = merge_header_maps include_prelude maps0 headers_included basedir reldir headers in
    maps

  (* Region: structdeclmap, enumdeclmap, inductivedeclmap, modulemap *)
  
  let pluginmap1 =
    ps |> List.fold_left begin fun pluginmap1 (PackageDecl (l, pn, ilist, ds)) ->
      ds |> List.fold_left begin fun pluginmap1 decl ->
        match decl with
          LoadPluginDecl (l, lx, x) ->
          if pluginmap0 <> [] || pluginmap1 <> [] then static_error l "VeriFast does not yet support loading multiple plugins" None;
          if options.option_safe_mode then static_error l "Loading plugins is not allowed in safe mode" None;
          begin try
            let p = Plugins_private.load_plugin (concat basedir (x ^ "_verifast_plugin")) in
            let x = full_name pn x in
            (x, ((p, p#create_instance plugin_context), get_unique_var_symb x (PredType ([], [], None))))::pluginmap1
          with
            Plugins_private.LoadPluginError msg -> static_error l ("Could not load plugin: " ^ msg) None
          end
        | _ -> pluginmap1
      end pluginmap1
    end []
  
  let pluginmap = pluginmap1 @ pluginmap0
  
  let () = globalPluginMap := pluginmap1 @ !globalPluginMap
  
  let unloadable =
    match language with
      | CLang ->
        let [PackageDecl (_, _, _, ds)] = ps in
        List.exists (function (UnloadableModuleDecl l) -> true | _ -> false) ds
      | Java -> false
  
  let typedefdeclmap =
    let rec iter tddm ds =
      match ds with
        [] -> List.rev tddm
      | TypedefDecl (l, te, d)::ds ->
        (* C compiler detects duplicate typedefs *)
        iter ((d, (l, te))::tddm) ds
      | _::ds ->
        iter tddm ds
    in
    if language = Java then [] else
    let [PackageDecl(_,"",[],ds)] = ps in iter [] ds
  
  let structdeclmap =
    let rec iter sdm ds =
      match ds with
        [] -> sdm
      | Struct (l, sn, fds_opt)::ds ->
        begin
          match try_assoc sn structmap0 with
            Some (_, Some _, _) -> static_error l "Duplicate struct name." None
          | Some (_, None, _) | None -> ()
        end;
        begin
          match try_assoc sn sdm with
            Some (_, Some _) -> static_error l "Duplicate struct name." None
          | Some (_, None) | None -> iter ((sn, (l, fds_opt))::sdm) ds
        end
      | _::ds -> iter sdm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    | _ when file_type path=Java -> []
  
  let enumdeclmap = 
    let rec iter edm ds = 
      match ds with
        [] -> List.rev edm
      | EnumDecl(l, en, elems) :: ds ->
        begin 
          match try_assoc en edm with
        | Some((l', elems')) -> static_error l "Duplicate enum name." None
        | None -> iter ((en, (l, elems)) :: edm) ds
        end
      | _ :: ds -> iter edm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    | _ when file_type path=Java -> []
  
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
                    IntLit (_, n, _) -> n
                  | Var (l, x, _) ->
                    begin match try_assoc2 x enummap1 enummap0 with
                      None -> static_error l "No such enumeration constant" None
                    | Some n -> n
                    end
                  | Operation (l, op, [e1; e2], _) ->
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
    let ds=match ps with
        [PackageDecl(_,"",[],ds)] -> ds
      | _ when file_type path=Java -> []
    in
    flatmap (function (FuncTypeDecl (l, gh, _, g, tps, ftps, _, _)) -> [g, (l, gh, tps, ftps)] | _ -> []) ds
  
  let inductivedeclmap=
    let rec iter pn idm ds =
      match ds with
        [] -> idm
      | (Inductive (l, i, tparams, ctors))::ds -> let n=full_name pn i in
        if n = "bool" || n = "boolean" || n = "int" || List.mem_assoc n idm || List.mem_assoc n inductivemap0 then
          static_error l "Duplicate datatype name." None
        else
          iter pn ((n, (l, tparams, ctors))::idm) ds
      | _::ds -> iter pn idm ds
    in
    let rec iter' idm ps=
      match ps with
      PackageDecl(l,pn,ilist,ds)::rest -> iter' (iter pn idm ds) rest
      | [] -> List.rev idm
    in
    iter' [] ps
   
  (* Region: Java name resolution functions *)
  
  let rec try_assoc' (pn,imports) name map=
    match imports with
      _ when List.mem_assoc (full_name pn name) map -> Some (List.assoc (full_name pn name) map)
    | _ when List.mem_assoc name map-> Some (List.assoc name map)
    | Import(l,p,None)::rest when List.mem_assoc (full_name p name) map->  Some (List.assoc (full_name p name) map)
    | Import(l,p,Some name')::rest when name=name' && List.mem_assoc (full_name p name) map-> Some (List.assoc (full_name p name) map) 
    | _::rest -> try_assoc' (pn,rest) name map
    | [] -> None
  
  let rec try_assoc_pair' (pn,imports) (n,n') map=
    match imports with
      _ when List.mem_assoc (full_name pn n,List.map (fun n-> full_name pn n) n') map -> Some (List.assoc (full_name pn n,List.map (fun n-> full_name pn n) n') map)
    | _ when List.mem_assoc (n,n') map-> Some (List.assoc (n,n') map)
    | Import(l,p,None)::rest when List.mem_assoc (full_name p n,List.map (fun n-> full_name p n) n') map->  Some (List.assoc (full_name p n,List.map (fun n-> full_name p n) n') map)
    | Import(l,p,Some n2)::rest when n=n2 && List.mem_assoc (full_name p n,List.map (fun n-> full_name p n) n') map-> Some (List.assoc (full_name p n,List.map (fun n-> full_name p n) n') map) 
    | _::rest -> try_assoc_pair' (pn,rest) (n,n') map
    | [] -> None

  let try_assoc2' (pn,imports)x xys1 xys2 =
    match try_assoc' (pn,imports) x xys1 with
      None -> try_assoc' (pn,imports) x xys2
    | result -> result
  
  let rec search name (pn,imports) map=
    match imports with
      _ when List.mem_assoc (full_name pn name) map -> true
    | _ when List.mem_assoc name map -> true
    | Import(l,p,None)::_ when List.mem_assoc (full_name p name) map-> true
    | Import(l,p,Some name')::rest when name=name' && List.mem_assoc (full_name p name) map-> true
    | _::rest -> search name (pn,rest) map
    | []->  false
  
  let rec search' name (pn,imports) map=
    match imports with
      _ when List.mem_assoc name map-> Some name
    | _ when List.mem_assoc (full_name pn name) map -> Some (full_name pn name)
    | Import(l,p,None)::_ when List.mem_assoc (full_name p name) map-> Some (full_name p name)
    | Import(l,p,Some name')::rest when name=name' && List.mem_assoc (full_name p name) map ->Some (full_name p name)
    | _::rest -> search' name (pn,rest) map
    | [] -> None
  
  let resolve (pn, imports) l name map =
    match try_assoc0 name map with
      Some xy as result -> result
    | None ->
      if String.contains name '.' then
        None
      else
        match if pn = "" then None else try_assoc0 (pn ^ "." ^ name) map with
          Some xy as result -> result
        | None ->
          let matches =
            flatmap
              begin function
                Import (l, p, None) ->
                begin match try_assoc0 (p ^ "." ^ name) map with None -> [] | Some xy -> [xy] end
              | Import (l, p, Some name') when name = name' ->
                begin match try_assoc0 (p ^ "." ^ name) map with None -> [] | Some xy -> [xy] end
              | _ -> []
              end
              imports
          in
          match matches with
            [] -> None
          | [xy] -> Some xy
          | _ ->
            let fqns = List.map (fun (x, y) -> "'" ^ x ^ "'") matches in
            static_error l ("Ambiguous imports for name '" ^ name ^ "': " ^ String.concat ", " fqns ^ ".") None
  
  let search2' x (pn,imports) xys1 xys2 =
    match search' x (pn,imports) xys1 with
      None -> search' x (pn,imports) xys2
    | result -> result
  
  (* Region: interfdeclmap, classmap1 *)
  
  let (interfmap1,classmap1)=
    let rec iter (pn,il) ifdm classlist ds =
      match ds with
        [] -> (ifdm, classlist)
      | (Interface (l, i, interfs, fields, meths, pred_specs))::ds -> let i= full_name pn i in 
        if List.mem_assoc i ifdm then
          static_error l ("There exists already an interface with this name: "^i) None
        else
        if List.mem_assoc i classlist then
          static_error l ("There exists already a class with this name: "^i) None
        else
          let interfs =
            let rec check_interfs ls=
                match ls with
                  [] -> []
                | i::ls -> match search2' i (pn,il) ifdm interfmap0 with 
                            Some i -> i::check_interfs ls
                          | None -> static_error l ("Interface wasn't found: " ^ i) None
            in
            check_interfs interfs
          in
          iter (pn, il) ((i, (l, fields, meths, pred_specs, interfs, pn, il))::ifdm) classlist ds
      | (Class (l, abstract, fin, i, meths,fields,constr,super,interfs,preds))::ds -> 
        let i= full_name pn i in
        if List.mem_assoc i ifdm then
          static_error l ("There exists already an interface with this name: "^i) None
        else
        if List.mem_assoc i classlist then
          static_error l ("There exists already a class with this name: "^i) None
        else
          let interfs =
            let rec check_interfs ls=
                match ls with
                  [] -> []
                | i::ls -> match search2' i (pn,il) ifdm interfmap0 with 
                            Some i -> i::check_interfs ls
                          | None -> static_error l ("Interface wasn't found: "^i) None
            in
            check_interfs interfs
          in
          let super =
            if i = "java.lang.Object" then "" else
            match search2' super (pn,il) classlist classmap0 with
              None-> static_error l ("Superclass wasn't found: "^super) None
            | Some super -> super
          in
          iter (pn,il) ifdm ((i, (l,abstract,fin,meths,fields,constr,super,interfs,preds,pn,il))::classlist) ds
      | _::ds -> iter (pn,il) ifdm classlist ds
    in
    let rec iter' (ifdm,classlist) ps =
      match ps with

      PackageDecl(l,pn,ilist,ds)::rest -> iter' (iter (pn,ilist) ifdm classlist ds) rest
      | [] -> (List.rev ifdm, List.rev classlist)
    in
    iter' ([],[]) ps
  
  let inductive_arities =
    List.map (fun (i, (l, tparams, _)) -> (i, (l, List.length tparams))) inductivedeclmap
    @ List.map (fun (i, (l, tparams, _, _)) -> (i, (l, List.length tparams))) inductivemap0
  
  (* Region: check_pure_type: checks validity of type expressions *)
  
  let check_pure_type_core typedefmap1 (pn,ilist) tpenv te =
    let rec check te =
    match te with
      ManifestTypeExpr (l, t) -> t
    | ArrayTypeExpr (l, t) -> 
        let tp = check t in
        ArrayType(tp)
    | StaticArrayTypeExpr (l, t, s) ->
        let tp = check t in
        StaticArrayType(tp, s)
    | IdentTypeExpr (l, None, id) ->
      if List.mem id tpenv then
        TypeParam id
      else
      begin
      match try_assoc2 id typedefmap0 typedefmap1 with
        Some t -> t
      | None ->
      match resolve (pn,ilist) l id inductive_arities with
        Some (s, (ld, n)) ->
        if n > 0 then static_error l "Missing type arguments." None;
        reportUseSite DeclKind_InductiveType ld l;
        InductiveType (s, [])
      | None ->
        match (search2' id (pn,ilist) classmap1 classmap0) with
          Some s -> ObjType s
        | None -> match (search2' id (pn,ilist) interfmap1 interfmap0) with
                    Some s->ObjType s
                  | None ->
                    if List.mem_assoc id functypenames || List.mem_assoc id functypemap0 then
                      FuncType id
                    else
                      static_error l ("No such type parameter, inductive datatype, class, interface, or function type: " ^pn^" "^id) None
      end
    | IdentTypeExpr (l, Some(pac), id) ->
      let full_name = pac ^ "." ^ id in
      begin match (search2' full_name (pn,ilist) classmap1 classmap0) with
          Some s -> ObjType s
        | None -> match (search2' full_name (pn,ilist) interfmap1 interfmap0) with
                    Some s->ObjType s
                  | None -> static_error l ("No such type parameter, inductive datatype, class, interface, or function type: " ^ full_name) None
      end
    | ConstructedTypeExpr (l, id, targs) ->
      begin
      match resolve (pn,ilist) l id inductive_arities with
        Some (id, (ld, n)) ->
        if n <> List.length targs then static_error l "Incorrect number of type arguments." None;
        reportUseSite DeclKind_InductiveType ld l;
        InductiveType (id, List.map check targs)
      | None -> static_error l "No such inductive datatype." None
      end
    | StructTypeExpr (l, sn) ->
      if not (List.mem_assoc sn structmap0 || List.mem_assoc sn structdeclmap) then
        static_error l "No such struct." None
      else
        StructType sn
    | PtrTypeExpr (l, te) -> PtrType (check te)
    | PredTypeExpr (l, tes, inputParamCount) -> PredType ([], List.map check tes, inputParamCount)
    | PureFuncTypeExpr (l, tes) ->
      let ts = List.map check tes in
      let rec iter ts =
        match ts with
          [t1; t2] -> PureFuncType (t1, t2)
        | t1::ts -> PureFuncType (t1, iter ts)
        | _ -> static_error l "A fixpoint function type requires at least two types: a domain type and a range type" None
      in
      iter ts
    in
    check te
  
  let typedefmap1 =
    let rec iter tdm1 tdds =
      match tdds with
        [] -> tdm1
      | (d, (l, te))::tdds ->
        let t = check_pure_type_core tdm1 ("",[]) [] te in
        iter ((d,t)::tdm1) tdds
    in
    iter [] typedefdeclmap
  
  let typedefmap = typedefmap1 @ typedefmap0
  
  let check_pure_type (pn,ilist) tpenv te = check_pure_type_core typedefmap (pn,ilist) tpenv te
  
  let classmap1 =
    List.map
      begin fun (sn, (l,abstract,fin,meths,fds,constr,super,interfs,preds,pn,ilist)) ->
        let rec iter fmap fds =
          match fds with
            [] -> (sn, (l,abstract,fin,meths, List.rev fmap,constr,super,interfs,preds,pn,ilist))
          | Field (fl, fgh, t, f, fbinding, fvis, ffinal, finit)::fds ->
            if List.mem_assoc f fmap then static_error fl "Duplicate field name." None;
            iter ((f, {fl; fgh; ft=check_pure_type (pn,ilist) [] t; fvis; fbinding; ffinal; finit; fvalue=ref None})::fmap) fds
        in
        iter [] fds
      end
      classmap1
  
  let rec instantiate_type tpenv t =
    if tpenv = [] then t else
    match t with
      TypeParam x -> List.assoc x tpenv
    | PtrType t -> PtrType (instantiate_type tpenv t)
    | InductiveType (i, targs) -> InductiveType (i, List.map (instantiate_type tpenv) targs)
    | PredType ([], pts, inputParamCount) -> PredType ([], List.map (instantiate_type tpenv) pts, inputParamCount)
    | PureFuncType (t1, t2) -> PureFuncType (instantiate_type tpenv t1, instantiate_type tpenv t2)
    | InferredType t ->
      begin match !t with
        None -> assert false
      | Some t -> instantiate_type tpenv t
      end
    | ArrayType t -> ArrayType (instantiate_type tpenv t)
    | _ -> t
  
  let instantiate_types tpenv ts =
    if tpenv = [] then ts else List.map (instantiate_type tpenv) ts
  
  let terms_of xys =
    xys |> List.map begin fun (x, _) ->
      let t = ctxt#mk_app (mk_symbol x [] ctxt#type_int Uninterp) [] in
      let serialNumber = !class_counter in
      class_counter := !class_counter + 1;
      ignore (ctxt#assume (ctxt#mk_eq (ctxt#mk_app class_serial_number [t]) (ctxt#mk_intlit serialNumber)));
      (x, t)
    end
  let classterms1 =  terms_of classmap1
  let interfaceterms1 = terms_of interfmap1

  let classterms = classterms1 @ classterms0
  let interfaceterms = interfaceterms1 @ interfaceterms0
  
  (* Region: structmap1 *)
  
  let structmap1 =
    List.map
      (fun (sn, (l, fds_opt)) ->
         let rec iter fmap fds has_ghost_fields =
           match fds with
             [] ->
             (sn,
              (l,
               Some (List.rev fmap),
               if has_ghost_fields then
                 None
               else
                 Some (get_unique_var_symb ("struct_" ^ sn ^ "_padding") (PredType ([], [PtrType (StructType sn)], Some 1)))
              )
             )
           | Field (lf, gh, t, f, Instance, Public, final, init)::fds ->
             if List.mem_assoc f fmap then
               static_error lf "Duplicate field name." None
             else
               iter ((f, (lf, gh, check_pure_type ("", []) [] t))::fmap) fds (has_ghost_fields || gh = Ghost)
         in
         begin
           match fds_opt with
             Some fds -> iter [] fds false
           | None -> (sn, (l, None, None))
         end
      )
      structdeclmap
   
  let structmap = structmap1 @ structmap0
  
  let enummap = enummap1 @ enummap0
  
  let isfuncs = if file_type path=Java then [] else
    flatmap (fun (ftn, (_, gh, tparams, ftps)) ->
      match (gh, tparams, ftps) with
        (Real, [], []) ->
        let isfuncname = "is_" ^ ftn in
        let domain = [ProverInt] in
        let symb = mk_func_symbol isfuncname domain ProverBool Uninterp in
        [(isfuncname, (dummy_loc, [], Bool, [PtrType Void], symb))]
      | _ -> []
    ) functypenames
  
  let rec is_subtype_of x y =
    x = y ||
    y = "java.lang.Object" ||
    match try_assoc x classmap1 with
      Some (_, _, _, _, _, _, super, interfaces, _, _, _) ->
      is_subtype_of super y || List.exists (fun itf -> is_subtype_of itf y) interfaces
    | None ->
      match try_assoc x classmap0 with
        Some {csuper=super; cinterfs=interfaces} ->
        is_subtype_of super y || List.exists (fun itf -> is_subtype_of itf y) interfaces
      | None -> begin match try_assoc x interfmap1 with
          Some (_, _, _, _, interfaces, _, _) -> List.exists (fun itf -> is_subtype_of itf y) interfaces
        | None -> begin match try_assoc x interfmap0 with
            Some (InterfaceInfo (_, _, _, _, interfaces)) -> List.exists (fun itf -> is_subtype_of itf y) interfaces
          | None -> false 
          end
        end
  
  let is_subtype_of_ x y =
    match (x, y) with
      (ObjType x, ObjType y) -> is_subtype_of x y
    | _ -> false
  
  let is_unchecked_exception_type tp = 
    match tp with
     ObjType cn -> (is_subtype_of cn "java.lang.RuntimeException") || (is_subtype_of cn "java.lang.Error")
    | _ -> false

  (* Region: globaldeclmap *)
  
  let globaldeclmap =
    let rec iter gdm ds =
      match ds with
        [] -> gdm
      | Global(l, te, x, init) :: ds -> (* typecheck the rhs *)
        begin
          match try_assoc x globalmap0 with
            Some(_) -> static_error l "Duplicate global variable name." None
          | None -> ()
        end;
        begin
          match try_assoc x gdm with
            Some (_) -> static_error l "Duplicate global variable name." None
          | None -> 
            let tp = check_pure_type ("",[]) [] te in
            let global_symb = get_unique_var_symb x (PtrType tp) in
            iter ((x, (l, tp, global_symb, ref init)) :: gdm) ds
        end
      | _::ds -> iter gdm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [] ds
    | _ when file_type path=Java -> []

  let globalmap1 = globaldeclmap
  let globalmap = globalmap1 @ globalmap0
 

  (* Region: modulemap *)

  let modulemap1 = 
    let rec iter mm ds = 
      match ds with
        [] -> List.rev mm
      | RequireModuleDecl(l, name)::ds ->
        begin
          match try_assoc name mm with
          | Some(_) -> iter mm ds (* Ignore duplicate module requirement *)
          | None -> let module_term = get_unique_var_symb name IntType in
                    iter ((name, module_term) :: mm) ds
        end
      | _ :: ds -> iter mm ds
    in
    match ps with
      [PackageDecl(_,"",[],ds)] -> iter [(current_module_name, current_module_term)] ds
    | _ when file_type path=Java -> []

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
    | _ when file_type path=Java -> []

  let importmodulemap = importmodulemap1 @ importmodulemap0

  (* Region: type compatibility checker *)
  
  let rec compatible_pointees t t0 =
    match (t, t0) with
      (_, Void) -> true
    | (Void, _) -> true
    | (PtrType t, PtrType t0) -> compatible_pointees t t0
    | _ -> t = t0
  
  let rec unfold_inferred_type t =
    match t with
      InferredType t' ->
      begin
        match !t' with
          None -> t
        | Some t -> unfold_inferred_type t
      end
    | _ -> t
  
  let rec unify t1 t2 =
    t1 == t2 ||
    match (unfold_inferred_type t1, unfold_inferred_type t2) with
      (InferredType t', InferredType t0') -> if t' == t0' then true else begin t0' := Some t1; true end
    | (t, InferredType t0) -> t0 := Some t; true
    | (InferredType t, t0) -> t := Some t0; true
    | (InductiveType (i1, args1), InductiveType (i2, args2)) ->
      i1=i2 && List.for_all2 unify args1 args2
    | (ArrayType t1, ArrayType t2) -> unify t1 t2
    | (PtrType t1, PtrType t2) -> compatible_pointees t1 t2
    | (t1, t2) -> t1 = t2
  
  let rec expect_type_core l msg t t0 =
    match (unfold_inferred_type t, unfold_inferred_type t0) with
      (ObjType "null", ObjType _) -> ()
    | (ObjType "null", ArrayType _) -> ()
    | (ArrayType _, ObjType "java.lang.Object") -> ()
    | (StaticArrayType _, PtrType _) -> ()
    | (UChar, IntType) -> ()
    | (UChar, ShortType) -> ()
    | (UChar, UShortType) -> ()
    | (UChar, UintPtrType) -> ()
    | (Char, IntType) -> ()
    | (Char, ShortType) -> ()
    | (UShortType, IntType) -> ()
    | (UShortType, UintPtrType) -> ()
    | (ShortType, IntType) -> ()
    | (ObjType x, ObjType y) when is_subtype_of x y -> ()
    | (PredType ([], ts, inputParamCount), PredType ([], ts0, inputParamCount0)) ->
      begin
        match zip ts ts0 with
          Some tpairs when List.for_all (fun (t, t0) -> unify t t0) tpairs && (inputParamCount0 = None || inputParamCount = inputParamCount0) -> ()
        | _ -> static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".") None
      end
    | (PureFuncType (t1, t2), PureFuncType (t10, t20)) -> expect_type_core l msg t10 t1; expect_type_core l msg t2 t20
    | (InductiveType _, AnyType) -> ()
    | (InductiveType (i1, args1), InductiveType (i2, args2)) when i1 = i2 ->
      List.iter2 (expect_type_core l msg) args1 args2
    | _ -> if unify t t0 then () else static_error l (msg ^ "Type mismatch. Actual: " ^ string_of_type t ^ ". Expected: " ^ string_of_type t0 ^ ".") None
  
  let expect_type l t t0 = expect_type_core l "" t t0
  
  let is_assignable_to t t0 =
    try expect_type dummy_loc t t0; true with StaticError (l, msg, url) -> false (* TODO: Consider eliminating this hack *)
  
  let is_assignable_to_sign sign sign0 = for_all2 is_assignable_to sign sign0
  
  let convert_provertype_expr e proverType proverType0 =
    if proverType = proverType0 then e else ProverTypeConversion (proverType, proverType0, e)
  
  let box e t t0 =
    match unfold_inferred_type t0 with TypeParam _ -> convert_provertype_expr e (provertype_of_type t) ProverInductive | _ -> e
  
  let unbox e t0 t =
    match unfold_inferred_type t0 with TypeParam _ -> convert_provertype_expr e ProverInductive (provertype_of_type t) | _ -> e
  
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
  
  let (inductivemap1, purefuncmap1, fixpointmap1) =
    let rec iter (pn,ilist) imap pfm fpm ds =
      match ds with
        [] -> (imap, pfm, fpm)
      | Inductive (l, i, tparams, ctors)::ds -> let i=full_name pn i in
        check_tparams l [] tparams;
        let rec citer j ctormap pfm ctors =
          match ctors with
            [] -> iter (pn,ilist) ((i, (l, tparams, List.rev ctormap))::imap) pfm fpm ds
          | Ctor (lc, cn, tes)::ctors ->
            let full_cn = full_name pn cn in
            if List.mem_assoc full_cn pfm || List.mem_assoc full_cn purefuncmap0 then
              static_error lc ("Duplicate pure function name: " ^ full_cn) None
            else (
              let ts = List.map (check_pure_type (pn,ilist) tparams) tes in
              let csym =
                mk_func_symbol full_cn (List.map provertype_of_type ts) ProverInductive (Proverapi.Ctor (CtorByOrdinal j))
              in
              let purefunc = (full_cn, (lc, tparams, InductiveType (i, List.map (fun x -> TypeParam x) tparams), ts, csym)) in
              citer (j + 1) ((cn, purefunc)::ctormap) (purefunc::pfm) ctors
            )
        in
        citer 0 [] pfm ctors
      | Func (l, Fixpoint, tparams, rto, g, ps, nonghost_callers_only, functype, contract, body_opt,Static,Public)::ds ->
        let g = full_name pn g in
        if List.mem_assoc g pfm || List.mem_assoc g purefuncmap0 then static_error l ("Duplicate pure function name: "^g) None;
        check_tparams l [] tparams;
        let rt =
          match rto with
            None -> static_error l "Return type of fixpoint functions cannot be void." None
          | Some rt -> (check_pure_type (pn,ilist) tparams rt)
        in
        if nonghost_callers_only then static_error l "A fixpoint function cannot be marked nonghost_callers_only." None;
        if functype <> None then static_error l "Fixpoint functions cannot implement a function type." None;
        if contract <> None then static_error l "Fixpoint functions cannot have a contract." None;
        let pmap =
          let rec iter pmap ps =
            match ps with
              [] -> List.rev pmap
            | (te, p)::ps ->
              let _ = if List.mem_assoc p pmap then static_error l "Duplicate parameter name." None in
              let t = check_pure_type (pn,ilist) tparams te in
              iter ((p, t)::pmap) ps
          in
          iter [] ps
        in
        begin match body_opt with
          Some ([SwitchStmt (ls, e, cs) as body], _) ->
          let index = 
            match e with
              Var (lx, x, _) ->
              begin match try_assoc_i x pmap with
                None -> static_error lx "Fixpoint function must switch on a parameter." None
              | Some (index, _) -> index
              end
            | _ -> static_error l "Fixpoint function must switch on a parameter." None
          in
          let fsym = mk_func_symbol g (List.map (fun (p, t) -> provertype_of_type t) pmap) (provertype_of_type rt) (Proverapi.Fixpoint index) in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) ((g, (l, tparams, rt, pmap, Some index, body, pn, ilist, fst fsym))::fpm) ds
        | Some ([ReturnStmt (lr, Some e) as body], _) ->
          let fsym = mk_func_symbol g (List.map (fun (p, t) -> provertype_of_type t) pmap) (provertype_of_type rt) Proverapi.Uninterp in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) ((g, (l, tparams, rt, pmap, None, body, pn, ilist, fst fsym))::fpm) ds
        | None ->
          let fsym = mk_func_symbol g (List.map (fun (p, t) -> provertype_of_type t) pmap) (provertype_of_type rt) Proverapi.Uninterp in
          iter (pn,ilist) imap ((g, (l, tparams, rt, List.map (fun (p, t) -> t) pmap, fsym))::pfm) fpm ds
        | _ -> static_error l "Body of fixpoint function must be switch statement or return statement." None
        end
      | _::ds -> iter (pn,ilist) imap pfm fpm ds
    in
    let rec iter' (imap,pfm,fpm) ps=
      match ps with
      PackageDecl(l,pn,il,ds)::rest -> iter' (iter (pn,il) imap pfm fpm ds) rest
      | [] -> (List.rev imap, List.rev pfm, List.rev fpm)
    in
    iter' ([],isfuncs,[]) ps
  
  let () =
    let welldefined_map = List.map (fun (i, info) -> let ec = ref (`EqClass (0, [])) in let ptr = ref ec in ec := `EqClass (0, [ptr]); (i, (info, ptr))) inductivemap1 in
    let merge_ecs ec0 ec1 =
      let `EqClass (ecrank0, ecmems0) = !ec0 in
      let `EqClass (ecrank1, ecmems1) = !ec1 in
      if ecrank0 <> ecrank1 then begin
        assert (ecrank0 < ecrank1);
        List.iter (fun ptr -> ptr := ec0) ecmems1;
        ec0 := `EqClass (ecrank0, ecmems1 @ ecmems0)
      end
    in
    let rec check_welldefined rank negative_rank pred_ptrs (i, ((l, _, ctors), ptr)) =
      (* Invariant:
         - All nodes reachable from a -1 node are -1
         - There are no cycles through -1 nodes that go through a negative occurrence.
         - The ranks of all nodes are less than the current rank [rank]
         - There are no cycles that go through a negative occurrence in the subgraph that is to the left of the current path.
         - All nodes reachable from a given node in the subgraph that is to the left of the current path, have either the same rank, a higher rank, or rank -1, but never rank 0
         - For any two nodes in the subgraph that is to the left of the current path, they are mutually reachable iff they are in the same equivalence class (and consequently have the same rank)
         - The ranks of the nodes on the current path are always (non-strictly) increasing
       *)
      let pred_ptrs = ptr::pred_ptrs in
      let ec = !ptr in
      let `EqClass (ecrank, ecmems) = !ec in
      if ecrank = -1 then
        ()
      else
      begin
        assert (ecrank = 0 && match ecmems with [ptr'] when ptr' == ptr -> true | _ -> false);
        ec := `EqClass (rank, ecmems);
        let rec check_ctor (ctorname, (_, (_, _, _, pts, _))) =
          let rec check_type negative pt =
            match pt with
            | Bool | Void | IntType | UShortType | ShortType | UintPtrType | RealType | UChar | Char | PtrType _ | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> ()
            | TypeParam _ -> if negative then static_error l "A type parameter may not appear in a negative position in an inductive datatype definition." None
            | InductiveType (i0, tps) ->
              List.iter (fun t -> check_type negative t) tps;
              begin match try_assoc i0 welldefined_map with
                None -> ()
              | Some (info0, ptr0) ->
                let ec0 = !ptr0 in
                let `EqClass (ecrank0, ecmems0) = !ec0 in
                let negative_rank = if negative then rank else negative_rank in
                if ecrank0 > 0 then begin
                  if ecrank0 <= negative_rank then static_error l "This inductive datatype is not well-defined; it occurs recursively in a negative position." None;
                  let rec merge_preds pred_ptrs =
                    match pred_ptrs with
                      [] -> ()
                    | ptr1::pred_ptrs ->
                      let ec1 = !ptr1 in
                      let `EqClass (ecrank1, ecmems1) = !ec1 in
                      if ecrank0 < ecrank1 then begin
                        merge_ecs ec0 ec1;
                        merge_preds pred_ptrs
                      end
                  in
                  merge_preds pred_ptrs
                end else
                  check_welldefined (rank + 1) negative_rank pred_ptrs (i0, (info0, ptr0))
              end
            | PredType (tps, pts, _) ->
              assert (tps = []);
              List.iter (fun t -> check_type true t) pts
            | PureFuncType (t1, t2) ->
              check_type true t1; check_type negative t2
            | t -> static_error l (Printf.sprintf "Type '%s' is not supported as an inductive constructor parameter type." (string_of_type t)) None
          in
          List.iter (check_type false) pts
        in
        List.iter check_ctor ctors;
        (* If this node is the leader of an equivalence class, then this equivalence class has now been proven to be well-defined. *)
        let ec = !ptr in
        let `EqClass (ecrank, ecmems) = !ec in
        if ecrank = rank then
          ec := `EqClass (-1, ecmems)
      end
    in
    List.iter (check_welldefined 1 0 []) welldefined_map
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
            let rec type_is_inhabited tp =
              match tp with
                Bool | IntType | ShortType | UintPtrType | RealType | Char | PtrType _ | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> true
              | TypeParam _ -> true  (* Should be checked at instantiation site. *)
              | PredType (tps, pts, _) -> true
              | PureFuncType (t1, t2) -> type_is_inhabited t2
              | InductiveType (i0, tps) ->
                List.for_all type_is_inhabited tps &&
                begin match try_assoc i0 inhabited_map with
                  None -> true
                | Some ((l0, _, ctors0), status0) ->
                  !status0 <> 1 &&
                  (check_inhabited i0 l0 ctors0 status0; true)
                end
            in
            if List.for_all type_is_inhabited pts then () else find_ctor ctors
        in
        find_ctor ctors;
        status := 2
      end
    in
    List.iter (fun (i, ((l, _, ctors), status)) -> check_inhabited i l ctors status) inhabited_map
  
  let inductivemap1 =
    let infinite_map = List.map (fun (i, info) -> let status = ref (0, []) in (i, (info, status))) inductivemap1 in
    (* Status: (n, tparams) with n: 0 = not visited; 1 = currently visiting; 2 = infinite if one of tparams is infinite; 3 = unconditionally infinite *)
    (* Infinite = has infinitely many values *)
    let rec determine_type_is_infinite (i, ((l, tparams, ctors), status)) =
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
            | TypeParam x -> Some [x]
            | IntType | ShortType | UintPtrType | RealType | Char | PtrType _ | PredType (_, _, _) | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> None
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
                  let (_, tparams, _) = info0 in
                  let Some tpenv = zip tparams targs in
                  fold_cond [] (fun x -> type_is_infinite (List.assoc x tpenv)) cond
                end
              | None ->
                let (_, tparams, _, cond) = List.assoc i0 inductivemap0 in
                begin match cond with
                  None -> None
                | Some cond ->
                  let Some tpenv = zip tparams targs in
                  fold_cond [] (fun x -> type_is_infinite (List.assoc x tpenv)) cond
                end
              end
          in
          fold_cond [] type_is_infinite pts
        in
        match fold_cond [] ctor_is_infinite ctors with
          None -> status := (3, [])
        | Some cond -> status := (2, cond)
      end
    in
    List.iter determine_type_is_infinite infinite_map;
    infinite_map |> List.map
      begin fun (i, ((l, tparams, ctors), status)) ->
        let (n, cond) = !status in
        let cond = if n = 2 then Some cond else None in
        (i, (l, tparams, ctors, cond))
      end
  
  let inductivemap = inductivemap1 @ inductivemap0
  
  (* A universal type is one that is isomorphic to the universe for purposes of type erasure *)
  let rec is_universal_type tp =
    match tp with
      Bool -> false
    | TypeParam x -> true
    | IntType | ShortType | UintPtrType | RealType | Char | PtrType _ | PredType (_, _, _) | ObjType _ | ArrayType _ | BoxIdType | HandleIdType | AnyType -> true
    | PureFuncType (t1, t2) -> is_universal_type t1 && is_universal_type t2
    | InductiveType (i0, targs) ->
      let (_, _, _, cond) = List.assoc i0 inductivemap in
      cond <> Some [] && List.for_all is_universal_type targs
  
  let functypedeclmap1 =
    let rec iter (pn,ilist) functypedeclmap1 ds =
      match ds with
        [] -> functypedeclmap1
      | FuncTypeDecl (l, gh, rt, ftn, tparams, ftxs, xs, (pre, post))::ds ->
        let ftn0 = ftn in
        let ftn = full_name pn ftn in
        if gh = Real && tparams <> [] then static_error l "Declaring type parameters on non-lemma function types is not supported." None;
        let _ = if List.mem_assoc ftn functypedeclmap1 || List.mem_assoc ftn functypemap0 then static_error l "Duplicate function type name." None in
        let rec check_tparams_distinct tparams =
          match tparams with
            [] -> ()
          | x::xs ->
            if List.mem x xs then static_error l "Duplicate type parameter" None;
            check_tparams_distinct xs
        in
        check_tparams_distinct tparams;
        (* The return type cannot mention type parameters. *)
        let rt = match rt with None -> None | Some rt -> Some (check_pure_type (pn,ilist) [] rt) in
        let ftxmap =
          let rec iter xm xs =
            match xs with
              [] -> List.rev xm
            | (te, x)::xs ->
              if List.mem_assoc x xm then static_error l "Duplicate function type parameter name." None;
              let t = check_pure_type (pn,ilist) tparams te in
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
              let t = check_pure_type (pn,ilist) tparams te in
              iter ((x, t)::xm) xs
          in
          iter [] xs
        in
        iter (pn,ilist) ((ftn, (l, gh, tparams, rt, ftxmap, xmap, ftn0, pn, ilist, pre, post))::functypedeclmap1) ds
      | _::ds -> iter (pn,ilist) functypedeclmap1 ds
    in
    let rec iter' functypedeclmap1 ps =
      match ps with
        [] -> List.rev functypedeclmap1
      | PackageDecl (_, pn, ilist, ds)::ps -> iter' (iter (pn,ilist) functypedeclmap1 ds) ps
    in
    iter' [] ps
  
  (* Region: predicate families *)
  
  let mk_predfam p l tparams arity ts inputParamCount = (p, (l, tparams, arity, ts, get_unique_var_symb p (PredType (tparams, ts, inputParamCount)), inputParamCount))

  let struct_padding_predfams1 =
    flatmap
      (function
         (sn, (l, fds, Some padding_predsymb)) -> [("struct_" ^ sn ^ "_padding", (l, [], 0, [PtrType (StructType sn)], padding_predsymb, Some 1))]
       | _ -> [])
      structmap1
  
  let functypedeclmap1 =
    List.map
      begin fun (g, (l, gh, tparams, rt, ftxmap, xmap, g0, pn, ilist, pre, post)) ->
        let predfammaps =
          if gh = Ghost || ftxmap <> [] then
            let paramtypes = [PtrType (FuncType g)] @ List.map snd ftxmap in
            [mk_predfam (full_name pn ("is_" ^ g0)) l tparams 0 paramtypes (Some (List.length paramtypes))]
          else
            []
        in
        (g, (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, predfammaps))
      end
      functypedeclmap1
  
  let isparamizedfunctypepreds1 = flatmap (fun (g, (l, gh, tparams, rt, ftxmap, xmap, pn, ilist, pre, post, predfammaps)) -> predfammaps) functypedeclmap1
  
  let malloc_block_pred_map1 = 
    structmap1 |> flatmap begin function
      (sn, (l, Some _, _)) -> [(sn, mk_predfam ("malloc_block_" ^ sn) l [] 0 [PtrType (StructType sn)] (Some 1))]
    | _ -> []
    end
  
  let malloc_block_pred_map = malloc_block_pred_map1 @ malloc_block_pred_map0

  let field_pred_map1 = (* dient om dingen te controleren bij read/write controle v velden*)
    match file_type path with
      Java ->
      classmap1 |> flatmap begin fun (cn, (_,_,_,_, fds,_,_,_,_,_,_)) ->
        fds |> List.map begin fun (fn, {fl; ft; fbinding}) ->
          let predfam =
            match fbinding with
              Static -> mk_predfam (cn ^ "_" ^ fn) fl [] 0 [ft] (Some 0)
            | Instance -> mk_predfam (cn ^ "_" ^ fn) fl [] 0 [ObjType cn; ft] (Some 1)
          in
          ((cn, fn), predfam)
        end
      end
    | _ ->
    flatmap
      (fun (sn, (_, fds_opt, _)) ->
         match fds_opt with
           None -> []
         | Some fds ->
           List.map
             (fun (fn, (l, gh, t)) ->
              ((sn, fn), mk_predfam (sn ^ "_" ^ fn) l [] 0 [PtrType (StructType sn); t] (Some 1))
             )
             fds
      )
      structmap1
  
  let field_pred_map = field_pred_map1 @ field_pred_map0
  
  let structpreds1 = List.map (fun (_, p) -> p) malloc_block_pred_map1 @ List.map (fun (_, p) -> p) field_pred_map1 @ struct_padding_predfams1
  
  let predfammap1 =
    let rec iter (pn,ilist) pm ds =
      match ds with
        PredFamilyDecl (l, p, tparams, arity, tes, inputParamCount)::ds -> let p=full_name pn p in
        let ts = List.map (check_pure_type (pn,ilist) tparams) tes in
        begin
          match try_assoc2' (pn,ilist) p pm predfammap0 with
            Some (l0, tparams0, arity0, ts0, symb0, inputParamCount0) ->
            let tpenv =
              match zip tparams0 (List.map (fun x -> TypeParam x) tparams) with
                None -> static_error l "Predicate family redeclarations declares a different number of type parameters." None
              | Some bs -> bs
            in
            let ts0' = List.map (instantiate_type tpenv) ts0 in
            if arity <> arity0 || ts <> ts0' || inputParamCount <> inputParamCount0 then
              static_error l ("Predicate family redeclaration does not match original declaration at '" ^ string_of_loc l0 ^ "'.") None;
            iter (pn,ilist) pm ds
          | None ->
            iter (pn,ilist) (mk_predfam p l tparams arity ts inputParamCount::pm) ds
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
              iter ((x, check_pure_type (pn,ilist) [] te)::pmap) ps
          in
          iter [] ps
        in
        let pfm = mk_predfam bcn l [] 0 (BoxIdType::List.map (fun (x, t) -> t) boxpmap) (Some 1)::pfm in
        let pfm = mk_predfam default_hpn l [] 0 (HandleIdType::BoxIdType::[]) (Some 1)::pfm in
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
                    iter ((x, check_pure_type (pn,ilist) [] te)::pmap) ps
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
                  let action_permission_pred = (mk_predfam action_permission_pred_name l [] 0 action_permission_pred_param_types action_permission_pred_inputParamCount) in
                  let  (_, (_, _, _, _, action_permission_pred_symb, _)) = action_permission_pred in
                  let (_, _, _, _, is_action_permissionx_symb) = List.assoc ("is_action_permission" ^ (string_of_int nb_action_parameters)) purefuncmap0 in
                  ignore (ctxt#assume (mk_app is_action_permissionx_symb [action_permission_pred_symb]));
                  if ps = [] then
                    (action_permission_pred :: pfm, Some (action_permission_pred_symb, None))
                  else begin
                    assert (List.length ps = 1);
                    let action_permission_dispenser_pred_name = action_permission_pred_name ^ "_dispenser" in
                    if List.mem_assoc action_permission_dispenser_pred_name pfm || List.mem_assoc action_permission_dispenser_pred_name purefuncmap0 then static_error l "Action permission name clashes with existing predicate name." None;
                    let [(_, action_param_type)] = pmap in 
                    let action_permission_dispenser_pred_param_types = [BoxIdType; InductiveType("list", [action_param_type])] in
                    let action_permission_dispenser_pred_inputParamCount = Some 2 in
                    let action_permission_dispenser_pred = (mk_predfam action_permission_dispenser_pred_name l [] 0 action_permission_dispenser_pred_param_types action_permission_dispenser_pred_inputParamCount) in
                    let  (_, (_, _, _, _, action_permission_dispenser_pred_symb, _)) = action_permission_dispenser_pred in
                    (* assuming is_action_permission1_dispenser(action_permission_dispenser_pred_symb) *)
                    let (_, _, _, _, is_action_permission1_dispenser_symb) = List.assoc "is_action_permission1_dispenser" purefuncmap0 in
                    ignore (ctxt#assume (mk_app is_action_permission1_dispenser_symb [action_permission_dispenser_pred_symb]));
                    (* assuming get_action_permission1_for_dispenser(action_permission_dispenser_pred_symb) = action_permission_pred_symb *)
                    let (_, _, _, _, get_action_permission1_for_dispenser_symb) = List.assoc "get_action_permission1_for_dispenser" purefuncmap0 in
                    ignore (ctxt#assume (ctxt#mk_eq (mk_app get_action_permission1_for_dispenser_symb [action_permission_dispenser_pred_symb]) action_permission_pred_symb));
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
                    iter ((x, check_pure_type (pn,ilist) [] te)::pmap) ps
                in
                iter [] ps
              in
              (match extends with 
                None -> ()
              | Some(ehn) -> 
                if not (List.mem_assoc ehn hpm) then static_error l "Extended handle must appear earlier in same box class." None;
                let (el, epmap, extendedInv, einv, epbcs) = List.assoc ehn hpm in
                (match einv with ExprAsn(_, _) -> () | _ -> static_error l "Extended handle's invariant must be pure assertion." None); 
                if (List.length pmap) < (List.length epmap) then static_error l "Extended handle's parameter list must be prefix of extending handle's parameter list." None;
                if not
                (List.for_all2
                  (fun (name1, tp1) (name2, tp2) -> name1 = name2 && tp1 = tp2)
                  (take (List.length epmap) pmap) epmap) 
                then static_error l "Extended handle's parameter list must be prefix of extending handle's parameter list." None;
              );
              iter (mk_predfam hpn l [] 0 (HandleIdType::BoxIdType::List.map (fun (x, t) -> t) pmap) (Some 1)::pfm) ((hpn, (l, pmap, extends, inv, pbcs))::hpm) hpds
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
  
  let predfammap = predfammap1 @ predfammap0 (* TODO: Check for name clashes here. *)
  
  let interfmap1 =
    let rec iter_interfs interfmap1_done interfmap1_todo =
      match interfmap1_todo with
        [] -> List.rev interfmap1_done
      | (tn, (li, fields, methods, preds, interfs, pn, ilist))::interfmap1_todo ->
        let rec iter_preds predmap preds =
          match preds with
            [] -> iter_interfs ((tn, (li, fields, methods, List.rev predmap, interfs, pn, ilist))::interfmap1_done) interfmap1_todo
          | InstancePredDecl (l, g, ps, body)::preds ->
            if List.mem_assoc g predmap then static_error l "Duplicate predicate name." None;
            let pmap =
              let rec iter pmap ps =
                match ps with
                  [] -> List.rev pmap
                | (tp, x)::ps ->
                  if List.mem_assoc x pmap then static_error l "Duplicate parameter name." None;
                  let tp = check_pure_type (pn,ilist) [] tp in
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
                    begin match try_assoc g preds with
                      Some (l, pmap, family, symb) -> [(family, pmap, symb)]
                    | None -> flatmap preds_in_itf itfs
                    end
                  | None -> fallback ()
                  end
                in
                check_itfmap (function (li, fields, methods, preds, interfs, pn, ilist) -> (preds, interfs)) interfmap1_done $. fun () ->
                check_itfmap (function InterfaceInfo (li, fields, methods, preds, interfs) -> (preds, interfs)) interfmap0 $. fun () ->
                []
              in
              match flatmap preds_in_itf interfs with
                [] -> (tn, get_unique_var_symb (tn ^ "#" ^ g) (PredType ([], [], None)))
              | [(family, pmap0, symb)] ->
                if not (for_all2 (fun (x, t) (x0, t0) -> expect_type_core l "Predicate parameter covariance check" t t0; true) pmap pmap0) then
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
      | (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist))::classmap1_todo ->
        let cont predmap = iter ((cn, (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, List.rev predmap, pn, ilist))::classmap1_done) classmap1_todo in
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
                  let tp = check_pure_type (pn,ilist) [] tp in
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
                    begin match try_assoc g preds with
                      Some (l, pmap, family, symb) -> [(family, pmap, symb)]
                    | None -> flatmap preds_in_itf itfs
                    end
                  | None -> fallback ()
                  end
                in
                check_itfmap (function (li, fields, methods, preds, interfs, pn, ilist) -> (preds, interfs)) interfmap1 $. fun () ->
                check_itfmap (function InterfaceInfo (li, fields, methods, preds, interfs) -> (preds, interfs)) interfmap0 $. fun () ->
                []
              in
              let rec preds_in_class cn =
                if cn = "" then [] else
                let check_classmap classmap proj fallback =
                  begin match try_assoc cn classmap with
                    Some info ->
                    let (super, interfs, predmap) = proj info in
                    begin match try_assoc g predmap with
                      Some (l, pmap, family, symb, body) -> [(family, pmap, symb)]
                    | None -> preds_in_class super @ flatmap preds_in_itf interfs
                    end
                  | None -> fallback ()
                  end
                in
                check_classmap classmap1_done
                  (function (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, predmap, pn, ilist) -> (super, interfs, predmap))
                  $. fun () ->
                check_classmap classmap0
                  (function {csuper; cinterfs; cpreds} -> (csuper, cinterfs, cpreds))
                  $. fun () ->
                []
              in
              match preds_in_class super @ flatmap preds_in_itf interfs with
                [] -> (cn, get_unique_var_symb (cn ^ "#" ^ g) (PredType ([], [], None)))
              | [(family, pmap0, symb)] ->
                if not (for_all2 (fun (x, t) (x0, t0) -> expect_type_core l "Predicate parameter covariance check" t t0; true) pmap pmap0) then
                  static_error l "Predicate override check: parameter count mismatch" None;
                (family, symb)
              | _ -> static_error l "Ambiguous override: multiple overridden predicates" None
            in
            iter ((g, (l, pmap, family, symb, body))::predmap) preds
        in
        iter [] preds
    in
    iter [] classmap1
  
  let (predctormap1, purefuncmap1) =
    let rec iter (pn,ilist) pcm pfm ds =
      match ds with
        PredCtorDecl (l, p, ps1, ps2, inputParamCount, body)::ds -> let p=full_name pn p in
        begin
          match try_assoc2' (pn,ilist) p pfm purefuncmap0 with
            Some _ -> static_error l "Predicate constructor name clashes with existing pure function name." None
          | None -> ()
        end;
        begin
          match try_assoc' (pn,ilist) p predfammap with
            Some _ -> static_error l "Predicate constructor name clashes with existing predicate or predicate familiy name." None
          | None -> ()
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
              let t = check_pure_type (pn,ilist) [] te in
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
              let t = check_pure_type (pn,ilist) [] te in
              iter ((x, t)::psmap) ((x, t)::pmap) ps
          in
          iter ps1 [] ps2
        in
        let funcsym = mk_func_symbol p (List.map (fun (x, t) -> provertype_of_type t) ps1) ProverInductive Proverapi.Uninterp in
        let pf = (p, (l, [], PredType ([], List.map (fun (x, t) -> t) ps2, inputParamCount), List.map (fun (x, t) -> t) ps1, funcsym)) in
        iter (pn,ilist) ((p, (l, ps1, ps2, inputParamCount, body, funcsym, pn, ilist))::pcm) (pf::pfm) ds
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
              (Func (l, (Regular|Lemma(_)), tparams, rt, g, ps, nonghost_callers_only, ft, c, b,Static,_)) -> [full_name pn g]
            | _ -> []
            end
            ds
        end
        ps
      end
  
  let check_classname (pn, ilist) (l, c) =
    match resolve (pn, ilist) l c classmap1 with 
      None -> static_error l "No such class name." None
    | Some (s, _) -> s
  
  let check_classnamelist (pn,ilist) is =
    List.map (check_classname (pn, ilist)) is
  
  let check_funcnamelist is =
    List.map (fun (l, i) -> if not (List.mem i funcnames) then static_error l "No such function name." None; i) is 
  
  let interfmap1 =
    interfmap1 |> List.map begin function (i, (l, fields, meths, preds, supers, pn, ilist)) ->
      let fieldmap =
        fields |> List.map begin function Field (fl, fgh, ft, f, _, _, _, finit) ->
          let ft = check_pure_type (pn,ilist) [] ft in
          (f, {fl; fgh; ft; fvis=Public; fbinding=Static; ffinal=true; finit; fvalue=ref None})
        end
      in
      (i, (l, fieldmap, meths, preds, supers, pn, ilist))
    end
  
  let rec lookup_class_field cn fn =
    match try_assoc cn classmap1 with
      Some (_, _, _, _, fds, _, super, itfs, _, _, _) ->
      begin match try_assoc fn fds with
        None when cn = "java.lang.Object" -> None
      | Some f -> Some (f, cn)
      | None ->
      match lookup_class_field super fn with
        Some _ as result -> result
      | None ->
      head_flatmap_option (fun cn -> lookup_class_field cn fn) itfs
      end
    | None -> 
    match try_assoc cn classmap0 with
      Some {cfds; csuper; cinterfs} ->
      begin match try_assoc fn cfds with
        None when cn = "java.lang.Object" -> None
      | Some f -> Some (f, cn)
      | None ->
      match lookup_class_field csuper fn with
        Some _ as result -> result
      | None ->
      head_flatmap_option (fun cn -> lookup_class_field cn fn) cinterfs
      end
    | None ->
    match try_assoc cn interfmap1 with
      Some (_, fds, _, _, supers, _, _) ->
      begin match try_assoc fn fds with
        Some f -> Some (f, cn)
      | None ->
      head_flatmap_option (fun cn -> lookup_class_field cn fn) supers
      end
    | None ->
    match try_assoc cn interfmap0 with
      Some (InterfaceInfo (_, fds, _, _, supers)) ->
      begin match try_assoc fn fds with
        Some f -> Some (f, cn)
      | None ->
      head_flatmap_option (fun cn -> lookup_class_field cn fn) supers
      end
    | None ->
    None

  let is_package x =
    let x = x ^ "." in
    let has_package map = List.exists (fun (cn, _) -> startswith cn x) map in
    has_package classmap1 || has_package classmap0 || has_package interfmap1 || has_package interfmap0
  
  let current_class = "#currentClass"
  
  let rec check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e: (expr (* typechecked expression *) * type_ (* expression type *) * big_int option (* constant integer expression => value*)) =
    let check e = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
    let checkt e t0 = check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e t0 false in
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
        check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e t0 true in
    let rec get_methods tn mn =
      if tn = "" then [] else
      match try_assoc tn classmap with
        Some {cmeths; csuper; cinterfs} ->
        let inherited_methods =
          get_methods csuper mn @ flatmap (fun ifn -> get_methods ifn mn) cinterfs
        in
        let declared_methods =
          flatmap
            begin fun ((mn', sign), (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, is_override, abstract)) ->
              if mn' = mn then [(sign, (tn, lm, gh, rt, xmap, pre_dyn, post_dyn, epost_dyn, fb, v, abstract))] else []
            end
            cmeths
        in
        declared_methods @ List.filter (fun (sign, info) -> not (List.mem_assoc sign declared_methods)) inherited_methods
      | None ->
      let InterfaceInfo (_, fields, meths, _, interfs) = List.assoc tn interfmap in
      let declared_methods = flatmap
        begin fun ((mn', sign), (lm, gh, rt, xmap, pre, pre_tenv, post, epost, v, abstract)) ->
          if mn' = mn then [(sign, (tn, lm, gh, rt, xmap, pre, post, epost, Instance, v, abstract))] else []
        end
        meths
      in
      let inherited_methods = flatmap (fun ifn -> get_methods ifn mn) interfs in
      declared_methods @ List.filter (fun (sign, info) -> not (List.mem_assoc sign declared_methods)) inherited_methods
    in
    let promote_numeric e1 e2 ts =
      let (w1, t1, _) = check e1 in
      let (w2, t2, _) = check e2 in
      match (unfold_inferred_type t1, unfold_inferred_type t2) with
        (IntType, RealType) ->
        let w1 = checkt e1 RealType in
        ts := Some [RealType; RealType];
        (w1, w2, RealType)
      | (RealType, IntType) ->
        let w2 = checkt e2 RealType in
        ts := Some [RealType; RealType];
        (w1, w2, RealType)
      | ((UChar | UShortType | UintPtrType), (UChar | UShortType | UintPtrType)) ->
        ts := Some [UintPtrType;UintPtrType];
        (w1, w2, UintPtrType)
      | ((Char|ShortType|IntType|UChar|UShortType), (Char|ShortType|IntType|UChar|UShortType)) ->
        ts := Some [IntType; IntType];
        (w1, w2, IntType)
      | (t1, t2) ->
        let w2 = checkt e2 t1 in
        ts := Some [t1; t1];
        (w1, w2, t1)
    in
    let promote l e1 e2 ts =
      match promote_numeric e1 e2 ts with
        (w1, w2, (Char | ShortType | IntType | RealType | UintPtrType | PtrType _ | UShortType | UChar)) as result -> result
      | _ -> static_error l "Expression of type char, short, int, real, or pointer type expected." None
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
    | Null l -> (e, ObjType "null", None)
    | Var (l, x, scope) ->
      begin
      match try_assoc x tenv with
      | Some(RefType(t)) -> scope := Some LocalVar; (Deref(l, e, ref (Some t)), t, None)
      | Some t -> scope := Some LocalVar; (e, t, None)
      | None ->
      begin fun cont ->
      if language <> Java then cont () else
      let field_of_this =
        match try_assoc "this" tenv with
        | Some ObjType cn ->
          begin match lookup_class_field cn x with
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
            Some (WRead (l, Var (l, "this", ref (Some LocalVar)), fclass, x, ft, fbinding = Static, fvalue, fgh), ft, constant_value)
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
          match lookup_class_field cn x with
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
            Some (WRead (l, Var (l, current_class, ref (Some LocalVar)), fclass, x, ft, true, fvalue, fgh), ft, constant_value)
      in
      match field_of_class with
        Some result -> result
      | None ->
      match resolve (pn,ilist) l x classmap1 with
        Some (cn, _) -> (e, ClassOrInterfaceName cn, None)
      | None ->
      match resolve (pn,ilist) l x interfmap1 with
        Some (cn, _) -> (e, ClassOrInterfaceName cn, None)
      | None ->
      match resolve (pn,ilist) l x classmap0 with
        Some (cn, _) -> (e, ClassOrInterfaceName cn, None)
      | None ->
      match resolve (pn,ilist) l x interfmap0 with
        Some (cn, _) -> (e, ClassOrInterfaceName cn, None)
      | None ->
      if is_package x then
        (e, PackageName x, None)
      else
        cont ()
      end $. fun () ->
      match resolve (pn,ilist) l x purefuncmap with
      | Some (x, (_, tparams, t, [], _)) ->
        if tparams <> [] then
        begin
          let targs = List.map (fun _ -> InferredType (ref None)) tparams in
          let Some tpenv = zip tparams targs in
          scope := Some PureCtor;
          (Var (l, x, scope), instantiate_type tpenv t, None)
        end
        else
        begin
          scope := Some PureCtor; (Var (l, x, scope), t, None)
        end
      | _ ->
      if List.mem x funcnames then
        match file_type path with
          Java -> static_error l "In java methods can't be used as pointers" None
        | _ -> scope := Some FuncName; (e, PtrType Void, None)
      else
      match resolve (pn,ilist) l x predfammap with
      | Some (x, (_, tparams, arity, ts, _, inputParamCount)) ->
        if arity <> 0 then static_error l "Using a predicate family as a value is not supported." None;
        if tparams <> [] then static_error l "Using a predicate with type parameters as a value is not supported." None;
        scope := Some PredFamName;
        (Var (l, x, scope), PredType (tparams, ts, inputParamCount), None)
      | None ->
      match try_assoc x enummap with
      | Some i ->
        scope := Some (EnumElemName i);
        (e, IntType, None)
      | None ->
      match try_assoc' (pn, ilist) x globalmap with
      | Some ((l, tp, symbol, init)) -> scope := Some GlobalName; (e, tp, None)
      | None -> 
      match try_assoc x modulemap with
      | Some _ when language <> Java -> scope := Some ModuleName; (e, IntType, None)
      | _ ->
      match resolve (pn,ilist) l x purefuncmap with
        Some (x, (_, tparams, t, pts, _)) ->
        let (pts, t) =
          if tparams = [] then
            (pts, t)
          else
            let tpenv = List.map (fun x -> (x, InferredType (ref None))) tparams in
            (List.map (instantiate_type tpenv) pts, instantiate_type tpenv t)
        in
        scope := Some PureFuncName; (Var (l, x, scope), List.fold_right (fun t1 t2 -> PureFuncType (t1, t2)) pts t, None)
      | None ->
      if language = Java then
        static_error l "No such variable, field, class, interface, package, inductive datatype constructor, or predicate" None
      else
        static_error l ("No such variable, constructor, regular function, predicate, enum element, global variable, or module: " ^ x) None
      end
    | PredNameExpr (l, g) ->
      begin
        match resolve (pn,ilist) l g predfammap with
          Some (g, (_, tparams, arity, ts, _, inputParamCount)) ->
          if arity <> 0 then static_error l "Using a predicate family as a value is not supported." None;
          if tparams <> [] then static_error l "Using a predicate with type parameters as a value is not supported." None;
          (PredNameExpr (l, g), PredType (tparams, ts, inputParamCount), None)
        | None -> static_error l "No such predicate." None
      end
    | Operation (l, (Eq | Neq as operator), [e1; e2], ts) -> 
      let (w1, w2, t) = promote_numeric e1 e2 ts in
      (Operation (l, operator, [w1; w2], ts), boolt, None)
    | Operation (l, (Or | And as operator), [e1; e2], ts) -> 
      let w1 = checkt e1 boolt in
      let w2 = checkt e2 boolt in
      (Operation (l, operator, [w1; w2], ts), boolt, None)
    | Operation (l, Not, [e], ts) -> 
      let w = checkt e boolt in
      (Operation (l, Not, [w], ts), boolt, None)
    | Operation (l, BitAnd, [e1; e2], ts) ->
      let (w1, t1, _) = check e1 in
      let (w2, t2, _) = check e2 in
      begin match (t1, t2) with
        ((Char|ShortType|IntType|UintPtrType), (Char|ShortType|IntType|UintPtrType)) ->
        let t = match (t1, t2) with (UintPtrType, _) | (_, UintPtrType) -> UintPtrType | _ -> IntType in
        ts := Some [t1; t2];
        (Operation (l, BitAnd, [w1; w2], ts), t, None)
      | _ -> static_error l "Arguments to bitwise operators must be integral types." None
      end
    | Operation (l, (BitXor | BitOr as operator), [e1; e2], ts) ->
      let (w1, t1, _) = check e1 in
      let (_, t2, _) = check e2 in
      begin
      match t1 with
        (Char | ShortType | IntType) -> let w2 = checkt e2 IntType in ts := Some [t1;t2]; (Operation (l, operator, [w1; w2], ts), IntType, None)
      | UintPtrType -> let w2 = checkt e2 UintPtrType in (Operation (l, operator, [w1; w2], ts), UintPtrType, None)
      | _ -> static_error l "Arguments to bitwise operators must be integral types." None
      end
    | Operation (l, Mod, [e1; e2], ts) ->
      let (w1, t1, _) = check e1 in
      let (_, t2, _) = check e2 in
      begin
      match t1 with
        (Char | ShortType | IntType) -> let w2 = checkt e2 IntType in ts :=
Some [t1;t2]; (Operation (l, Mod, [w1; w2], ts), IntType, None)
      | (UChar | UShortType | UintPtrType) -> let w2 = checkt e2 UintPtrType in (Operation (l, Mod, [w1; w2], ts), UintPtrType, None)
      | _ -> static_error l "Arguments to modulus operator must be integral types." None
      end
    | Operation (l, BitNot, [e], ts) ->
      let (w, t, _) = check e in
      begin
      match t with
        Char | ShortType | IntType -> ts := Some [IntType]; (Operation (l, BitNot, [w], ts), IntType, None)
      | UintPtrType -> ts := Some [UintPtrType]; (Operation (l, BitNot, [w], ts), UintPtrType, None)
      | _ -> static_error l "argument to ~ must be char, short, int or uintptr" None
      end
    | Operation (l, (Le | Lt as operator), [e1; e2], ts) -> 
      let (w1, w2, t) = promote l e1 e2 ts in
      (Operation (l, operator, [w1; w2], ts), boolt, None)
    | Operation (l, (Add | Sub as operator), [e1; e2], ts) ->
      let (w1, t1, value1) = check e1 in
      let (w2, t2, value2) = check e2 in
      let t1 = unfold_inferred_type t1 in
      let t2 = unfold_inferred_type t2 in
      begin
        match t1 with
          PtrType pt1 ->
          begin match t2 with
            PtrType pt2 when operator = Sub ->
            if pt1 <> pt2 then static_error l "Pointers must be of same type" None;
            if pt1 <> Char && pt1 <> Void then static_error l "Subtracting non-char pointers is not yet supported" None;
            ts:=Some [t1; t2];
            (Operation (l, operator, [w1; w2], ts), IntType, None)
          | _ ->
            let w2 = checkt e2 intt in
            ts:=Some [t1; IntType];
            (Operation (l, operator, [w1; w2], ts), t1, None)
          end
        | IntType | RealType | ShortType | Char | UintPtrType ->
          let (w1, w2, t) = promote l e1 e2 ts in
          (Operation (l, operator, [w1; w2], ts), t, if t = IntType then (match (value1, value2) with ((Some value1), (Some value2)) -> begin match operator with Add -> Some(add_big_int value1 value2) | Sub -> Some(sub_big_int value1 value2) end | _-> None) else None)
        | ObjType "java.lang.String" as t when operator = Add ->
          let w2 = checkt e2 t in
          ts:=Some [t1; ObjType "java.lang.String"];
          (Operation (l, operator, [w1; w2], ts), t1, None)
        | _ -> static_error l ("Operand of addition or subtraction must be pointer, integer, char, short, or real number: t1 "^(string_of_type t1)^" t2 "^(string_of_type t2)) None
      end
    | Operation (l, Mul, [e1; e2], ts) ->
      let (w1, w2, t) = promote l e1 e2 ts in
      begin match t with PtrType _ -> static_error l "Cannot multiply pointers." None | _ -> () end;
      (Operation (l, Mul, [w1; w2], ts), t, None)
    | Operation (l, Div, [e1; e2], ts) ->
      let (w1, w2, t) = promote l e1 e2 ts in
      begin match t with PtrType _ -> static_error l "Cannot divide pointers." None | _ -> () end;
      (Operation (l, Div, [w1; w2], ts), t, None)
    | Operation (l, (ShiftLeft | ShiftRight as op), [e1; e2], ts) ->
      let w1 = checkt e1 IntType in
      let w2 = checkt e2 IntType in
      ts := Some [IntType; IntType];
      (Operation (l, op, [w1; w2], ts), IntType, None)
    | IntLit (l, n, t) -> (e, (match !t with None -> t := Some intt; intt | Some t -> t), Some n)
    | RealLit(l, n) -> (e, RealType, None)
    | ClassLit (l, s) ->
      let s = check_classname (pn, ilist) (l, s) in
      (ClassLit (l, s), ObjType "java.lang.Class", None)
    | StringLit (l, s) -> (match file_type path with
        Java-> (e, ObjType "java.lang.String", None)
      | _ -> (e, (PtrType Char), None))
    | CastExpr (l, truncating, te, e) ->
      let t = check_pure_type (pn,ilist) tparams te in
      let w = checkt_cast e t in
      (CastExpr (l, truncating, ManifestTypeExpr (type_expr_loc te, t), w), t, None)
    | Read (l, e, f) ->
      check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv e f
    | Deref (l, e, tr) ->
      let (w, t, _) = check e in
      begin
        match t with
          PtrType t0 -> tr := Some t0; (Deref (l, w, tr), t0, None)
        | _ -> static_error l "Operand must be pointer." None
      end
    | AddressOf (l, Var(l2, x, scope)) when List.mem_assoc x tenv ->
      scope := Some(LocalVar); (Var(l2, x, scope), PtrType(match List.assoc x tenv with RefType(t) -> t | _ -> static_error l "Taking the address of this expression is not supported." None), None)
    | AddressOf (l, e) -> let (w, t, _) = check e in (AddressOf (l, w), PtrType t, None)
    | CallExpr (l, "getClass", [], [], [LitPat target], Instance) when language = Java ->
      let w = checkt target (ObjType "java.lang.Object") in
      (WMethodCall (l, "java.lang.Object", "getClass", [], [w], Instance), ObjType "java.lang.Class", None)
    | ExprCallExpr (l, e, es) ->
      let (w, t, _) = check e in
      begin match (t, es) with
        (PureFuncType (_, _), _) -> check_pure_fun_value_call l w t es
      | (ClassOrInterfaceName(cn), [e2]) -> check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv (CastExpr(l, false, IdentTypeExpr(expr_loc e, None, cn), e2))
      | _ -> static_error l "The callee of a call of this form must be a pure function value." None
      end 
    | CallExpr (l, g, targes, [], pats, fb) ->
      let es = List.map (function LitPat e -> e | _ -> static_error l "Patterns are not allowed in this position" None) pats in
      let process_targes callee_tparams =
        if callee_tparams <> [] && targes = [] then
          let targs = List.map (fun _ -> InferredType (ref None)) callee_tparams in
          let Some tpenv = zip callee_tparams targs in
          (targs, tpenv)
        else
          let targs = List.map (check_pure_type (pn,ilist) tparams) targes in
          let tpenv =
            match zip callee_tparams targs with
              None -> static_error l "Incorrect number of type arguments." None
            | Some bs -> bs
          in
          (targs, tpenv)
      in
      let func_call () =
        match try_assoc g tenv with
          Some (PtrType (FuncType ftn)) ->
          let (_, gh, tparams, rt, ftxmap, xmap, pre, post, ft_predfammap) =
            match try_assoc ftn functypemap with
              None -> static_error l "Function pointer calls are now allowed here." None
            | Some info -> info
          in
          let rt = match rt with None -> Void | Some rt -> rt in (* This depends on the fact that the return type does not mention type parameters. *)
          (WFunPtrCall (l, g, es), rt, None)
        | Some ((PureFuncType (t1, t2) as t)) ->
          if targes <> [] then static_error l "Pure function value does not have type parameters." None;
          check_pure_fun_value_call l (Var (l, g, ref (Some LocalVar))) t es
        | _ ->
        match (g, es) with
          ("malloc", [SizeofExpr (ls, StructTypeExpr (lt, tn))]) ->
          if not (List.mem_assoc tn structmap) then static_error lt "No such struct" None;
          (WFunCall (l, g, [], es), PtrType (StructType tn), None)
        | _ ->
        match resolve (pn,ilist) l g funcmap with
          Some (g, FuncInfo (funenv, fterm, lg, k, callee_tparams, tr, ps, nonghost_callers_only, pre, pre_tenv, post, functype_opt, body, fbf, v)) ->
          let (targs, tpenv) = process_targes callee_tparams in
          let rt0 = match tr with None -> Void | Some rt -> rt in
          let rt = instantiate_type tpenv rt0 in
          (WFunCall (l, g, targs, es), rt, None)
        | None ->
        match resolve (pn,ilist) l g purefuncmap with
          Some (g, (_, callee_tparams, t0, ts, _)) ->
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
          static_error l (match language with CLang -> "No such function" | Java -> "No such method or function") None
      in
      if language = CLang || classmap = [] then func_call () else
      let try_qualified_call tn es args fb on_fail =
        let ms = get_methods tn g in
        if ms = [] then on_fail () else
        let argtps = List.map (fun e -> let (_, tp, _) = (check e) in tp) args in
        let ms = List.filter (fun (sign, _) -> is_assignable_to_sign argtps sign) ms in
        begin match ms with
          [] -> static_error l "No matching method" None
        | [(sign, (tn', lm, gh, rt, xmap, pre, post, epost, fb', v, abstract))] ->
          let (fb, es) = if fb = Instance && fb' = Static then (Static, List.tl es) else (fb, es) in
          if fb <> fb' then static_error l "Instance method requires target object" None;
          let rt = match rt with None -> Void | Some rt -> rt in
          (WMethodCall (l, tn', g, sign, es, fb), rt, None)
        | _ -> static_error l "Multiple matching overloads" None
        end
      in
      begin match fb with
        Static ->
        begin fun on_fail ->
          match try_assoc "this" tenv with
            Some (ObjType cn) ->
            try_qualified_call cn (Var (l, "this", ref (Some LocalVar))::es) es Instance on_fail
          | _ ->
          match try_assoc current_class tenv with
            Some (ClassOrInterfaceName tn) ->
            try_qualified_call tn es es Static on_fail
          | _ ->
          on_fail ()
        end $. fun () ->
        func_call ()
      | Instance ->
        let arg0e::args = es in
        let (_, arg0tp, _) = check arg0e in
        let (tn, es, fb) =
          match unfold_inferred_type arg0tp with
            ObjType tn -> (tn, es, Instance)
          | ClassOrInterfaceName tn -> (tn, List.tl es, Static)
          | _ -> static_error l "Target of method call must be object or class" None
        in
        try_qualified_call tn es args fb (fun () -> static_error l "No such method" None)
      end
    | NewObject (l, cn, args) ->
      begin match resolve (pn,ilist) l cn classmap with
        Some (cn, {cabstract}) ->
        if cabstract then
          static_error l "Cannot create instance of abstract class." None
        else 
          (NewObject (l, cn, args), ObjType cn, None)
      | None -> static_error l "No such class" None
      end
    | ReadArray(l, arr, index) ->
      let (w1, arr_t, _) = check arr in
      let w2 = checkt index intt in
      begin match unfold_inferred_type arr_t with
        ArrayType tp -> (WReadArray (l, w1, tp, w2), tp, None)
      | StaticArrayType (tp, _) -> (WReadArray (l, w1, tp, w2), tp, None)
      | PtrType tp -> (WReadArray (l, w1, tp, w2), tp, None)
      | _ when language = Java -> static_error l "Target of array access is not an array." None
      | _ when language = CLang -> static_error l "Target of array access is not an array or pointer." None
      end
    | NewArray (l, te, len) ->
      let t = check_pure_type (pn,ilist) tparams te in
      ignore $. checkt len IntType;
      (e, (ArrayType t), None)
    | NewArrayWithInitializer (l, te, es) ->
      let t = check_pure_type (pn,ilist) tparams te in
      (e, ArrayType t, None)
    | IfExpr (l, e1, e2, e3) ->
      let w1 = checkt e1 boolt in
      let (w2, t, _) = check e2 in
      let w3 = checkt e3 t in
      (IfExpr (l, w1, w2, w3), t, None)
    | SwitchExpr (l, e, cs, cdef_opt, tref) ->
      let (w, t, _) = check e in
      begin
        match t with
          InductiveType (i, targs) ->
          begin
            let (_, inductive_tparams, ctormap, _) = List.assoc i inductivemap in
            let (Some tpenv) = zip inductive_tparams targs in
            let rec iter t0 wcs ctors cs =
              match cs with
                [] ->
                let (t0, wcdef_opt) =
                  match cdef_opt with
                    None ->
                    if ctors <> [] then static_error l ("Missing cases: " ^ String.concat ", " (List.map (fun (ctor, _) -> ctor) ctors)) None;
                    (t0, None)
                  | Some (lcdef, edef) ->
                    if ctors = [] then static_error lcdef "Superfluous default clause" None;
                    let (wdef, tdef, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv edef in
                    let t0 =
                      match t0 with
                        None -> Some tdef
                      | Some t0 -> expect_type (expr_loc edef) tdef t0; Some t0
                    in
                    (t0, Some (lcdef, wdef))
                in
                begin
                  match t0 with
                    None -> static_error l "Switch expressions with zero clauses are not yet supported." None
                  | Some t0 -> tref := Some (t, tenv, targs, t0); (SwitchExpr (l, w, wcs, wcdef_opt, tref), t0, None)
                end
              | SwitchExprClause (lc, cn, xs, e)::cs ->
                begin
                  match try_assoc cn ctormap with
                    None ->
                    static_error lc ("Not a constructor of inductive type '" ^ i ^ "'.") None
                  | Some (_, (_, _, _, ts, _)) ->
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
                    let (w, t, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams (xenv@tenv) e in
                    let t0 =
                      match t0 with
                        None -> Some t
                      | Some t0 -> expect_type (expr_loc e) t t0; Some t0
                    in
                    let ctors = List.filter (fun (ctorname, _) -> ctorname <> cn) ctors in
                    iter t0 (SwitchExprClause (lc, cn, xs, w)::wcs) ctors cs
                end
            in
            iter None [] ctormap cs
          end
        | _ -> static_error l "Switch expression operand must be inductive value." None
      end
    | SizeofExpr(l, te) ->
      let t = check_pure_type (pn,ilist) tparams te in
      (SizeofExpr (l, ManifestTypeExpr (type_expr_loc te, t)), IntType, None)
    | InstanceOfExpr(l, e, te) ->
      let t = check_pure_type (pn,ilist) tparams te in
      let w = checkt e (ObjType "java.lang.Object") in
      (InstanceOfExpr (l, w, ManifestTypeExpr (type_expr_loc te, t)), boolt, None)
    | SuperMethodCall(l, mn, args) ->
      let rec get_implemented_instance_method cn mn argtps =
        if cn = "java.lang.Object" then None else
        match try_assoc cn classmap with 
        | Some {cmeths; csuper} ->
          begin try
            let m =
              List.find
                begin fun ((mn', sign), (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, is_override, abstract)) ->
                  mn = mn' &&  is_assignable_to_sign argtps sign && not abstract
                end
                cmeths
            in
            Some m
          with Not_found ->
            get_implemented_instance_method csuper mn argtps
          end
        | None -> None
      in
      let args_checked = List.map (fun a -> let (w, tp, _) = check a in (w, tp)) args in 
      let argtps = List.map snd args_checked in
      let wargs = List.map fst args_checked in
      let thistype = try_assoc "this" tenv in
      begin match thistype with
        None -> static_error l "super calls not allowed in static context." None
      | Some(ObjType(cn)) -> 
        begin match try_assoc cn classmap with
          None -> static_error l "No matching method." None
        | Some {csuper} ->
            begin match get_implemented_instance_method csuper mn argtps with
              None -> static_error l "No matching method." None
            | Some(((mn', sign), (lm, gh, rt, xmap, pre, pre_tenv, post, epost, pre_dyn, post_dyn, epost_dyn, ss, fb, v, is_override, abstract))) -> 
             (WSuperMethodCall(l, mn, (Var (l, "this", ref (Some LocalVar))) :: wargs, (lm, gh, rt, xmap, pre, post, epost, v)), (match rt with Some(tp) -> tp | _ -> Void), None)
            end
        end
      end 
    | AssignExpr (l, e1, e2) ->
      let (w1, t1, _) = check e1 in
      let w2 = checkt e2 t1 in
      (AssignExpr (l, w1, w2), t1, None)
    | AssignOpExpr(l, e1, (Add | Sub | Mul as operator), e2, postOp, ts, lhs_type) ->
      let (w1, t1, _) = check e1 in
      lhs_type := Some t1;
      let (w2, t2, _) = check e2 in
      begin
        match t1 with
          PtrType pt1 when operator = Add || operator = Sub ->
          begin match t2 with
            PtrType pt2 when operator = Sub ->
            if pt1 <> pt2 then static_error l "Pointers must be of same type" None;
            if pt1 <> Char && pt1 <> Void then static_error l "Subtracting non-char pointers is not yet supported" None;
            ts:=Some [t1; t2];
            (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), IntType, None)
          | _ ->
            let w2 = checkt e2 intt in
            ts:=Some [t1; IntType];
            (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), t1, None)
          end
        | IntType | RealType | ShortType | Char ->
          let (w1, w2, t) = promote l e1 e2 ts in
          (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), t1, None)
        | ObjType "java.lang.String" as t when operator = Add ->
          let w2 = checkt e2 t in
          ts:=Some [t1; ObjType "java.lang.String"];
          (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), t1, None)
        | _ -> static_error l ("Operand of addition, subtraction or multiplication must be pointer, integer, char, short, or real number: t1 "^(string_of_type t1)^" t2 "^(string_of_type t2)) None
      end
    | AssignOpExpr(l, e1, (And | Or | Xor as operator), e2, postOp, ts, lhs_type) ->
      let (w1, t1, _) = check e1 in
      let (w2, t2, _) = check e2 in
      lhs_type := Some t1;
      ts := Some [t1; t2];
      begin match (t1, t2) with
        ((Bool, Bool)) -> (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), t1, None)
      | ((Char|ShortType|IntType), (Char|ShortType|IntType)) ->
        (AssignOpExpr(l, w1, (match operator with And -> BitAnd | Or -> BitOr | Xor -> BitXor), w2, postOp, ts, lhs_type), IntType, None)
       | _ -> static_error l "Arguments to |=, &= and ^= must be boolean or integral types." None
      end
    | AssignOpExpr(l, e1, (ShiftLeft | ShiftRight | Div | Mod as operator), e2, postOp, ts, lhs_type) ->
      let (w1, t1, _) = check e1 in
      if t1 <> IntType then static_error (expr_loc e1) "Variable of type int expected" None;
      let w2 = checkt e2 IntType in
      lhs_type := Some IntType;
      ts := Some [IntType; IntType];
      (AssignOpExpr(l, w1, operator, w2, postOp, ts, lhs_type), IntType, None)
    | InitializerList (l, es) ->
      let rec to_list_expr es =
        match es with
          [] -> CallExpr (l, "nil", [], [], [], Static)
        | e::es -> CallExpr (l, "cons", [], [], [LitPat e; LitPat (to_list_expr es)], Static)
      in
      check (to_list_expr es)
    | e -> static_error (expr_loc e) "Expression form not allowed here." None
  and check_expr_t_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e t0 =
    check_expr_t_core_core functypemap funcmap classmap interfmap (pn, ilist) tparams tenv e t0 false
  and check_expr_t_core_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e t0 isCast =
    match (e, unfold_inferred_type t0) with
      (Operation(l, Div, [IntLit(_, i1, _); IntLit(_, i2, _)], _), RealType) -> RealLit(l, (num_of_big_int i1) // (num_of_big_int i2))
    | (IntLit (l, n, t), PtrType _) when isCast || eq_big_int n zero_big_int -> t:=Some t0; e
    | (IntLit (l, n, t), RealType) -> t:=Some RealType; e
    | (IntLit (l, n, t), UChar) ->
      t:=Some UChar;
      if not (le_big_int min_uchar_big_int n && le_big_int n max_uchar_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 256)) in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as uchar must be between 0 and 255." None
      else
        e
    | (IntLit (l, n, t), Char) ->
      t:=Some Char;
      if not (le_big_int min_char_big_int n && le_big_int n max_char_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 256)) in
          let n = if 128 <= n then n - 256 else n in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as char must be between -128 and 127." None
      else
        e
    | (IntLit (l, n, t), UShortType) ->
      t:=Some UShortType;
      if not (le_big_int min_ushort_big_int n && le_big_int n max_ushort_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 65536)) in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as ushort must be between 0 and 65535." None
      else
        e
    | (IntLit (l, n, t), ShortType) ->
      t:=Some ShortType;
      if not (le_big_int min_short_big_int n && le_big_int n max_short_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_int 65536)) in
          let n = if 32768 <= n then n - 65536 else n in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as short must be between -32768 and 32767." None
      else
        e
    | (IntLit (l, n, t), UintPtrType) ->
      t:=Some UintPtrType;
      if not (le_big_int min_ptr_big_int n && le_big_int n max_ptr_big_int) then
        if isCast then
          let n = int_of_big_int (mod_big_int n (big_int_of_string "4294967296")) in
          IntLit (l, big_int_of_int n, t)
        else
          static_error l "Integer literal used as ushort must be between 0 and 65535." None
      else
        e  
    | _ ->
      let (w, t, value) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
      let check () = begin match (t, t0) with
          (ObjType _, ObjType _) when isCast -> w
        | (PtrType _, UintPtrType) when isCast -> w
        | (UintPtrType, PtrType _) when isCast -> w
        | (IntType, Char) when isCast -> w
        | (IntType, UChar) when isCast -> w
        | (IntType, ShortType) when isCast -> w
        | (IntType, UShortType) when isCast -> w
        | (IntType, UintPtrType) when isCast -> w
        | (UintPtrType, Char) when isCast -> w
        | (UintPtrType, UChar) when isCast -> w
        | (UintPtrType, ShortType) when isCast -> w
        | (UintPtrType, UShortType) when isCast -> w
        | (UintPtrType, IntType) when isCast -> w
        | (ShortType, UChar) when isCast -> w
        | (ShortType, Char) when isCast -> w
        | (ShortType, UShortType) when isCast -> w
        | (UShortType, UChar) when isCast -> w
        | (UShortType, Char) when isCast -> w
        | (UShortType, ShortType) when isCast -> w
        | (Char, UChar) when isCast -> w
        | (UChar, Char) when isCast -> w
        | (ObjType ("java.lang.Object"), ArrayType _) when isCast -> w
        | _ ->
          expect_type (expr_loc e) t t0;
          if try expect_type dummy_loc t0 t; false with StaticError _ -> true then
            Upcast (w, t, t0)
          else
            w
        end
      in
      match (value, t, t0) with
        (Some(value), IntType, Char) when le_big_int min_char_big_int value && le_big_int value max_char_big_int -> w
      | (Some(value), IntType, ShortType) when le_big_int min_short_big_int value && le_big_int value max_short_big_int -> w
      | _ -> check ()
  and check_deref_core functypemap funcmap classmap interfmap (pn,ilist) l tparams tenv e f =
    let (w, t, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
    begin
    match unfold_inferred_type t with
    | PtrType (StructType sn) ->
      begin
      match List.assoc sn structmap with
        (_, Some fds, _) ->
        begin
          match try_assoc f fds with
            None -> static_error l ("No such field in struct '" ^ sn ^ "'.") None
          | Some (_, gh, t) -> (WRead (l, w, sn, f, t, false, ref (Some None), gh), t, None)
        end
      | (_, None, _) -> static_error l ("Invalid dereference; struct type '" ^ sn ^ "' was declared without a body.") None
      end
    | ObjType cn ->
      begin
      match lookup_class_field cn f with
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
        (WRead (l, w, fclass, f, ft, false, ref (Some None), fgh), ft, constant_value)
      end
    | ArrayType _ when f = "length" ->
      (ArrayLengthExpr (l, w), IntType, None)
    | ClassOrInterfaceName cn ->
      begin match lookup_class_field cn f with
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
        (WRead (l, w, fclass, f, ft, true, fvalue, fgh), ft, constant_value)
      end
    | PackageName pn ->
      let name = pn ^ "." ^ f in
      if List.mem_assoc name classmap1 || List.mem_assoc name interfmap1 || List.mem_assoc name classmap0 || List.mem_assoc name interfmap0 then
        (e, ClassOrInterfaceName name, None)
      else if is_package name then
        (e, PackageName name, None)
      else
        static_error l "No such type or package" None
    | _ -> static_error l "Target expression of field dereference should be of type pointer-to-struct." None
    end
  
  let check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e =
   let (w, tp, _) = check_expr_core functypemap funcmap classmap interfmap (pn,ilist) tparams tenv e in
   (w, tp)
  
  let check_expr (pn,ilist) tparams tenv e = check_expr_core [] [] [] [] (pn,ilist) tparams tenv e
  let check_expr_t (pn,ilist) tparams tenv e tp = check_expr_t_core [] [] [] [] (pn,ilist) tparams tenv e tp
  
  (* Region: Type checking of fixpoint function bodies *)

  let fixpointmap1 =
    let rec iter fpm_done fpm_todo =
      match fpm_todo with
        [] -> List.rev fpm_done
      | (g, (l, tparams, rt, pmap, index, body, pn, ilist, fsym))::fpm_todo ->
      match (index, body) with
        (Some index, SwitchStmt (ls, Var (lx, x, _), cs)) ->
        let (i, targs) =
          match List.assoc x pmap with
            InductiveType (i, targs) -> (i, targs)
          | _ -> static_error l "Switch operand is not an inductive value." None
        in
        let (_, inductive_tparams, ctormap, _) = List.assoc i inductivemap in
        let (Some tpenv) = zip inductive_tparams targs in
        let rec check_cs ctormap wcs cs =
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
                let xs = List.map (function LitPat (Var (_, x, _)) -> x | _ -> static_error lc "Constructor arguments must be variable names" None) pats in
                (cn, xs)
              | Var (_, cn, _) -> (cn, [])
              | _ -> static_error lc "Case expression must be constructor pattern" None
            in
            let ts =
              match try_assoc cn ctormap with
                None -> static_error lc "No such constructor." None
              | Some (_, (_, _, _, ts, _)) -> ts
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
            let wbody = check_expr_t (pn,ilist) tparams tenv body rt in
            let rec iter0 components e =
              let rec iter () e =
                let iter1 e = iter () e in
                match e with
                  WPureFunCall (l, g', targs, args) ->
                  if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot call a fixpoint function that appears later in the program text" None;
                  if g' = g then begin
                    match List.nth args index with
                      Var (l, x, _) when List.mem x components -> ()
                    | _ -> static_error l "Inductive argument of recursive call must be switch clause pattern variable." None
                  end;
                  List.iter iter1 args
                | Var (l, g', scope) when (match !scope with Some PureFuncName -> true | _ -> false) ->
                  if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot mention a fixpoint function that appears later in the program text" None;
                  if g' = g then static_error l "A fixpoint function that mentions itself is not yet supported." None
                | SwitchExpr (l, Var (_, x, _), cs, def_opt, _) when List.mem x components ->
                  List.iter (fun (SwitchExprClause (_, _, pats, e)) -> iter0 (pats @ components) e) cs;
                  (match def_opt with None -> () | Some (l, e) -> iter1 e)
                | _ -> expr_fold_open iter () e
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
            let wbody = check_expr_t (pn,ilist) tparams pmap body rt in
            let expr_is_ok e =
              match e with
                WPureFunCall (l, g', targs, args) ->
                if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot call a fixpoint function that appears later in the program text" None;
                if g' = g then static_error l "Recursive calls are not allowed in a default clause." None
              | Var (l, g', scope) when (match !scope with Some PureFuncName -> true | _ -> false) ->
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
        iter ((g, (l, rt, pmap, Some index, SwitchExpr (ls, Var (lx, x, ref None), wcs, None, ref None), pn, ilist, fsym))::fpm_done) fpm_todo
      | (None, ReturnStmt (lr, Some e)) ->
        let tenv = pmap in
        let w = check_expr_t (pn,ilist) tparams tenv e rt in
        let rec iter0 e =
          let rec iter () e =
            let iter1 e = iter () e in
            match e with
              WPureFunCall (l, g', targs, args) ->
              if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot call a fixpoint function that appears later in the program text" None;
              if g' = g then static_error l "A fixpoint function whose body is a return statement cannot call itself." None;
              List.iter iter1 args
            | Var (l, g', scope) when (match !scope with Some PureFuncName -> true | _ -> false) ->
              if List.mem_assoc g' fpm_todo then static_error l "A fixpoint function cannot mention a fixpoint function that appears later in the program text" None;
              if g' = g then static_error l "A fixpoint function whose body is a return statement cannot mention itself." None
            | _ -> expr_fold_open iter () e
          in
          iter () e
        in
        iter0 w;
        iter ((g, (l, rt, pmap, None, w, pn, ilist, fsym))::fpm_done) fpm_todo
    in
    iter [] fixpointmap1
  
  (* Static field initializers cannot have side-effects; otherwise, class initialization would be tricky to verify. *)
  let check_static_field_initializer e =
    let rec iter e =
      match e with
        True _ | False _ | Null _ | Var _ | IntLit _ | RealLit _ | StringLit _ | ClassLit _ -> ()
      | Operation (l, _, es, _) -> List.iter iter es
      | NewArray (l, t, e) -> iter e
      | NewArrayWithInitializer (l, t, es) -> List.iter iter es
      | CastExpr (l, _, _, e) -> iter e
      | Upcast (e, _, _) -> iter e
      | WRead (_, e, _, _, _, _, _, _) -> iter e
      | _ -> static_error (expr_loc e) "This expression form is not supported in a static field initializer." None
    in
    iter e
  
  (* Region: Type checking of field initializers for static fields *)
  
  let classmap1 =
    List.map
      begin fun (cn, (l, abstract, fin, meths, fds, constr, super, interfs, preds, pn, ilist)) ->
        let fds =
          List.map
            begin function
              (f, ({ft; fbinding=Static; finit=Some e} as fd)) ->
                let e = check_expr_t (pn,ilist) [] [current_class, ClassOrInterfaceName cn] e ft in
                check_static_field_initializer e;
                (f, {fd with finit=Some e})
            | fd -> fd
            end
            fds
        in
        (cn, (l, abstract, fin, meths, fds, constr, super, interfs, preds, pn, ilist))
      end
      classmap1
  
  let rec check_c_initializer e tp =
    match tp, e with
    | StaticArrayType (Char, n), StringLit (ls, s) ->
      if String.length s + 1 > n then static_error ls "String literal does not fit inside character array." None;
      e
    | StaticArrayType (elemTp, elemCount), InitializerList (ll, es) ->
      let rec iter n es =
        match es with
          [] -> []
        | e::es ->
          if n = 0 then static_error ll "Initializer list too long." None;
          let e = check_c_initializer e elemTp in
          let es = iter (n - 1) es in
          e::es
      in
      InitializerList (ll, iter elemCount es)
    | StructType sn, InitializerList (ll, es) ->
      let fds =
        match List.assoc sn structmap with
          (_, Some fds, _) -> fds
        | _ -> static_error ll "Cannot initialize struct declared without a body." None
      in
      let rec iter fds es =
        match fds, es with
          _, [] -> []
        | (_, (_, Ghost, _))::fds, es -> iter fds es
        | (_, (_, _, tp))::fds, e::es ->
          let e = check_c_initializer e tp in
          let es = iter fds es in
          e::es
        | _ -> static_error ll "Initializer list too long." None
      in
      InitializerList (ll, iter fds es)
    | tp, e ->
      check_expr_t ("", []) [] [] e tp
  
  let () =
    globalmap1 |> List.iter begin fun (x, (lg, tp, symb, ref_init)) ->
      ref_init := option_map (fun e -> check_c_initializer e tp) !ref_init
    end
  
  (* Region: Computing constant field values *)
  
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
      | Operation (l, Add, [e1; e2], _) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (add_big_int n1 n2)
        | (StringConst s1, v) -> StringConst (s1 ^ string_of_const v)
        | (v, StringConst s2) -> StringConst (string_of_const v ^ s2)
        | _ -> raise NotAConstant
        end
      | Operation (l, Sub, [e1; e2], _) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (sub_big_int n1 n2)
        | _ -> raise NotAConstant
        end
      | Operation (l, Mul, [e1; e2], _) ->
        begin match (ev e1, ev e2) with
          (IntConst n1, IntConst n2) -> IntConst (mult_big_int n1 n2)
        | _ -> raise NotAConstant
        end
      | IntLit (l, n, _) -> IntConst n
      | StringLit (l, s) -> StringConst s
      | WRead (l, _, fparent, fname, _, fstatic, _, _) when fstatic -> eval_field callers (fparent, fname)
      | CastExpr (l, truncating, ManifestTypeExpr (_, t), e) ->
        let v = ev e in
        begin match (t, v) with
          (Char, IntConst n) ->
          let n =
            if not (le_big_int (big_int_of_int (-128)) n && le_big_int n (big_int_of_int 127)) then
              let n = int_of_big_int (mod_big_int n (big_int_of_int 256)) in
              let n = if 128 <= n then n - 256 else n in
              big_int_of_int n
            else
              n
          in
          IntConst n
        | (ShortType, IntConst n) ->
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
      | WidenedParameterArgument e -> ev e
      | _ -> raise NotAConstant
    and eval_field callers ((cn, fn) as f) =
      if List.mem f callers then raise NotAConstant;
      match try_assoc cn classmap1 with
        Some (l, abstract, fin, meths, fds, const, super, interfs, preds, pn, ilist) -> eval_field_body (f::callers) (List.assoc fn fds)
      | None ->
      match try_assoc cn classmap0 with
        Some {cfds} -> eval_field_body (f::callers) (List.assoc fn cfds)
      | None ->
      match try_assoc cn interfmap1 with
        Some (li, fds, meths, preds, interfs, pn, ilist) -> eval_field_body (f::callers) (List.assoc fn fds)
      | None ->
      match try_assoc cn interfmap0 with
        Some (InterfaceInfo (li, fields, meths, preds, interfs)) -> eval_field_body (f::callers) (List.assoc fn fields)
      | None ->
      assert false
    and eval_field_body callers {fbinding; ffinal; finit; fvalue} =
      match !fvalue with
        Some None -> raise NotAConstant
      | Some (Some v) -> v
      | None ->
        match (fbinding, ffinal, finit) with
          (Static, true, Some e) ->
          begin try
            let v = eval callers e in
            fvalue := Some (Some v);
            v
          with NotAConstant -> fvalue := Some None; raise NotAConstant
          end
        | _ -> fvalue := Some None; raise NotAConstant
    in
    let compute_fields fds =
      fds |> List.iter (fun (f, fbody) -> try ignore $. eval_field_body [] fbody with NotAConstant -> ())
    in
    classmap1 |> List.iter (fun (cn, (l, abstract, fin, meths, fds, constr, super, interfs, preds, pn, ilist)) -> compute_fields fds);
    interfmap1 |> List.iter (fun (ifn, (li, fds, meths, preds, interfs, pn, ilist)) -> compute_fields fds)
  
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
      let (w, tp) = check_expr (pn,ilist) tparams tenv e in
      expect_type (expr_loc e) t tp;
      (LitPat (WidenedParameterArgument w), [])
    | LitPat e -> let w = check_expr_t (pn,ilist) tparams tenv e t in (LitPat w, [])
    | VarPat (l, x) ->
      if List.mem_assoc x tenv then static_error l ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
      (p, [(x, t)])
    | DummyPat -> (p, [])
    | CtorPat (l, g, pats) ->
      begin match resolve (pn,ilist) l g purefuncmap with
        Some (_, (_, _, rt, _, _)) ->
        begin match rt with
          InductiveType (i, _) ->
          let (_, inductive_tparams, ctormap, _) = List.assoc i inductivemap in
          begin match try_assoc g ctormap with
            Some (_, (_, _, _, ts0, symb)) ->
            let targs = List.map (fun _ -> InferredType (ref None)) inductive_tparams in
            let Some tpenv = zip inductive_tparams targs in
            let ts = List.map (instantiate_type tpenv) ts0 in
            let t0 = InductiveType (i, targs) in
            expect_type l t t0;
            let (pats, tenv') = check_pats_core (pn,ilist) l tparams tenv ts pats in
            (WCtorPat (l, i, targs, g, ts0, ts, pats), tenv')
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
    WMethodCall (dummy_loc, "java.lang.Object", "getClass", [], [Var (dummy_loc, "this", ref (Some LocalVar))], Instance)
  
  let get_class_finality tn = (* Returns ExtensibleClass if tn is an interface *)
    match try_assoc tn classmap1 with
      Some (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist) ->
      fin
    | None ->
      match try_assoc tn classmap0 with
        Some {cfinal} ->
        cfinal
      | None -> ExtensibleClass
  
  let check_inst_pred_asn l cn g check_call error =
    let rec find_in_interf itf =
      let search_interfmap get_interfs_and_preds interfmap fallback =
        match try_assoc itf interfmap with
          Some info ->
          let (interfs, preds) = get_interfs_and_preds info in
          begin match try_assoc g preds with
            Some (_, pmap, family, symb) -> [(family, pmap)]
          | None -> List.flatten (List.map (fun i -> find_in_interf i) interfs)
          end
        | None -> fallback ()
      in
      search_interfmap (function (li, fields, meths, preds, interfs, pn, ilist) -> (interfs, preds)) interfmap1 $. fun () ->
      search_interfmap (function InterfaceInfo (li, fields, meths, preds, interfs) -> (interfs, preds)) interfmap0 $. fun () ->
      []
    in
    let rec find_in_class cn =
      let search_classmap classmap proj fallback =
        match try_assoc cn classmap with
          Some info ->
          let (super, interfs, preds) = proj info in
          begin match try_assoc g preds with
            Some (_, pmap, family, symb, body) -> [(family, pmap)]
          | None -> find_in_class super @ flatmap find_in_interf interfs
          end
        | None -> fallback ()
      in
      search_classmap classmap1
        (function (_, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist) -> (super, interfs, preds))
        $. fun () ->
      search_classmap classmap0
        (function {csuper; cinterfs; cpreds} -> (csuper, cinterfs, cpreds))
        $. fun () ->
      []
    in
    begin match find_in_class cn @ find_in_interf cn with
      [] -> error ()
    | [(family, pmap)] -> check_call family pmap
    | _ -> static_error l (Printf.sprintf "Ambiguous instance predicate assertion: multiple predicates named '%s' in scope" g) None
    end
  
  let get_pred_symb p = let (_, _, _, _, symb, _) = List.assoc p predfammap in symb
  
  let lazy_value f =
    let cell = ref None in
    fun () ->
      match !cell with
        None -> let result = f() in cell := Some result; result
      | Some result -> result
  
  let lazy_predfamsymb name = lazy_value (fun () -> get_pred_symb name)
  
  let array_element_symb = lazy_predfamsymb "java.lang.array_element"
  let array_slice_symb = lazy_predfamsymb "java.lang.array_slice"
  let array_slice_deep_symb = lazy_predfamsymb "java.lang.array_slice_deep"
  
  let pointee_tuple chunk_pred_name array_pred_name =
    let array_malloc_block_pred_name = "malloc_block_" ^ array_pred_name in
    chunk_pred_name, lazy_predfamsymb chunk_pred_name, array_pred_name, lazy_predfamsymb array_pred_name, array_malloc_block_pred_name, lazy_predfamsymb array_malloc_block_pred_name
  
  let _, pointer_pred_symb, _, pointers_pred_symb, _, malloc_block_pointers_pred_symb as pointer_pointee_tuple = pointee_tuple "pointer" "pointers"
  let _, int_pred_symb, _, ints_pred_symb, _, malloc_block_ints_pred_symb as int_pointee_tuple = pointee_tuple "integer" "ints"
  let _, uint_pred_symb, _, uints_pred_symb, _, malloc_block_uints_pred_symb as uint_pointee_tuple = pointee_tuple "u_integer" "uints"
  let _, char_pred_symb, _, chars_pred_symb, _, malloc_block_chars_pred_symb as char_pointee_tuple = pointee_tuple "character" "chars"
  let _, uchar_pred_symb, _, uchars_pred_symb, _, malloc_block_uchars_pred_symb as uchar_pointee_tuple = pointee_tuple "u_character" "uchars"
  
  let deref_pointee_tuple (cn, csym, an, asym, mban, mbasym) = (cn, csym(), an, asym(), mban, mbasym())
  
  let try_pointee_pred_symb0 pointeeType =
    option_map deref_pointee_tuple
    begin match pointeeType with
      PtrType _ -> Some pointer_pointee_tuple
    | IntType -> Some int_pointee_tuple
    | UintPtrType -> Some uint_pointee_tuple
    | Char -> Some char_pointee_tuple
    | UChar -> Some uchar_pointee_tuple
    | _ -> None
    end
  
  let supported_types_text = "int, unsigned int, char, unsigned char, or a pointer type"
  
  let try_pointee_pred_symb pointeeType = option_map (fun (_, x, _, _, _, _) -> x) (try_pointee_pred_symb0 pointeeType)
  
  let list_type elemType = InductiveType ("list", [elemType])
  
  let rec check_asn_core (pn,ilist) tparams tenv p =
    let check_asn = check_asn_core in
    match p with
    | PointsTo (l, ReadArray (lread, earray, SliceExpr (lslice, pstart, pend)), rhs) ->
      let (warray, tarray) = check_expr (pn,ilist) tparams tenv earray in
      let (wstart, tenv) =
        match pstart with
          None -> (None, tenv)
        | Some pstart ->
          let (wstart, tenv) = check_pat (pn,ilist) tparams tenv IntType pstart in
          Some wstart, tenv
      in
      let (wend, tenv) =
        match pend with
          None -> (None, tenv)
        | Some pend ->
          let (wend, tenv) = check_pat (pn,ilist) tparams tenv IntType pend in
          Some wend, tenv
      in
      begin match language with
      | CLang ->
        let elemtype =
          match tarray with
            PtrType t -> t
          | StaticArrayType (t, _) -> t
          | _ -> static_error lread "Array in array dereference must be of pointer type." None
        in
        let (pointee_pred_name, pointee_pred_symb, array_pred_name, array_pred_symb, _, _) =
          match try_pointee_pred_symb0 elemtype with
            Some info -> info
          | None -> static_error l ("Only arrays whose element type is "^supported_types_text^" are currently supported here.") None
        in
        let (wrhs, tenv) = check_pat (pn,ilist) tparams tenv (list_type elemtype) rhs in
        let p = new predref array_pred_name in
        p#set_domain [PtrType elemtype; IntType; list_type elemtype];
        p#set_inputParamCount (Some 2);
        let wfirst, wlength =
          match wstart, wend with
            None, Some wend -> warray, wend
          | Some (LitPat (IntLit (_, n, _))), Some wend when eq_big_int n zero_big_int -> warray, wend
          | Some (LitPat wstart), Some (LitPat wend) ->
            Operation (lslice, Add, [warray; wstart], ref (Some [PtrType elemtype; IntType])),
            LitPat (Operation (lslice, Sub, [wend; wstart], ref (Some [IntType; IntType])))
          | _ -> static_error l "Malformed array assertion." None
        in
        (WPredAsn (l, p, true, [], [], [LitPat wfirst; wlength; wrhs]), tenv, [])
      | Java ->
        let elemtype =
          match tarray with
            ArrayType t -> t
          | _ -> static_error lread "Array in array dereference must be of array type." None
        in
        let (wrhs, tenv) = check_pat (pn,ilist) tparams tenv (list_type elemtype) rhs in
        let p = new predref "java.lang.array_slice" in
        p#set_domain [ArrayType elemtype; IntType; IntType; list_type elemtype]; p#set_inputParamCount (Some 3);
        let wstart = match wstart with None -> LitPat (IntLit (lslice, zero_big_int, ref (Some IntType))) | Some wstart -> wstart in
        let wend = match wend with None -> LitPat (ArrayLengthExpr (lslice, warray)) | Some wend -> wend in
        let args = [LitPat warray; wstart; wend; wrhs] in
        (WPredAsn (l, p, true, [elemtype], [], args), tenv, [])
      end
    | PointsTo (l, lhs, v) ->
      let (wlhs, t) = check_expr (pn,ilist) tparams tenv lhs in
      begin match wlhs with
        WRead (_, _, _, _, _, _, _, _) | WReadArray (_, _, _, _) -> ()
      | Var (_, _, scope) when !scope = Some GlobalName -> ()
      | Deref (_, _, _) -> ()
      | _ -> static_error l "The left-hand side of a points-to assertion must be a field dereference, a global variable, a pointer variable dereference or an array element expression." None
      end;
      let (wv, tenv') = check_pat (pn,ilist) tparams tenv t v in
      (WPointsTo (l, wlhs, t, wv), tenv', [])
    | PredAsn (l, p, targs, ps0, ps) ->
      let targs = List.map (check_pure_type (pn, ilist) tparams) targs in
      begin fun cont ->
         match try_assoc p#name tenv with
           Some (PredType (callee_tparams, ts, inputParamCount)) -> cont (new predref (p#name), false, callee_tparams, [], ts, inputParamCount)
         | None | Some _ ->
          begin match resolve (pn,ilist) l p#name predfammap with
            Some (pname, (_, callee_tparams, arity, xs, _, inputParamCount)) ->
            let ts0 = match file_type path with
              Java-> list_make arity (ObjType "java.lang.Class")
            | _   -> list_make arity (PtrType Void)
            in
            cont (new predref pname, true, callee_tparams, ts0, xs, inputParamCount)
          | None ->
            begin match
              match try_assoc p#name predctormap1 with
                Some (l, ps1, ps2, inputParamCount, body, funcsym, pn, ilist) -> Some (ps1, ps2, inputParamCount)
              | None ->
              match try_assoc p#name predctormap0 with
                Some (PredCtorInfo (l, ps1, ps2, inputParamCount, body, funcsym)) -> Some (ps1, ps2, inputParamCount)
              | None -> None
            with
              Some (ps1, ps2, inputParamCount) ->
              cont (new predref (p#name), true, [], List.map snd ps1, List.map snd ps2, inputParamCount)
            | None ->
              let error () = 
                begin match try_assoc p#name tenv with
                  None ->  static_error l ("No such predicate: " ^ p#name) None 
                | Some _ -> static_error l ("Variable " ^ p#name ^ " is not of predicate type.") None 
                end
              in
              begin match try_assoc "this" tenv with
                None -> error ()
              | Some (ObjType cn) ->
                let check_call family pmap =
                  if targs <> [] then static_error l "Incorrect number of type arguments." None;
                  if ps0 <> [] then static_error l "Incorrect number of indices." None;
                  let (wps, tenv) = check_pats (pn,ilist) l tparams tenv (List.map snd pmap) ps in
                  let index =
                    if List.mem_assoc cn classmap1 || List.mem_assoc cn classmap0 then
                      ClassLit (l, cn)
                    else
                      get_class_of_this
                  in
                  (WInstPredAsn (l, None, cn, get_class_finality cn, family, p#name, index, wps), tenv, [])
                in
                check_inst_pred_asn l cn p#name check_call error
              | Some(_) -> error ()
              end
            end
          end
      end $. fun (p, is_global_predref, callee_tparams, ts0, xs, inputParamCount) ->
      begin
        let (targs, tpenv, inferredTypes) =
          if targs = [] then
            let tpenv = List.map (fun x -> (x, ref None)) callee_tparams in
            (List.map (fun (x, r) -> InferredType r) tpenv,
             List.map (fun (x, r) -> (x, InferredType r)) tpenv,
             List.map (fun (x, r) -> r) tpenv)
          else
            match zip callee_tparams targs with
              None -> static_error l (Printf.sprintf "Predicate requires %d type arguments." (List.length callee_tparams)) None
            | Some bs -> (targs, bs, [])
        in
        if List.length ps0 <> List.length ts0 then static_error l "Incorrect number of indexes." None;
        let (wps0, tenv) = check_pats (pn,ilist) l tparams tenv ts0 ps0 in
        let xs' = List.map (instantiate_type tpenv) xs in
        let (wps, tenv) = check_pats (pn,ilist) l tparams tenv xs' ps in
        p#set_domain (ts0 @ xs'); p#set_inputParamCount inputParamCount;
        (WPredAsn (l, p, is_global_predref, targs, wps0, wps), tenv, inferredTypes)
      end
    | InstPredAsn (l, e, g, index, pats) ->
      let (w, t) = check_expr (pn,ilist) tparams tenv e in
      begin match unfold_inferred_type t with
        ObjType cn ->
        let check_call family pmap =
          let (wpats, tenv) = check_pats (pn,ilist) l tparams tenv (List.map snd pmap) pats in
          let index = check_expr_t (pn,ilist) tparams tenv index (ObjType "java.lang.Class") in
          (WInstPredAsn (l, Some w, cn, get_class_finality cn, family, g, index, wpats), tenv, [])
        in
        let error () = static_error l (Printf.sprintf "Type '%s' does not declare such a predicate" cn) None in
        check_inst_pred_asn l cn g check_call error
      | _ -> static_error l "Target of instance predicate assertion must be of class type" None
      end
    | ExprAsn (l, e) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in (ExprAsn (l, w), tenv, [])
    | MatchAsn (l, e1, pat) ->
      let (w1, t) = check_expr (pn,ilist) tparams tenv e1 in
      let (wpat, tenv) = check_pat (pn,ilist) tparams tenv t pat in
      (WMatchAsn (l, w1, wpat, t), tenv, [])
    | Sep (l, p1, p2) ->
      let (p1, tenv, infTps1) = check_asn (pn,ilist) tparams tenv p1 in
      let (p2, tenv, infTps2) = check_asn (pn,ilist) tparams tenv p2 in
      (Sep (l, p1, p2), tenv, infTps1 @ infTps2)
    | IfAsn (l, e, p1, p2) ->
      let w = check_expr_t (pn,ilist) tparams tenv e boolt in
      let (wp1, _, infTps1) = check_asn (pn,ilist) tparams tenv p1 in
      let (wp2, _, infTps2) = check_asn (pn,ilist) tparams tenv p2 in
      (IfAsn (l, w, wp1, wp2), tenv, infTps1 @ infTps2)
    | SwitchAsn (l, e, cs) ->
      let (w, t) = check_expr (pn,ilist) tparams tenv e in
      begin
      match unfold_inferred_type t with
      | InductiveType (i, targs) ->
        begin
        match try_assoc i inductivemap with
          None -> static_error l "Switch operand is not an inductive value." None
        | Some (_, inductive_tparams, ctormap, _) ->
          let (Some tpenv) = zip inductive_tparams targs in
          let rec iter wcs ctormap cs infTps =
            match cs with
              [] ->
              let _ = 
                match ctormap with
                  [] -> ()
                | (cn, _)::_ ->
                  static_error l ("Missing case: '" ^ cn ^ "'.") None
              in (WSwitchAsn (l, w, i, wcs), tenv, infTps)
            | SwitchAsnClause (lc, cn, xs, ref_xsInfo, body)::cs ->
              begin
              match try_assoc cn ctormap with
                None -> static_error lc "No such constructor." None
              | Some (_, (_, _, _, ts, _)) ->
                let (xmap, xsInfo) =
                  let rec iter xmap xsInfo ts xs =
                    match (ts, xs) with
                      ([], []) -> (xmap, List.rev xsInfo)
                    | (t::ts, x::xs) ->
                      if List.mem_assoc x tenv then static_error lc ("Pattern variable '" ^ x ^ "' hides existing local variable '" ^ x ^ "'.") None;
                      let _ = if List.mem_assoc x xmap then static_error lc "Duplicate pattern variable." None in
                      let xInfo = match unfold_inferred_type t with TypeParam x -> Some (provertype_of_type (List.assoc x tpenv)) | _ -> None in
                      iter ((x, instantiate_type tpenv t)::xmap) (xInfo::xsInfo) ts xs
                    | ([], _) -> static_error lc "Too many pattern variables." None
                    | _ -> static_error lc "Too few pattern variables." None
                  in
                  iter [] [] ts xs
                in
                ref_xsInfo := Some xsInfo;
                let tenv = xmap @ tenv in
                let (wbody, _, clauseInfTps) = check_asn (pn,ilist)  tparams tenv body in
                iter (SwitchAsnClause (lc, cn, xs, ref_xsInfo, wbody)::wcs) (List.remove_assoc cn ctormap) cs (clauseInfTps @ infTps)
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
          let t = check_pure_type (pn,ilist) tparams te in
          let w = check_expr_t (pn,ilist) tparams ((i, t) :: tenv) e boolt in
          (ForallAsn(l, ManifestTypeExpr(l, t), i, w), tenv, [])
      | Some _ -> static_error l ("bound variable " ^ i ^ " hides existing local variable " ^ i) None
      end
    | CoefAsn (l, coef, body) ->
      let (wcoef, tenv') = check_pat_core (pn,ilist) tparams tenv RealType coef in
      let (wbody, tenv, infTps) = check_asn (pn,ilist) tparams tenv body in
      (CoefAsn (l, wcoef, wbody), merge_tenvs l tenv' tenv, infTps)
    | EnsuresAsn (l, body) ->
      begin match try_assoc "#pre" tenv with
        None -> static_error l "Ensures clause not allowed here." None
      | Some rt ->
        let tenv = List.remove_assoc "#pre" tenv in
        let tenv = if rt = Void then tenv else ("result", rt)::tenv in
        let (wbody, tenv, infTps) = check_asn (pn,ilist) tparams tenv body in
        (EnsuresAsn (l, wbody), tenv, infTps)
      end
    | PluginAsn (l, text) ->
      match pluginmap with
        [] -> static_error l "Load a plugin before using a plugin assertion" None
      | [_, ((plugin, _), _)] ->
        let to_plugin_type t =
          match t with
            PtrType (StructType sn) -> Plugins.StructPointerType sn
          | PluginInternalType t -> Plugins.PluginInternalType t
          | _ -> Plugins.VeriFastInternalType
        in
        let from_plugin_type t =
          match t with
            Plugins.StructPointerType sn -> PtrType (StructType sn)
          | Plugins.VeriFastInternalType -> failwith "plugin_typecheck_assertion must not create binding with type VeriFastInternalType"
          | Plugins.PluginInternalType t -> PluginInternalType t
        in        
        let plugin_tenv = List.map (fun (x, t) -> (x, to_plugin_type t)) tenv in
        begin try
          let (w, plugin_bindings) = plugin#typecheck_assertion plugin_tenv text in
          let bindings = List.map (fun (x, t) -> (x, from_plugin_type t)) plugin_bindings in
          (WPluginAsn (l, List.map fst bindings, w), bindings @ tenv, [])
        with
          Plugins.PluginStaticError (off, len, msg) ->
          let ((path, line, col), _) = l in
          let l = ((path, line, col + 1 + off), (path, line, col + 1 + off + len)) in (* TODO: Suport multiline assertions *)
          static_error l msg None
        end
  
  let rec fix_inferred_type r =
    match !r with
      None -> r := Some Bool (* any type will do *)
    | Some (InferredType r) -> fix_inferred_type r
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
             let pre = check_expr_t (pn,ilist) [] ([("actionHandle", HandleIdType)] @ pmap @ boxvarmap) pre boolt in
             let post = check_expr_t (pn,ilist) [] ([("actionHandle", HandleIdType)] @ pmap @ boxvarmap @ old_boxvarmap) post boolt in
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
        (bcn, (l, boxpmap, winv, boxvarmap, amap, hpmap))
      end
      boxmap
  
  (* Region: predicate preciseness check *)
  
  let rec vars_used e =
    let rec iter state e =
      match e with
      | Var (l, x, scope) -> begin match !scope with Some LocalVar -> x::state | Some _ -> state end
      | SwitchExpr (l, e, cs, cdef_opt, _) ->
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
      LitPat (Var (_, x, scope)) when !scope = Some LocalVar -> [x]
    | LitPat _ -> []
    | VarPat (_, x) -> [x]
    | DummyPat -> []
    | WCtorPat (l, i, targs, g, ts0, ts, pats) ->
      List.concat (List.map fixed_pat_fixed_vars pats)
  
  let assume_pat_fixed fixed pat =
    fixed_pat_fixed_vars pat @ fixed
  
  let assert_pats_fixed l fixed pats =
    List.iter (function (LitPat e) -> assert_expr_fixed fixed e | _ -> static_error l "Non-fixed pattern used in input position." None) pats
  
  let assume_pats_fixed fixed pats =
    flatmap fixed_pat_fixed_vars pats @ fixed
  
  let expr_is_fixed fixed e =
    let used = vars_used e in
    List.for_all (fun x -> List.mem x fixed) used
  
  let rec check_pred_precise fixed p =
    match p with
      WPointsTo (l, lhs, tp, pv) ->
      begin match lhs with
        WRead (lr, et, _, _, _, _, _, _) -> assert_expr_fixed fixed et
      | WReadArray (la, ea, tp, ei) -> assert_expr_fixed fixed ea; assert_expr_fixed fixed ei
      end;
      assume_pat_fixed fixed pv
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
    | ExprAsn (l, Operation (_, Eq, [Var (_, x, scope); e2], _)) when !scope = Some LocalVar ->
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
        | SwitchAsnClause (l, c, xs, _, p)::cs ->
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
        | DummyPat -> ()
      end;
      check_pred_precise fixed p
  
  (* Region: Predicate instances *)
  
  let predinstmap1 =
    flatmap
      begin
        function
          (sn, (_, Some fmap, _)) ->
          flatmap
            begin
              function
                (f, (l, Real, t)) ->
                begin
                let (g, (_, _, _, _, symb, _)) = List.assoc (sn, f) field_pred_map in
                let predinst p =
                  p#set_inputParamCount (Some 1);
                  ((g, []),
                   ([], l, [], [sn, PtrType (StructType sn); "value", t], symb, Some 1,
                    let r = WRead (l, Var (l, sn, ref (Some LocalVar)), sn, f, t, false, ref (Some None), Real) in
                    WPredAsn (l, p, true, [], [], [LitPat (AddressOf (l, r)); LitPat (Var (l, "value", ref (Some LocalVar)))])
                   )
                  )
                in
                match t with
                  PtrType _ ->
                  let pref = new predref "pointer" in
                  pref#set_domain [PtrType (PtrType Void); PtrType Void];
                  [predinst pref]
                | IntType ->
                  let pref = new predref "integer" in
                  pref#set_domain [PtrType IntType; IntType];
                  [predinst pref]
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
      match zip predfam_tparams (List.map (fun x -> TypeParam x) predinst_tparams) with
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
          let t = check_pure_type (pn,ilist) tparams' te in
          expect_type l t (instantiate_type tpenv t0);
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
      match resolve (pn,ilist) l p predfammap with
        None -> static_error l ("No such predicate family: "^p) None
      | Some (p, (lfam, predfam_tparams, arity, ps, psymb, inputParamCount)) ->
        if fns = [] && language = CLang then begin
          let famPath = let (((basePath, relPath), _, _), _) = lfam in concat basePath relPath in
          let instPath = let (((basePath, relPath), _, _), _) = l in concat basePath relPath in
          let famPathNoExt = try Filename.chop_extension famPath with Invalid_argument _ -> famPath in
          if instPath <> famPath && instPath <> famPathNoExt ^ ".c" then
            static_error l "A predicate declared in a header file may be defined only in the corresponding .c file." None
        end;
        (p, predfam_tparams, arity, ps, psymb, inputParamCount)
    in
    check_predinst0 predfam_tparams arity ps psymb inputParamCount (pn, ilist) tparams tenv env l p predinst_tparams fns xs body
  
  let predinstmap1 = 
    let rec iter (pn,ilist) pm ds =
      match ds with
        PredFamilyInstanceDecl (l, p, tparams, is, xs, body)::ds ->
        let fns = match file_type path with
          Java-> check_classnamelist (pn,ilist) is
        | _ -> check_funcnamelist is 
        in
        let (pfns, info) as entry = check_predinst (pn, ilist) [] [] [] l p tparams fns xs body in
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
          (g, (l, ps1, ps2, inputParamCount, body, funcsym,pn,ilist)) ->
          let (wbody, _) = check_asn (pn,ilist) [] (ps1 @ ps2) body in
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
          (g, PredCtorInfo (l, ps1, ps2, inputParamCount, wbody, funcsym))
      )
      predctormap1
  
  let predctormap = predctormap1 @ predctormap0
  
  let classmap1 =
    classmap1 |> List.map
      begin fun (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist)) ->
        let preds =
          preds |> List.map
            begin function
              (g, (l, pmap, family, symb, Some body)) ->
              let tenv = (current_class, ClassOrInterfaceName cn)::("this", ObjType cn)::pmap in
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
        (cn, (lc, abstract, fin, methods, fds_opt, ctors, super, interfs, preds, pn, ilist))
      end
  
  (* Region: evaluation helpers; pushing and popping assumptions and execution trace elements *)
  
  let check_ghost ghostenv l e =
    expr_iter
      begin function
        Var (l, x, _) -> if List.mem x ghostenv then static_error l "Cannot read a ghost variable in a non-pure context." None
      | _ -> ()
      end
      e

  let funcnameterms = List.map (fun fn -> (fn, get_unique_var_symb fn (PtrType Void))) funcnames
  
  let struct_sizes =
    List.map
      begin fun (sn, _) ->
        let s = get_unique_var_symb ("struct_" ^ sn ^ "_size") IntType in
        ignore $. ctxt#assume (ctxt#mk_lt (ctxt#mk_intlit 0) s);
        (sn, s)
      end
      structmap
  
  let rec sizeof l t =
    match t with
      Void | Char | UChar -> ctxt#mk_intlit 1
    | ShortType | UShortType -> ctxt#mk_intlit 2
    | IntType | UintPtrType -> ctxt#mk_intlit 4
    | PtrType _ -> ctxt#mk_intlit 4
    | StructType sn -> List.assoc sn struct_sizes
    | StaticArrayType (elemTp, elemCount) -> ctxt#mk_mul (sizeof l elemTp) (ctxt#mk_intlit elemCount)
    | _ -> static_error l ("Taking the size of type " ^ string_of_type t ^ " is not yet supported.") None
  
  let field_offsets =
    flatmap
      begin
        function
          (sn, (_, Some fmap, _)) ->
          let offsets = flatmap (fun (f, (_, gh, _)) -> if gh = Ghost then [] else [((sn, f), get_unique_var_symb (sn ^ "_" ^ f ^ "_offset") IntType)]) fmap in
          begin
            match offsets with
              ((_, _), offset0)::_ ->
              ignore (ctxt#assume (ctxt#mk_eq offset0 (ctxt#mk_intlit 0)))
            | _ -> ()
          end;
          offsets
        | _ -> []
      end
      structmap
  
  let field_offset l fparent fname =
    match try_assoc (fparent, fname) field_offsets with
      Some term -> term
    | None -> static_error l "Cannot take the address of a ghost field" None
  
  let field_address l t fparent fname = ctxt#mk_add t (field_offset l fparent fname)
  
  let convert_provertype term proverType proverType0 =
    if proverType = proverType0 then term else apply_conversion proverType proverType0 term
  
  let prover_convert_term term t t0 =
    if t = t0 then term else convert_provertype term (provertype_of_type t) (provertype_of_type t0)

  let mk_nil () =
    let (_, _, _, _, nil_symb) = List.assoc "nil" purefuncmap in
    mk_app nil_symb []
  
  let mk_cons elem_tp head tail =
    let (_, _, _, _, cons_symb) = List.assoc "cons" purefuncmap in
    mk_app cons_symb [apply_conversion (provertype_of_type elem_tp) ProverInductive head; tail]
  
  let mk_all_eq elem_tp xs x =
    let (_, _, _, _, all_eq_symb) = List.assoc "all_eq" purefuncmap in
    mk_app all_eq_symb [xs; apply_conversion (provertype_of_type elem_tp) ProverInductive x]
  
  let rec mk_list elem_tp elems =
    match elems with
      [] -> mk_nil()
    | e::es -> mk_cons elem_tp e (mk_list elem_tp es)
  
  let mk_take n xs =
    let (_, _, _, _, take_symb) = List.assoc "take" purefuncmap in
    mk_app take_symb [n; xs]
  
  let mk_drop n xs =
    let (_, _, _, _, drop_symb) = List.assoc "drop" purefuncmap in
    mk_app drop_symb [n; xs]
  
  let mk_append l1 l2 =
    let (_, _, _, _, append_symb) = List.assoc "append" purefuncmap in
    mk_app append_symb [l1; l2]
  
  let mk_length l =
    let (_, _, _, _, length_symb) = List.assoc "length" purefuncmap in
    mk_app length_symb [l]
  
  let rec mk_zero_list n =
    assert (0 <= n);
    if n = 0 then
      mk_nil ()
    else
      mk_cons Char (ctxt#mk_intlit 0) (mk_zero_list (n - 1))
  
  let mk_char_list_of_c_string size s =
    let n = String.length s in
    let as_signed_char n = if 127 < n then n - 256 else n in
    let rec iter k =
      if k = n then
        mk_zero_list (size - n)
      else
        mk_cons Char (ctxt#mk_intlit (as_signed_char (Char.code s.[k]))) (iter (k + 1))
    in
    iter 0
  
  
  
  (* TODO: To improve performance, push only when branching, i.e. not at every assume. *)
  
  let assume t cont =
    stats#proverAssume;
    push_context (Assuming t);
    ctxt#push;
    let result =
      match ctxt#assume t with
        Unknown -> cont()
      | Unsat -> SymExecSuccess
    in
    pop_context();
    ctxt#pop;
    result
  
  let assume_eq t1 t2 cont = assume (ctxt#mk_eq t1 t2) cont
  let assume_neq t1 t2 cont = assume (ctxt#mk_not (ctxt#mk_eq t1 t2)) cont
  
  let query_term t = 
    stats#proverOtherQuery;
    (ctxt#query t)
  
  let assert_term t h env l msg url = 
    stats#proverOtherQuery;
    if not (ctxt#query t) then
      raise (SymbolicExecutionError (pprint_context_stack !contextStack, ctxt#pprint t, l, msg, url))

  let rec prover_type_term l tp = 
    match tp with
      ObjType(n) -> 
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
  
  let eval_op l op v1 v2 ts ass_term =
    let check_overflow l min t max =
      begin match ass_term with
        Some assert_term -> check_overflow l min t max assert_term
      | _ -> ()
      end;
      t
    in
    let bounds = if ass_term = None then (* in ghost code, where integer types do not imply limits *) None else 
    match ts with
      Some ([UintPtrType; _] | [_; UintPtrType]) -> Some (int_zero_term, max_ptr_term)
    | Some ([IntType; _] | [_; IntType]) -> Some (min_int_term, max_int_term)
    | Some ([ShortType; _] | [_; ShortType]) -> Some (min_short_term, max_short_term)
    | Some ([Char; _] | [_; Char]) -> Some (min_char_term, max_char_term)
    | _ -> None
    in
    begin match op with
      And -> ctxt#mk_and v1 v2
    | Or -> ctxt#mk_or v1 v2
    | Eq ->
      let Some [tp1; tp2] = ts in
      if (tp1, tp2) = (Bool, Bool) then
        ctxt#mk_iff v1 v2
      else
        ctxt#mk_eq v1 v2
    | Neq -> ctxt#mk_not (ctxt#mk_eq v1 v2)
    | Add ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        (IntType, IntType) ->
        check_overflow l min_int_term (ctxt#mk_add v1 v2) max_int_term
      | (PtrType t, IntType) ->
        let n = sizeof l t in
        check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_add v1 (ctxt#mk_mul n v2)) max_ptr_term
      | (RealType, RealType) ->
        ctxt#mk_real_add v1 v2
      | (ShortType, ShortType) ->
        check_overflow l min_short_term (ctxt#mk_add v1 v2) max_short_term
      | (Char, Char) ->
        check_overflow l min_char_term (ctxt#mk_add v1 v2) max_char_term
      | (UintPtrType, UintPtrType) ->
        check_overflow l min_uint_term (ctxt#mk_add v1 v2) max_uint_term
      | _ -> static_error l "Internal error in eval." None
      end
    | Sub ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        (IntType, IntType) ->
        check_overflow l min_int_term (ctxt#mk_sub v1 v2) max_int_term
      | (PtrType t, IntType) ->
        let n = sizeof l t in
        check_overflow l (ctxt#mk_intlit 0) (ctxt#mk_sub v1 (ctxt#mk_mul n v2)) max_ptr_term
      | (RealType, RealType) ->
        ctxt#mk_real_sub v1 v2
      | (ShortType, ShortType) ->
        check_overflow l min_short_term (ctxt#mk_sub v1 v2) max_short_term
      | (Char, Char) ->
        check_overflow l min_char_term (ctxt#mk_sub v1 v2) max_char_term
      | (PtrType (Char | Void), PtrType (Char | Void)) ->
        check_overflow l min_int_term (ctxt#mk_sub v1 v2) max_int_term
      | (UintPtrType, UintPtrType) ->
        check_overflow l min_uint_term (ctxt#mk_sub v1 v2) max_uint_term
      end
    | Mul ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        (IntType, IntType) ->
        check_overflow l min_int_term (ctxt#mk_mul v1 v2) max_int_term
      | (UintPtrType, UintPtrType) ->
        check_overflow l min_uint_term (ctxt#mk_mul v1 v2) max_uint_term
      | (RealType, RealType) ->
        ctxt#mk_real_mul v1 v2
      | (UShortType, UShortType) ->
        check_overflow l min_ushort_term (ctxt#mk_mul v1 v2) max_ushort_term
      | (UChar, UChar) ->
        check_overflow l min_uchar_term (ctxt#mk_mul v1 v2) max_uchar_term
      end
    | Le ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        ((IntType, IntType) | (PtrType _, PtrType _) |
         (UintPtrType, UintPtrType)) | (UShortType, UShortType) |
         (UChar, UChar)-> ctxt#mk_le v1 v2
      | (RealType, RealType) -> ctxt#mk_real_le v1 v2
      end
    | Lt ->
      let Some [tp1; tp2] = ts in
      begin match (tp1, tp2) with
        ((IntType, IntType) | (PtrType _, PtrType _) |
         (UintPtrType, UintPtrType)) | (UShortType, UShortType) |
         (UChar, UChar) -> ctxt#mk_lt v1 v2
      | (RealType, RealType) -> ctxt#mk_real_lt v1 v2
      end
    | Div ->
      begin match ts with
        Some ([RealType; RealType]) -> static_error l "Realdiv not supported yet in /=." None
      | Some ([IntType; IntType]) | Some([UShortType; UShortType]) | Some([UChar; UChar]) -> 
        begin match ass_term with
          Some assert_term -> assert_term l (ctxt#mk_not (ctxt#mk_eq v2 (ctxt#mk_intlit 0))) "Denominator might be 0." None
        | None -> ()
        end;
        (ctxt#mk_div v1 v2)
      end
    | BitAnd | BitXor | BitOr ->
      let symb = match op with
          BitAnd -> bitwise_and_symbol
        | BitXor -> bitwise_xor_symbol
        | BitOr -> bitwise_or_symbol
      in
      let app = ctxt#mk_app symb [v1;v2] in
      begin match bounds with
        None -> ()
      | Some(min_term, max_term) -> 
        ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_term app) (ctxt#mk_le app max_term)));
      end;
      app
    | ShiftRight -> 
      let app = ctxt#mk_app shiftright_symbol [v1;v2] in
      begin match bounds with
        None -> ()
      | Some(min_term, max_term) -> 
        ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le min_term app) (ctxt#mk_le app max_term)));
      end;
      app
    | Mod -> ctxt#mk_mod v1 v2
    | ShiftLeft when ts = Some [IntType; IntType] -> ctxt#mk_app shiftleft_int32_symbol [v1;v2]
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
    | Var (l, x, scope) ->
      cont state
      begin
        if !scope = None then print_endline (string_of_loc l);
        let (Some scope) = !scope in
        match scope with
          LocalVar -> (try List.assoc x env with Not_found -> assert_false [] env l (Printf.sprintf "Unbound variable '%s'" x) None)
        | PureCtor -> let Some (lg, tparams, t, [], s) = try_assoc x purefuncmap in mk_app s []
        | FuncName -> List.assoc x funcnameterms
        | PredFamName -> let Some (_, _, _, _, symb, _) = try_assoc x predfammap in symb
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
        | PureFuncName -> let (lg, tparams, t, tps, (fsymb, vsymb)) = List.assoc x purefuncmap in vsymb
      end
    | PredNameExpr (l, g) -> let Some (_, _, _, _, symb, _) = try_assoc g predfammap in cont state symb
    | CastExpr (l, truncating, ManifestTypeExpr (_, t), e) ->
      begin
        match (e, t, truncating) with
          (IntLit (_, n, _), PtrType _, _) ->
          if ass_term <> None && not (le_big_int zero_big_int n &&
le_big_int n max_ptr_big_int) then static_error l "CastExpr: Int literal is out of range." None;
          cont state (ctxt#mk_intlit_of_string (string_of_big_int n))
        | (e, Char, false) ->
          ev state e $. fun state t ->
          cont state (check_overflow l min_char_term t max_char_term)
        | (e, ShortType, false) ->
          ev state e $. fun state t ->
          cont state (check_overflow l min_short_term t max_short_term)
        | (e, IntType, false) ->
          ev state e $. fun state t ->
          cont state (check_overflow l min_int_term t max_int_term)
        | (e, Char, true) ->
          ev state e $. fun state t ->
          cont state (ctxt#mk_app truncate_int8_symbol [t])
        | (e, UChar, true) ->
          ev state e $. fun state t ->
          cont state (ctxt#mk_app truncate_uint8_symbol [t])
        | (e, ShortType, true) ->
          ev state e $. fun state t ->
          cont state (ctxt#mk_app truncate_int16_symbol [t])
        | (_, (ObjType _|ArrayType _), _) when ass_term = None -> static_error l "Class casts are not allowed in annotations." None
        | _ -> ev state e cont (* No other cast allowed by the type checker changes the value *)
      end
    | Upcast (e, fromType, toType) -> ev state e cont
    | WidenedParameterArgument e -> ev state e cont
    | RealLit(l, n) ->
      cont state begin 
        if eq_num n (num_of_big_int unit_big_int) then
        real_unit
            else
        ctxt#mk_reallit_of_num n
      end
    | IntLit (l, n, t) ->
      begin match !t with
        Some RealType ->
        cont state
          begin
            if eq_big_int n unit_big_int then
              real_unit
            else
              ctxt#mk_reallit_of_num (num_of_big_int n)
          end
      | Some t ->
        if ass_term <> None then
        begin
          let (min, max) =
            match t with 
              IntType -> (min_int_big_int, max_int_big_int)
            | UChar -> (min_uchar_big_int, max_uchar_big_int)
            | Char -> (min_char_big_int, max_char_big_int)
            | UShortType -> (min_ushort_big_int, max_ushort_big_int)
            | ShortType -> (min_short_big_int, max_short_big_int)
            | UintPtrType -> (zero_big_int, max_ptr_big_int)
            | PtrType _ -> (zero_big_int, max_ptr_big_int)
          in
          if not (le_big_int min n && le_big_int n max) then static_error l "IntLit: Int literal is out of range." None
        end;
        cont state
          begin
            try
              let n = int_of_big_int n in ctxt#mk_intlit n
            with Failure "int_of_big_int" -> ctxt#mk_intlit_of_string (string_of_big_int n)
          end
      end
    | ClassLit (l,s) -> cont state (List.assoc s classterms)
    | StringLit (l, s) ->
      if ass_term = None then static_error l "String literals are not allowed in ghost code." None;
      cont state
        begin match file_type path with
          Java -> get_unique_var_symb "stringLiteral" (ObjType "java.lang.String")
        | _ -> get_unique_var_symb "stringLiteral" (PtrType Char)
        end
    | WMethodCall (l, "java.lang.Object", "getClass", [], [target], Instance) ->
      ev state target $. fun state t ->
      cont state (ctxt#mk_app get_class_symbol [t])
    | WPureFunCall (l, g, targs, args) ->
      begin match try_assoc g predctormap with
        Some (PredCtorInfo(l, ps1, ps2, inputParamCount, body, (s, st))) ->
          evs state args $. fun state vs ->
          let fun_app = (mk_app (s, st) vs) in
          (if((List.length ps1) = (List.length vs)) then
            register_pred_ctor_application fun_app s st vs inputParamCount);
          cont state fun_app
      | None ->
        begin match try_assoc g purefuncmap with
          None -> static_error l ("No such pure function: "^g) None
        | Some (lg, tparams, t, pts, s) ->
          evs state args $. fun state vs ->
          cont state (mk_app s vs)
        end
      end
    | WPureFunValueCall (l, e, es) ->
      evs state (e::es) $. fun state (f::args) ->
      cont state (List.fold_left (fun f arg -> ctxt#mk_app apply_symbol [f; arg]) f args)
    | IfExpr (l, e1, e2, e3) ->
      evs state [e1; e2; e3] $. fun state [v1; v2; v3] ->
      cont state (ctxt#mk_ifthenelse v1 v2 v3) (* Only sound if e2 and e3 are side-effect-free *)
    | Operation (l, BitAnd, [e1; Operation (_, BitNot, [e2], ts2)], ts1) ->
      ev state e1 $. fun state v1 -> ev state e2 $. fun state v2 ->
      cont state (ctxt#mk_app bitwise_and_symbol [v1; ctxt#mk_app bitwise_not_symbol [v2]])
    | Operation (l, Not, [e], ts) -> ev state e $. fun state v -> cont state (ctxt#mk_not v)
    | Operation (l, BitNot, [e], ts) ->
      begin match !ts with
        Some [IntType] -> ev state e $. fun state v -> cont state (ctxt#mk_app bitwise_not_symbol [v])
      | _ ->
        static_error l "VeriFast does not currently support taking the bitwise complement (~) of an unsigned integer except as part of a bitwise AND (x & ~y)." None
      end
    | Operation (l, Div, [e1; e2], ts) ->
      begin match ! ts with
        Some ([RealType; RealType]) ->
        begin match (e1, e2) with
          (RealLit (_, n), IntLit (_, d, _)) when eq_num n (num_of_big_int unit_big_int) && eq_big_int d two_big_int -> cont state real_half
        | (IntLit (_, n, _), IntLit (_, d, _)) when eq_big_int n unit_big_int && eq_big_int d two_big_int -> cont state real_half
        | _ -> 
          let rec eval_reallit e =
              match e with
              IntLit (l, n, t) -> num_of_big_int n
            | RealLit (l, n) -> n
            | _ -> static_error (expr_loc e) "The denominator of a division must be a literal." None
          in
          ev state e1 $. fun state v1 -> cont state (ctxt#mk_real_mul v1 (ctxt#mk_reallit_of_num (div_num (num_of_int 1) (eval_reallit e2)))) 
        end
      | Some ([IntType; IntType]) -> 
        ev state e1 $. fun state v1 -> ev state e2 $. fun state v2 -> 
        begin match ass_term with
          Some assert_term -> assert_term l (ctxt#mk_not (ctxt#mk_eq v2 (ctxt#mk_intlit 0))) "Denominator might be 0." None
        | None -> ()
        end;
        cont state (ctxt#mk_div v1 v2)
      end
    | Operation (l, BitAnd, [e1; IntLit(_, i, _)], ts) when le_big_int zero_big_int i && ass_term <> None -> (* optimization *)
      ev state e1 $. fun state v1 ->
        let iterm = ctxt#mk_intlit (int_of_big_int i) in
        let app = ctxt#mk_app bitwise_and_symbol [v1;iterm] in
        ignore (ctxt#assume (ctxt#mk_and (ctxt#mk_le int_zero_term app) (ctxt#mk_le app iterm)));
        begin if eq_big_int i unit_big_int then
          ignore (ctxt#assume (ctxt#mk_eq (ctxt#mk_mod v1 (ctxt#mk_intlit 2)) app));
        end;
        cont state app
    | Operation (l, op, ([e1; e2] as es), ts) ->
      evs state es $. fun state [v1; v2] -> cont state (eval_op l op v1 v2 !ts ass_term) 
    | ArrayLengthExpr (l, e) ->
      ev state e $. fun state t ->
      begin match ass_term with
        Some assert_term -> assert_term l (ctxt#mk_not (ctxt#mk_eq t (ctxt#mk_intlit 0))) "Target of array length expression might be null" None
      | None -> ()
      end;
      cont state (ctxt#mk_app arraylength_symbol [t])
    | WRead(l, e, fparent, fname, frange, fstatic, fvalue, fghost) ->
      if fstatic then
        cont state
          begin match !fvalue with
            Some (Some v) ->
            begin match v with
              IntConst n -> ctxt#mk_intlit_of_string (string_of_big_int n)
            | BoolConst b -> if b then ctxt#mk_true else ctxt#mk_false
            | StringConst s -> static_error l "String constants are not yet supported." None
            | NullConst -> ctxt#mk_intlit 0
            end
          | _ ->
            match read_field with
              None -> static_error l "Cannot use field read expression in this context." None
            | Some (read_field, read_static_field, deref_pointer, read_array) -> read_static_field l fparent fname
          end
      else
        ev state e $. fun state v ->
        begin
          match frange with
            StaticArrayType (elemTp, elemCount) ->
            cont state (field_address l v fparent fname)
          | _ ->
          match read_field with
            None -> static_error l "Cannot use field dereference in this context." None
          | Some (read_field, read_static_field, deref_pointer, read_array) -> cont state (read_field l v fparent fname)
        end
    | WReadArray(l, arr, tp, i) ->
      evs state [arr; i] $. fun state [arr; i] ->
      begin
        match read_field with
          None -> static_error l "Cannot use array indexing in this context." None
        | Some (read_field, read_static_field, deref_pointer, read_array) -> cont state (read_array l arr i tp)
      end
    | Deref (l, e, t) ->
      ev state e $. fun state v ->
      begin
        match read_field with
          None -> static_error l "Cannot perform dereference in this context." None
        | Some (read_field, read_static_field, deref_pointer, read_array) ->
          let (Some t) = !t in
          cont state (deref_pointer l v t)
      end
    | AddressOf (l, e) ->
      begin
        match e with
          WRead (le, e, fparent, fname, frange, fstatic, fvalue, fghost) -> 
          (* MS Visual C++ behavior: http://msdn.microsoft.com/en-us/library/hx1b6kkd.aspx (= depends on command-line switches and pragmas) *)
          (* GCC documentation is not clear about it. *)
          ev state e $. fun state v ->
          cont state (field_address l v fparent fname)
        | Var (l, x, scope) when !scope = Some GlobalName ->
          let Some (l, tp, symbol, init) = try_assoc x globalmap in cont state symbol
        (* The address of a function symbol is commonly used in the
           assignment of function pointers. We tread (&function) in the
           same way as (function), which is what most compilers do: *)
        | Var (l, x, scope) when !scope = Some FuncName ->
            cont state (List.assoc x funcnameterms)
        | _ -> static_error l "Taking the address of this expression is not supported." None
      end
    | SwitchExpr (l, e, cs, cdef_opt, tref) ->
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
      let (Some (tt, tenv, targs, tp)) = !tref in
      let symbol = ctxt#mk_symbol g (typenode_of_type tt :: List.map (fun (x, _) -> typenode_of_type (List.assoc x tenv)) env) (typenode_of_type tp) (Proverapi.Fixpoint 0) in
      let case_clauses = List.map (fun (SwitchExprClause (_, cn, ps, e)) -> (cn, (ps, e))) cs in
      let InductiveType (i, targs) = tt in
      let (_, _, ctormap, _) = List.assoc i inductivemap in
      let fpclauses =
        List.map
          begin fun (cn, (_, (_, tparams, _, pts, (csym, _)))) ->
            match try_assoc cn case_clauses with
              Some (ps, e) ->
              let apply (_::gvs) cvs =
                let Some genv = zip (List.map (fun (x, t) -> x) env) gvs in
                let Some penv = zip ps cvs in
                let penv =
                  if tparams = [] then penv else
                  let Some penv = zip penv pts in
                  let Some tpenv = zip tparams targs in
                  List.map
                    (fun ((pat, term), typ) ->
                     match unfold_inferred_type typ with
                       TypeParam x -> (pat, convert_provertype term ProverInductive (provertype_of_type (List.assoc x tpenv)))
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
                let Some genv = zip (List.map (fun (x, t) -> x) env) gvs in
                eval_core None None genv e
              in
              (csym, apply)
          end
          ctormap
      in
      ctxt#set_fpclauses symbol 0 fpclauses;
      cont state (ctxt#mk_app symbol (t::List.map (fun (x, t) -> t) env))
    | ProverTypeConversion (tfrom, tto, e) -> ev state e $. fun state v -> cont state (convert_provertype v tfrom tto)
    | SizeofExpr (l, ManifestTypeExpr (_, t)) ->
      cont state (sizeof l t)
    | InstanceOfExpr(l, e, ManifestTypeExpr (l2, tp)) ->
      ev state e $. fun state v ->
        begin match tp with (* hack: if tp is a final class, then instanceof is translated as getClass *)
          ObjType(c) when get_class_finality c = FinalClass -> cont state (ctxt#mk_eq (prover_type_term l2 tp) (ctxt#mk_app get_class_symbol [v]))
        | _ -> cont state (ctxt#mk_app instanceof_symbol [v; prover_type_term l2 tp])
        end
    | _ -> static_error (expr_loc e) "Construct not supported in this position." None
  
  let rec eval_core ass_term read_field env e =
    let rec ev () e cont = eval_core_cps0 eval_core ev () ass_term read_field env e cont in
    ev () e $. fun () v -> v
  
  let eval_core_cps ev state ass_term read_field env e cont = eval_core_cps0 eval_core ev state ass_term read_field env e cont
  
  let eval read_field env e = eval_core None read_field env e

  let _ =
    List.iter
    begin function
       (g, (l, t, pmap, Some index, SwitchExpr (_, Var (_, x, _), cs, _, _), pn, ilist, fsym)) ->
       let rec index_of_param i x0 ps =
         match ps with
           [] -> assert false
         | (x, tp)::ps -> if x = x0 then (i, tp) else index_of_param (i + 1) x0 ps
       in
       let (i, InductiveType (_, targs)) = index_of_param 0 x pmap in
       let clauses =
         List.map
           (function SwitchExprClause (_, cn, pats, e) ->
              let (_, tparams, _, ts, (ctorsym, _)) = match try_assoc' (pn,ilist) cn purefuncmap with Some x -> x in
              let eval_body gts cts =
                let Some pts = zip pmap gts in
                let penv = List.map (fun ((p, tp), t) -> (p, t)) pts in
                let Some patenv = zip pats cts in
                let patenv = List.filter (fun (x, t) -> x <> "_") patenv in
                let patenv =
                  if tparams = [] then patenv else
                  let Some tpenv = zip tparams targs in
                  let Some patenv = zip patenv ts in
                  List.map
                    (fun ((x, term), typ) ->
                     let term =
                     match unfold_inferred_type typ with
                       TypeParam x -> convert_provertype term ProverInductive (provertype_of_type (List.assoc x tpenv))
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
       ctxt#set_fpclauses fsym i clauses
     | (g, (l, t, pmap, None, w, pn, ilist, fsym)) ->
       ctxt#begin_formal;
       let env = imap (fun i (x, tp) -> let pt = typenode_of_type tp in (pt, (x, ctxt#mk_bound i pt))) pmap in
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
