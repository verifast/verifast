open Printf
open Util
open Lexer
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
| PluginChunkInfo of Plugins.plugin_state
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
type 'termnode context =
  Assuming of 'termnode
| Executing of 'termnode heap * 'termnode env * loc * string
| PushSubcontext
| PopSubcontext
type node = Node of string * int list * node list ref

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

let rec string_of_type t =
  match t with
    Bool -> "bool"
  | Void -> "void"
  | IntType -> "int"
  | UShortType -> "ushort"
  | ShortType -> "short"
  | UintPtrType -> "uintptr_t"
  | RealType -> "real"
  | UChar -> "uint8"
  | Char -> "int8"
  | InductiveType (i, []) -> i
  | InductiveType (i, targs) -> i ^ "<" ^ String.concat ", " (List.map string_of_type targs) ^ ">"
  | ObjType l -> "class " ^ l
  | StructType sn -> "struct " ^ sn
  | PtrType t -> string_of_type t ^ " *"
  | FuncType ft -> ft
  | PredType (tparams, ts, inputParamCount) ->
    let tparamsText = if tparams = [] then "" else "<" ^ String.concat ", " tparams ^ ">" in
    let paramTypesText =
      let typesText ts = String.concat ", " (List.map string_of_type ts) in
      match inputParamCount with
        None -> typesText ts
      | Some n ->
        let (ts1, ts2) = take_drop n ts in
        typesText ts1 ^ ";" ^ if ts2 = [] then "" else " " ^ typesText ts2
    in
    Printf.sprintf "predicate%s(%s)" tparamsText paramTypesText
  | PureFuncType (t1, t2) ->
    let (pts, rt) =  (* uncurry *)
      let rec iter pts rt =
        match rt with
          PureFuncType (t1, t2) -> iter (t1::pts) t2
        | _ -> (List.rev pts, rt)
      in
      iter [t1] t2
    in
    Printf.sprintf "fixpoint(%s, %s)" (String.concat ", " (List.map string_of_type pts)) (string_of_type rt)
  | BoxIdType -> "box"
  | HandleIdType -> "handle"
  | AnyType -> "any"
  | TypeParam x -> x
  | InferredType t -> begin match !t with None -> "?" | Some t -> string_of_type t end
  | ArrayType(t) -> (string_of_type t) ^ "[]"
  | StaticArrayType(t, s) -> (string_of_type t) ^ "[" ^ (string_of_int s) ^ "]" 
  | ClassOrInterfaceName(n) -> n (* not a real type; used only during type checking *)
  | PackageName(n) -> n (* not a real type; used only during type checking *)
  | RefType(t) -> "ref " ^ (string_of_type t)

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

exception SymbolicExecutionError of string context list * string * loc * string * string option

let full_name pn n = if pn = "" then n else pn ^ "." ^ n

type options = {
  option_verbose: int;
  option_disable_overflow_check: bool;
  option_allow_should_fail: bool;
  option_emit_manifest: bool;
  option_allow_assume: bool;
  option_simplify_terms: bool;
  option_runtime: string option;
  option_provides: string list;
  option_keep_provide_files: bool;
  option_include_paths: string list;
  option_safe_mode: bool; (* for invocation through web interface *)
  option_header_whitelist: string list;
  option_use_java_frontend : bool
} (* ?options *)

(* Region: verify_program_core: the toplevel function *)

(* result of symbolic execution; used instead of unit to detect branches not guarded by push and pop calls *)
type symexec_result = SymExecSuccess



(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)
(*+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++*)

(* To be moved to other location *)

(*let compare_packages p1 p2 =
  let write_to_file p name =
    let sexpr = SExpressions.string_of_sexpression ~margin:4 (SExpressionEmitter.sexpr_of_package p) in
    let file = open_out name in
    Printf.fprintf file "AST:\n%s" sexpr;
    close_out file
  in
  write_to_file p1 "sexpr1.txt";
  write_to_file p2 "sexpr2.txt";
  Sys.command "diff sexpr1.txt sexpr2.txt"*)

let parse_java_file (path: string) (reportRange: range_kind -> loc -> unit) reportShouldFail use_java_frontend: package =
  if (Filename.check_suffix path ".javaspec") || not (use_java_frontend) then
    Parser.parse_java_spec_file path reportRange reportShouldFail
  else begin
(*     let original = Parser.parse_java_spec_file path reportRange reportShouldFail in *)
    let ast_server_launch =
      try Sys.getenv "VERIFAST_JAVA_AST_SERVER"  
      with Not_found ->
        let error_message =
          "\nYou specified the option -javac to use the Java frontend. " ^
          "However, to use the Java frontend, you need to retrieve the file ast_server.jar from: \n" ^
              "\t https://bitbucket.org/gijsv/stance-java-frontend \n" ^
           "Then you must set the environment variable VERIFAST_JAVA_AST_SERVER as follows: \n" ^
              "\t export VERIFAST_JAVA_AST_SERVER=\"java -jar path_to_ast_server_jar\" \n"
        in
        Printf.printf "%s" error_message;
        failwith error_message
    in
    let ann_checker = new Annotation_type_checker.dummy_ann_type_checker () in
    let package = 
      try
        Java_frontend.attach(ast_server_launch);
        let options = [Java_frontend.desugar; Java_frontend.bodyless_methods_own_trailing_annotations] in
        Java_frontend.ast_from_java_file path options ann_checker
      with
        Java_frontend.JavaFrontendException(l, m) -> 
          let message = 
            String.concat "  ||" (Misc.split_string '\n' m)
          in
          match l with
            Some l -> raise (Lexer.ParseException(l, message))
          | None -> raise (Parser.CompilationError message)
    in
    let annotations = ann_checker#retrieve_annotations () in
    let result = Ast_translator.translate_ast package annotations in
(* compare_packages original result; *)
    result
  end
