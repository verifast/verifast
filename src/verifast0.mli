val lookup : ('a * 'b) list -> 'a -> 'b
val update : ('a * 'b) list -> 'a -> 'b -> ('a * 'b) list
val string_of_env : (string * string) list -> string
val is_lemma : Ast.func_kind -> bool
val printff : ('a, out_channel, unit, unit) format4 -> 'a
type 'a pat0 = SrcPat of Ast.pat | TermPat of 'a
type chunk_info =
    PredicateChunkSize of int
  | PluginChunkInfo of Plugins.plugin_state
type 'a chunk =
    Chunk of ('a * bool) * Ast.type_ list * 'a * 'a list * chunk_info option
type 'a heap = 'a chunk list
type 'a env = (string * 'a) list
type 'a context =
    Assuming of 'a
  | Executing of 'a heap * 'a env * Lexer.loc * string
  | PushSubcontext
  | PopSubcontext
val get_callers : 'a context list -> Lexer.loc option list
val get_root_caller : 'a context list -> Lexer.loc option
val string_of_type : Ast.type_ -> string
val string_of_targs : Ast.type_ list -> string
val string_of_chunk : string chunk -> string
val string_of_heap : string chunk list -> string
val string_of_context : string context -> string
exception SymbolicExecutionError of string context list * string *
            Lexer.loc * string * string option
val full_name : string -> string -> string
type options = {
  option_verbose : int;
  option_disable_overflow_check : bool;
  option_allow_should_fail : bool;
  option_emit_manifest : bool;
  option_allow_assume : bool;
  option_simplify_terms : bool;
  option_runtime : string option;
  option_run_preprocessor : bool;
  option_provides : string list;
  option_keep_provide_files : bool;
  option_include_paths: string list;
}
type symexec_result = SymExecSuccess
