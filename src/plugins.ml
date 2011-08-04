type typechecked_plugin_assertion = TypecheckedPluginAssertion of DynType.dyn

type variable_type =
  StructPointerType of string (* struct name *)
| VeriFastInternalType
| PluginInternalType of DynType.dyn

type type_environment = (string * variable_type) list

exception PluginStaticError of int (* offset of error in assertion *) * int (* length of error in assertion *) * string (* error message *)

type plugin_state = PluginState of DynType.dyn

type 'term environment = (string * 'term) list

type term_type = PointerTerm | IntTerm | CharListTerm

type rel = Eq | Neq | Lt

type 'term context = <
  mk_symbol: string -> term_type -> 'term;
  query_formula: 'term -> rel -> 'term -> bool;
  push: unit;
  assert_formula: 'term -> rel -> 'term -> bool; (* true if the context has become inconsistent *)
  pop: unit;
>

exception PluginConsumeError of int * int * string

type 'term plugin_instance = <
  empty_state: plugin_state;
  check_leaks: plugin_state -> string option;
  produce_assertion: 'a. plugin_state -> 'term environment -> typechecked_plugin_assertion -> (plugin_state -> 'term environment -> 'a) -> 'a;
  consume_assertion: 'a. plugin_state -> 'term environment -> typechecked_plugin_assertion -> (plugin_state -> 'term environment -> 'a) -> 'a;
  string_of_state: plugin_state -> string (* For display in the IDE *)
>
  
type plugin = <
  (** [plugin_typecheck_assertion tenv asn] returns a typechecked version of [asn] as well as a list of the variables bound by the assertion, with their types.
      An assertion must not bind variables that are already bound. (I.e., [tenv] and the returned type environment must have disjoint domains.)
      If an error is found, raise a [PluginStaticError (off, len, msg)] exception, specifying the offset and length of the erroneous snippet in the assertion
      string, and an appropriate error message.
    *)
  typecheck_assertion: type_environment -> string -> typechecked_plugin_assertion * type_environment;
  (** Creates an instance of the plugin for a particular type of SMT solver terms. *)
  create_instance: 'term. 'term context -> 'term plugin_instance
>
