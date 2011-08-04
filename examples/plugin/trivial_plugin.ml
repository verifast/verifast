open Plugins
open Plugins2

let (create_typechecked_assertion, match_typechecked_assertion) = DynType.create_ctor ()

let (create_state, match_state) = DynType.create_ctor ()

let typecheck_assertion tenv text =
  try
    let value = int_of_string text in
    (TypecheckedPluginAssertion (create_typechecked_assertion value), [])
  with
    Failure "int_of_string" -> raise (PluginStaticError (0, String.length text, "Integer literal expected"))

let create_instance ctxt =
  object
    method empty_state = PluginState (create_state 0)
    method check_leaks (PluginState state) = let (Some s) = match_state state in if s <> 0 then Some "Function leaks trivial resource" else None
    method produce_assertion: 'a. plugin_state -> 'term environment -> typechecked_plugin_assertion -> (plugin_state -> 'term environment -> 'a) -> 'a =
      fun (PluginState s) env (TypecheckedPluginAssertion asn) cont ->
      let Some s = match_state s in
      let Some asn = match_typechecked_assertion asn in
      cont (PluginState (create_state (s + asn))) env
    method consume_assertion: 'a. plugin_state -> 'term environment -> typechecked_plugin_assertion -> (plugin_state -> 'term environment -> 'a) -> 'a =
      fun (PluginState s) env (TypecheckedPluginAssertion asn) cont ->
      let Some s = match_state s in
      let Some asn = match_typechecked_assertion asn in
      if s < asn then raise (PluginConsumeError (0, 1, "Insufficient trivial resource"));
      cont (PluginState (create_state (s - asn))) env
    method string_of_state (PluginState state) = let (Some s) = match_state state in string_of_int s
  end

let plugin = object
  method typecheck_assertion = typecheck_assertion
  method create_instance: 'term. 'term context -> 'term plugin_instance = create_instance
end

let () = register_plugin plugin