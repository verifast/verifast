open Plugins
open Plugins2

let gt (Some x) = x

let mk_dtasn, gt_dtasn = DynType.create_ctor ()
let mk_ptasn tasn = TypecheckedPluginAssertion (mk_dtasn tasn)
let gt_ptasn (TypecheckedPluginAssertion dtasn) = gt (gt_dtasn dtasn)

let mk_dstate, gt_dstate = DynType.create_ctor ()
let mk_pstate state = PluginState (mk_dstate state)
let gt_pstate (PluginState dstate) = gt (gt_dstate dstate)

let (>>) f g x = g (f x)

let typecheck_assertion tenv text =
  try
    mk_ptasn (int_of_string text), []
  with
    Failure "int_of_string" -> raise (PluginStaticError (0, String.length text, "Integer literal expected"))

let create_instance ctxt =
  object
    method empty_state = mk_pstate 0
    method check_leaks pstate = if gt_pstate pstate <> 0 then Some "Function leaks trivial resource" else None
    method produce_assertion: 'a. plugin_state -> 'term environment -> typechecked_plugin_assertion -> (plugin_state -> 'term environment -> 'a) -> 'a =
      fun pstate env ptasn cont ->
      cont (mk_pstate (gt_pstate pstate + gt_ptasn ptasn)) env
    method consume_assertion: 'a. plugin_state -> 'term environment -> typechecked_plugin_assertion -> (plugin_state -> 'term environment -> 'a) -> 'a =
      gt_pstate >> fun state env -> gt_ptasn >> fun tasn cont ->
      if state < tasn then raise (PluginConsumeError (0, 1, "Insufficient trivial resource"));
      cont (mk_pstate (state - tasn)) env
    method string_of_state pstate = string_of_int (gt_pstate pstate)
  end

let plugin = object
  method typecheck_assertion = typecheck_assertion
  method create_instance: 'term. 'term context -> 'term plugin_instance = create_instance
end

let () = register_plugin plugin