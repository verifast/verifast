open Plugins

let register_plugin_func: (plugin -> unit) ref = ref (fun _ -> failwith "register_plugin called at an unexpected time")

exception LoadPluginError of string

let loaded_plugins = ref []  (* O'Caml does not seem to garbage collect loaded modules. This prevents memory leaks in long-running vfide sessions. *)

let load_plugin path =
  if List.mem_assoc path !loaded_plugins then List.assoc path !loaded_plugins else
  let old_func = !register_plugin_func in
  let plugin = ref None in
  register_plugin_func := (fun p -> match !plugin with None -> plugin := Some p | _ -> failwith "register_plugin called more than once");
  let restore_register_plugin_func () = register_plugin_func := old_func in
  try
    try
      Dynlink.loadfile_private (path ^ ".cmxs");
      restore_register_plugin_func ();
      match !plugin with
        None -> failwith "plugin did not call register_plugin"
      | Some p ->
        loaded_plugins := (path, p)::!loaded_plugins;
        p
    with e ->
      restore_register_plugin_func ();
      raise e
  with Dynlink.Error e -> raise (LoadPluginError (Dynlink.error_message e))
