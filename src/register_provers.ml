let register_provers () =
  VerifastPluginRedux.register_plugin ();
  VerifastPluginZ3v4dot5.register_plugin ()
