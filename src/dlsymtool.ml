let error msg =
  Printf.fprintf stderr "%s\n" msg;
  exit 1
let input_line_and_trim file =
  let line = input_line file in
  let n = String.length line in
  if n > 0 && line.[n - 1] = '\r' then String.sub line 0 (n - 1) else line

let read_specfile specpath =
  try
    let specfile = open_in specpath in
    let symbol = input_line_and_trim specfile in
    let header = input_line_and_trim specfile in
    let funtype = input_line_and_trim specfile in
    let unloadable = input_line_and_trim specfile in
    close_in specfile;
    let unloadable = match unloadable with "unloadable" -> true | "not unloadable" -> false | _ -> error "Fourth line of spec file must be either 'unloadable' or 'not unloadable'" in
    (symbol, header, funtype, unloadable)
  with
    Sys_error s -> error (Printf.sprintf "Could not read spec file '%s': %s" specpath s)
  | End_of_file -> error "Premature end of file while reading spec file '%s'. Four lines required."

let () =
  match Sys.argv with
  | [| _; specpath |] ->
    let (symbol, header, funtype, unloadable) = read_specfile specpath in
    let specname = Filename.chop_extension (Filename.basename specpath) in
    let proxypath = Filename.concat (Filename.dirname specpath) (Printf.sprintf "%s_proxy" specname) in
    let proxyheaderpath = proxypath ^ ".h" in
    begin
      try
        let file = open_out proxyheaderpath in
        Printf.fprintf file "/* Automatically generated from %s */\n" (Filename.basename specpath);
        let define = String.uppercase_ascii specname ^ "_PROXY_H" in
        Printf.fprintf file "#ifndef %s\n" define;
        Printf.fprintf file "#define %s\n" define;
        Printf.fprintf file "\n";
        Printf.fprintf file "#include \"libraries.h\"\n";
        Printf.fprintf file "#include \"%s\"\n" header;
        Printf.fprintf file "\n";
        Printf.fprintf file "%s *library_lookup_symbol_%s(struct library *library);\n" funtype symbol;
        if unloadable then begin
          Printf.fprintf file "    //@ requires [?f]library(library, ?mainModule);\n";
          Printf.fprintf file "    //@ ensures [f]library(library, mainModule) &*& [_]is_%s(result, mainModule);\n" funtype;
        end else begin
          Printf.fprintf file "    //@ requires [_]library(library, ?mainModule);\n";
          Printf.fprintf file "    //@ ensures [_]is_%s(result, mainModule);\n" funtype;
        end;
        Printf.fprintf file "\n";
        Printf.fprintf file "#endif\n";
        close_out file;
        Printf.fprintf stderr "Written %s\n" proxyheaderpath
      with
        Sys_error s -> error (Printf.sprintf "Could not write proxy header file '%s': %s" proxyheaderpath s)
    end;
    let proxyimplpath = proxypath ^ ".c" in
    begin
      try
        let file = open_out proxyimplpath in
        Printf.fprintf file "/* Automatically generated from %s */\n" (Filename.basename specpath);
        Printf.fprintf file "#include \"libraries.h\"\n";
        Printf.fprintf file "#include \"%s\"\n" header;
        Printf.fprintf file "#include \"%s_proxy.h\"\n" specname;
        Printf.fprintf file "\n";
        Printf.fprintf file "%s *library_lookup_symbol_%s(struct library *library)\n" funtype symbol;
        Printf.fprintf file "{\n";
        Printf.fprintf file "    return library_lookup_symbol(library, \"%s\");\n" symbol;
        Printf.fprintf file "}\n";
        close_out file;
        Printf.fprintf stderr "Written %s\n" proxyimplpath
      with
        Sys_error s -> error (Printf.sprintf "Could not write proxy implementation file '%s': %s" proxyimplpath s)
    end;
    let proxymanifestpath = proxypath ^ ".vfmanifest" in
    begin
      try
        let file = open_out proxymanifestpath in
        Printf.fprintf file ".provides .\\%s_proxy.h#library_lookup_symbol_%s\n" specname symbol;
        close_out file;
        Printf.fprintf stderr "Written %s\n" proxymanifestpath
      with
        Sys_error s -> error (Printf.sprintf "Could not write proxy manifest file '%s': %s" proxymanifestpath s)
    end
  | [| _; specpath; modulename |] ->
    let (symbol, header, funtype, unloadable) = read_specfile specpath in
    let specname = Filename.chop_extension (Filename.basename specpath) in
    let manifestpath = Filename.concat (Filename.dirname specpath) (Printf.sprintf "%s_%s.vfmanifest" specname modulename) in
    begin
      try
        let manifest = open_out manifestpath in
        Printf.fprintf manifest ".produces module %s\n" modulename;
        Printf.fprintf manifest ".provides .\\%s#%s : %s(%s)%s\n" header symbol funtype modulename (if unloadable then " unloadable" else "");
        close_out manifest;
        Printf.fprintf stderr "Written %s\n" manifestpath
      with
        Sys_error s -> error (Printf.sprintf "Could not write manifest file '%s': %s" manifestpath s)
    end
  | _ ->
    error
      begin
      "invalid command line\n" ^
      "DLL dynamic symbol lookup verification helper tool\n" ^
      "Usage:\n" ^
      "  dlsymtool specpath\n" ^
      "    Generate proxy header, proxy implementation, and proxy manifest\n" ^
      "    for use by client code that dynamically loads DLLs that implement\n" ^
      "    the DLL specification at 'specpath'\n" ^
      "  dlsymtool specpath modulename\n" ^
      "    Generate a manifest file that describes the elements to be provided\n" ^
      "    by a DLL that implements the DLL specification at 'specpath' and\n" ^
      "    whose main module is called 'modulename'\n" ^
      "DLL specification file format:\n" ^
      "  The file must consist of four lines. The meaning of each line is as follows:\n" ^
      "  1. symbol: the symbol exported by the DLL (only one symbol per spec)\n" ^
      "  2. header: the header file that declares the function type specified in line 3\n" ^
      "  3. functype: the name of the function type to be implemented by the exported symbol\n" ^
      "     This function type must take exactly one function type argument:\n" ^
      "     the module name of the main module of the DLL\n" ^
      "  4. either \"unloadable\" or \"not unloadable\". Indicates whether the DLL is unloadable"
      end
