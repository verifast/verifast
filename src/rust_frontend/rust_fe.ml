let parse_rs_file (path : string) =
  let dloc = Ast.Lexed Ast.dummy_loc0 in
  let contract = Some (Ast.True dloc, Ast.True dloc) in
  let main_func =
    Ast.Func
      ( dloc,
        Ast.Regular,
        [],
        Some (Ast.ManifestTypeExpr (dloc, Ast.Int (Ast.Signed, Ast.IntRank))),
        "main",
        [],
        false,
        None,
        contract,
        true,
        Some
          ( [
              Ast.ReturnStmt
                ( dloc,
                  Some
                    (Ast.IntLit
                       ( dloc,
                         Big_int.zero_big_int,
                         true (* decimal *),
                         false (* U suffix *),
                         Ast.NoLSuffix (* int literal*) )) );
            ],
            dloc ),
        Ast.Static,
        Ast.Package )
  in
  let decls = [ main_func ] in
  ([ (*headers*) ], [ Ast.PackageDecl (dloc, "", [], decls) ])
