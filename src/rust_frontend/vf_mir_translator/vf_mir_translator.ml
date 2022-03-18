module TestDataHardCoded = struct
  let c_func_main =
    let dloc = Ast.Lexed Ast.dummy_loc0 in
    let contract = Some (Ast.True dloc, Ast.True dloc) in
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
end

module VfMirStub = Vf_mir.Make (Capnp.BytesMessage)
module VfMirRd = VfMirStub.Reader.VfMir

let translate_vf_mir (mir : VfMirRd.t) =
  let decls = [ TestDataHardCoded.c_func_main ] in
  ([ (*headers*) ], [ Ast.PackageDecl (Ast.dummy_loc, "", [], decls) ])
