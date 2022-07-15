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

module type VF_MIR_TRANSLATOR_ARGS = sig
  val data_model_opt : Ast.data_model option

  val report_should_fail : string -> Ast.loc0 -> unit

  val report_range : Lexer.range_kind -> Ast.loc0 -> unit
end

module Make (Args : VF_MIR_TRANSLATOR_ARGS) = struct
  module VfMirAnnotParser = Vf_mir_annot_parser.Make (Args)
  module VfMirStub = Vf_mir.Make (Capnp.BytesMessage)
  module VfMirRd = VfMirStub.Reader.VfMir
  module BodyRd = VfMirStub.Reader.Body
  module ContractRd = BodyRd.Contract
  module AnnotationRd = BodyRd.Annotation

  let translate_contract (contract_cpn : ContractRd.t) =
    let annots_cpn = ContractRd.annotations_get_list contract_cpn in
    let annots = List.map AnnotationRd.raw_get annots_cpn in
    VfMirAnnotParser.parse_func_contract annots

  let translate_body (body_cpn : BodyRd.t) =
    let open BodyRd in
    let def_kind_cpn = def_kind_get body_cpn in
    let def_kind = DefKind.get def_kind_cpn in
    match def_kind with
    | DefKind.Fn ->
        let dloc = Ast.Lexed Ast.dummy_loc0 in
        let def_path = def_path_get body_cpn in
        let contract_cpn = contract_get body_cpn in
        let nonghost_callers_only, fn_type_clause, pre_post, terminates =
          translate_contract contract_cpn
        in
        Ast.Func
          ( dloc,
            Ast.Regular,
            [],
            Some
              (Ast.ManifestTypeExpr (dloc, Ast.Int (Ast.Signed, Ast.IntRank))),
            def_path,
            [],
            nonghost_callers_only,
            fn_type_clause,
            pre_post,
            terminates,
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
    | _ -> failwith "Unknown MIR Body kind"

  let translate_vf_mir (vf_mir_cpn : VfMirRd.t) =
    let bodies_cpn = VfMirRd.bodies_get_list vf_mir_cpn in
    let decls = List.map translate_body bodies_cpn in
    ([ (*headers*) ], [ Ast.PackageDecl (Ast.dummy_loc, "", [], decls) ])
end
