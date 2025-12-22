From VeriFast Require Export VfMir.

Definition bodies := [
    ("reverse_iter", {|
        inputs := [RawPtr (Uint U8); RawPtr (Uint U8)];
        output := RawPtr (Uint U8);
        local_decls := [
            ("$_0", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("n", {| mutability := Not; ty := RawPtr (Uint U8) |});
            ("m", {| mutability := Not; ty := RawPtr (Uint U8) |});
            ("$_3", {| mutability := Not; ty := Tuple0 |});
            ("$_4", {| mutability := Not; ty := Tuple0 |});
            ("$_5", {| mutability := Mut; ty := Bool |});
            ("$_6", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_7", {| mutability := Mut; ty := Never |});
            ("k", {| mutability := Not; ty := RawPtr (Uint U8) |});
            ("$_9", {| mutability := Mut; ty := RawPtr (RawPtr (Uint U8)) |});
            ("$_10", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_11", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_12", {| mutability := Mut; ty := RawPtr (RawPtr (Uint U8)) |});
            ("$_13", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_14", {| mutability := Not; ty := Tuple0 |});
            ("$_15", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_16", {| mutability := Mut; ty := RawPtr (Uint U8) |})
        ];
        basic_blocks := [
            ("0", {|
                statements := [
                    StorageLive "$_3"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "VeriFast_ghost_command" GALNil));
                    destination := ("$_3", []);
                    target := Some "1"
                |}
            |});
            ("1", {|
                statements := [
                    StorageDead "$_3";
                    StorageLive "$_4";
                    StorageLive "$_5";
                    StorageLive "$_6";
                    Assign ("$_6", []) (Use (Copy ("n", [])))
                ];
                terminator := Call {|
                    args := [Move ("$_6", [])];
                    func := Constant (Val ZeroSized (FnDef "std::ptr::mut_ptr::<impl *mut T>::is_null" (GALCons (Type_ (Uint U8)) GALNil)));
                    destination := ("$_5", []);
                    target := Some "2"
                |}
            |});
            ("2", {|
                statements := [];
                terminator := SwitchInt (Move ("$_5", [])) [0%N] ["4"; "3"]
            |});
            ("3", {|
                statements := [
                    StorageDead "$_6";
                    Assign ("$_0", []) (Use (Copy ("m", [])));
                    StorageDead "$_5";
                    StorageDead "$_4"
                ];
                terminator := Goto "7"
            |});
            ("4", {|
                statements := [
                    StorageDead "$_6";
                    Assign ("$_4", []) (Use (Constant (Val ZeroSized Tuple0)));
                    StorageDead "$_5";
                    StorageDead "$_4";
                    StorageLive "k";
                    StorageLive "$_9";
                    StorageLive "$_10";
                    Assign ("$_10", []) (Use (Copy ("n", [])));
                    Assign ("$_9", []) (Cast PtrToPtr (Move ("$_10", [])) (RawPtr (RawPtr (Uint U8))));
                    StorageDead "$_10";
                    Assign ("k", []) (Use (Copy ("$_9", [Deref])));
                    StorageDead "$_9";
                    StorageLive "$_11";
                    Assign ("$_11", []) (Use (Copy ("m", [])));
                    StorageLive "$_12";
                    StorageLive "$_13";
                    Assign ("$_13", []) (Use (Copy ("n", [])));
                    Assign ("$_12", []) (Cast PtrToPtr (Move ("$_13", [])) (RawPtr (RawPtr (Uint U8))));
                    StorageDead "$_13";
                    Assign ("$_12", [Deref]) (Use (Move ("$_11", [])));
                    StorageDead "$_11";
                    StorageDead "$_12";
                    StorageLive "$_14"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "VeriFast_ghost_command" GALNil));
                    destination := ("$_14", []);
                    target := Some "5"
                |}
            |});
            ("5", {|
                statements := [
                    StorageDead "$_14";
                    StorageLive "$_15";
                    Assign ("$_15", []) (Use (Copy ("k", [])));
                    StorageLive "$_16";
                    Assign ("$_16", []) (Use (Copy ("n", [])))
                ];
                terminator := Call {|
                    args := [Move ("$_15", []); Move ("$_16", [])];
                    func := Constant (Val ZeroSized (FnDef "reverse_iter" GALNil));
                    destination := ("$_0", []);
                    target := Some "6"
                |}
            |});
            ("6", {|
                statements := [
                    StorageDead "$_16";
                    StorageDead "$_15";
                    StorageDead "k"
                ];
                terminator := Goto "7"
            |});
            ("7", {|
                statements := [];
                terminator := Return
            |})
        ]
    |});
    ("reverse", {|
        inputs := [RawPtr (Uint U8)];
        output := RawPtr (Uint U8);
        local_decls := [
            ("$_0", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("n", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_2", {| mutability := Not; ty := Tuple0 |});
            ("$_3", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_4", {| mutability := Mut; ty := RawPtr (Uint U8) |})
        ];
        basic_blocks := [
            ("0", {|
                statements := [
                    StorageLive "$_2"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "VeriFast_ghost_command" GALNil));
                    destination := ("$_2", []);
                    target := Some "1"
                |}
            |});
            ("1", {|
                statements := [
                    StorageDead "$_2";
                    StorageLive "$_3";
                    Assign ("$_3", []) (Use (Copy ("n", [])));
                    StorageLive "$_4"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "std::ptr::null_mut" (GALCons (Type_ (Uint U8)) GALNil)));
                    destination := ("$_4", []);
                    target := Some "2"
                |}
            |});
            ("2", {|
                statements := [];
                terminator := Call {|
                    args := [Move ("$_3", []); Move ("$_4", [])];
                    func := Constant (Val ZeroSized (FnDef "reverse_iter" GALNil));
                    destination := ("$_0", []);
                    target := Some "3"
                |}
            |});
            ("3", {|
                statements := [
                    StorageDead "$_4";
                    StorageDead "$_3"
                ];
                terminator := Return
            |})
        ]
    |});
    ("main", {|
        inputs := [];
        output := Tuple0;
        local_decls := [
            ("$_0", {| mutability := Mut; ty := Tuple0 |});
            ("$_1", {| mutability := Mut; ty := Never |});
            ("$_2", {| mutability := Not; ty := Tuple0 |});
            ("node1", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_4", {| mutability := Not; ty := Tuple0 |});
            ("node2", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_6", {| mutability := Mut; ty := RawPtr (RawPtr (Uint U8)) |});
            ("$_7", {| mutability := Not; ty := Tuple0 |});
            ("$_8", {| mutability := Not; ty := RawPtr (Uint U8) |});
            ("$_9", {| mutability := Mut; ty := RawPtr (Uint U8) |});
            ("$_10", {| mutability := Mut; ty := RawPtr (RawPtr (Uint U8)) |});
            ("$_11", {| mutability := Not; ty := Never |})
        ];
        basic_blocks := [
            ("0", {|
                statements := [
                    StorageLive "$_2"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "VeriFast_ghost_command" GALNil));
                    destination := ("$_2", []);
                    target := Some "1"
                |}
            |});
            ("1", {|
                statements := [
                    StorageDead "$_2";
                    StorageLive "node1"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "std::ptr::null_mut" (GALCons (Type_ (Uint U8)) GALNil)));
                    destination := ("node1", []);
                    target := Some "2"
                |}
            |});
            ("2", {|
                statements := [
                    StorageLive "$_4"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "VeriFast_ghost_command" GALNil));
                    destination := ("$_4", []);
                    target := Some "3"
                |}
            |});
            ("3", {|
                statements := [
                    StorageDead "$_4";
                    StorageLive "node2";
                    StorageLive "$_6";
                    Assign ("$_6", []) (RawPtr_ ("node1", []));
                    Assign ("node2", []) (Cast PtrToPtr (Move ("$_6", [])) (RawPtr (Uint U8)));
                    StorageDead "$_6";
                    StorageLive "$_7"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "VeriFast_ghost_command" GALNil));
                    destination := ("$_7", []);
                    target := Some "4"
                |}
            |});
            ("4", {|
                statements := [
                    StorageDead "$_7";
                    StorageLive "$_8";
                    StorageLive "$_9";
                    StorageLive "$_10";
                    Assign ("$_10", []) (RawPtr_ ("node2", []));
                    Assign ("$_9", []) (Cast PtrToPtr (Move ("$_10", [])) (RawPtr (Uint U8)));
                    StorageDead "$_10"
                ];
                terminator := Call {|
                    args := [Move ("$_9", [])];
                    func := Constant (Val ZeroSized (FnDef "reverse" GALNil));
                    destination := ("$_8", []);
                    target := Some "5"
                |}
            |});
            ("5", {|
                statements := [
                    StorageDead "$_9";
                    StorageDead "$_8";
                    StorageLive "$_11"
                ];
                terminator := Call {|
                    args := [];
                    func := Constant (Val ZeroSized (FnDef "std::process::abort" GALNil));
                    destination := ("$_11", []);
                    target := None
                |}
            |})
        ]
    |})
].

From VeriFast Require Export Annotations.

Definition preds := [
    ("Nodes", {|
        params := [("n", RawPtr (Uint U8))];
        body := IfAsn (Eq (Var "n") NullPtr) (BoolAsn (BoolLit true)) (SepAsn (PointsToAsn (RawPtr (Uint U8)) (Var "n") (VarPat "next")) (PredAsn "Nodes" [LitPat (Var "next")]))
    |})
].

Definition specs := [
    ("reverse_iter", {|
        spec_params := [("n", RawPtr (Uint U8)); ("m", RawPtr (Uint U8))];
        spec_output := RawPtr (Uint U8);
        pre := SepAsn (PredAsn "Nodes" [LitPat (Var "n")]) (PredAsn "Nodes" [LitPat (Var "m")]);
        post := PredAsn "Nodes" [LitPat (Var "result")]
    |});
    ("reverse", {|
        spec_params := [("n", RawPtr (Uint U8))];
        spec_output := RawPtr (Uint U8);
        pre := PredAsn "Nodes" [LitPat (Var "n")];
        post := PredAsn "Nodes" [LitPat (Var "result")]
    |});
    ("main", {|
        spec_params := [];
        spec_output := Tuple0;
        pre := BoolAsn (BoolLit true);
        post := BoolAsn (BoolLit true)
    |})
].

Open Scope annot_scope.

Definition symex_trees := [
    (Verifying "reverse_iter", 
        ParamAddrTaken "n" false;;
        ParamAddrTaken "m" false;;
        LocalAddrTaken "$_0" false;;
        LocalAddrTaken "$_3" true;;
        LocalAddrTaken "$_4" true;;
        LocalAddrTaken "$_5" false;;
        LocalAddrTaken "$_6" false;;
        LocalAddrTaken "$_7" true;;
        LocalAddrTaken "k" false;;
        LocalAddrTaken "$_9" false;;
        LocalAddrTaken "$_10" false;;
        LocalAddrTaken "$_11" false;;
        LocalAddrTaken "$_12" false;;
        LocalAddrTaken "$_13" false;;
        LocalAddrTaken "$_14" true;;
        LocalAddrTaken "$_15" false;;
        LocalAddrTaken "$_16" false;;
        Open;;
        (* h = [[1]Nodes<>(m); [1]Nodes<>(n)] *)
        ConsumeChunk 1%nat;;
        Fork (
            Fork (
                (* h = [[1]Nodes<>(m)] *)
                ConsumeChunk 0%nat;;
                Done
            ) (
                Done
            )
        ) (
            Fork (
                Done
            ) (
                (* h = [[1]Nodes<>(next); [1]points_to<*u8>(n, next); [1]Nodes<>(m)] *)
                ConsumeChunk 1%nat;;
                (* h = [[1]points_to<*u8>(n, next); [1]Nodes<>(next); [1]Nodes<>(m)] *)
                AutoOpen 0%nat;;
                (* h = [[1]points_to_<*u8>(n, some(next)); [1]Nodes<>(next); [1]Nodes<>(m)] *)
                ConsumeChunk 0%nat;;
                Close (RealLit 1%Q) "Nodes" [] [LitPat (Var "n")];;
                Fork (
                    Done
                ) (
                    (* h = [[1]points_to<*u8>(n, m); [1]Nodes<>(next); [1]Nodes<>(m)] *)
                    ConsumeChunk 0%nat;;
                    (* h = [[1]Nodes<>(next); [1]Nodes<>(m)] *)
                    ConsumeChunk 1%nat;;
                    (* h = [[1]Nodes<>(n); [1]Nodes<>(next)] *)
                    ConsumeChunk 1%nat;;
                    (* h = [[1]Nodes<>(n)] *)
                    ConsumeChunk 0%nat;;
                    (* h = [[1]Nodes<>($_0)] *)
                    ConsumeChunk 0%nat;;
                    Done
                )
            )
        ));
    (Verifying "reverse", 
        ParamAddrTaken "n" false;;
        LocalAddrTaken "$_0" false;;
        LocalAddrTaken "$_2" true;;
        LocalAddrTaken "$_3" false;;
        LocalAddrTaken "$_4" false;;
        Close (RealLit 1%Q) "Nodes" [] [LitPat NullPtr];;
        Fork (
            (* h = [[1]Nodes<>(null_pointer); [1]Nodes<>(n)] *)
            ConsumeChunk 1%nat;;
            (* h = [[1]Nodes<>(null_pointer)] *)
            ConsumeChunk 0%nat;;
            (* h = [[1]Nodes<>($_0)] *)
            ConsumeChunk 0%nat;;
            Done
        ) (
            Done
        ));
    (Verifying "main", 
        LocalAddrTaken "$_0" true;;
        LocalAddrTaken "$_1" true;;
        LocalAddrTaken "$_2" true;;
        LocalAddrTaken "node1" true;;
        LocalAddrTaken "$_4" true;;
        LocalAddrTaken "node2" true;;
        LocalAddrTaken "$_6" false;;
        LocalAddrTaken "$_7" true;;
        LocalAddrTaken "$_8" false;;
        LocalAddrTaken "$_9" false;;
        LocalAddrTaken "$_10" false;;
        LocalAddrTaken "$_11" true;;
        Close (RealLit 1%Q) "Nodes" [] [LitPat NullPtr];;
        Fork (
            (* h = [[1]Nodes<>(null_pointer); [1]points_to_<*u8>(node2_addr, dummy0); [1]points_to_<*u8>(node1_addr, dummy)] *)
            ConsumeChunk 2%nat;;
            Close (RealLit 1%Q) "Nodes" [] [LitPat (Var "node1")];;
            Fork (
                Done
            ) (
                (* h = [[1]points_to<*u8>(node1_addr, null_pointer); [1]points_to_<*u8>(node2_addr, dummy0); [1]Nodes<>(null_pointer)] *)
                ConsumeChunk 0%nat;;
                (* h = [[1]points_to_<*u8>(node2_addr, dummy0); [1]Nodes<>(null_pointer)] *)
                ConsumeChunk 1%nat;;
                (* h = [[1]Nodes<>(node1_addr); [1]points_to_<*u8>(node2_addr, dummy0)] *)
                ConsumeChunk 1%nat;;
                Close (RealLit 1%Q) "Nodes" [] [LitPat (Var "node2")];;
                Fork (
                    Done
                ) (
                    (* h = [[1]points_to<*u8>(node2_addr, node1_addr); [1]Nodes<>(node1_addr)] *)
                    ConsumeChunk 0%nat;;
                    (* h = [[1]Nodes<>(node1_addr)] *)
                    ConsumeChunk 0%nat;;
                    (* h = [[1]Nodes<>(node2_addr)] *)
                    ConsumeChunk 0%nat;;
                    Done
                )
            )
        ) (
            Done
        ))
].

From VeriFast Require Import SymbolicExecution.

Ltac step :=
  match goal with
  | |- ?P /\ ?Q => split
  | |- ?P -> ?Q => intro; try congruence
  | |- forall _, _ => intro; repeat rewrite value_eqb_def_
  | |- ?x = ?y => congruence
  | |- _ => tauto
  end.

Goal bodies_are_correct preds specs symex_trees bodies.
Proof.
  Opaque Error.
  Opaque not.
  cbv.
  Transparent not.
  repeat step.
Qed.
