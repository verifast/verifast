From VeriFast Require Export VfMir.

Definition bodies := [
    ("add_u32", {|
        inputs := [Uint U32; Uint U32];
        output := Uint U32;
        local_decls := [
            ("$_0", {| mutability := Mut; ty := Uint U32 |});
            ("a", {| mutability := Not; ty := Uint U32 |});
            ("b", {| mutability := Not; ty := Uint U32 |});
            ("$_3", {| mutability := Mut; ty := Uint U32 |});
            ("$_4", {| mutability := Mut; ty := Uint U32 |})
        ];
        basic_blocks := [
            ("0", {|
                statements := [
                    StorageLive "$_3";
                    Assign ("$_3", []) (Use (Copy ("a", [])));
                    StorageLive "$_4";
                    Assign ("$_4", []) (Use (Copy ("b", [])));
                    Assign ("$_0", []) (Move ("$_3", []))(Move ("$_4", []));
                    StorageDead "$_4";
                    StorageDead "$_3"
                ];
                terminator := Return
            |})
        ]
    |});
    ("swap_u32", {|
        inputs := [RawPtr (Uint U32); RawPtr (Uint U32)];
        output := Tuple0;
        local_decls := [
            ("$_0", {| mutability := Mut; ty := Tuple0 |});
            ("p", {| mutability := Not; ty := RawPtr (Uint U32) |});
            ("q", {| mutability := Not; ty := RawPtr (Uint U32) |});
            ("tmp", {| mutability := Not; ty := Uint U32 |});
            ("$_4", {| mutability := Mut; ty := Uint U32 |});
            ("$_5", {| mutability := Mut; ty := Uint U32 |})
        ];
        basic_blocks := [
            ("0", {|
                statements := [
                    StorageLive "tmp";
                    Assign ("tmp", []) (Use (Copy ("p", [Deref])));
                    StorageLive "$_4";
                    Assign ("$_4", []) (Use (Copy ("q", [Deref])));
                    Assign ("p", [Deref]) (Use (Move ("$_4", [])));
                    StorageDead "$_4";
                    StorageLive "$_5";
                    Assign ("$_5", []) (Use (Copy ("tmp", [])));
                    Assign ("q", [Deref]) (Use (Move ("$_5", [])));
                    StorageDead "$_5";
                    Assign ("$_0", []) (Use (Constant (Val ZeroSized Tuple0)));
                    StorageDead "tmp"
                ];
                terminator := Return
            |})
        ]
    |});
    ("max_u32", {|
        inputs := [Uint U32; Uint U32];
        output := Uint U32;
        local_decls := [
            ("$_0", {| mutability := Mut; ty := Uint U32 |});
            ("x", {| mutability := Not; ty := Uint U32 |});
            ("y", {| mutability := Not; ty := Uint U32 |});
            ("$_3", {| mutability := Mut; ty := Bool |});
            ("$_4", {| mutability := Mut; ty := Uint U32 |});
            ("$_5", {| mutability := Mut; ty := Uint U32 |})
        ];
        basic_blocks := [
            ("0", {|
                statements := [
                    StorageLive "$_3";
                    StorageLive "$_4";
                    Assign ("$_4", []) (Use (Copy ("x", [])));
                    StorageLive "$_5";
                    Assign ("$_5", []) (Use (Copy ("y", [])));
                    Assign ("$_3", []) (Move ("$_4", []))(Move ("$_5", []))
                ];
                terminator := SwitchInt (Move ("$_3", [])) [0%N] ["2"; "1"]
            |});
            ("1", {|
                statements := [
                    StorageDead "$_5";
                    StorageDead "$_4";
                    Assign ("$_0", []) (Use (Copy ("x", [])))
                ];
                terminator := Goto "3"
            |});
            ("2", {|
                statements := [
                    StorageDead "$_5";
                    StorageDead "$_4";
                    Assign ("$_0", []) (Use (Copy ("y", [])))
                ];
                terminator := Goto "3"
            |});
            ("3", {|
                statements := [
                    StorageDead "$_3"
                ];
                terminator := Return
            |})
        ]
    |});
    ("abs_diff_u32", {|
        inputs := [Uint U32; Uint U32];
        output := Uint U32;
        local_decls := [
            ("$_0", {| mutability := Mut; ty := Uint U32 |});
            ("a", {| mutability := Not; ty := Uint U32 |});
            ("b", {| mutability := Not; ty := Uint U32 |});
            ("$_3", {| mutability := Mut; ty := Bool |});
            ("$_4", {| mutability := Mut; ty := Uint U32 |});
            ("$_5", {| mutability := Mut; ty := Uint U32 |});
            ("$_6", {| mutability := Mut; ty := Uint U32 |});
            ("$_7", {| mutability := Mut; ty := Uint U32 |});
            ("$_8", {| mutability := Mut; ty := Uint U32 |});
            ("$_9", {| mutability := Mut; ty := Uint U32 |})
        ];
        basic_blocks := [
            ("0", {|
                statements := [
                    StorageLive "$_3";
                    StorageLive "$_4";
                    Assign ("$_4", []) (Use (Copy ("a", [])));
                    StorageLive "$_5";
                    Assign ("$_5", []) (Use (Copy ("b", [])));
                    Assign ("$_3", []) (Move ("$_4", []))(Move ("$_5", []))
                ];
                terminator := SwitchInt (Move ("$_3", [])) [0%N] ["2"; "1"]
            |});
            ("1", {|
                statements := [
                    StorageDead "$_5";
                    StorageDead "$_4";
                    StorageLive "$_6";
                    Assign ("$_6", []) (Use (Copy ("a", [])));
                    StorageLive "$_7";
                    Assign ("$_7", []) (Use (Copy ("b", [])));
                    Assign ("$_0", []) (Move ("$_6", []))(Move ("$_7", []));
                    StorageDead "$_7";
                    StorageDead "$_6"
                ];
                terminator := Goto "3"
            |});
            ("2", {|
                statements := [
                    StorageDead "$_5";
                    StorageDead "$_4";
                    StorageLive "$_8";
                    Assign ("$_8", []) (Use (Copy ("b", [])));
                    StorageLive "$_9";
                    Assign ("$_9", []) (Use (Copy ("a", [])));
                    Assign ("$_0", []) (Move ("$_8", []))(Move ("$_9", []));
                    StorageDead "$_9";
                    StorageDead "$_8"
                ];
                terminator := Goto "3"
            |});
            ("3", {|
                statements := [
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
            ("$_0", {| mutability := Mut; ty := Tuple0 |})
        ];
        basic_blocks := [
            ("0", {|
                statements := [
                    Assign ("$_0", []) (Use (Constant (Val ZeroSized Tuple0)))
                ];
                terminator := Return
            |})
        ]
    |})
].

From VeriFast Require Export Annotations.

Definition preds := [
].

Definition specs := [
    ("add_u32", {|
        spec_params := [("a", Uint U32); ("b", Uint U32)];
        spec_output := Uint U32;
        pre := BoolAsn UnknownExpr;
        post := BoolAsn (Eq (Var "result") UnknownExpr)
    |});
    ("swap_u32", {|
        spec_params := [("p", RawPtr (Uint U32)); ("q", RawPtr (Uint U32))];
        spec_output := Tuple0;
        pre := SepAsn (PointsToAsn (Uint U32) (Var "p") (VarPat "v1")) (PointsToAsn (Uint U32) (Var "q") (VarPat "v2"));
        post := SepAsn (PointsToAsn (Uint U32) (Var "p") (LitPat (Var "v2"))) (PointsToAsn (Uint U32) (Var "q") (LitPat (Var "v1")))
    |});
    ("max_u32", {|
        spec_params := [("x", Uint U32); ("y", Uint U32)];
        spec_output := Uint U32;
        pre := BoolAsn (BoolLit true);
        post := IfAsn UnknownExpr (BoolAsn (Eq (Var "result") (Var "x"))) (BoolAsn (Eq (Var "result") (Var "y")))
    |});
    ("abs_diff_u32", {|
        spec_params := [("a", Uint U32); ("b", Uint U32)];
        spec_output := Uint U32;
        pre := BoolAsn (BoolLit true);
        post := IfAsn UnknownExpr (BoolAsn (Eq (Var "result") UnknownExpr)) (BoolAsn (Eq (Var "result") UnknownExpr))
    |});
    ("main", {|
        spec_params := [];
        spec_output := Tuple0;
        pre := SepAsn (SepAsn (PredAsn "thread_token" [VarPat "_t"]) (BoolAsn (Eq (Var "_t") (Var "currentThread")))) UnknownAsn;
        post := SepAsn (PredAsn "thread_token" [LitPat (Var "_t")]) (BoolAsn (BoolLit true))
    |})
].

Open Scope annot_scope.

Definition symex_trees := [
    (Verifying "add_u32", 
        ParamAddrTaken "a" false;;
        ParamAddrTaken "b" false;;
        LocalAddrTaken "$_0" false;;
        LocalAddrTaken "$_3" false;;
        LocalAddrTaken "$_4" false;;
        Done);
    (Verifying "swap_u32", 
        ParamAddrTaken "p" false;;
        ParamAddrTaken "q" false;;
        LocalAddrTaken "$_0" true;;
        LocalAddrTaken "tmp" false;;
        LocalAddrTaken "$_4" false;;
        LocalAddrTaken "$_5" false;;
        (* h = [[1]points_to<u32>(q, v2); [1]points_to<u32>(p, v1)] *)
        ConsumeChunk 1%nat;;
        (* h = [[1]points_to<u32>(p, v1); [1]points_to<u32>(q, v2)] *)
        ConsumeChunk 1%nat;;
        (* h = [[1]points_to<u32>(q, v2); [1]points_to<u32>(p, v1)] *)
        AutoOpen 1%nat;;
        (* h = [[1]points_to_<u32>(p, some(v1)); [1]points_to<u32>(q, v2)] *)
        ConsumeChunk 0%nat;;
        (* h = [[1]points_to<u32>(p, v2); [1]points_to<u32>(q, v2)] *)
        AutoOpen 1%nat;;
        (* h = [[1]points_to_<u32>(q, some(v2)); [1]points_to<u32>(p, v2)] *)
        ConsumeChunk 0%nat;;
        (* h = [[1]points_to<u32>(q, v1); [1]points_to<u32>(p, v2)] *)
        ConsumeChunk 1%nat;;
        (* h = [[1]points_to<u32>(q, v1)] *)
        ConsumeChunk 0%nat;;
        Done);
    (Verifying "max_u32", 
        ParamAddrTaken "x" false;;
        ParamAddrTaken "y" false;;
        LocalAddrTaken "$_0" false;;
        LocalAddrTaken "$_3" false;;
        LocalAddrTaken "$_4" false;;
        LocalAddrTaken "$_5" false;;
        Fork (
            Fork (
                Done
            ) (
                Done
            )
        ) (
            Fork (
                Done
            ) (
                Done
            )
        ));
    (Verifying "abs_diff_u32", 
        ParamAddrTaken "a" false;;
        ParamAddrTaken "b" false;;
        LocalAddrTaken "$_0" false;;
        LocalAddrTaken "$_3" false;;
        LocalAddrTaken "$_4" false;;
        LocalAddrTaken "$_5" false;;
        LocalAddrTaken "$_6" false;;
        LocalAddrTaken "$_7" false;;
        LocalAddrTaken "$_8" false;;
        LocalAddrTaken "$_9" false;;
        Fork (
            Fork (
                Done
            ) (
                Done
            )
        ) (
            Fork (
                Done
            ) (
                Done
            )
        ));
    (Verifying "main", 
        LocalAddrTaken "$_0" true;;
        (* h = [[1]thread_token<>(_t)] *)
        ConsumeChunk 0%nat;;
        Done)
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
