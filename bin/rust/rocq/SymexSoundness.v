From iris.proofmode Require Import proofmode.
Require Export AxSem LogicalHeaps.

Section gfunctors.

Context {Σ: gFunctors}.

Parameter lh_big_ast: forall (H: LogHeap) (f: PrimChunk → iProp Σ), iProp Σ.
Axiom lh_big_ast_lh_comp_intro:
  forall (H1 H2: LogHeap) (f: PrimChunk → iProp Σ),
  lh_big_ast H1 f ∗ lh_big_ast H2 f -∗ lh_big_ast (H1 ⋅ H2) f.
Axiom lh_big_ast_lh_comp_elim:
  forall (H1 H2: LogHeap) (f: PrimChunk → iProp Σ),
  lh_big_ast (H1 ⋅ H2) f -∗ lh_big_ast H1 f ∗ lh_big_ast H2 f.
Axiom lh_big_ast_lh_sing_intro:
  forall chunk f,
  f chunk -∗ lh_big_ast {[+ chunk +]} f.
Axiom lh_big_ast_lh_sing_elim:
  forall chunk f,
  lh_big_ast {[+ chunk +]} f -∗ f chunk.

Definition own_logheap(H: LogHeap): iProp Σ :=
  lh_big_ast H (λ '(PointsTo_ ty ptr v), points_to_ ty ptr v).

Definition place_as_ptr(env: AxSem.Env)(place: Place): Value :=
  match place with
    PNonAddrTakenLocal x => VPtr (snd (env x))
  | PDeref ptr => ptr
  end.

Section preds.

Variable preds: list (string * PredDef).

Definition own_heap(h: Heap): iProp Σ :=
  ∃ H,
  ⌜ heap_holds preds H h ⌝ ∗
  own_logheap H.

Definition own_env_entry(Γ: AxSem.Env)(x: string)(state: LocalState): iProp Σ :=
  match state with
    LSValue (Some v) => points_to (fst (Γ x)) (VPtr (snd (Γ x))) v
  | LSValue None => ∃ v, points_to_ (fst (Γ x)) (VPtr (snd (Γ x))) v
  | LSPlace ptr => ⌜ ptr = snd (Γ x) ⌝
  end.

Fixpoint own_env(Γ: AxSem.Env)(env: Env): iProp Σ :=
  match env with
    [] => True
  | (x, state)::env => own_env_entry Γ x state ∗ own_env Γ env
  end.

Inductive place_has_ty(Γ: AxSem.Env): Place -> Ty -> Prop :=
| PNonAddrTakenLocal_has_ty x:
  place_has_ty Γ (PNonAddrTakenLocal x) (fst (Γ x))
| PDeref_has_ty ptr ty:
  place_has_ty Γ (PDeref ptr) ty
.

Lemma load_from_non_addr_taken_local Γ env x v:
  assoc x env = Some (LSValue (Some v)) →
  own_env Γ env -∗
  points_to (Γ x).1 (VPtr (Γ x).2) v ∗
  (points_to (Γ x).1 (VPtr (Γ x).2) v -∗ own_env Γ env).
Proof.
  induction env.
  - (* nil *)
    intros.
    discriminate.
  - (* cons *)
    destruct a as [x' state].
    intros.
    simpl in *.
    destruct (string_dec x x').
    + subst.
      injection H; clear H; intros; subst.
      iStartProof.
      iIntros "[H11 H12]".
      iSplitL "H11".
      * iExact "H11".
      * iIntros "H2".
        iSplitL "H2"; iAssumption.
    + apply IHenv in H.
      iStartProof.
      iIntros "[H1 H2]".
      iPoseProof (H with "H2") as "[H H']".
      iSplitL "H".
      iExact "H".
      iIntros "H".
      iSplitL "H1".
      iAssumption.
      iApply "H'".
      iAssumption.
Qed.

Lemma store_to_non_addr_taken_local x env v0 env' Γ:
  remove1_assoc x env = Some (LSValue v0, env') →
  own_env Γ env -∗
  (∃ v0, points_to_ (Γ x).1 (VPtr (Γ x).2) v0) ∗
  own_env Γ env'.
Proof.
  revert env'.
  induction env as [|x'_state env]; simpl; intro env'.
  - (* nil *)
    discriminate.
  - (* cons *)
    destruct x'_state as [x' state].
    destruct (string_dec x' x).
    + (* x' = x *)
      subst.
      intros H; injection H; intros; subst.
      iIntros "[Hx Henv']".
      iSplitL "Hx". {
        simpl.
        destruct v0.
        - (* Some v *)
          iExists (VSome v).
          iApply (points_to_def with "Hx").
        - (* None *)
          iAssumption.
      }
      iAssumption.
    + (* x' ≠ x *)
      destruct (remove1_assoc x env) as [[state0 env'']|].
      * (* Some *)
        intro Hstate0.
        injection Hstate0; intros; subst.
        iIntros "[Hx' Henv]".
        simpl.
        iDestruct ((IHenv env'') with "Henv") as "Henv".
        reflexivity.
        iFrame.
        iFrame.
      * (* None *)
        intros; discriminate.
Qed.

Lemma place_local_ptr_eq Γ env x ptr:
  assoc x env = Some (LSPlace ptr) →
  own_env Γ env -∗
  ⌜ ptr = (Γ x).2 ⌝ ∗
  own_env Γ env.
Proof.
  induction env.
  - (* nil *)
    intros.
    discriminate.
  - (* cons *)
    simpl; intros.
    destruct a as [x0 state].
    destruct (string_dec x x0).
    + (* x = x0 *)
      subst.
      injection H; intros; subst.
      iIntros "[Hx0 Henv]".
      simpl in *.
      iDestruct "Hx0" as %Hx0.
      subst.
      iSplitL "". {
        iPureIntro.
        reflexivity.
      }
      iSplitL "". {
        iPureIntro.
        reflexivity.
      }
      iAssumption.
    + (* x ≠ x0 *)
      iIntros "[Hx0 Henv]".
      iDestruct (IHenv H with "Henv") as "Henv".
      iFrame.
      iAssumption.
Qed.

Lemma consume_points_to_sound trace h tree ty ptr Qsymex Q:
  consume_points_to trace h tree ty ptr Qsymex →
  (∀ h tree v, Qsymex h tree v → own_heap h -∗ Q v) →
  own_heap h -∗
  ∃ v,
  points_to ty ptr v ∗ Q v.
Proof.
  intros Hconsume HQ.
  unfold own_heap.
  iIntros "Hh".
  iDestruct "Hh" as (H) "[Hh HH]".
  iDestruct "Hh" as %Hh.
  apply consume_points_to_sound with (1:=Hh) in Hconsume.
  destruct Hconsume as (H' & h' & tree' & v & HHeq & Hh' & HQsymex).
  apply HQ in HQsymex.
  iExists v.
  subst.
  unfold own_logheap.
  subst.
  iPoseProof (lh_big_ast_lh_comp_elim with "HH") as "HH".
  iDestruct "HH" as "[Hpoints_to_ HH']".
  iPoseProof (lh_big_ast_lh_sing_elim with "Hpoints_to_") as "Hpoints_to_".
  iSplitL "Hpoints_to_". {
    iApply (points_to_def with "Hpoints_to_").
  }
  iApply HQsymex.
  unfold own_heap.
  iExists H'.
  iSplitL "". {
    iPureIntro.
    assumption.
  }
  iAssumption.
Qed.

Lemma consume_points_to__sound trace h tree ty ptr Qsymex Q:
  consume_points_to_ trace h tree ty ptr Qsymex →
  (∀ h tree v, Qsymex h tree v → own_heap h -∗ Q v) →
  own_heap h -∗
  ∃ v,
  points_to_ ty ptr v ∗ Q v.
Proof.
  intros Hconsume HQ.
  unfold own_heap.
  iIntros "Hh".
  iDestruct "Hh" as (H) "[Hh HH]".
  iDestruct "Hh" as %Hh.
  apply consume_points_to__sound with (1:=Hh) in Hconsume.
  destruct Hconsume as (H' & h' & tree' & v & HHeq & Hh' & HQsymex).
  apply HQ in HQsymex.
  iExists v.
  subst.
  unfold own_logheap.
  subst.
  iPoseProof (lh_big_ast_lh_comp_elim with "HH") as "HH".
  iDestruct "HH" as "[Hpoints_to_ HH']".
  iPoseProof (lh_big_ast_lh_sing_elim with "Hpoints_to_") as "Hpoints_to_".
  iFrame.
  iApply HQsymex.
  unfold own_heap.
  iExists H'.
  iSplitL "". {
    iPureIntro.
    assumption.
  }
  iAssumption.
Qed.

Lemma load_from_pointer_sound trace h tree ty ptr Qsymex Q:
  load_from_pointer trace h tree ty ptr Qsymex →
  (∀ h tree v, Qsymex h tree v → own_heap h -∗ Q v) →
  own_heap h -∗
  ∃ v,
  points_to ty ptr v ∗
  (points_to ty ptr v -∗ Q v).
Proof.
  intros Hload HQ.
  unfold load_from_pointer in Hload.
  apply consume_points_to_sound with (Q:=λ v, (points_to ty ptr v -∗ Q v)%I) in Hload.
  - assumption.
  - intros.
    apply HQ in H.
    iIntros "Hh0 Hpoints_to".
    iApply H.
    unfold own_heap.
    iDestruct "Hh0" as (H0) "[Hh0 HH0]".
    iDestruct "Hh0" as %Hh0.
    iExists ({[+ PointsTo_ ty ptr (VSome v) +]} ⋅ H0).
    iSplitL "". {
      iPureIntro.
      simpl.
      exists {[+ PointsTo_ ty ptr (VSome v) +]}.
      exists H0.
      tauto.
    }
    unfold own_logheap.
    iApply lh_big_ast_lh_comp_intro.
    iSplitL "Hpoints_to". {
      iApply lh_big_ast_lh_sing_intro.
      iApply points_to_def.
      iAssumption.
    }
    iAssumption.
Qed.

Lemma load_from_place_sound trace h env tree place ty Qsymex Γ Q:
  load_from_place trace h env tree place ty Qsymex →
  place_has_ty Γ place ty →
  (∀ h tree v, Qsymex h tree v → own_heap h -∗ own_env Γ env -∗ Q v) →
  own_heap h -∗
  own_env Γ env -∗
  ∃ v,
  points_to ty (place_as_ptr Γ place) v ∗
  (points_to ty (place_as_ptr Γ place) v -∗
   Q v).
Proof.
  intros.
  iStartProof.
  iIntros "Hh Henv".
  destruct place.
  - (* PNonAddrTakenLocal *)
    simpl in H.
    simpl.
    inversion H0; subst.
    case_eq (assoc x env); intros; rewrite H2 in H; try tauto.
    rename l into state.
    destruct state; try tauto.
    destruct v; try tauto.
    iExists v.
    iPoseProof (load_from_non_addr_taken_local with "Henv") as "[H1 H2]".
    apply H2.
    iSplitL "H1". iAssumption.
    iIntros "H".
    iPoseProof ((H1 h tree v H) with "Hh") as "H'".
    iApply "H'".
    iApply "H2".
    iAssumption.
  - (* PDeref *)
    simpl in H.
    apply load_from_pointer_sound with (Q:=λ v, (own_env Γ env -∗ Q v)%I) in H.
    + iDestruct (H with "Hh") as "Hh".
      iDestruct "Hh" as (v) "[Hpoints_to HQ]".
      iExists v.
      iFrame.
      iIntros "Hpoints_to".
      iApply ("HQ" with "Hpoints_to").
      iAssumption.
    + assumption.
Qed.

Lemma store_to_place_sound trace h env tree place ty v Qsymex Γ Q:
  store_to_place trace h env tree place ty v Qsymex →
  place_has_ty Γ place ty →
  (∀ h env tree, Qsymex h env tree → own_heap h -∗ own_env Γ env -∗ Q) →
  own_heap h -∗
  own_env Γ env -∗
  (∃ v0, points_to_ ty (place_as_ptr Γ place) v0) ∗
  (points_to ty (place_as_ptr Γ place) v -∗
   Q).
Proof.
  intros Hstore Hplace_has_ty HQ.
  iIntros "Hh Henv".
  unfold store_to_place in Hstore.
  destruct (Ty_eq_dec ty Tuple0).
  - (* ty = Tuple0 *)
    subst.
    iSplitL "". {
      iApply points_to__Tuple0.
    }
    iIntros.
    apply HQ in Hstore.
    iApply (Hstore with "Hh Henv").
  - destruct place.
    + (* PNonAddrTakenLocal *)
      simpl in Hstore.
      simpl.
      case_eq (remove1_assoc x env). 2:{
        intro Hx; rewrite Hx in Hstore; tauto.
      }
      intros [y' xys'] Hxys'.
      rewrite Hxys' in Hstore.
      destruct y'; try tauto.
      apply HQ in Hstore.
      inversion Hplace_has_ty; subst.
      iDestruct ((store_to_non_addr_taken_local _ _ _ _ _ Hxys') with "Henv") as "[Hx Henv]".
      iFrame.
      iIntros "Hx".
      iApply (Hstore with "Hh").
      simpl.
      iFrame.
    + (* PDeref *)
      simpl in *.
      iDestruct ((consume_points_to__sound _ _ _ _ _ _ (λ v0, (points_to ty ptr v -∗ own_env Γ env -∗ Q)%I) Hstore) with "Hh") as "Hh".
      * intros h0 tree0 v0 HQ'.
        apply HQ in HQ'.
        iIntros "Hh0 Hptr".
        iApply HQ'.
        unfold own_heap.
        iDestruct "Hh0" as (H) "[Hh0 HH]".
        iDestruct "Hh0" as %Hh0.
        simpl.
        iExists ({[+ PointsTo_ ty ptr (VSome v) +]} ⋅ H).
        iSplitL "". {
          iPureIntro.
          exists {[+ PointsTo_ ty ptr (VSome v) +]}.
          exists H.
          split. reflexivity.
          split. reflexivity.
          assumption.
        }
        unfold own_logheap.
        iApply lh_big_ast_lh_comp_intro.
        iSplitL "Hptr". {
          iApply lh_big_ast_lh_sing_intro.
          iApply points_to_def.
          iAssumption.
        }
        iAssumption.
      * iDestruct "Hh" as (v0) "[Hptr HQ]".
        iSplitL "Hptr". {
          iExists v0.
          iAssumption.
        }
        iIntros "Hptr".
        iApply ("HQ" with "Hptr").
        iAssumption.
Qed.

Section local_decls.

Variable local_decls: list (Local * LocalDecl).

Section Γ.

Variable Γ: AxSem.Env.

Hypothesis Γ_well_typed: ∀ x local_decl,
  assoc x local_decls = Some local_decl → ty local_decl = (Γ x).1.

Lemma verify_local_sound trace env x Qsymex ty vptr Q:
  verify_local local_decls trace env x Qsymex →
  vptr = VPtr (Γ x).2 →
  ty = (Γ x).1 →
  (∀ place, Qsymex place ty →
   place_has_ty Γ place ty →
   own_env Γ env -∗
   Q (place_as_ptr Γ place) ty) →
  own_env Γ env -∗
  Q vptr ty.
Proof.
  unfold verify_local.
  case_eq (assoc x local_decls); intros; try tauto.
  pose proof (Γ_well_typed _ _ H).
  subst.
  destruct l.
  simpl in H4.
  subst.
  case_eq (assoc x env); intros; rewrite H1 in H0; try tauto.
  destruct l.
  * apply H3 in H0.
    -- simpl in H0.
       assumption.
    -- apply PNonAddrTakenLocal_has_ty.
  * apply H3 in H0.
    -- simpl in H0.
       iIntros "Henv".
       iDestruct (place_local_ptr_eq with "Henv") as "Henv". {
         eassumption.
       }
       iDestruct "Henv" as "[Hptr Henv]".
       iDestruct "Hptr" as %Hptr.
       subst.
       iApply (H0 with "Henv").
    -- constructor.
Qed.

Lemma verify_place_expr_elem_sound trace h env tree place ty place_expr_elem Qsymex ptr Q:
  verify_place_expr_elem trace h env tree place ty place_expr_elem Qsymex →
  place_has_ty Γ place ty →
  ptr = place_as_ptr Γ place →
  (∀ h tree place ty,
   Qsymex h tree place ty →
   place_has_ty Γ place ty →
   own_heap h -∗ own_env Γ env -∗ Q (place_as_ptr Γ place) ty) →
  own_heap h -∗
  own_env Γ env -∗
  wp_PlaceExprElem ptr ty place_expr_elem Q.
Proof.
  intros Hverify Hty Hptr HQ.
  subst.
  destruct place_expr_elem.
  - (* Deref *)
    unfold verify_place_expr_elem in Hverify.
    apply load_from_place_sound with (Γ:=Γ)
      (Q:=λ ptr, (∃ pointee_ty, ⌜ ty = RawPtr pointee_ty ⌝ ∗ Q ptr pointee_ty)%I) in Hverify.
    + iIntros "Hh Henv".
      iDestruct (Hverify with "Hh Henv") as "HQ".
      iDestruct "HQ" as (v) "[Hpoints_to HQ]".
      iApply wp_Deref_intro.
      iFrame.
    + assumption.
    + intros.
      destruct ty; try tauto.
      apply HQ in H. 2:constructor.
      iIntros "Hh0 Henv".
      iDestruct (H with "Hh0 Henv") as "HQ".
      iExists ty.
      iSplitL "". {
        iPureIntro.
        reflexivity.
      }
      iAssumption.
Qed.

Lemma verify_place_expr_elems_sound trace h env tree place ty place_expr_elems Qsymex ptr Q:
  verify_place_expr_elems trace h env tree place ty place_expr_elems Qsymex →
  place_has_ty Γ place ty →
  ptr = place_as_ptr Γ place →
  (∀ h tree place ty,
   Qsymex h tree place ty →
   place_has_ty Γ place ty →
   own_heap h -∗ own_env Γ env -∗ Q (place_as_ptr Γ place) ty) →
  own_heap h -∗
  own_env Γ env -∗
  wp_PlaceExprElems ptr ty place_expr_elems Q.
Proof.
  revert trace h env tree place ty Qsymex ptr Q.
  induction place_expr_elems.
  - (* nil *)
    intros.
    simpl in *.
    subst.
    apply H2 with (1:=H).
    assumption.
  - (* cons *)
    intros.
    simpl in *.
    apply verify_place_expr_elem_sound with (1:=H) (2:=H0) (3:=H1).
    intros.
    apply IHplace_expr_elems with (1:=H3); try assumption.
    reflexivity.
Qed.

Lemma verify_place_expr_sound trace h env tree place_expr Qsymex Q:
  verify_place_expr local_decls trace h env tree place_expr Qsymex →
  (∀ h tree place ty,
   Qsymex h tree place ty →
   place_has_ty Γ place ty →
   own_heap h -∗ own_env Γ env -∗ Q (place_as_ptr Γ place) ty) →
  own_heap h -∗
  own_env Γ env -∗
  wp_PlaceExpr Γ place_expr Q.
Proof.
  intros Hverify HQ.
  destruct place_expr as [x place_expr_elems].
  simpl in *.
  case_eq (Γ x); intros ty ptr Hx.
  iIntros "Hh Henv".
  iRevert "Henv Hh".
  iApply ((verify_local_sound _ _ _ _ _ (VPtr ptr) (λ vptr ty, (own_heap h -∗ wp_PlaceExprElems vptr ty place_expr_elems Q)%I))).
  - apply Hverify.
  - rewrite Hx; reflexivity.
  - rewrite Hx; reflexivity.
  - intros.
    iIntros "Henv Hh".
    iRevert "Hh Henv".
    iApply verify_place_expr_elems_sound.
    + apply H.
    + assumption.
    + reflexivity.
    + assumption.
Qed.

Lemma verify_operand_sound trace h env tree operand Qsymex Q:
  verify_operand local_decls trace h env tree operand Qsymex →
  (∀ h tree v ty,
   Qsymex h tree v ty →
   own_heap h -∗ own_env Γ env -∗ Q v ty) →
  own_heap h -∗ own_env Γ env -∗ wp_Operand Γ operand Q.
Proof.
  destruct operand; simpl; intros Hverify HQ; iIntros "Hh Henv".
  - (* Move *)
    iApply wp_Move_intro.
    iRevert "Hh Henv".
    iStopProof.
    apply verify_place_expr_sound with (1:=Hverify).
    intros h0 tree0 place0 ty Hload Hplace_has_ty.
    apply load_from_place_sound with (1:=Hload); try assumption.
    intros h1 tree1 v HQ'.
    apply HQ with (1:=HQ').
  - (* Copy *)
    iApply wp_Copy_intro.
    iRevert "Hh Henv".
    iStopProof.
    apply verify_place_expr_sound with (1:=Hverify).
    intros h0 tree0 place0 ty Hload Hplace_has_ty.
    apply load_from_place_sound with (1:=Hload); try assumption.
    intros h1 tree1 v HQ'.
    apply HQ with (1:=HQ').
  - (* Constant *)
    destruct const; try tauto.
    destruct value; try tauto.
    destruct ty; try tauto.
    iApply wp_Constant_Tuple0_intro.
    iApply ((HQ _ _ _ _ Hverify) with "Hh Henv").
Qed.

Lemma verify_rvalue_sound trace h env tree rvalue Qsymex Q:
  verify_rvalue local_decls trace h env tree rvalue Qsymex →
  (∀ h tree v ty,
   Qsymex h tree v ty →
   own_heap h -∗ own_env Γ env -∗ Q v ty) →
  own_heap h -∗ own_env Γ env -∗ wp_Rvalue Γ rvalue Q.
Proof.
  destruct rvalue; simpl; intros Hverify HQ; iIntros "Hh Henv".
  - (* Use *)
    iApply wp_Use_intro.
    iRevert "Hh Henv".
    iStopProof.
    apply verify_operand_sound with (1:=Hverify).
    apply HQ.
  - (* RawPtr_ *)
    iApply wp_RawPtr__intro.
    iRevert "Hh Henv".
    iStopProof.
    apply verify_place_expr_sound with (1:=Hverify).
    intros h0 tree0 place0 ty HQ'.
    destruct place0; try tauto.
    apply HQ in HQ'.
    intros.
    apply HQ'.
  - (* Cast *)
    destruct kind; try tauto.
    iApply wp_Cast_PtrToPtr_intro.
    iRevert "Hh Henv".
    iStopProof.
    apply verify_operand_sound with (1:=Hverify).
    intros h0 tree0 v ty' HQ'.
    apply HQ with (1:=HQ').
Qed.

(* TODO: Once we support StorageLive and StorageDead, Γ will not be fixed across statement execution. *)

Lemma verify_statement_sound trace h env tree statement Qsymex Q:
  verify_statement local_decls trace h env tree statement Qsymex →
  (∀ h env tree,
   Qsymex h env tree → own_heap h -∗ own_env Γ env -∗ Q) →
  own_heap h -∗ own_env Γ env -∗ wp_Statement Γ statement Q.
Proof.
  destruct statement; simpl; intros Hverify HQ; iIntros "Hh Henv".
  - (* Assign *)
    iApply wp_Assign_intro.
    iRevert "Hh Henv".
    iStopProof.
    apply verify_rvalue_sound with (1:=Hverify).
    intros h0 tree0 v ty Hverify'.
    apply verify_place_expr_sound with (1:=Hverify').
    intros h1 tree1 place ty0 Hstore Hplace_has_ty.
    apply store_to_place_sound with (1:=Hstore) (2:=Hplace_has_ty).
    assumption.
  - (* StorageLive *)
    apply HQ in Hverify.
    iApply wp_StorageLive_intro_UNSOUND.
    iApply (Hverify with "Hh").
    iAssumption.
  - (* StorageDead *)
    apply HQ in Hverify.
    iApply wp_StorageDead_intro_UNSOUND.
    iApply (Hverify with "Hh").
    iAssumption.
  - (* Nop *)
    apply HQ in Hverify.
    iApply wp_Nop_intro.
    iApply (Hverify with "Hh").
    iAssumption.
Qed.

Lemma verify_statements_sound trace h env tree statements Qsymex Q:
  verify_statements local_decls trace h env tree statements Qsymex →
  (∀ h env tree,
   Qsymex h env tree → own_heap h -∗ own_env Γ env -∗ Q) →
  own_heap h -∗ own_env Γ env -∗ wp_Statements Γ statements Q.
Proof.
Admitted.

End Γ.

End local_decls.

End preds.

End gfunctors.
