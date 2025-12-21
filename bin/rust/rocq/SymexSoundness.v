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
    LSValue v => points_to (fst (Γ x)) (VPtr (snd (Γ x))) v
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
  assoc x env = Some (LSValue v) →
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

End Γ.

End local_decls.

End preds.

End gfunctors.
