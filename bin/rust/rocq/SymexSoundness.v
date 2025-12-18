From iris.proofmode Require Import proofmode.
Require Export AxSem LogicalHeaps.

Instance EqDecision_Ty: EqDecision Ty.
Admitted.

Instance Countable_Ty: Countable Ty.
Admitted.

Instance EqDecision_Ptr: EqDecision Ptr.
Admitted.

Instance Countable_Ptr: Countable Ptr.
Admitted.

Definition PhysHeap := gmap (Ty * Ptr) Value.

Definition logheap_of_physheap(hp: PhysHeap): LogHeap :=
  map_fold (fun '(ty, ptr) v H => {[+ PointsTo_ ty (VPtr ptr) v +]} ⋅ H) ∅ hp.

Section gfunctors.

Context {Σ: gFunctors}.

Definition own_physheap(hp: PhysHeap): iProp Σ :=
  [∗ map] '(ty, ptr) ↦ v ∈ hp, points_to_ ty (VPtr ptr) v.

Definition place_as_ptr(env: AxSem.Env)(place: Place): Value :=
  match place with
    PNonAddrTakenLocal x => VPtr (snd (env x))
  | PDeref ptr => ptr
  end.

Section preds.

Variable preds: list (string * PredDef).

Definition own_heap(h: Heap): iProp Σ :=
  ∃ hp,
  ⌜ heap_holds preds (logheap_of_physheap hp) h ⌝ ∗
  own_physheap hp.

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

Lemma consume_points_to_sound trace h tree ty ptr Qsymex Q:
  consume_points_to trace h tree ty ptr Qsymex →
  (∀ h tree v, Qsymex h tree v → own_heap h -∗ Q v) →
  own_heap h -∗
  ∃ v,
  points_to ty ptr v ∗ Q v.
Proof.
  intros.
  unfold own_heap.
  iIntros "H".
  iDestruct "H" as (hp) "[H1 H2]".
  iDestruct "H1" as %H1.
  apply consume_points_to_sound with (1:=H1) in H.
  destruct H as (H' & h' & tree' & v & Hhp & Hh' & HQsymex).
  apply H0 in HQsymex.
  
Qed.

Lemma load_from_pointer_sound trace h tree ty ptr Qsymex Q:
  load_from_pointer trace h tree ty ptr Qsymex →
  (∀ h tree v, Qsymex h tree v → own_heap h -∗ Q v) →
  own_heap h -∗
  ∃ v,
  points_to ty ptr v ∗
  (points_to ty ptr v -∗ Q v).

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

Lemma verify_place_expr_elem_sound trace h env tree place ty place_expr_elem Qsymex Γ ptr Q:
  verify_place_expr_elem trace h env tree place ty place_expr_elem Qsymex →
  ptr = place_as_ptr Γ place →
  (∀ h tree place ty, Qsymex h tree place ty → own_heap h -∗ own_env Γ env -∗ Q (place_as_ptr Γ place) ty) →
  own_heap h -∗
  own_env Γ env -∗
  wp_PlaceExprElem ptr ty place_expr_elem Q.
Proof.
  
