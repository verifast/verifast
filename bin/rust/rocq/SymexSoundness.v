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
Axiom lh_big_ast_lh_empty_intro:
  forall f,
  ⊢ lh_big_ast ∅ f. 

Definition own_logheap(H: LogHeap): iProp Σ :=
  lh_big_ast H (λ '(PointsTo_ ty ptr v), points_to_ ty ptr v).

Lemma own_logheap_lh_comp_intro H1 H2:
  own_logheap H1 ∗ own_logheap H2 -∗ own_logheap (H1 ⋅ H2).
Proof.
  apply lh_big_ast_lh_comp_intro.
Qed.

Lemma own_logheap_lh_comp_elim H1 H2:
  own_logheap (H1 ⋅ H2) -∗ own_logheap H1 ∗ own_logheap H2.
Proof.
  apply lh_big_ast_lh_comp_elim.
Qed.

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

Definition own_chunk(chunk: Chunk): iProp Σ :=
  ∃ H, ⌜ chunk_holds preds H chunk ⌝ ∗ own_logheap H.

Lemma own_chunk_prim_intro ty ptr v:
  points_to_ ty ptr v -∗
  own_chunk (Prim (PointsTo_ ty ptr v)).
Proof.
  iIntros "Hptr".
  unfold own_chunk.
  iExists {[+ PointsTo_ ty ptr v +]}.
  iSplitL "". {
    iPureIntro.
    constructor.
  }
  unfold own_logheap.
  iApply (lh_big_ast_lh_sing_intro).
  iAssumption.
Qed.

Lemma own_heap_cons_intro(chunk: Chunk)(h: Heap):
  own_chunk chunk -∗
  own_heap h -∗
  own_heap (chunk::h).
Proof.
  unfold own_chunk, own_heap.
  iIntros "[%Hchunk [%HHchunk HHchunk]] [%Hh [%HHh HHh]]".
  iExists (Hchunk ⋅ Hh).
  iSplitL "". {
    iPureIntro.
    simpl.
    exists Hchunk.
    exists Hh.
    split. reflexivity.
    tauto.
  }
  iApply (own_logheap_lh_comp_intro).
  iFrame.
Qed.

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

Lemma remove1_assoc_own_env x env v0 env' Γ:
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
  (∀ h tree v, ⌜ Qsymex h tree v ⌝ -∗ own_heap h -∗ Q v) -∗
  own_heap h -∗
  ∃ v,
  points_to ty ptr v ∗ Q v.
Proof.
  intros Hconsume.
  unfold own_heap.
  iIntros "HQ Hh".
  iDestruct "Hh" as (H) "[Hh HH]".
  iDestruct "Hh" as %Hh.
  apply consume_points_to_sound with (1:=Hh) in Hconsume.
  destruct Hconsume as (H' & h' & tree' & v & HHeq & Hh' & HQsymex).
  iExists v.
  subst.
  unfold own_logheap.
  iPoseProof (lh_big_ast_lh_comp_elim with "HH") as "HH".
  iDestruct "HH" as "[Hpoints_to_ HH']".
  iPoseProof (lh_big_ast_lh_sing_elim with "Hpoints_to_") as "Hpoints_to_".
  iSplitL "Hpoints_to_". {
    iApply (points_to_def with "Hpoints_to_").
  }
  iApply ("HQ" with "[% //]").
  iExists H'.
  iSplitL "". {
    iPureIntro.
    assumption.
  }
  iAssumption.
Qed.

Lemma consume_points_to__sound trace h tree ty ptr Qsymex:
  consume_points_to_ trace h tree ty ptr Qsymex →
  ∀ Q,
  (∀ h tree v, ⌜ Qsymex h tree v ⌝ -∗ own_heap h -∗ Q v) -∗
  own_heap h -∗
  ∃ v,
  points_to_ ty ptr v ∗ Q v.
Proof.
  intros Hconsume Q.
  unfold own_heap.
  iIntros "HQ Hh".
  iDestruct "Hh" as (H) "[Hh HH]".
  iDestruct "Hh" as %Hh.
  apply consume_points_to__sound with (1:=Hh) in Hconsume.
  destruct Hconsume as (H' & h' & tree' & v & HHeq & Hh' & HQsymex).
  iExists v.
  subst.
  unfold own_logheap.
  iPoseProof (lh_big_ast_lh_comp_elim with "HH") as "HH".
  iDestruct "HH" as "[Hpoints_to_ HH']".
  iPoseProof (lh_big_ast_lh_sing_elim with "Hpoints_to_") as "Hpoints_to_".
  iFrame.
  iApply ("HQ" with "[% //]").
  iExists H'.
  iSplitL "". {
    iPureIntro.
    assumption.
  }
  iAssumption.
Qed.

Lemma load_from_pointer_sound trace h tree ty ptr Qsymex Q:
  load_from_pointer trace h tree ty ptr Qsymex →
  (∀ h tree v, ⌜ Qsymex h tree v ⌝ -∗ own_heap h -∗ Q v) -∗
  own_heap h -∗
  ∃ v,
  points_to ty ptr v ∗
  (points_to ty ptr v -∗ Q v).
Proof.
  intros Hload.
  unfold load_from_pointer in Hload.
  apply consume_points_to_sound with (Q:=λ v, (points_to ty ptr v -∗ Q v)%I) in Hload.
  iIntros "HQ Hh".
  iApply (Hload with "[HQ] Hh").
  unfold own_heap.
  iIntros (h0 tree0 v) "%HQsymex Hh0 Hpoints_to". 
  iDestruct "Hh0" as (H0) "[%Hh0 HH0]".
  iApply ("HQ" with "[% //]").
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
  (∀ h tree v, ⌜ Qsymex h tree v ⌝ -∗ own_heap h -∗ own_env Γ env -∗ Q v) -∗
  own_heap h -∗
  own_env Γ env -∗
  ∃ v,
  points_to ty (place_as_ptr Γ place) v ∗
  (points_to ty (place_as_ptr Γ place) v -∗
   Q v).
Proof.
  intros.
  iStartProof.
  iIntros "HQ Hh Henv".
  destruct place.
  - (* PNonAddrTakenLocal *)
    simpl in H.
    simpl.
    inversion H0; subst.
    case_eq (assoc x env); intros; rewrite H1 in H; try tauto.
    rename l into state.
    destruct state; try tauto.
    destruct v; try tauto.
    iExists v.
    iPoseProof (load_from_non_addr_taken_local with "Henv") as "[H1 H2]".
    apply H1.
    iSplitL "H1". iAssumption.
    iIntros "H".
    iPoseProof ("HQ" with "[% //] Hh") as "H'".
    iApply "H'".
    iApply "H2".
    iAssumption.
  - (* PDeref *)
    simpl in H.
    apply load_from_pointer_sound with (Q:=Q) in H.
    iApply (H with "[HQ Henv] Hh").
    iIntros (h0 tree0 v) "%HQsymex Hh0".
    iApply ("HQ" with "[% //] Hh0 Henv").
Qed.

Lemma store_to_place_sound trace h env tree place ty v Qsymex Γ Q:
  store_to_place trace h env tree place ty v Qsymex →
  place_has_ty Γ place ty →
  (∀ h env tree, ⌜ Qsymex h env tree ⌝ -∗ own_heap h -∗ own_env Γ env -∗ Q) -∗
  own_heap h -∗
  own_env Γ env -∗
  (∃ v0, points_to_ ty (place_as_ptr Γ place) v0) ∗
  (points_to ty (place_as_ptr Γ place) v -∗
   Q).
Proof.
  intros Hstore Hplace_has_ty.
  iIntros "HQ Hh Henv".
  unfold store_to_place in Hstore.
  destruct (Ty_eq_dec ty Tuple0).
  - (* ty = Tuple0 *)
    subst.
    iSplitL "". {
      iApply points_to__Tuple0.
    }
    iIntros.
    iApply ("HQ" with "[% //] Hh Henv").
  - destruct place.
    + (* PNonAddrTakenLocal *)
      simpl.
      case_eq (remove1_assoc x env). 2:{
        intro Hx; rewrite Hx in Hstore; tauto.
      }
      intros [y' xys'] Hxys'.
      rewrite Hxys' in Hstore.
      destruct y'; try tauto.
      iDestruct ("HQ" with "[% //] Hh") as "HQ".
      inversion Hplace_has_ty; subst.
      iDestruct ((remove1_assoc_own_env _ _ _ _ _ Hxys') with "Henv") as "[Hx Henv]".
      iFrame.
      iIntros "Hx".
      simpl.
      iApply ("HQ" with "[Hx Henv]").
      iFrame.
    + (* PDeref *)
      simpl in *.
      eapply consume_points_to__sound with (Q:=λ _, (points_to ty ptr v -∗ Q)%I) in Hstore.
      iDestruct (Hstore with "[HQ Henv] Hh") as "HQ".
      * iIntros (h0 tree0 v0) "HQ' Hh0 Hptr".
        iApply ("HQ" with "HQ' [Hh0 Hptr] Henv").
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
      * iDestruct "HQ" as (v0) "[Hptr HQ]".
        iSplitL "Hptr". {
          iExists v0.
          iAssumption.
        }
        iAssumption.
Qed.

Section specs.

Variable specs: list (string * Spec).

Section Γ.

Variable Γ: AxSem.Env.

Hypothesis Γ_non_null: ∀ x, (Γ x).2 ≠ null_ptr.

Section local_decls.

Variable local_decls: list (Local * LocalDecl).

Hypothesis Γ_well_typed: ∀ x local_decl,
  assoc x local_decls = Some local_decl → ty local_decl = (Γ x).1.

Lemma verify_local_sound trace env x Qsymex ty vptr Q:
  verify_local local_decls trace env x Qsymex →
  vptr = VPtr (Γ x).2 →
  ty = (Γ x).1 →
  (∀ place,
   ⌜ Qsymex place ty ⌝ -∗
   ⌜ place_has_ty Γ place ty ⌝ -∗
   own_env Γ env -∗
   Q (place_as_ptr Γ place) ty) -∗
  own_env Γ env -∗
  Q vptr ty.
Proof.
  unfold verify_local.
  case_eq (assoc x local_decls); intros; try tauto.
  pose proof (Γ_well_typed _ _ H).
  subst.
  destruct l.
  simpl in H3.
  subst.
  case_eq (assoc x env); intros; rewrite H1 in H0; try tauto.
  iIntros  "HQ Henv".
  destruct l.
  * iApply ("HQ" with "[% //] [%] Henv").
    apply PNonAddrTakenLocal_has_ty.
  * iDestruct (place_local_ptr_eq with "Henv") as "[%Ha Henv]". {
      eassumption.
    }
    subst.
    iApply ("HQ" with "[% //] [%] Henv").
    constructor.
Qed.

Lemma verify_place_expr_elem_sound trace h env tree place ty place_expr_elem Qsymex ptr Q:
  verify_place_expr_elem trace h env tree place ty place_expr_elem Qsymex →
  place_has_ty Γ place ty →
  ptr = place_as_ptr Γ place →
  (∀ h tree place ty,
   ⌜ Qsymex h tree place ty ⌝ -∗
   ⌜ place_has_ty Γ place ty ⌝ -∗
   own_heap h -∗ own_env Γ env -∗ Q (place_as_ptr Γ place) ty) -∗
  own_heap h -∗
  own_env Γ env -∗
  wp_PlaceExprElem ptr ty place_expr_elem Q.
Proof.
  intros Hverify Hty Hptr.
  iIntros "HQ".
  subst.
  destruct place_expr_elem.
  - (* Deref *)
    unfold verify_place_expr_elem in Hverify.
    iIntros "Hh Henv".
    eapply load_from_place_sound with (2:=Hty) in Hverify.
    iDestruct (Hverify with "[HQ] Hh Henv") as "Hverify". 2: {
      iDestruct "Hverify" as (v) "[Hpoints_to HQ']".
      iApply wp_Deref_intro.
      iFrame.
    }
    iIntros (h0 tree0 v) "%HQ Hh0 Henv".
    destruct ty; try tauto.
    iExists ty.
    iSplitL "". {
      iPureIntro.
      reflexivity.
    }
    iApply ("HQ" with "[% //] [%] Hh0 Henv").
    constructor.
Qed.

Lemma verify_place_expr_elems_sound trace h env tree place ty place_expr_elems Qsymex ptr Q:
  verify_place_expr_elems trace h env tree place ty place_expr_elems Qsymex →
  place_has_ty Γ place ty →
  ptr = place_as_ptr Γ place →
  (∀ h tree place ty,
   ⌜ Qsymex h tree place ty ⌝ -∗
   ⌜ place_has_ty Γ place ty ⌝ -∗
   own_heap h -∗ own_env Γ env -∗ Q (place_as_ptr Γ place) ty) -∗
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
    iIntros "HQ".
    iApply ("HQ" with "[% //] [% //]").
  - (* cons *)
    intros. iIntros "HQ Hh Henv".
    simpl in *.
    eapply verify_place_expr_elem_sound in H; try eassumption.
    iApply (H with "[HQ] Hh Henv").
    iIntros (h0 tree0 place0 ty0) "%Hverify %Hplace0 Hh0 Henv".
    eapply IHplace_expr_elems in Hverify; try assumption.
    iApply (Hverify with "HQ Hh0 Henv").
    reflexivity.
Qed.

Lemma verify_place_expr_sound trace h env tree place_expr Qsymex Q:
  verify_place_expr local_decls trace h env tree place_expr Qsymex →
  (∀ h tree place ty,
   ⌜ Qsymex h tree place ty ⌝ -∗
   ⌜ place_has_ty Γ place ty ⌝ -∗
   own_heap h -∗ own_env Γ env -∗ Q (place_as_ptr Γ place) ty) -∗
  own_heap h -∗
  own_env Γ env -∗
  wp_PlaceExpr Γ place_expr Q.
Proof.
  intros Hverify. iIntros "HQ".
  destruct place_expr as [x place_expr_elems].
  simpl in *.
  case_eq (Γ x); intros ty ptr Hx.
  iIntros "Hh Henv".
  iRevert "Henv Hh".
  iApply ((verify_local_sound _ _ _ _ _ (VPtr ptr) (λ vptr ty, (own_heap h -∗ wp_PlaceExprElems vptr ty place_expr_elems Q)%I))).
  - apply Hverify.
  - rewrite Hx; reflexivity.
  - rewrite Hx; reflexivity.
  - iIntros (place) "%Hverify' %Hplace Henv Hh".
    iRevert "Hh Henv".
    iApply verify_place_expr_elems_sound.
    + apply Hverify'.
    + assumption.
    + reflexivity.
    + iAssumption.
Qed.

Lemma verify_operand_sound trace h env tree operand Qsymex Q:
  verify_operand local_decls trace h env tree operand Qsymex →
  (∀ h tree v ty,
   ⌜ Qsymex h tree v ty ⌝ -∗
   own_heap h -∗ own_env Γ env -∗ Q v ty) -∗
  own_heap h -∗ own_env Γ env -∗ wp_Operand Γ operand Q.
Proof.
  destruct operand; simpl; intros Hverify; iIntros "HQ Hh Henv".
  - (* Move *)
    iApply wp_Move_intro.
    iRevert "Hh Henv".
    iApply verify_place_expr_sound; try eassumption.
    iIntros (h0 tree0 place0 ty) "%Hload %Hplace_has_ty".
    iApply load_from_place_sound; try eassumption.
    iIntros (h1 tree1 v) "%HQ'".
    iDestruct ("HQ" with "[% //]") as "HQ".
    iAssumption.
  - (* Copy *)
    iApply wp_Copy_intro.
    iRevert "Hh Henv".
    iApply verify_place_expr_sound; try eassumption.
    iIntros (h0 tree0 place0 ty) "%Hload %Hplace_has_ty".
    iApply load_from_place_sound; try eassumption.
    iIntros (h1 tree1 v) "%HQ'".
    iApply ("HQ" with "[% //]").
  - (* Constant *)
    destruct const; try tauto.
    destruct value; try tauto.
    destruct ty; try tauto.
    iApply wp_Constant_Tuple0_intro.
    iApply ("HQ" with "[% //] Hh Henv").
Qed.

Lemma verify_operands_sound trace h env tree operands Qsymex Q:
  verify_operands local_decls trace h env tree operands Qsymex →
  (∀ h tree vs,
   ⌜ Qsymex h tree vs ⌝ -∗
   own_heap h -∗ own_env Γ env -∗ Q vs) -∗
  own_heap h -∗ own_env Γ env -∗ wp_Operands Γ operands Q.
Proof.
  revert trace h env tree Qsymex Q.
  induction operands as [|operand operands]; simpl.
  - (* nil *)
    iIntros (trace h env tree Qsymex Q Hverify) "HQ Hh Henv".
    iApply ("HQ" with "[% //] Hh Henv").
  - (* cons *)
    iIntros (trace h env tree Qsymex Q Hverify) "HQ Hh Henv".
    iApply (verify_operand_sound with "[HQ] Hh Henv"); try eassumption.
    clear Hverify.
    iIntros (h0 tree0 v ty) "%Hverify Hh0 Henv".
    iApply (IHoperands with "[HQ] Hh0 Henv"); try eassumption.
    clear Hverify.
    iIntros (h1 tree1 vs) "%Hverify Hh1 Henv".
    iApply ("HQ" with "[% //] Hh1 Henv").
Qed.

Lemma verify_rvalue_sound trace h env tree rvalue Qsymex Q:
  verify_rvalue local_decls trace h env tree rvalue Qsymex →
  (∀ h tree v ty,
   ⌜ Qsymex h tree v ty ⌝ -∗
   own_heap h -∗ own_env Γ env -∗ Q v ty) -∗
  own_heap h -∗ own_env Γ env -∗ wp_Rvalue Γ rvalue Q.
Proof.
  destruct rvalue; simpl; intros Hverify; iIntros "HQ Hh Henv".
  - (* Use *)
    iApply wp_Use_intro.
    iRevert "Hh Henv".
    iApply verify_operand_sound; try eassumption.
    iApply "HQ".
  - (* RawPtr_ *)
    iApply wp_RawPtr__intro.
    iRevert "Hh Henv".
    iApply verify_place_expr_sound; try eassumption.
    iIntros (h0 tree0 place0 ty) "%HQ' %Hplace".
    destruct place0; try tauto.
    iApply ("HQ" with "[% //]").
  - (* Cast *)
    destruct kind; try tauto.
    iApply wp_Cast_PtrToPtr_intro.
    iRevert "Hh Henv".
    iApply verify_operand_sound; try eassumption.
    iIntros (h0 tree0 v ty') "%HQ'".
    iApply ("HQ" with "[% //]").
Qed.

(* TODO: Once we support StorageLive and StorageDead, Γ will not be fixed across statement execution. *)

Lemma verify_statement_sound trace h env tree statement Qsymex Q:
  verify_statement local_decls trace h env tree statement Qsymex →
  (∀ h env tree,
   ⌜ Qsymex h env tree ⌝ -∗ own_heap h -∗ own_env Γ env -∗ Q) -∗
  own_heap h -∗ own_env Γ env -∗ wp_Statement Γ statement Q.
Proof.
  destruct statement; simpl; intros Hverify; iIntros "HQ Hh Henv".
  - (* Assign *)
    iApply wp_Assign_intro.
    iRevert "Hh Henv".
    iApply verify_rvalue_sound; try eassumption.
    iIntros (h0 tree0 v ty) "%Hverify'".
    iApply verify_place_expr_sound; try eassumption.
    iIntros (h1 tree1 place ty0) "%Hstore %Hplace_has_ty".
    iApply store_to_place_sound; try eassumption.
    iAssumption.
  - (* StorageLive *)
    iApply wp_StorageLive_intro_UNSOUND.
    iApply ("HQ" with "[% //] Hh Henv").
  - (* StorageDead *)
    iApply wp_StorageDead_intro_UNSOUND.
    iApply ("HQ" with "[% //] Hh Henv").
  - (* Nop *)
    iApply wp_Nop_intro.
    iApply ("HQ" with "[% //] Hh Henv").
Qed.

Lemma verify_statements_sound trace h env tree statements Qsymex Q:
  verify_statements local_decls trace h env tree statements Qsymex →
  (∀ h env tree,
   ⌜ Qsymex h env tree ⌝ → own_heap h -∗ own_env Γ env -∗ Q) -∗
  own_heap h -∗ own_env Γ env -∗ wp_Statements Γ statements Q.
Proof.
  revert trace h env tree Qsymex Q.
  induction statements.
  - (* nil *)
    intros trace h env tree Qsymex Q Hverify; iIntros "HQ".
    iApply ("HQ" with "[% //]").
  - (* cons *)
    intros trace h env tree Qsymex Q Hverify; iIntros "HQ".
    simpl in *.
    iApply verify_statement_sound; try eassumption.
    iIntros (h0 env0 tree0) "%Hverify_statements".
    iApply IHstatements; try eassumption.
    iAssumption.
Qed.

Lemma assume_value_eq_N_sound trace v ty value Q:
  assume_value_eq_N trace v ty value Q →
  value_eqb_N ty v value = Some true →
  Q.
Proof.
  intros Hassume Heq.
  destruct value as [|[ | | ]]; destruct ty; simpl in Hassume; try tauto.
  - (* 0%N *)
    apply value_eqb_N_Bool_0_eq_true in Heq.
    tauto.
  - (* 1%N *)
    apply value_eqb_N_Bool_1_eq_true in Heq.
    tauto.
Qed.

Lemma assume_value_neq_N_sound trace v ty value Q:
  assume_value_neq_N trace v ty value Q →
  value_eqb_N ty v value = Some false →
  Q.
Proof.
  intros Hassume Hneq.
  destruct value as [|[ | | ]]; destruct ty; simpl in Hassume; try tauto.
  - (* 0%N *)
    apply value_eqb_N_Bool_0_eq_false in Hneq.
    tauto.
  - (* 1%N *)
    apply value_eqb_N_Bool_1_eq_false in Hneq.
    tauto.
Qed.

Lemma verify_switch_int_sound trace tree discr ty values targets Qsymex_bb (Qbb: BasicBlock → iProp Σ):
  verify_switch_int trace tree discr ty values targets Qsymex_bb →
  ▷ (∀ tree bb, ⌜ Qsymex_bb tree bb ⌝ -∗ Qbb bb) -∗
  wp_SwitchInt discr ty values targets Qbb.
Proof.
  revert trace tree targets.
  induction values as [|value values]; intros trace tree targets Hverify; iIntros "HQ".
  - (* nil *)
    destruct targets as [|target [|?]]; simpl in Hverify; try tauto.
    iApply wp_SwitchInt_default.
    iNext.
    iApply "HQ".
    iPureIntro.
    apply Hverify.
  - (* cons *)
    destruct targets as [|target targets]; try tauto.
    destruct tree; try tauto.
    simpl in Hverify.
    destruct Hverify as [Hverify_neq Hverify_eq].
    iApply wp_SwitchInt_compare.
    case_eq (value_eqb_N ty discr value).
    + (* Some *)
      intros b Hb.
      destruct b.
      * (* true *)
        apply assume_value_eq_N_sound with (2:=Hb) in Hverify_eq.
        iNext.
        iApply "HQ".
        iPureIntro.
        apply Hverify_eq.
      * (* false *)
        apply assume_value_neq_N_sound with (2:=Hb) in Hverify_neq.
        iApply IHvalues.
        apply Hverify_neq.
        iNext.
        iAssumption.
    + (* None *)
      intros.
      iPureIntro.
      constructor.
Qed.

Definition own_asn(env: Env)(a: Asn)(env': Env): iProp Σ :=
  ∃ H: LogHeap, ⌜ asn_holds preds H env a env' ⌝ ∗ own_logheap H.

Lemma produce_sound trace h env tree a Qsymex env' Q:
  produce trace h env tree a Qsymex →
  (∀ h tree,
   ⌜ Qsymex h env' tree ⌝ -∗
   own_heap h -∗ Q) -∗
  own_heap h -∗
  own_asn env a env' -∗
  Q.
Proof.
  intros Hproduce.
  iIntros "HQ Hh Ha".
  unfold own_heap.
  unfold own_asn.
  iDestruct "Hh" as (H) "[%Hh HH]".
  iDestruct "Ha" as (H0) "[%Ha HH0]".
  apply produce_sound with (1:=Hh) (2:=Ha) in Hproduce.
  destruct Hproduce as (h' & tree' & HQsymex & Hh').
  iApply ("HQ" with "[% //]").
  iExists (H ⋅ H0).
  iSplitL "". {
    iPureIntro.
    assumption.
  }
  iApply own_logheap_lh_comp_intro.
  iFrame.
Qed.

Lemma consume_sound trace h env tree a Qsymex Q:
  consume trace h env tree a Qsymex →
  (∀ h env' tree,
   ⌜ Qsymex h env' tree ⌝ -∗
   own_asn env a env' ∗ own_heap h -∗ Q) -∗
  own_heap h -∗
  Q.
Proof.
  intros Hconsume.
  iIntros "HQ Hh".
  unfold own_heap.
  iDestruct "Hh" as (H) "[Hh HH]".
  iDestruct "Hh" as %Hh.
  apply consume_sound with (1:=Hh) in Hconsume.
  destruct Hconsume as (h' & env' & tree' & H1 & H2 & HH & Ha & Hh' & HQsymex).
  iApply ("HQ" with "[% //]").
  subst H.
  iDestruct (own_logheap_lh_comp_elim with "HH") as "[HH1 HH2]".
  iSplitL "HH1". {
    unfold own_asn.
    iExists H1.
    iSplitL "". {
      iPureIntro.
      assumption.
    }
    iAssumption.
  }
  unfold own_heap.
  iExists H2.
  iSplitL "". {
    iPureIntro.
    assumption.
  }
  iAssumption.
Qed.

Lemma forall_ty_sound trace ty Q v:
  forall_ty trace ty Q →
  value_has_ty ty v →
  Q v.
Proof.
  intros Hforall Hhas; destruct ty; try tauto; simpl in *; inversion Hhas; subst; auto.
Qed.

Definition spec_holds
    (spec: Spec)(targs: list GenericArg)(args: list Value)
    (wp_call: (Value → iProp Σ) → iProp Σ)
    : iProp Σ :=
  (* ⌜ values_have_tys (map snd (spec_params spec)) args ⌝ -∗ *)
  let env := combine (map fst (spec_params spec)) (map (fun v => LSValue (Some v)) args) in
  ∀ env',
  own_asn env (pre spec) env' -∗
  ∀ Q,
  (∀ result,
   ⌜ value_has_ty (spec_output spec) result ⌝ ∗
   (∃ env'', own_asn (("result", LSValue (Some result))::env') (post spec) env'') -∗
   Q result) -∗
  wp_call Q.

Definition spec_sound
    (func_name: string)(targs: list GenericArg)(args: list Value)
    (wp_call: string → list GenericArg → list Value → (Value → iProp Σ) → iProp Σ)
    : iProp Σ :=
  match assoc func_name specs with
    None => True
  | Some spec => spec_holds spec targs args (wp_call func_name targs args)
  end.

Lemma verify_call_sound trace h tree func_name targs args Qsymex wp_call Q:
  verify_call specs trace h tree func_name targs args Qsymex →
  (∀ h tree v, ⌜ Qsymex h tree v ⌝ -∗ own_heap h -∗ Q v) -∗
  (∀ func_name targs args, spec_sound func_name targs args wp_call) -∗
  own_heap h -∗
  wp_call_std wp_call func_name targs args Q.
Proof.
  intros Hverify.
  iIntros "HQ Hspecs Hh".
  unfold wp_call_std.
  unfold verify_call in Hverify.
  destruct (string_dec func_name "std::ptr::mut_ptr::<impl *mut T>::is_null"). {
    (* func_name = "std::ptr::mut_ptr::<impl *mut T>::is_null" *)
    destruct args as [|arg [|]]; try tauto.
    iApply ("HQ" with "[% //] Hh").
  }
  destruct (string_dec func_name "std::ptr::null_mut"). {
    (* func_name = "std::ptr::null_mut" *)
    iApply ("HQ" with "[% //] Hh").
  }
  destruct (string_dec func_name "std::process::abort"). {
    (* func_name = "std::process:abort" *)
    iPureIntro.
    tauto.
  }
  iDestruct ("Hspecs" $! func_name targs args) as "Hspec".
  unfold spec_sound.
  destruct (assoc func_name specs); try tauto.
  eapply consume_sound in Hverify.
  iApply (Hverify with "[HQ Hspec] Hh").
  iIntros (h' env' tree') "%Hforall".
  iIntros "[Hpre Hh']".
  iDestruct ("Hspec" $! env' with "Hpre") as "Hpost".
  iApply "Hpost".
  iIntros (result) "[Hresult Hpost]".
  iDestruct "Hresult" as %Hresult.
  iDestruct "Hpost" as (env'') "Hpost".
  apply forall_ty_sound with (2:=Hresult) in Hforall.
  iRevert "Hh' Hpost".
  iApply produce_sound; try eassumption.
  iIntros (h'' tree'').
  iApply "HQ".
Qed.

Lemma consume_chunk_sound trace h tree Qsymex Q:
  consume_chunk trace h tree Qsymex →
  (∀ h tree chunk,
   ⌜ Qsymex h tree chunk ⌝ -∗
   own_heap h -∗ own_chunk chunk -∗ Q) -∗
  own_heap h -∗ Q.
Proof.
  intros Hconsume.
  iIntros "HQ Hh".
  unfold own_heap.
  iDestruct "Hh" as (H) "[Hh HH]".
  iDestruct "Hh" as %Hh.
  apply consume_chunk_sound with (1:=Hh) in Hconsume.
  destruct Hconsume as (Hchunk & H' & h' & tree' & chunk & HH & HHchunk & Hh' & HQsymex).
  iDestruct ("HQ" with "[% //]") as "HQ".
  subst H.
  iDestruct (own_logheap_lh_comp_elim with "HH") as "[HHchunk HH']".
  iApply ("HQ" with "[HH'] [HHchunk]").
  - unfold own_heap.
    iExists H'.
    iSplitL "". {
      iPureIntro. assumption.
    }
    iAssumption.
  - unfold own_chunk.
    iExists Hchunk.
    iSplitL "". {
      iPureIntro. assumption.
    }
    iAssumption.
Qed.

Lemma eval_pats_sound trace env pats Qsymex:
  eval_pats trace env pats Qsymex →
  ∃ vs, Qsymex vs.
Proof.
  revert trace env Qsymex.
  induction pats as [|pat pats]; intros trace env Qsymex; simpl.
  - (* nil *)
    intro HQsymex.
    exists [].
    assumption.
  - (* cons *)
    destruct pat.
    + (* LitPat *)
      intros Hpats.
      apply IHpats in Hpats.
      destruct Hpats as [vs Hpats].
      exists (eval env e::vs).
      assumption.
    + (* VarPat *)
      intros; tauto.
Qed.

Lemma verify_ghost_command_sound trace h env tree Qsymex Q:
  verify_ghost_command preds trace h env tree Qsymex →
  (∀ h tree, ⌜ Qsymex h tree ⌝ -∗ own_heap h -∗ Q) -∗
  own_heap h -∗ Q.
Proof.
  iIntros (Hverify) "HQ".
  destruct tree; try tauto.
  destruct data; try tauto; simpl in Hverify.
  - (* Open *)
    iApply consume_chunk_sound; try eassumption.
    clear Hverify.
    iIntros (h' tree' chunk) "%Hchunk".
    destruct chunk; try tauto.
    case_eq (assoc pred_name preds). {
      intros pred_def Hpred_name.
      rewrite Hpred_name in Hchunk.
      iIntros "Hh' Hchunk".
      unfold own_chunk.
      iDestruct "Hchunk" as (H) "[Hchunk HH]".
      iDestruct "Hchunk" as %Hchunk'.
      simpl in Hchunk'.
      rewrite Hpred_name in Hchunk'.
      destruct pred_def.
      simpl in Hchunk.
      destruct (combine_ params args) as [env' [[] []]]; try tauto.
      destruct Hchunk' as [env'' Hbody].
      iApply (produce_sound with "[HQ] Hh' [HH]").
      - eassumption.
      - iAssumption.
      - unfold own_asn.
        iExists H.
        iSplitL "". {
          iPureIntro. eassumption.
        }
        iAssumption.
    }
    intro Hpred_name.
    rewrite Hpred_name in Hchunk.
    tauto.
  - (* Close *)
    destruct coef; try tauto.
    destruct q; try tauto.
    destruct Qnum; try tauto.
    destruct p; try tauto.
    destruct Qden; try tauto.
    destruct targs; try tauto.
    apply eval_pats_sound in Hverify.
    destruct Hverify as [vs Hverify].
    case_eq (assoc pred_name preds). 2:{
      intros Hpred_name.
      rewrite Hpred_name in Hverify.
      tauto.
    }
    intros pred_def Hpred_name.
    rewrite Hpred_name in Hverify.
    case_eq (combine_ (params pred_def) vs); intros env' [l l'] Hcombine_.
    rewrite Hcombine_ in Hverify.
    destruct l; try tauto.
    destruct l'; try tauto.
    iApply consume_sound; try eassumption.
    iIntros (h' env'' tree') "%HQsymex".
    iDestruct ("HQ" with "[% //]") as "HQ".
    iIntros "[Hbody Hh']".
    iApply "HQ".
    unfold own_heap, own_asn.
    iDestruct "Hbody" as (Hbody) "[Hbody_holds HHbody]".
    iDestruct "Hbody_holds" as %Hbody_holds.
    iDestruct "Hh'" as (Hh') "[Hh' HHh']".
    iDestruct "Hh'" as %HHh'.
    iExists (Hbody ⋅ Hh').
    iSplitL "". {
      iPureIntro.
      simpl.
      exists Hbody.
      exists Hh'.
      split. reflexivity.
      rewrite Hpred_name.
      destruct pred_def.
      rewrite Hcombine_.
      split. eexists; eassumption.
      assumption.
    }
    iApply own_logheap_lh_comp_intro.
    iFrame.
Qed.

Lemma verify_terminator_sound trace h env tree terminator Qsymex_return Qsymex_bb wp_call Qbb Qreturn:
  verify_terminator preds specs local_decls trace h env tree terminator Qsymex_return Qsymex_bb →
  (∀ h env tree, ⌜ Qsymex_return h env tree ⌝ -∗ own_heap h -∗ own_env Γ env -∗ Qreturn) -∗
  ▷ (∀ func_name targs args, spec_sound func_name targs args wp_call) -∗
  ▷ (∀ h env tree bb,
     ⌜ Qsymex_bb h env tree bb ⌝ -∗
     (∀ h env tree, ⌜ Qsymex_return h env tree ⌝ -∗ own_heap h -∗ own_env Γ env -∗ Qreturn) -∗
     own_heap h -∗ own_env Γ env -∗ Qbb bb) -∗
  own_heap h -∗
  own_env Γ env -∗
  wp_Terminator Γ terminator (wp_call_std wp_call) Qbb Qreturn.
Proof.
  intros Hverify.
  iIntros "Hreturn Hspecs HQbb Hh Henv".
  destruct terminator; simpl in Hverify.
  - (* Goto *)
    iApply wp_Goto_intro.
    iNext.
    iApply ("HQbb" $! h env tree target with "[% //] Hreturn Hh Henv").
  - (* SwitchInt *)
    iApply wp_SwitchInt_intro.
    iApply (verify_operand_sound with "[Hreturn Hspecs HQbb] Hh Henv"); try eassumption.
    clear Hverify.
    iIntros (h0 tree0 v ty) "%Hverify Hh Henv".
    iApply verify_switch_int_sound; try eassumption.
    iNext.
    iIntros (tree1 bb) "HQsymex_bb".
    iApply ("HQbb" with "HQsymex_bb Hreturn Hh Henv").
  - (* Return *)
    iApply wp_Return_intro.
    iApply ("Hreturn" with "[% //] Hh Henv").
  - (* Unreachable *)
    tauto.
  - (* Call *)
    destruct call.
    destruct func; try tauto.
    destruct const; try tauto.
    destruct value; try tauto.
    destruct ty; try tauto.
    rename id into name.
    destruct (string_dec name "VeriFast_ghost_command").
    + (* name = "VeriFast_ghost_command" *)
      subst.
      iApply (verify_ghost_command_sound with "[Hreturn Hspecs HQbb Henv] Hh"); try eassumption.
      clear Hverify.
      iIntros (h0 tree0) "%Hverify Hh0".
      simpl in Hverify.
      destruct target; try tauto.
      iApply wp_ghost_command_intro.
      iNext.
      iApply ("HQbb" with "[% //] Hreturn Hh0 Henv").
    + (* name ≠ "VeriFast_ghost_command" *)
      iApply wp_Call_intro.
      iApply (verify_operands_sound with "[Hreturn Hspecs HQbb] Hh Henv"); try eassumption.
      clear Hverify.
      iIntros (h0 tree0 vs) "%Hverify Hh0 Henv".
      iNext.
      iApply (verify_call_sound with "[Hreturn HQbb Henv] Hspecs Hh0"); try eassumption.
      clear Hverify.
      iIntros (h1 tree1 v) "%Hverify Hh1".
      iApply (verify_place_expr_sound with "[Hreturn HQbb] Hh1 Henv"); try eassumption.
      clear Hverify.
      iIntros (h2 tree2 place ty) "%Hverify %Hplace Hh2 Henv".
      iDestruct (store_to_place_sound with "[Hreturn HQbb] Hh2 Henv") as "Hstore"; try eassumption. 2: {
        iDestruct "Hstore" as "[Hpoints_to HQ]".
        iDestruct "Hpoints_to" as (v0) "Hpoints_to".
        iExists v0.
        iFrame.
      }
      clear Hverify.
      iIntros (h3 env0 tree3) "%Hverify Hh3 Henv0".
      simpl in Hverify.
      destruct target; try tauto.
      iNext.
      iApply ("HQbb" with "[% //] Hreturn Hh3 Henv0").
Qed.

Lemma verify_basic_block_sound trace h env tree bb Qsymex_return Qsymex_bb wp_call Qbb Qreturn:
  verify_basic_block preds specs local_decls trace h env tree bb Qsymex_return Qsymex_bb →
  (∀ h env tree, ⌜ Qsymex_return h env tree ⌝ -∗ own_heap h -∗ own_env Γ env -∗ Qreturn) -∗
  ▷ (∀ func_name targs args, spec_sound func_name targs args wp_call) -∗
  ▷ (∀ h env tree bb,
     ⌜ Qsymex_bb h env tree bb ⌝ -∗
     (∀ h env tree, ⌜ Qsymex_return h env tree ⌝ -∗ own_heap h -∗ own_env Γ env -∗ Qreturn) -∗
     own_heap h -∗ own_env Γ env -∗ Qbb bb) -∗
  own_heap h -∗
  own_env Γ env -∗
  wp_BasicBlock Γ bb (wp_call_std wp_call) Qbb Qreturn.
Proof.
  iIntros (Hverify) "Hreturn Hspecs Hbb Hh Henv".
  unfold verify_basic_block in Hverify.
  unfold wp_BasicBlock.
  iApply (verify_statements_sound with "[Hreturn Hspecs Hbb] Hh Henv"); try eassumption.
  clear Hverify.
  iIntros (h0 env0 tree0) "%Hverify Hh0 Henv".
  iApply (verify_terminator_sound with "Hreturn Hspecs Hbb Hh0 Henv"); eassumption.
Qed.

Lemma verify_basic_blocks_sound trace basic_blocks fuel h env tree bb Qsymex_return wp_call Qreturn:
  verify_basic_blocks preds specs local_decls trace basic_blocks fuel h env tree bb Qsymex_return →
  (∀ h env tree, ⌜ Qsymex_return h env tree ⌝ -∗ own_heap h -∗ own_env Γ env -∗ Qreturn) -∗
  □ ▷ (∀ func_name targs args, spec_sound func_name targs args wp_call) -∗
  own_heap h -∗
  own_env Γ env -∗
  wp_BasicBlocks Γ basic_blocks bb (wp_call_std wp_call) Qreturn.
Proof.
  revert trace h env tree bb.
  induction fuel as [|fuel].
  - (* O *)
    intros trace h env tree bb Hverify.
    tauto.
  - (* S fuel *)
    intros trace h env tree bb Hverify.
    iIntros "Hreturn #Hspecs Hh Henv".
    iApply wp_BasicBlocks_intro.
    simpl in Hverify.
    iApply (verify_basic_block_sound with "Hreturn Hspecs [] Hh Henv"); try eassumption.
    clear Hverify.
    iNext.
    iIntros (h0 env0 tree0 bb0) "%Hverify Hreturn Hh0 Henv0".
    destruct (assoc bb0 basic_blocks) as [bb'|]; try tauto.
    iApply (IHfuel with "Hreturn Hspecs Hh0 Henv0"); try eassumption.
Qed.

End local_decls.

Lemma alloc_params_sound trace h tree param_env Qsymex Q:
  Forall (λ '((x, info), arg), ty info = (Γ x).1) param_env →
  alloc_params trace h tree param_env Qsymex →
  (∀ h env tree dealloc_params,
   ⌜ Qsymex h env tree dealloc_params ⌝ -∗
   (∀ trace h env tree Qsymex Q,
    ⌜ dealloc_params trace h env tree Qsymex ⌝ -∗
    (∀ h tree,
     ⌜ Qsymex h tree ⌝ -∗
     own_heap h -∗
     Q) -∗
    own_heap h -∗
    own_env Γ env -∗
    ([∗ list] '((x, {| ty := ty |}), _) ∈ param_env, ∃ state, points_to_ ty (VPtr (Γ x).2) state) ∗
    Q) -∗
   own_heap h -∗
   own_env Γ env -∗
   Q) -∗
  own_heap h -∗
  ([∗ list] '((x, {| ty := ty |}), v) ∈ param_env, points_to ty (VPtr (Γ x).2) v) -∗
  Q.
Proof.
  revert trace h tree Qsymex Q.
  induction param_env as [|[[x info] arg] param_env]; simpl.
  - (* nil *)
    iIntros (trace h tree Qsymex Q HΓ Halloc) "HQ Hh Hparam_env".
    iApply ("HQ" with "[% //] [] Hh []").
    + iIntros (_ h0 env tree0 Qsymex0 Q0) "%HQsymex0 HQ0 Hh0 Henv".
      iSplitL "". done.
      iApply ("HQ0" with "[% //] Hh0").
    + simpl.
      done.
  - (* cons *)
    iIntros (trace h etree Qsymex Q HΓ Halloc).
    inversion HΓ; subst.
    clear HΓ.
    rename H1 into Hty_info.
    rename H2 into HΓ.
    destruct etree; try tauto.
    destruct data; try tauto.
    destruct (string_dec x0 x); try tauto.
    subst.
    iIntros "HQ Hh".
    destruct info.
    iIntros "[Hx Hparam_env]".
    destruct addr_taken; try tauto.
    iApply (IHparam_env with "[HQ Hx] Hh Hparam_env"); try eassumption.
    iIntros (h0 env tree dealloc_params0) "%HQsymex Hdealloc_params0 Hh0 Henv".
    iApply ("HQ" with "[% //] [Hdealloc_params0] Hh0 [Hx Henv]").
    + iIntros (trace0 h1 env0 tree0 Qsymex0 Q0) "%Hdealloc HQ0 Hh1 Henv0".
      case_eq (remove1_assoc x env0). 2:{
        intros Hx; rewrite Hx in Hdealloc; tauto.
      }
      intros [xstate env1] Hx.
      rewrite Hx in Hdealloc.
      destruct xstate; try tauto.
      iDestruct (remove1_assoc_own_env with "Henv0") as "[Hx Henv1]"; try eassumption.
      rewrite <- Hty_info.
      iFrame.
      iApply ("Hdealloc_params0" with "[% //] HQ0 Hh1 Henv1").
    + simpl.
      rewrite <- Hty_info.
      iFrame.
Qed.

Lemma alloc_locals_sound trace h env tree local_decls Qsymex Q:
  Forall (λ '(x, info), ty info = (Γ x).1) local_decls →
  alloc_locals trace h env tree local_decls Qsymex →
  (∀ h env tree dealloc_locals,
   ⌜ Qsymex h env tree dealloc_locals ⌝ -∗
   (∀ trace h env tree Qsymex Q,
    ⌜ dealloc_locals trace h env tree Qsymex ⌝ -∗
    (∀ h env tree,
     ⌜ Qsymex h env tree ⌝ -∗
     own_heap h -∗
     own_env Γ env -∗
     Q) -∗
    own_heap h -∗
    own_env Γ env -∗
    ([∗ list] '(x, {| ty := ty |}) ∈ local_decls, ∃ state, points_to_ ty (VPtr (Γ x).2) state) ∗
    Q) -∗
   own_heap h -∗
   own_env Γ env -∗
   Q) -∗
  own_heap h -∗
  own_env Γ env -∗
  ([∗ list] '(x, {| ty := ty |}) ∈ local_decls, ∃ state, points_to_ ty (VPtr (Γ x).2) state) -∗
  Q.
Proof.
  revert trace h env tree Qsymex Q.
  induction local_decls as [|[x info] local_decls]; simpl.
  - (* nil *)
    iIntros (trace h env tree Qsymex Q _ Halloc) "HQ Hh Henv _".
    iApply ("HQ" with "[% //] [] Hh Henv").
    iIntros (trace0 h0 env0 tree0 Qsymex0 Q0) "%HQsymex0 HQ0 Hh0 Henv0".
    iSplitL "". done.
    iApply ("HQ0" with "[% //] Hh0 Henv0").
  - (* cons *)
    iIntros (trace h env tree Qsymex Q HΓ Halloc) "HQ Hh Henv [Hx Hlocal_decls]".
    inversion HΓ; subst.
    clear HΓ.
    destruct info.
    simpl in H1.
    rename H1 into Hty.
    rename H2 into HΓ.
    destruct tree; try tauto.
    destruct data; try tauto.
    destruct (string_dec x x0); try tauto.
    subst x0.
    destruct addr_taken.
    + (* true *)
      destruct (Ty_eqb ty Never || Ty_eqb ty Tuple0).
      * (* true *)
        pose proof (Halloc':=Halloc (Γ x).2 VDummy (Γ_non_null x)).
        iApply (IHlocal_decls with "[HQ Hx] Hh [Henv] Hlocal_decls"); try eassumption. 2:{
          simpl.
          iFrame.
          done.
        }
        iIntros (h0 env0 tree0 dealloc_locals) "%HQsymex Hdealloc_locals_sound Hh0 Henv0".
        iApply ("HQ" with "[% //] [Hdealloc_locals_sound Hx] Hh0 Henv0").
        iIntros (trace0 h1 env1 tree1 Qsymex0 Q0) "%Hdealloc_locals HQ0 Hh1 Henv1".
        iFrame.
        iApply ("Hdealloc_locals_sound" with "[% //] [HQ0] Hh1 Henv1").
        iAssumption.
      * (* false *)
        iDestruct "Hx" as (state) "Hx".
        pose proof (Halloc':=Halloc (Γ x).2 state (Γ_non_null x)).
        iApply (IHlocal_decls with "[HQ] [Hx Hh] [Henv] Hlocal_decls"); try eassumption.
        2:{
          iApply (own_heap_cons_intro with "[Hx] Hh").
          iApply (own_chunk_prim_intro).
          done.
        }
        2:{
          simpl.
          iSplitL "". done.
          done.
        }
        iIntros (h0 env0 tree0 dealloc_locals) "%HQsymex Hdealloc_locals_sound Hh0 Henv0".
        iApply ("HQ" with "[% //] [Hdealloc_locals_sound] Hh0 Henv0").
        iIntros (trace0 h1 env1 tree1 Qsymex0 Q0) "%Hconsume HQ0 Hh1 Henv1".
        assert (Hex: ∀ P (Q R: iProp Σ), (∃ (v: Value), P v ∗ Q ∗ R) -∗ ((∃ v, P v) ∗ Q) ∗ R). {
          iIntros (P Q1 R) "[%v [HP [HQ HR]]]".
          iSplitR "HR". {
            iSplitR "HQ". {
              iExists v.
              done.
            }
            done.
          }
          done.
        }
        iApply Hex.
        iApply (consume_points_to__sound with "[Hdealloc_locals_sound HQ0 Henv1] Hh1"); try eassumption.
        iIntros (h2 tree2 v) "%Hdealloc Hh2".
        iApply ("Hdealloc_locals_sound" with "[% //] [HQ0] Hh2 Henv1").
        iAssumption.
    + (* false *)
      iApply (IHlocal_decls with "[HQ] Hh [Hx Henv] Hlocal_decls"); try eassumption. 2:{
        rewrite Hty.
        simpl. iFrame.
      }
      iIntros (h0 env0 tree0 dealloc_locals) "%HQsymex Hdealloc_locals_sound Hh0 Henv0".
      iApply ("HQ" with "[% //] [Hdealloc_locals_sound] Hh0 Henv0").
      iIntros (trace0 h1 env1 tree1 Qsymex0 Q0) "%Hdealloc HQ0 Hh1 Henv1".
      case_eq (remove1_assoc x env1). 2:{
        intros Hx; rewrite Hx in Hdealloc; tauto.
      }
      intros [xstate env2] Hx.
      rewrite Hx in Hdealloc.
      destruct xstate; try tauto.
      iDestruct (remove1_assoc_own_env with "Henv1") as "[Hx Henv2]"; try eassumption.
      rewrite Hty.
      iFrame.
      iApply ("Hdealloc_locals_sound" with "[% //] HQ0 Hh1 Henv2").
Qed.

End Γ.

Lemma verify_body_sound trace h tree body args Qsymex wp_call Q:
  verify_body preds specs trace h tree body args Qsymex →
  □ ▷ (∀ func_name targs args, spec_sound func_name targs args wp_call) -∗
  (∀ h tree result,
   ⌜ Qsymex h tree result ⌝ -∗
   own_heap h -∗
   Q result) -∗
  own_heap h -∗
  wp_Body body args (wp_call_std wp_call) Q.
Proof.
  iIntros (Hverify) "#Hspecs HQ Hh".
  unfold verify_body in Hverify.
  unfold wp_Body.
  iIntros (Γ) "%Γ_well_typed %Γ_non_null %Hlocal_decls_unique".
  case_eq (local_decls body). {
    intros Hlocal_decls.
    rewrite Hlocal_decls in Hverify.
    tauto.
  }
  intros [result_var result_var_info] local_decls' Hlocal_decls.
  rewrite {1}Hlocal_decls in Hverify.
  case_eq (combine_ local_decls' args).
  intros param_env [local_decls'' args'] Hcombine_.
  rewrite Hcombine_ in Hverify.
  destruct (combine__append local_decls' args param_env local_decls'' args' Hcombine_) as [Hcombine_1 Hcombine_2].
  subst.
  iApply (alloc_params_sound with "[HQ] Hh"); try eassumption. {
    rewrite Hlocal_decls in Hlocal_decls_unique.
    apply Forall_cons_1 in Hlocal_decls_unique.
    destruct Hlocal_decls_unique as [_ Hlocal_decls'_unique].
    apply Forall_app in Hlocal_decls'_unique.
    destruct Hlocal_decls'_unique as [H1 H2].
    apply Forall_map in H1.
    apply Forall_impl with (2:=H1).
    intros.
    destruct a.
    simpl in H.
    destruct p.
    apply Γ_well_typed.
    rewrite Hlocal_decls.
    apply H.
  }
  clear Hverify.
  iIntros (h0 env0 tree0 dealloc_params) "%Halloc_locals Hdealloc_params_sound Hh0 Henv0".
  iApply (alloc_locals_sound with "[Hdealloc_params_sound HQ] Hh0 Henv0"); try eassumption. {
    rewrite Hlocal_decls in Hlocal_decls_unique.
    apply Forall_cons_1 in Hlocal_decls_unique.
    destruct Hlocal_decls_unique as [Hresult_var_unique Hlocal_decls'_unique].
    apply Forall_app in Hlocal_decls'_unique.
    destruct Hlocal_decls'_unique as [Hparams_unique Hlocal_decls''_unique].
    apply Forall_cons. {
      apply Γ_well_typed.
      rewrite Hlocal_decls.
      assumption.
    }
    apply Forall_impl with (2:=Hlocal_decls''_unique).
    intros [x info] Hx.
    apply Γ_well_typed.
    rewrite Hlocal_decls.
    apply Hx.
  }
  clear Halloc_locals.
  iIntros (h1 env tree1 dealloc_locals) "%Hverify_bb Hdealloc_locals_sound Hh1 Henv".
  case_eq (basic_blocks body). {
    intros Hbasic_blocks.
    rewrite Hbasic_blocks in Hverify_bb.
    tauto.
  }
  intros [bb0 bb_data0] basic_blocks' Hbasic_blocks.
  rewrite <- Hbasic_blocks.
  rewrite {1}Hbasic_blocks in Hverify_bb.
  iApply (verify_basic_blocks_sound with "[-Hh1 Henv] Hspecs Hh1 Henv"); try eassumption.
  clear Hverify_bb.
  iIntros (h2 env1 tree2) "%Hverify_operand Hh2 Henv1".
  iApply (verify_operand_sound with "[-Hh2 Henv1] Hh2 Henv1"); try eassumption.
  iIntros (h3 tree3 result result_ty) "%Hdealloc_locals Hh3 Henv1".
  iApply ("Hdealloc_locals_sound" with "[% //] [-Hh3 Henv1] Hh3 Henv1").
  iIntros (h4 env2 tree4) "%Hdealloc_params Hh4 Henv2".
  iApply ("Hdealloc_params_sound" with "[% //] [-Hh4 Henv2] Hh4 Henv2").
  iIntros (h5 tree5) "%HQsymex Hh5".
  iApply ("HQ" with "[% //] Hh5").
Qed.

Lemma forall_tys_sound trace tys Q vs:
  forall_tys trace tys Q →
  values_have_tys tys vs → Q vs.
Proof.
  revert trace Q vs.
  induction tys as [|ty tys]; intros trace Q vs Hforall Hvs; destruct vs; simpl in *; try tauto.
  destruct Hvs as [Hv Hvs].
  apply forall_ty_sound with (v:=v) (2:=Hv) in Hforall.
  apply IHtys with (1:=Hforall) (2:=Hvs).
Qed.

Lemma own_heap_nil:
  ⊢ own_heap [].
Proof.
  unfold own_heap.
  iExists ∅.
  iSplitL "". {
    iPureIntro.
    unfold heap_holds.
    reflexivity.
  }
  unfold own_logheap.
  iApply lh_big_ast_lh_empty_intro.
Qed.

Lemma body_is_correct_sound trace body spec tree wp_call:
  body_is_correct preds specs trace body spec tree →
  inputs body = map snd (spec_params spec) →
  output body = spec_output spec →
  □ ▷ (∀ func_name targs args, spec_sound func_name targs args wp_call) -∗
  ∀ targs args,
  spec_holds spec targs args (wp_Body' body args (wp_call_std wp_call)).
Proof.
  iIntros (Hcorrect Hinputs Houtput) "#Hspecs %targs %args".
  unfold spec_holds.
  iIntros (env') "Hpre %Q HQ".
  unfold body_is_correct in Hcorrect.
  unfold wp_Body'.
  iIntros "%Hvalues_have_tys".
  rewrite -{1}Hinputs in Hcorrect.
  apply forall_tys_sound with (2:=Hvalues_have_tys) in Hcorrect.
  iApply (produce_sound with "[HQ] [] Hpre"); try eassumption. 2:{
    iApply own_heap_nil.
  }
  iIntros (h tree0) "%Hverify Hh".
  iApply (verify_body_sound with "Hspecs [HQ] Hh"); try eassumption.
  iIntros (h0 tree1 result) "%Hconsume Hh0".
  iApply (consume_sound with "[HQ] Hh0"); try eassumption.
  iIntros (h1 env'0 tree2) "_ [Hpost Hh1] %Hresult".
  iApply ("HQ" with "[Hpost]").
  iSplitL "". {
    iPureIntro.
    rewrite <- Houtput.
    done.
  }
  iExists env'0.
  iFrame.
Qed.

End specs.

End preds.

End gfunctors.
