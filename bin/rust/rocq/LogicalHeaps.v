(*

A VeriFast logical heap is a multiset of primitive heap chunks.
A primitive heap chunk is any heap chunk other than a user-defined
predicate chunk.

Note: in full VeriFast, logical heaps are *fractional multisets*
(i.e. functions from X to Real+, not to Nat). Also, they may be
*infinite multisets* (see the I/O work and copredicates).

*)

From Coq Require Export Utf8.
Require Export SymbolicExecution.

Parameter LogHeap: Type.

Parameter lh_empty: LogHeap.
Parameter lh_comp: LogHeap → LogHeap → LogHeap.
Parameter lh_sing: PrimChunk → LogHeap.

Declare Scope logheap_scope.

Notation "∅" := lh_empty (format "∅") : logheap_scope.

Infix "⋅" := lh_comp (at level 50, left associativity) : logheap_scope.

Open Scope logheap_scope.

Definition lh_le(lh1 lh2: LogHeap): Prop :=
  ∃ lh1', lh1 ⋅ lh1' = lh2.

Infix "≼" := lh_le (at level 70) : logheap_scope.

Notation "{[+ x +]}" := (lh_sing x)
  (at level 1, format "{[+ x +]}") : logheap_scope.

Axiom lh_left_id: forall H, ∅ ⋅ H = H.
Axiom lh_right_id: forall H, H ⋅ ∅  = H.
Axiom lh_assoc: forall H1 H2 H3, H1 ⋅ (H2 ⋅ H3) = (H1 ⋅ H2) ⋅ H3.
Axiom lh_comm: forall H1 H2, H1 ⋅ H2 = H2 ⋅ H1.

Inductive has_type: Value -> Ty -> Prop :=
| has_type_Bool b:
  has_type (VBool b) Bool
| has_type_RawPtr ptr pointeeTy:
  has_type (VPtr ptr) (RawPtr pointeeTy)
.

Section preds.

Variable preds: list (string * PredDef).

Inductive pat_matches: forall (env: Env)(pat: Pat)(v: Value)(env': Env), Prop :=
| LitPat_matches env e v:
  eval env e = v →
  pat_matches env (LitPat e) v env
| VarPat_matches env x v:
  pat_matches env (VarPat x) v ((x, LSValue (Some v))::env)
.

Inductive pats_match: forall (env: Env)(pats: list Pat)(vs: list Value)(env': Env), Prop :=
| empty_pats_match env:
  pats_match env [] [] env
| nonempty_pats_match env pat pats v vs env' env'':
  pat_matches env pat v env' →
  pats_match env' pats vs env'' →
  pats_match env (pat::pats) (v::vs) env''
.

Inductive asn_holds: forall (H: LogHeap)(env: Env)(a: Asn)(env': Env), Prop :=
| BoolAsn_holds H env e:
  eval env e = VBool true →
  H = ∅ →
  asn_holds H env (BoolAsn e) env
| PointsToAsn_holds H env ty ptr pat v env':
  H = {[+ PointsTo_ ty (eval env ptr) (VSome v) +]} →
  pat_matches env pat v env' →
  asn_holds H env (PointsToAsn ty ptr pat) env'
| PredAsn_holds H env pred_name pats vs env' params body env'' env''':
  assoc pred_name preds = Some {| params := params; body := body |} →
  combine_ params vs = (env'', ([], [])) →
  asn_holds H (map (fun '((x, ty), v) => (x, LSValue (Some v))) env'') body env''' →
  pats_match env pats vs env' →
  asn_holds H env (PredAsn pred_name pats) env'
| SepAsn_holds H1 H2 env a1 env' a2 env'':
  asn_holds H1 env a1 env' →
  asn_holds H2 env' a2 env'' →
  asn_holds (H1 ⋅ H2) env (SepAsn a1 a2) env''
| IfAsn_holds_true H env cond a1 a2 env':
  eval env cond = VBool true →
  asn_holds H env a1 env' →
  asn_holds H env (IfAsn cond a1 a2) env'
| IfAsn_holds_false H env cond a1 a2 env':
  eval env cond ≠ VBool true →
  asn_holds H env a2 env' →
  asn_holds H env (IfAsn cond a1 a2) env'
.

Definition chunk_holds(H: LogHeap)(chunk: Chunk): Prop :=
  match chunk with
    Prim chunk => H = {[+ chunk +]}
  | PointsTo ty ptr v => H = {[+ PointsTo_ ty ptr (VSome v) +]}
  | User pred_name vs =>
    match assoc pred_name preds with
      None => False
    | Some {| params := params; body := body |} =>
      match combine_ params vs with
        (env, ([], [])) =>
        ∃ env', asn_holds H (map (fun '((x, ty), v) => (x, LSValue (Some v))) env) body env'
      | _ => False
      end
    end
  end.

Fixpoint heap_holds(H: LogHeap)(h: Heap): Prop :=
  match h with
    [] => H = ∅
  | chunk::chunks =>
    ∃ H1 H2,
    H = H1 ⋅ H2 ∧ chunk_holds H1 chunk ∧ heap_holds H2 chunks
  end.

Lemma heap_holds_append(H1 H2: LogHeap)(h1 h2: Heap):
  heap_holds H1 h1 →
  heap_holds H2 h2 →
  heap_holds (H1 ⋅ H2) (h1 ++ h2).
Proof.
  revert H1 H2 h2.
  induction h1; intros H1 H2 h2 Hh1 Hh2; simpl in *; subst.
  - (* nil *)
    rewrite lh_left_id.
    assumption.
  - (* cons *)
    destruct Hh1 as (Hchunk & Hh1 & HH1 & HHchunk & HHh1).
    exists Hchunk.
    exists (Hh1 ⋅ H2).
    split. {
      rewrite HH1.
      rewrite lh_assoc.
      reflexivity.
    }
    split. assumption.
    apply IHh1; assumption.
Qed.

Lemma nth__iter_sound(H_done H_todo: LogHeap)(k: nat)(h_done h_todo: Heap)(chunk: Chunk)(h: Heap):
  heap_holds H_done h_done →
  heap_holds H_todo h_todo →
  nth__iter k h_done h_todo = Some (chunk, h) →
  ∃ Hchunk Hh,
  H_done ⋅ H_todo = Hchunk ⋅ Hh ∧
  chunk_holds Hchunk chunk ∧
  heap_holds Hh h.
Proof.
  revert H_done H_todo h_done h_todo chunk h.
  induction k; intros H_done H_todo h_done h_todo chunk h Hh_done Hh_todo Hnth__iter.
  - (* O *)
    destruct h_todo as [|chunk' h']; try discriminate.
    simpl in Hnth__iter.
    injection Hnth__iter; intros; subst.
    inversion Hh_todo.
    rename x into Hchunk.
    rename H into HH_todo.
    destruct HH_todo as [Hh' [HH_todo [HHchunk HHh']]].
    exists Hchunk.
    exists (H_done ⋅ Hh').
    split. {
      rewrite lh_assoc.
      rewrite lh_comm with (H1:=Hchunk).
      rewrite <- lh_assoc.
      congruence.
    }
    split. assumption.
    apply heap_holds_append; assumption.
  - (* S k *)
    destruct h_todo as [|chunk' h']; try discriminate.
    simpl in Hnth__iter.
    inversion Hh_todo.
    rename x into Hchunk'.
    rename H into HH_todo.
    destruct HH_todo as [H' [HH_todo [HHchunk' Hh']]].
    destruct (IHk (Hchunk' ⋅ H_done) H' (chunk'::h_done) h' chunk h) as [Hchunk [Hh [Hchunk1 [Hchunk2 HHh]]]].
    + simpl.
      exists Hchunk'.
      exists H_done.
      tauto.
    + assumption.
    + assumption.
    + exists Hchunk.
      exists Hh.
      split. {
        rewrite HH_todo.
        rewrite <- Hchunk1.
        rewrite lh_comm with (H2:=H_done).
        apply lh_assoc.
      }
      tauto.
Qed.

Lemma nth__sound(H: LogHeap)(h: Heap)(k: nat)(chunk: Chunk)(h': Heap):
  heap_holds H h →
  nth_ k h = Some (chunk, h') →
  ∃ Hchunk Hh',
  H = Hchunk ⋅ Hh' ∧
  chunk_holds Hchunk chunk ∧
  heap_holds Hh' h'.
Proof.
  intros.
  unfold nth_ in H1.
  apply nth__iter_sound with (H_done:=∅) (2:=H0) in H1. 2:{
    simpl.
    reflexivity.
  }
  destruct H1 as (Hchunk & Hh & HH & HHchunk & Hh').
  exists Hchunk.
  exists Hh.
  rewrite lh_left_id in HH.
  tauto.
Qed.

Lemma consume_chunk_sound(H: LogHeap)(trace: Trace)(h: Heap)(tree: SymexTree)(Q: Heap → SymexTree → Chunk → Prop):
  heap_holds H h →
  consume_chunk trace h tree Q →
  ∃ Hchunk H' h' tree' chunk,
  H = Hchunk ⋅ H' ∧
  chunk_holds Hchunk chunk ∧
  heap_holds H' h' ∧
  Q h' tree' chunk.
Proof.
  revert H trace h Q.
  induction tree; intros; try tauto.
  destruct data; try tauto.
  - (* ConsumeChunk *)
    simpl in H1.
    case_eq (nth_ chunk_index h); intros; rewrite H2 in H1; try tauto.
    destruct p as [chunk h'].
    apply nth__sound with (1:=H0) in H2.
    destruct H2 as (Hchunk & Hh' & HH & HHchunk & H').
    exists Hchunk.
    exists Hh'.
    exists h'.
    exists tree.
    exists chunk.
    tauto.
  - (* AutoOpen *)
    simpl in H1.
    case_eq (nth_ chunk_index h); intros; rewrite H2 in H1; try tauto.
    destruct p as [chunk h'].
    destruct chunk; try tauto.
    apply nth__sound with (1:=H0) in H2.
    destruct H2 as (Hchunk & Hh' & HH & HHchunk & H').
    simpl in HHchunk.
    apply IHtree with (H:=H) (2:=H1).
    simpl.
    exists Hchunk.
    exists Hh'.
    split. assumption.
    split. {
      rewrite HHchunk.
      reflexivity.
    }
    assumption.
Qed.

Lemma consume_points_to_sound H trace h tree ty ptr Q:
  heap_holds H h →
  consume_points_to trace h tree ty ptr Q →
  ∃ H' h' tree' v,
  H = {[+ PointsTo_ ty ptr (VSome v) +]} ⋅ H' ∧
  heap_holds H' h' ∧
  Q h' tree' v.
Proof.
  intros.
  unfold consume_points_to in H1.
  apply consume_chunk_sound with (1:=H0) in H1.
  destruct H1 as (Hchunk & H' & h' & tree' & chunk & ? & ? & ?).
  destruct chunk; try tauto.
  destruct H3 as (? & ? & ? & ?).
  subst.
  simpl in H2.
  exists H'.
  exists h'.
  exists tree'.
  exists rhs.
  split. {
    rewrite H2.
    reflexivity.
  }
  tauto.
Qed.

Lemma consume_points_to__sound H trace h tree ty ptr Q:
  heap_holds H h →
  consume_points_to_ trace h tree ty ptr Q →
  ∃ H' h' tree' v,
  H = {[+ PointsTo_ ty ptr v +]} ⋅ H' ∧
  heap_holds H' h' ∧
  Q h' tree' v.
Proof.
  intros.
  unfold consume_points_to_ in H1.
  apply consume_chunk_sound with (1:=H0) in H1.
  destruct H1 as (Hchunk & H' & h' & tree' & chunk & ? & ? & ?).
  destruct chunk; try tauto.
  destruct chunk; try tauto.
  destruct H3 as (? & ? & ? & ?).
  subst.
  simpl in H2.
  exists H'.
  exists h'.
  exists tree'.
  exists rhs.
  split. {
    rewrite H2.
    reflexivity.
  }
  tauto.
Qed.

Lemma match_pat_sound env pat v Q:
  match_pat env pat v Q →
  ∃ env',
  pat_matches env pat v env' ∧
  Q env'.
Proof.
  destruct pat; simpl; intros.
  - (* LitPat *)
    destruct H.
    subst.
    exists env.
    split. {
      constructor.
      reflexivity.
    }
    assumption.
  - (* VarPat *)
    exists ((x, LSValue (Some v))::env).
    split. {
      constructor.
    }
    assumption.
Qed.

Lemma match_pats_sound trace env pats vs Q:
  match_pats trace env pats vs Q →
  ∃ env',
  pats_match env pats vs env' ∧
  Q env'.
Proof.
  revert trace env vs Q.
  induction pats.
  - (* nil *)
    intros trace env vs Q ?.
    destruct vs; try tauto.
    exists env.
    split. constructor.
    assumption.
  - (* cons *)
    intros trace env vs Q ?.
    destruct vs as [|v vs]; try tauto.
    simpl in H.
    apply match_pat_sound in H.
    destruct H as [env' [? ?]].
    apply IHpats in H0.
    destruct H0 as [env'' [? ?]].
    exists env''.
    split. {
      apply nonempty_pats_match with (env':=env'); assumption.
    }
    assumption.
Qed.

Lemma assume_sound env e Q:
  assume env e Q →
  eval env e = VBool true → Q.
Proof.
  destruct e; try tauto.
  destruct b; try tauto.
  simpl.
  intros.
  discriminate.
Qed.

Lemma assume_false_sound env e Q:
  assume_false env e Q →
  eval env e ≠ VBool true → Q.
Proof.
  destruct e; try tauto.
  destruct b; try tauto.
Qed.

Lemma consume_sound(H: LogHeap)(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(a: Asn)(Q: Heap → Env → SymexTree → Prop):
  heap_holds H h →
  consume trace h env tree a Q →
  ∃ h' env' tree' H1 H2,
  H = H1 ⋅ H2 ∧ asn_holds H1 env a env' ∧
  heap_holds H2 h' ∧
  Q h' env' tree'.
Proof.
  revert H trace h env tree Q.
  induction a; intros H trace h env tree Q Hh Hconsume; simpl in Hconsume.
  - (* BoolAsn *)
    exists h.
    exists env.
    exists tree.
    exists ∅.
    exists H.
    split. {
      rewrite lh_left_id.
      reflexivity.
    }
    assert (HeQ: eval env e = VBool true ∧ Q h env tree). {
      destruct e; simpl in Hconsume; try tauto.
      destruct b; tauto.
    }
    destruct HeQ as [He HQ].
    split. {
      constructor.
      - assumption.
      - reflexivity.
    }
    tauto.
  - (* PointsToAsn *)
    apply consume_points_to_sound with (1:=Hh) in Hconsume.
    destruct Hconsume as (H' & h' & tree' & v & HH & HH' & ?).
    apply match_pat_sound in H0.
    destruct H0 as [env' [? ?]].
    exists h'.
    exists env'.
    exists tree'.
    exists {[+ PointsTo_ ty (eval env ptr) (VSome v) +]}.
    exists H'.
    split. assumption.
    split. {
      apply PointsToAsn_holds with (v:=v); tauto.
    }
    tauto.
  - (* PredAsn *)
    apply consume_chunk_sound with (1:=Hh) in Hconsume.
    destruct Hconsume as (Hchunk & H' & h' & tree' & chunk & HH & HHchunk & HH' & ?).
    destruct chunk; try tauto.
    destruct H0.
    subst pred_name0.
    apply match_pats_sound in H1.
    destruct H1 as [env' [? ?]].
    exists h'.
    exists env'.
    exists tree'.
    exists Hchunk.
    exists H'.
    split. assumption.
    split. {
      simpl in HHchunk.
      case_eq (assoc pred_name preds); intros; rewrite H2 in HHchunk; try tauto.
      destruct p as [params body].
      case_eq (combine_ params args0); intros; rewrite H3 in HHchunk.
      rename l into env''.
      destruct p as [params' args'].
      destruct params'; try tauto.
      destruct args'; try tauto.
      destruct HHchunk as [env''' Hbody].
      apply PredAsn_holds with (vs:=args0) (params:=params) (body:=body) (env'':=env'') (env''':=env'''); try assumption.
    }
    tauto.
  - (* SepAsn *)
    apply IHa1 with (1:=Hh) in Hconsume.
    destruct Hconsume as (h' & env' & tree' & Ha1 & H' & HH & HHa1 & HH' & Hconsume).
    subst H.
    apply IHa2 with (1:=HH') in Hconsume.
    destruct Hconsume as (h'' & env'' & tree'' & Ha2 & H'' & HH'eq & HHa2 & Hh'' & HQ).
    exists h''.
    exists env''.
    exists tree''.
    exists (Ha1 ⋅ Ha2).
    exists H''.
    subst H'.
    split. apply lh_assoc.
    split. {
      apply SepAsn_holds with (env':=env'); assumption.
    }
    tauto.
  - (* IfAsn *)
    destruct tree; try tauto.
    destruct Hconsume as [Htrue Hfalse].
    assert ({eval env cond = VBool true} + {eval env cond ≠ VBool true}). {
      apply value_eq_dec.
    }
    destruct H0.
    + (* true *)
      apply assume_sound with (2:=e) in Htrue.
      apply IHa1 with (1:=Hh) in Htrue.
      destruct Htrue as (h' & env' & tree' & H1 & H2 & HH & Ha1 & Hh' & HQ).
      exists h'.
      exists env'.
      exists tree'.
      exists H1.
      exists H2.
      split. assumption.
      split. {
        constructor; assumption.
      }
      tauto.
    + (* false *)
      apply assume_false_sound with (2:=n) in Hfalse.
      apply IHa2 with (1:=Hh) in Hfalse.
      destruct Hfalse as (h' & env' & tree' & H1 & H2 & HH & Ha1 & Hh' & HQ).
      exists h'.
      exists env'.
      exists tree'.
      exists H1.
      exists H2.
      split. assumption.
      split. {
        constructor; assumption.
      }
      tauto.
Qed.

Lemma produce_pat_sound trace env ty pat Q v env':
  produce_pat trace env ty pat Q →
  pat_matches env pat v env' →
  Q env' v.
Proof.
  destruct pat.
  - (* LitPat *)
    simpl.
    intros.
    inversion H0; subst.
    assumption.
  - (* VarPat *)
    simpl.
    intros.
    inversion H0; subst.
    apply H.
Qed.

Lemma produce_pats_sound trace env pats Q vs env':
  produce_pats trace env pats Q →
  pats_match env pats vs env' →
  Q env' vs.
Proof.
  revert trace env Q vs env'.
  induction pats.
  - (* nil *)
    intros trace env Q vs env' Hproduce Hmatch.
    simpl in Hproduce.
    inversion Hmatch; subst.
    assumption.
  - (* cons *)
    intros trace env Q vs env' Hproduce Hmatch.
    inversion Hmatch; subst.
    simpl in Hproduce.
    destruct a.
    + (* LitPat *)
      inversion H2; subst.
      apply IHpats with (vs:=vs0) (env' := env') in Hproduce; assumption.
    + tauto.
Qed.

Lemma produce_sound(H0: LogHeap)(H: LogHeap)(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(a: Asn)(env': Env)(Q: Heap → Env → SymexTree → Prop):
  heap_holds H0 h →
  asn_holds H env a env' →
  produce trace h env tree a Q →
  ∃ h' tree',
  Q h' env' tree' ∧ heap_holds (H0 ⋅ H) h'.
Proof.
  revert H0 H trace h env tree env' Q.
  induction a; intros H0 H trace h env tree env' Q.
  - (* BoolAsn *)
    intros Hh Hholds Hproduce.
    inversion Hholds; subst.
    simpl in Hproduce.
    apply assume_sound with (2:=H3) in Hproduce.
    exists h.
    exists tree.
    rewrite lh_right_id.
    tauto.
  - (* PointsToAsn *)
    intros Hh Hholds Hproduce.
    inversion Hholds; subst.
    simpl in Hproduce.
    apply produce_pat_sound with (2:=H9) in Hproduce.
    exists (PointsTo ty (eval env ptr) v::h).
    exists tree.
    split. assumption.
    simpl.
    exists {[+ PointsTo_ ty (eval env ptr) (VSome v) +]}.
    exists H0.
    split. apply lh_comm.
    split. reflexivity.
    assumption.
  - (* PredAsn *)
    intros Hh Hholds Hproduce.
    simpl in Hproduce.
    inversion Hholds; subst.
    apply produce_pats_sound with (2:=H10) in Hproduce.
    exists (User pred_name vs::h).
    exists tree.
    split. assumption.
    simpl.
    exists H.
    exists H0.
    split. apply lh_comm.
    split. {
      rewrite H4.
      rewrite H5.
      exists env'''.
      assumption.
    }
    assumption.
  - (* SepAsn *)
    intros Hh Hholds Hproduce.
    inversion Hholds; subst.
    simpl in Hproduce.
    apply IHa1 with (1:=Hh) (2:=H7) in Hproduce.
    destruct Hproduce as (h' & tree' & Hproduce & Hh').
    apply IHa2 with (1:=Hh') (2:=H9) in Hproduce.
    destruct Hproduce as (h'' & tree'' & HQ & Hh'').
    exists h''.
    exists tree''.
    rewrite lh_assoc.
    tauto.
  - (* IfAsn *)
    intros Hh Hholds Hproduce.
    simpl in Hproduce.
    destruct tree; try tauto.
    destruct Hproduce as [Htrue Hfalse].
    inversion Hholds; subst.
    + (* true *)
      apply assume_sound with (2:=H8) in Htrue.
      apply IHa1 with (1:=Hh) (2:=H9) in Htrue.
      assumption.
    + (* false *)
      apply assume_false_sound with (2:=H8) in Hfalse.
      apply IHa2 with (1:=Hh) (2:=H9) in Hfalse.
      assumption.
Qed.

End preds.
