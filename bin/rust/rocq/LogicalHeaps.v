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

Section preds.

Variable preds: list (string * PredDef).

Inductive pat_matches: forall (env: Env)(pat: Pat)(v: Value)(env': Env), Prop :=
| LitPat_matches env e v:
  eval env e = v →
  pat_matches env (LitPat e) v env
| VarPat_matches env x v:
  pat_matches env (VarPat x) v ((x, LSValue v)::env)
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
  asn_holds H (map (fun '((x, ty), v) => (x, LSValue v)) env'') body env''' →
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
        ∃ env', asn_holds H (map (fun '((x, ty), v) => (x, LSValue v)) env) body env'
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
    exists ((x, LSValue v)::env).
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
    apply match_pats_sound in H0.
    destruct H0 as [env' [? ?]].
    exists h'.
    exists env'.
    exists tree'.
    exists Hchunk.
    exists H'.
    split. assumption.
    split. {
      simpl in HHchunk.
      case_eq (assoc pred_name0 preds); intros; rewrite H2 in HHchunk; try tauto.
      destruct p as [params body].
      case_eq (combine_ params args0); intros; rewrite H3 in HHchunk.
      rename l into env''.
      destruct p as [params' args'].
      destruct params'; try tauto.
      destruct args'; try tauto.
      
      apply PredAsn_holds with (vs:=args0) (params:=params) (body:=body).
    
Admitted.

Lemma produce_sound(H0: LogHeap)(H: LogHeap)(trace: Trace)(h: Heap)(env: Env)(tree: SymexTree)(a: Asn)(env': Env)(Q: Heap → Env → SymexTree → Prop):
  heap_holds H0 h →
  asn_holds H env a env' →
  produce trace h env tree a Q →
  ∃ h' tree',
  Q h' env' tree' ∧ heap_holds (H0 ⋅ H) h'.

End preds.
