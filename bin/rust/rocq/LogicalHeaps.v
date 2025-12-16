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

Infix "⋅" := lh_comp (at level 50, left associativity) : logheap_scope.

Open Scope logheap_scope.

Definition lh_le(lh1 lh2: LogHeap): Prop :=
  ∃ lh1', lh1 ⋅ lh1' = lh2.

Infix "≼" := lh_le (at level 70) : logheap_scope.

Notation "{[+ x +]}" := (lh_sing x)
  (at level 1, format "{[+ x +]}") : logheap_scope.

Require KnasterTarski.

Module LogHeapPredTarskiParams.
  Definition X: Type := string * list Value * LogHeap.
End LogHeapPredTarskiParams.

Module Tarski_ := KnasterTarski.Predicates LogHeapPredTarskiParams.
Module Tarski := Tarski_.T.

Section preds.

Variable preds: list (string * PredDef).

Section pred_interp.

Variable pred_interp: string * list Value * LogHeap -> Prop.

Fixpoint lh_consume(H: LogHeap)(env: Env)(a: Asn)(Q: LogHeap → Env → Prop): Prop :=
  match a with
    BoolAsn e => eval env e = VBool true ∧ Q H env
  | PointsToAsn ty ptr rhs =>
    ∃ v H',
    H = {[+ PointsTo ty (eval env ptr) v +]} ⋅ H' ∧
    match_pat env rhs v @@ fun env =>
    Q H' env
  | PredAsn pred_name pats =>
    ∃ vs Hp H',
    H = Hp ⋅ H' ∧
    pred_interp (pred_name, vs, Hp) ∧
    match_pats [] env pats vs @@ fun env =>
    Q H' env
  | SepAsn a1 a2 =>
    lh_consume H env a1 @@ fun H env =>
    lh_consume H env a2 Q
  | IfAsn cond a1 a2 =>
    (eval env cond = VBool true → lh_consume H env a1 Q) ∧
    (eval env cond ≠ VBool true → lh_consume H env a2 Q)
  end.

Definition asn_holds(H: LogHeap)(env: Env)(a: Asn): Prop :=
  lh_consume H env a @@ fun _ _ => True.

Definition pred_holds_ '(pred_name, args, H): Prop :=
  match assoc pred_name preds with
    None => False
  | Some {| params := params; body := body |} =>
    match combine_ params args with
      (bindings, ([], [])) =>
      let env := map (fun '((x, ty), v) => (x, LSValue v)) bindings in
      asn_holds H env body
    | _ => False
    end
  end.

End pred_interp.

Lemma pred_holds_mono
    (pred_interp1: string * list Value * LogHeap -> Prop)
    (pred_interp2: string * list Value * LogHeap -> Prop):
  (forall chunk, pred_interp1 chunk -> pred_interp2 chunk) ->
  (forall chunk, pred_holds_ pred_interp1 chunk -> pred_holds_ pred_interp2 chunk).
Proof.
Admitted.

Definition pred_interp: string * list Value * LogHeap -> Prop := Tarski.fp pred_holds_.

Definition pred_holds := pred_holds_ pred_interp.

Lemma pred_fold(pred_name: string)(args: list Value)(H: LogHeap):
  pred_holds (pred_name, args, H) -> pred_interp (pred_name, args, H).
Proof.
  apply (Tarski.tarski_left _ pred_holds_mono).
Qed.

Lemma pred_unfold(pred_name: string)(args: list Value)(H: LogHeap):
  pred_interp (pred_name, args, H) -> pred_holds (pred_name, args, H).
Proof.
  apply (Tarski.tarski_right _ pred_holds_mono).
Qed.

End preds.

