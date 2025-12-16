Module Type TarskiParams.

    Parameter L: Type.
    Parameter le: L -> L -> Prop.
    Axiom le_trans: forall l1 l2 l3, le l1 l2 -> le l2 l3 -> le l1 l3.
    Definition ub(u: L)(D: L -> Prop): Prop := forall d, D d -> le d u.
    Definition is_lub(u: L)(D: L -> Prop): Prop :=
      ub u D /\ forall u', ub u' D -> le u u'.
    Parameter lub: forall (D: L -> Prop), L.
    Axiom lub_is_lub: forall D, is_lub (lub D) D.

End TarskiParams.

Module Tarski(Params: TarskiParams).

Export Params.

Section Tarski.

Variable f: L -> L.
Hypothesis mono: forall x y, le x y -> le (f x) (f y).

Definition fp := lub (fun x => le x (f x)).

Lemma tarski_right: le fp (f fp).
pose proof mono.
pose proof (lub_is_lub (fun x => le x (f x))).
assert (ub (f fp) (fun x => le x (f x))).
unfold ub.
intro x.
intros.
assert (le (f x) (f (f x))).
apply H.
assumption.
destruct H0.
unfold ub in H0.
assert (le x fp).
apply H0.
assumption.
assert (le (f x) (f fp)).
apply H.
assumption.
apply le_trans with (1:=H1) (2:=H5).
unfold is_lub in H0.
destruct H0.
apply H2 with (1:=H1).
Qed.

Lemma tarski_left: le (f fp) fp.
assert (is_lub fp (fun x => le x (f x))).
apply lub_is_lub.
destruct H.
apply H.
apply mono.
apply tarski_right.
Qed.

End Tarski.

End Tarski.

Module Type PredTarskiParams.

  Parameter X: Type.

End PredTarskiParams.

Module Predicates(Params: PredTarskiParams).
  Include Params.

  Module PredsTarskiParams.
    Definition L := X -> Prop.
    Definition le(P1 P2: X -> Prop) := forall x, P1 x -> P2 x.
    Definition ub(u: L)(D: L -> Prop): Prop := forall d, D d -> le d u.
    Definition is_lub(u: L)(D: L -> Prop): Prop :=
      ub u D /\ forall u', ub u' D -> le u u'.
    Lemma le_trans(P1 P2 P3: X -> Prop):
      le P1 P2 -> le P2 P3 -> le P1 P3.
    Proof.
      intros H1 H2 x H3.
      apply H2.
      apply H1.
      assumption.
    Qed.
    Definition lub(D: (X -> Prop) -> Prop)(x: X): Prop :=
      exists P, D P /\ P x.
    Lemma lub_is_lub(D: (X -> Prop) -> Prop): is_lub (lub D) D.
    Proof.
      split.
      - intros P HP x Hx.
        exists P; tauto.
      - intros P HP x Hx.
        destruct Hx as [P0 [HP0 HP0']].
        apply (HP P0 HP0).
        assumption.
    Qed.
  End PredsTarskiParams.

  Module T := Tarski PredsTarskiParams.
End Predicates.
