From Coq Require Export QArith.

Parameter Ptr: Set.

Parameter null_ptr: Ptr.

Parameter Ptr_eq_dec: forall (ptr1 ptr2: Ptr), {ptr1 = ptr2} + {ptr1 <> ptr2}.

Inductive Value :=
| VPtr(ptr: Ptr)
| VBool(b: bool)
| VReal(q: Q)
| VDummy (* Used as the value of nonsensical expressions *)
| VSome(v: Value)
| VTuple0
.

Definition value_eq_dec(v1 v2: Value): {v1 = v2} + {v1 <> v2}.
Admitted.

Definition value_eqb(v1 v2: Value): bool.
Admitted.

Lemma value_eqb_def_(v1 v2: Value): (VBool (value_eqb v1 v2) = VBool true) = (v1 = v2).
Admitted.

From Coq Require Export List String.
Import ListNotations.

Fixpoint assoc{T}(x: string)(xys: list (string * T)): option T :=
  match xys with
    [] => None
  | (x', y)::xys =>
    if string_dec x x' then
      Some y
    else
      assoc x xys
  end.

Fixpoint combine_{A B}(xs: list A)(ys: list B): list (A * B) * (list A * list B) :=
  match xs, ys with
    [], ys => ([], ([], ys))
  | xs, [] => ([], (xs, []))
  | (x::xs), (y::ys) =>
    let '(xys, (xs, ys)) := combine_ xs ys in
    ((x, y)::xys, (xs, ys))
  end.

Lemma combine__append{A B}(xs: list A)(ys: list B) xys xs' ys':
  combine_ xs ys = (xys, (xs', ys')) ->
  xs = map fst xys ++ xs' /\
  ys = map snd xys ++ ys'.
Proof.
  revert ys xys xs' ys'.
  induction xs; simpl; intros ys zys xs' ys'.
  - (* nil *)
    intros.
    injection H; clear H; intros; subst.
    split. {
      reflexivity.
    }
    reflexivity.
  - (* cons *)
    destruct ys as [|y ys].
    + intros.
      injection H; clear H; intros; subst.
      split. {
        reflexivity.
      }
      reflexivity.
    + case_eq (combine_ xs ys).
      intros xys' [xs'' ys''] Hcombine_.
      apply IHxs in Hcombine_.
      destruct Hcombine_.
      subst.
      intros.
      injection H; clear H; intros; subst.
      split. {
        reflexivity.
      }
      reflexivity.
Qed.
