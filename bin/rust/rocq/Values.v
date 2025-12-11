From Coq Require Export QArith.

Parameter Ptr: Set.

Parameter null_ptr: Ptr.

Inductive Value :=
| VPtr(ptr: Ptr)
| VBool(b: bool)
| VReal(q: Q)
| VDummy (* Used as the value of nonsensical expressions *)
| VSome(v: Value)
| VTuple0
.

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

