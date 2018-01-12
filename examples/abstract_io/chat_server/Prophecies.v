(* Checked with Coq 8.7.1 *)

Require Import PeanoNat.
Require Import FunctionalExtensionality.

Parameter config: Type.
Parameter value: Type.
Parameter value0: value.
Definition address := nat.

Inductive label := tau | create_pvar(addr: address) | assign_pvar(addr: address)(val: value).

Parameter step: config -> label -> config -> Prop.

CoInductive sequence := scons(head: value)(tail: sequence).

Definition erased_config := (config * (address -> bool))%type.
Definition instr_config := (config * (address -> option sequence))%type.

Definition insert a A := fun a' => if Nat.eq_dec a a' then true else A a'.

Inductive erased_step: erased_config -> label -> erased_config -> Prop :=
| erased_tau_step cfg A cfg':
  step cfg tau cfg' ->
  erased_step (cfg, A) tau (cfg', A)
| erased_create_step cfg A addr cfg':
  A addr = false ->
  step cfg (create_pvar addr) cfg' ->
  erased_step (cfg, A) (create_pvar addr) (cfg', insert addr A)
| erased_assign_step cfg A addr val cfg':
  A addr = true ->
  step cfg (assign_pvar addr val) cfg' ->
  erased_step (cfg, A) (assign_pvar addr val) (cfg', A)
.

Definition update H a (seq: option sequence) := fun a' => if Nat.eq_dec a a' then seq else H a'.

Inductive instr_step: instr_config -> label -> instr_config -> Prop :=
| instr_tau_step cfg H cfg':
  step cfg tau cfg' ->
  instr_step (cfg, H) tau (cfg', H)
| instr_create_step cfg H addr cfg' seq:
  H addr = None ->
  step cfg (create_pvar addr) cfg' ->
  instr_step (cfg, H) (create_pvar addr) (cfg', update H addr (Some seq))
| instr_assign_step_match cfg H addr val seq cfg':
  H addr = Some (scons val seq) ->
  step cfg (assign_pvar addr val) cfg' ->
  instr_step (cfg, H) (assign_pvar addr val) (cfg', update H addr (Some seq))
| instr_assign_step_nomatch cfg H addr val val' seq cfg':
  H addr = Some (scons val' seq) ->
  step cfg (assign_pvar addr val) cfg' -> (* The PL semantics must not consider this assignment to be going wrong. *)
  val <> val' ->
  instr_step (cfg, H) (assign_pvar addr val) (cfg, H)
.

Definition erased_stuck(cfg: erased_config) := ~ exists l cfg', erased_step cfg l cfg'.
Definition instr_stuck(cfg: instr_config) := ~ exists l cfg', instr_step cfg l cfg'.

Inductive erased_reachable(cfg: erased_config): erased_config -> Prop :=
| erased_reachable_refl: erased_reachable cfg cfg
| erased_reachable_step cfg' l cfg'':
  erased_reachable cfg cfg' -> erased_step cfg' l cfg'' ->
  erased_reachable cfg cfg''
.

Inductive instr_reachable(cfg: instr_config): instr_config -> Prop :=
| instr_reachable_refl: instr_reachable cfg cfg
| instr_reachable_step cfg' l cfg'':
  instr_reachable cfg cfg' -> instr_step cfg' l cfg'' ->
  instr_reachable cfg cfg''
.

Definition erased_safe(cfg: erased_config) :=
  ~ exists cfg', erased_reachable cfg cfg' /\ erased_stuck cfg'.
Definition instr_safe(cfg: instr_config) :=
  ~ exists cfg', instr_reachable cfg cfg' /\ instr_stuck cfg'.

Definition Aemp := fun a: address => false.
Definition Hemp: address -> option sequence := fun a: address => None.

Lemma main_lemma cfg:
  forall cfg1,
  erased_reachable (cfg, Aemp) cfg1 ->
  forall cfg' A,
  cfg1 = (cfg', A) ->
  forall H,
  (forall addr, H addr = None <-> A addr = false) ->
  instr_reachable (cfg, Hemp) (cfg', H).
Proof.
induction 1.
- intros.
  injection H; intros; subst.
  assert (H0 = Hemp). {
    apply functional_extensionality.
    intro.
    unfold Hemp.
    apply H1.
    reflexivity.
  }
  rewrite H2.
  constructor.
- intros.
  destruct H0.
  + rename cfg' into cfg''.
    rename cfg0 into cfg'.
    rename A0 into A'.
    injection H1; intros.
    subst A.
    subst cfg'0.
    apply instr_reachable_step with (cfg':=(cfg', H2)) (l:=tau).
    * apply IHerased_reachable with (A:=A').
      -- congruence.
      -- assumption.
    * constructor.
      assumption.
  + apply instr_reachable_step with (cfg':=(cfg0, update H2 addr None)) (l:=create_pvar addr).
    * apply IHerased_reachable with (A:=A0).
      -- reflexivity.
      -- intros.
         unfold update.
         injection H1; intros; subst.
         unfold insert in H3.
         pose proof (H3 addr0).
         destruct (Nat.eq_dec addr addr0).
         ++ subst addr0.
            tauto.
         ++ assumption.
    * injection H1; intros; subst.
      case_eq (H2 addr); intros.
      -- assert (H2 = update (update H2 addr None) addr (Some s)). {
           apply functional_extensionality.
           intros.
           unfold update.
           destruct (Nat.eq_dec addr x); congruence.
         }
         rewrite H6 at 2.
         apply instr_create_step.
         ++ unfold update.
            destruct (Nat.eq_dec addr addr); tauto.
         ++ assumption.
      -- apply H3 in H5.
         unfold insert in H5.
         destruct (Nat.eq_dec addr addr).
         ++ discriminate.
         ++ elim n; reflexivity.
  + injection H1; intros; subst.
    case_eq (H2 addr); intros.
    * apply instr_reachable_step with (cfg':=(cfg0, update H2 addr (Some (scons val s)))) (l:=assign_pvar addr val).
      -- apply IHerased_reachable with (A0:=A).
         ++ reflexivity.
         ++ intros.
            unfold update.
            destruct (Nat.eq_dec addr addr0).
            ** subst addr0. rewrite H0. split; congruence.
            ** apply H3.
      -- assert (H2 = update (update H2 addr (Some (scons val s))) addr (Some s)). {
           apply functional_extensionality.
           intros.
           unfold update.
           destruct (Nat.eq_dec addr x); congruence.
         }
         rewrite H6 at 2.
         apply instr_assign_step_match.
         ++ unfold update.
            destruct (Nat.eq_dec addr addr); congruence.
         ++ assumption.
   * apply H3 in H5. congruence.
Qed.

CoFixpoint seq0 := scons value0 seq0.

Theorem prophecies_soundness cfg: instr_safe (cfg, Hemp) -> erased_safe (cfg, Aemp).
intros.
intro.
apply H.
destruct H0 as [[cfg' A'] [Hreach Hstuck]].
set (H' := fun a => if A' a then Some seq0 else None).
exists (cfg', H').
split.
- apply main_lemma with (1:=Hreach) (A:=A').
  + reflexivity.
  + intros.
    unfold H'.
    destruct (A' addr).
    *  split; congruence.
    * split; congruence.
- intro.
  apply Hstuck.
  destruct H0 as [l [[cfg'' H''] Hstep]].
  inversion Hstep; subst.
  + exists tau.
    exists (cfg'', A').
    apply erased_tau_step.
    assumption.
  + exists (create_pvar addr).
    exists (cfg'', insert addr A').
    constructor.
    * unfold H' in H5.
      destruct (A' addr).
      -- discriminate.
      -- reflexivity.
    * assumption.
  + exists (assign_pvar addr val).
    exists (cfg'', A').
    constructor.
    * unfold H' in H5.
      destruct (A' addr) in *.
      -- reflexivity.
      -- discriminate.
    * assumption.
  + exists (assign_pvar addr val).
    exists (cfg'0, A').
    constructor.
    * unfold H' in H6.
      destruct (A' addr) in *.
      -- reflexivity.
      -- discriminate.
    * assumption.
Qed.
