(* Checked with Coq 8.7.1 *)

Require Import PeanoNat.
Require Import FunctionalExtensionality.

Parameter config: Type.
Parameter value: Type.
Definition address := nat.

CoInductive sequence := scons(head: value)(tail: sequence).

Inductive label :=
  tau
| create_pvar(addr: address)(range: sequence -> Prop)
| assign_pvar(addr: address)(val: value).

Parameter step: config -> label -> config -> Prop.

Definition erased_config := (config * (address -> option (sequence -> Prop)))%type.
Definition instr_config := (config * (address -> option ((sequence -> Prop) * sequence)))%type.

Definition update {X} (H: address -> X) a v := fun a' => if Nat.eq_dec a a' then v else H a'.

Definition contains_cons(S: sequence -> Prop)(val: value)(S': sequence): Prop := S (scons val S').

Inductive erased_step: erased_config -> label -> erased_config -> Prop :=
| erased_tau_step cfg A cfg':
  step cfg tau cfg' ->
  erased_step (cfg, A) tau (cfg', A)
| erased_create_step cfg A addr S witness cfg':
  A addr = None ->
  (S witness : Prop) ->
  step cfg (create_pvar addr S) cfg' ->
  erased_step (cfg, A) (create_pvar addr S) (cfg', update A addr (Some S))
| erased_assign_step cfg A addr val S witness cfg':
  A addr = Some S ->
  (S (scons val witness) : Prop) ->
  step cfg (assign_pvar addr val) cfg' ->
  erased_step (cfg, A) (assign_pvar addr val) (cfg', update A addr (Some (contains_cons S val)))
.

Inductive instr_step: instr_config -> label -> instr_config -> Prop :=
| instr_tau_step cfg H cfg':
  step cfg tau cfg' ->
  instr_step (cfg, H) tau (cfg', H)
| instr_create_step cfg H addr S witness cfg' seq:
  H addr = None ->
  (S witness : Prop) ->
  (S seq : Prop) ->
  step cfg (create_pvar addr S) cfg' ->
  instr_step (cfg, H) (create_pvar addr S) (cfg', update H addr (Some (S, seq)))
| instr_assign_step_match cfg H addr val S seq cfg':
  H addr = Some (S, scons val seq) ->
  step cfg (assign_pvar addr val) cfg' ->
  instr_step (cfg, H) (assign_pvar addr val) (cfg', update H addr (Some (contains_cons S val, seq)))
| instr_assign_step_nomatch cfg H addr val witness S val' seq cfg':
  H addr = Some (S, scons val' seq) ->
  (S (scons val witness) : Prop) ->
  step cfg (assign_pvar addr val) cfg' -> (* This label must be enabled in the PL semantics *)
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

Definition Hemp {X}: address -> option X := fun a: address => None.

Definition erase_Hentry(entry: option ((sequence -> Prop) * sequence)): option (sequence -> Prop) :=
  match entry with
    None => None
  | Some (S_, seq) => Some S_
  end.

Lemma restrictions_satisfiable_lemma cfg:
  forall cfg1,
  erased_reachable (cfg, Hemp) cfg1 ->
  let (cfg', A) := cfg1 in
  exists H, forall addr, match H addr with Some (S_, seq) => S_ seq /\ A addr = Some S_ | None => A addr = None end.
Proof.
induction 1.
- exists (fun _ => None).
  intros.
  reflexivity.
- destruct cfg'' as [cfg'' A].
  destruct cfg' as [cfg' A0].
  destruct IHerased_reachable as [W0 HW0].
  inversion H0; subst.
  + exists W0; assumption.
  + exists (update W0 addr (Some (S, witness))).
    intros.
    unfold update.
    destruct (Nat.eq_dec addr addr0).
    * tauto.
    * apply HW0.
  + exists (update W0 addr (Some (contains_cons S val, witness))).
    intros.
    unfold update.
    destruct (Nat.eq_dec addr addr0).
    * tauto.
    * apply HW0.
Qed.

Lemma main_lemma cfg:
  forall cfg1,
  erased_reachable (cfg, Hemp) cfg1 ->
  forall cfg' A,
  cfg1 = (cfg', A) ->
  forall H,
  (forall addr S seq, H addr = Some (S, seq) -> (S seq : Prop)) ->
  (forall addr, A addr = erase_Hentry (H addr)) ->
  instr_reachable (cfg, Hemp) (cfg', H).
Proof.
induction 1.
- intros.
  injection H; intros; subst.
  assert (H0 = Hemp). {
    apply functional_extensionality.
    intro.
    unfold Hemp.
    pose proof (H2 x).
    destruct (H0 x).
    - simpl in H3.
      destruct p.
      discriminate H3.
    - reflexivity.
  }
  rewrite H3.
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
      -- assumption.
    * constructor.
      assumption.
  + apply instr_reachable_step with (cfg':=(cfg0, update H2 addr None)) (l:=create_pvar addr S).
    * apply IHerased_reachable with (A:=A0).
      -- reflexivity.
      -- intros.
         unfold update in H7.
         destruct (Nat.eq_dec addr addr0).
         ++ discriminate.
         ++ apply H3 in H7. assumption.
      -- intros.
         injection H1; intros; subst.
         pose proof (H4 addr0).
         unfold update. unfold update in H7.
         destruct (Nat.eq_dec addr addr0).
         ++ subst addr0.
            simpl. assumption.
         ++ assumption.
    * injection H1; intros; subst.
      case_eq (H2 addr); intros.
      -- destruct p as [S' seq'].
         assert (H2 = update (update H2 addr None) addr (Some (S', seq'))). {
           apply functional_extensionality.
           intros.
           unfold update.
           destruct (Nat.eq_dec addr x); congruence.
         }
         rewrite H8 at 2.
         pose proof (H4 addr).
         rewrite H7 in H9.
         unfold update in H9.
         destruct (Nat.eq_dec addr addr) in H9; try congruence.
         simpl in H9.
         injection H9; intros; subst S'.
         apply instr_create_step with (witness:=witness).
         ++ unfold update.
            destruct (Nat.eq_dec addr addr); tauto.
         ++ assumption.
         ++ apply H3 in H7. assumption.
         ++ assumption.
      -- pose proof (H4 addr).
         rewrite H7 in H8.
         unfold update in H8.
         destruct (Nat.eq_dec addr addr); try congruence.
         simpl in H8.
         discriminate.
  + injection H1; intros; subst.
    case_eq (H2 addr); intros.
    * destruct p as [S' seq'].
      pose proof (H4 addr). rewrite H7 in H8.
      unfold update in H8.
      destruct (Nat.eq_dec addr addr); try congruence.
      simpl in H8.
      injection H8; intros; subst.
      apply instr_reachable_step with (cfg':=(cfg0, update H2 addr (Some (S, scons val seq')))) (l:=assign_pvar addr val).
      -- apply IHerased_reachable with (A:=A0).
         ++ reflexivity.
         ++ intros.
            unfold update in H9.
            destruct (Nat.eq_dec addr addr0).
            ** subst addr0.
               injection H9; intros; subst.
               apply H3 in H7. apply H7.
            ** apply H3 in H9. assumption.
         ++ intros.
            pose proof (H4 addr0).
            unfold update. unfold update in H9.
            destruct (Nat.eq_dec addr addr0).
            ** subst addr0.
               apply H0.
            ** assumption.
      -- assert (H2 = update (update H2 addr (Some (S, scons val seq'))) addr (Some (contains_cons S val, seq'))). {
           apply functional_extensionality.
           intros.
           unfold update.
           destruct (Nat.eq_dec addr x); congruence.
         }
         rewrite H9 at 2.
         apply instr_assign_step_match.
         ++ unfold update.
            destruct (Nat.eq_dec addr addr); congruence.
         ++ assumption.
   * pose proof (H4 addr). rewrite H7 in H8. simpl in H8.
     unfold update in H8.
     destruct (Nat.eq_dec addr addr); try congruence.
Qed.

Theorem prophecies_soundness cfg: instr_safe (cfg, Hemp) -> erased_safe (cfg, Hemp).
intros.
intro.
apply H.
destruct H0 as [[cfg' A'] [Hreach Hstuck]].
destruct (restrictions_satisfiable_lemma cfg (cfg', A') Hreach) as [W' HW'].
exists (cfg', W').
split.
- apply main_lemma with (1:=Hreach) (A:=A').
  + reflexivity.
  + intros.
    pose proof (HW' addr).
    rewrite H0 in H1.
    tauto.
  + intros.
    pose proof (HW' addr).
    destruct (W' addr).
    * destruct p. tauto.
    * tauto.
- intro.
  apply Hstuck.
  destruct H0 as [l [[cfg'' H''] Hstep]].
  inversion Hstep; subst.
  + exists tau.
    exists (cfg'', A').
    apply erased_tau_step.
    assumption.
  + exists (create_pvar addr S).
    exists (cfg'', update A' addr (Some S)).
    apply erased_create_step with (witness:=witness).
    * pose proof (HW' addr).
      rewrite H5 in H0.
      assumption.
    * assumption.
    * assumption.
  + exists (assign_pvar addr val).
    exists (cfg'', update A' addr (Some (contains_cons S val))).
    pose proof (HW' addr).
    rewrite H5 in H0.
    apply erased_assign_step with (witness:=seq).
    * tauto.
    * tauto.
    * assumption.
  + exists (assign_pvar addr val).
    exists (cfg'0, update A' addr (Some (contains_cons S val))).
    pose proof (HW' addr).
    rewrite H5 in H0.
    apply erased_assign_step with (witness:=witness).
    * tauto.
    * tauto. 
    * assumption.
Qed.
