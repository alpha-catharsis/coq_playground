From Coq Require Import Logic.ChoiceFacts.
From Coq Require Import Logic.Decidable.

From STM Require Import Stm.

(* State machine step definition *)
Inductive Step S E (tr : Trans S E) (stm : Stm tr) : S -> S -> Prop :=
| step (s1 : S) (e : E) (s2 : S) (tprf : tr s1 e s2)
  : Step S E tr stm s1 s2.

Arguments Step {S} {E} _ {stm}.
Arguments step {S} {E} _ {stm}.

(* State machine step theorems *)
Theorem step_eq_etransstep : forall {S} {E} tr {stm : Stm tr} (s1 : S) (s2 : S),
    (exists e : E, tr s1 e s2) <-> Step tr s1 s2.
Proof.
  intros S E tr stm s1 s2.
  split.
  - intros [e H].
    apply (step tr s1 e s2).
    apply H.
  - intros H.
    inversion H.
    exists e.
    apply tprf.
Qed.

Section Example.

  Definition sem_step_decidable (s1 : Sem) (s2 : Sem) :
      decidable (Step SemTrans s1 s2).
    unfold decidable.
    destruct s1.
    - destruct s2.
      + left. apply (step SemTrans _ Stop). constructor.
      + left. apply (step SemTrans _ Next). constructor.
      + right. intros H. inversion H. inversion tprf.
      + left. apply (step SemTrans _ Fail). constructor.
    - destruct s2.
      + right. intros H. inversion H. inversion tprf.
      + right. intros H. inversion H. inversion tprf.
      + left. apply (step SemTrans _ Next). constructor.
      + left. apply (step SemTrans _ Fail). constructor.
    - destruct s2.
      + left. apply (step SemTrans _ Next). constructor.
      + right. intros H. inversion H. inversion tprf.
      + left. apply (step SemTrans _ Stop). constructor.
      + left. apply (step SemTrans _ Fail). constructor.
    - right. intros H. inversion H. inversion tprf.
  Defined.

  Compute sem_step_decidable Green Black.

  Example step_ex_1 : Step SemTrans Green Yellow.
  Proof. apply (step SemTrans Green Next). constructor. Qed.

  Check step SemTrans Green Next Yellow green_next.

End Example.
