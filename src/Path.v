From STM Require Import Stm.
From STM Require Import Step.

(* State machine path definition *)
Inductive Path S E (tr : Trans S E) (stm : Stm tr) : S -> S -> Prop :=
| path_singl (ps1 ps2 : S) (stp : Step tr ps1 ps2)
  : Path S E tr stm ps1 ps2
| path_next (ps1 ps2 ps3 : S) (path : Path S E tr stm ps1 ps2)
    (stp : Step tr ps2 ps3) : Path S E tr stm ps1 ps3.

Arguments Path {S} {E} _ {stm}.
Arguments path_singl {S} {E} _ {stm}.
Arguments path_next {S} {E} _ {stm}.

(* State machine path theorems *)

Theorem path_extend_before : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                    (ss ss' es : S),
    Path tr ss es -> Step tr ss' ss -> Path tr ss' es.
Proof.
  intros S E tr stm ss ss' es H1 H2.
  induction H1.
  - apply (path_next tr ss' ps1 ps2).
    + apply path_singl. apply H2.
    + apply stp.
  - apply (path_next tr ss' ps2 ps3).
    + apply IHPath. apply H2.
    + apply stp.
Qed.

Theorem path_extend_after : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                   (ss es es' : S),
    Path tr ss es -> Step tr es es' -> Path tr ss es'.
Proof.
  intros S E tr stm ss es es' H1 H2.
  apply (path_next tr ss es es').
  - apply H1.
  - apply H2.
Qed.

Theorem path_join : forall {S E} (tr : Trans S E) {stm : Stm tr}
                           (ss ms es : S),
    Path tr ss ms -> Path tr ms es -> Path tr ss es.
  intros S E tr stm ss ms es H1 H2.
  induction H2.
  - apply (path_next tr ss ps1 ps2).
    + apply H1.
    + apply stp.
  - apply (path_next tr ss ps2 ps3).
    + apply IHPath. apply H1.
    + apply stp.
Qed.

Theorem path_split : forall {S E} (tr : Trans S E) {stm : Stm tr}
                            (ss es : S),
    Path tr ss es -> ~(Step tr ss es) ->
    exists ms : S, Path tr ss ms /\ Path tr ms es.
Proof.
  intros S E tr stm ss es H1 H2.
  destruct H1.
  - contradiction.
  - exists ps2.
    split.
    + apply H1.
    + apply path_singl. apply stp.
Qed.

Theorem path_reduce_start : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                   (ss es : S),
    Path tr ss es -> ~(Step tr ss es) ->
    exists ss' : S, Step tr ss ss' -> Path tr ss' es.
Proof.
  intros S E tr stm ss es H1 H2.
  destruct H1.
  - contradiction.
  - exists ps2. intros _. apply path_singl. apply stp.
Qed.

Theorem path_reduce_end : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                   (ss es : S),
    Path tr ss es -> ~(Step tr ss es) ->
    exists es' : S, Step tr es' es -> Path tr ss es'.
Proof.
  intros S E tr stm ss es H1 H2.
  destruct H1.
  - contradiction.
  - exists ps2. intros _. apply H1.
Qed.


From STM Require Import Sem.
Section Example.

  Theorem sem_path_ex1 : Path SemTrans Green Red.
  Proof.
    apply (path_next SemTrans Green Yellow Red).
    - apply path_singl. apply (step _ _ Next). constructor.
    - apply (step _ _ Next). constructor.
  Qed.

  Theorem sem_path_ex2 : Path SemTrans Green Red.
  Proof.
    apply (path_extend_before SemTrans Yellow Green Red).
    - apply path_singl. apply (step _ _ Next). constructor.
    - apply (step _ _ Next). constructor.
  Qed.

  Theorem sem_path_ex3 : Path SemTrans Green Red.
  Proof.
    apply (path_join SemTrans Green Yellow Red).
    - apply path_singl. apply (step _ _ Next). constructor.
    - apply path_singl. apply (step _ _ Next). constructor.
  Qed.

End Example.
