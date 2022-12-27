From STM Require Import Stm.
From STM Require Import Step.

(* State machine path definition *)
Inductive Path S E (tr : Trans S E) (stm : Stm tr) : S -> S -> Prop :=
| path_singl (ps1 : S) (ps2 : S) (stp : Step tr ps1 ps2)
  : Path S E tr stm ps1 ps2
| path_next (ps1 : S) (ps2 : S) (ps3 : S) (path : Path S E tr stm ps1 ps2)
    (stp : Step tr ps2 ps3) : Path S E tr stm ps1 ps3.

Arguments Path {S} {E} _ {stm}.
Arguments path_singl {S} {E} _ {stm}.
Arguments path_next {S} {E} _ {stm}.

(* State machine path theorems *)

Theorem path_extend_before : forall {S} {E} (tr : Trans S E) {stm : Stm tr}
                                    (ss : S) (ss' : S) (es : S),
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

Theorem path_extend_after : forall {S} {E} (tr : Trans S E) {stm : Stm tr}
                                   (ss : S) (es : S) (es' : S),
    Path tr ss es -> Step tr es es' -> Path tr ss es'.
Proof.
  intros S E tr stm ss es es' H1 H2.
  apply (path_next tr ss es es').
  - apply H1.
  - apply H2.
Qed.

Theorem path_join : forall {S} {E} (tr : Trans S E) {stm : Stm tr}
                           (ss : S) (ms : S) (es : S),
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

Theorem path_split : forall {S} {E} (tr : Trans S E) {stm : Stm tr}
                            (ss : S) (es : S),
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

Theorem path_reduce_start : forall {S} {E} (tr : Trans S E) {stm : Stm tr}
                                   (ss : S) (es : S),
    Path tr ss es -> ~(Step tr ss es) ->
    exists ss' : S, Step tr ss ss' -> Path tr ss' es.
Proof.
  intros S E tr stm ss es H1 H2.
  destruct H1.
  - contradiction.
  - exists ps2. intros _. apply path_singl. apply stp.
Qed.

Theorem path_reduce_end : forall {S} {E} (tr : Trans S E) {stm : Stm tr}
                                   (ss : S) (es : S),
    Path tr ss es -> ~(Step tr ss es) ->
    exists es' : S, Step tr es' es -> Path tr ss es'.
Proof.
  intros S E tr stm ss es H1 H2.
  destruct H1.
  - contradiction.
  - exists ps2. intros _. apply H1.
Qed.


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



(* (* State sequence and path theorems *) *)

(* Theorem seq_from_path : forall S E (stm : Stm S E) (ss : S) (es : S), *)
(*     Path stm ss es -> exists l : list S, Seq stm (es :: l ++ [ss]). *)
(* Proof. *)
(*   intros S E stm ss es H. *)
(*   induction H. *)
(*   - exists []. simpl. apply seq_next. *)
(*     + apply seq_one. *)
(*     + apply psprf. *)
(*   - destruct IHPath as [l' IHPath']. *)
(*     exists (ps2 :: l'). *)
(*     simpl. *)
(*     apply (seq_extend_after _ _ _ _ ps2 ps3) in IHPath'. *)
(*     + apply IHPath'. *)
(*     + apply sprf. *)
(* Qed. *)

(* Theorem path_from_seq : forall S E (stm : Stm S E) (ss : S) (es : S) *)
(*                                (l : list S), *)
(*     Seq stm (es :: l ++ [ss]) -> Path stm ss es. *)
(* Proof. *)
(* Admitted. *)
