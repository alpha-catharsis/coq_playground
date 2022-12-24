From Coq Require Import Lists.List.

Import ListNotations.

From STM Require Import Stm.
From STM Require Import Step.
From STM Require Import Seq.

(* State path definition *)

Inductive Path (S : Type) (E : Type) (stm : Stm S E) : S -> S -> Prop :=
  | path_singl (ps1 : S) (ps2 : S)
      (psprf : Step stm ps1 ps2) : Path S E stm ps1 ps2
  | path_next (ps1 : S) (ps2 : S) (ps3 : S) (pthprf : Path S E stm ps1 ps2)
      (sprf : Step stm ps2 ps3) : Path S E stm ps1 ps3.

Arguments Path {S} {E}.
Arguments path_singl {S} {E}.
Arguments path_next {S} {E}.

(* State path notations *)

Notation "ps1 +- ps2" := (path_singl ps1 ps2) (at level 50).
Notation "ps1 +-+ ps2" := (path_next ps1 ps2)
                            (at level 60, right associativity).

(* State path theorems *)

Theorem path_extend_after : forall S E (stm : Stm S E) (ss : S)
                                    (es : S) (es' : S),
    Path stm ss es -> Step stm es es' -> Path stm ss es'.
Proof.
  intros S E stm ss es es' H1 H2.
  apply (path_next stm ss es es').
  - apply H1.
  - apply H2.
Qed.

Theorem path_extend_before : forall S E (stm : Stm S E) (ss : S)
                                     (ss' : S) (es : S),
    Path stm ss es -> Step stm ss' ss -> Path stm ss' es.
Proof.
  intros S E stm ss ss' es H1 H2.
  induction H1.
  - apply (path_next stm ss' ps1 ps2).
    + apply path_singl in H2. apply H2.
    + apply psprf.
  - apply (path_next stm ss' ps2 ps3).
    + apply IHPath. apply H2.
    + apply sprf.
Qed.

Theorem path_join : forall S E (stm: Stm S E) (ss : S)
                           (ms : S) (es : S),
    Path stm ss ms -> Path stm ms es -> Path stm ss es.
Proof.
  intros S E stm ss ms es H1 H2.
  induction H2.
  - apply (path_next stm ss ps1 ps2).
    + apply H1.
    + apply psprf.
  - apply (path_next stm ss ps2 ps3).
    + apply IHPath. apply H1.
    + apply sprf.
Qed.

Theorem path_reduce_start : forall S E (stm : Stm S E) (ss : S) (es :S),
    Path stm ss es -> ~(Step stm ss es) ->
    exists ss' : S, Step stm ss ss' -> Path stm ss' es.
Proof.
  intros S E stm ss es H1 H2.
  inversion H1.
  - contradiction.
  - exists ss.
    intro H3. apply H1.
Qed.

Theorem path_reduce_end : forall S E (stm : Stm S E) (ss : S) (es : S),
    Path stm ss es -> ~(Step stm ss es) ->
    exists es' : S, Step stm es' es -> Path stm ss es'.
Proof.
  intros S E stm ss es H1 H2.
  inversion H1.
  - contradiction.
  - exists ps2.
    intro H3. apply pthprf.
Qed.

(* State sequence and path theorems *)

Theorem seq_from_path : forall S E (stm : Stm S E) (ss : S) (es : S),
    Path stm ss es -> exists l : list S, Seq stm (es :: l ++ [ss]).
Proof.
  intros S E stm ss es H.
  induction H.
  - exists []. simpl. apply seq_next.
    + apply seq_one.
    + apply psprf.
  - destruct IHPath as [l' IHPath'].
    exists (ps2 :: l').
    simpl.
    apply (seq_extend_after _ _ _ _ ps2 ps3) in IHPath'.
    + apply IHPath'.
    + apply sprf.
Qed.

Theorem path_from_seq : forall S E (stm : Stm S E) (ss : S) (es : S)
                               (l : list S),
    Seq stm (es :: l ++ [ss]) -> Path stm ss es.
Proof.
Admitted.
