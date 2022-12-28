From Coq Require Import Lists.List.
Import ListNotations.

From STM Require Import Stm.
From STM Require Import Step.

(* State sequence definition *)

Inductive Seq (S E : Type) (tr : Trans S E) (stm : Stm tr) : list S -> Prop :=
  | seq_one (ss : S) : Seq S E tr stm [ss]
  | seq_next (l : list S) (ss1 : S) (ss2 : S)
      (lprf : Seq S E tr stm (ss1 :: l))
      (nprf : Step tr ss1 ss2) : Seq S E tr stm (ss2 :: ss1 :: l).

Arguments Seq {S} {E} _ {stm}.
Arguments seq_one {S} {E} _ {stm}.
Arguments seq_next {S} {E} _ {stm}.

(* State sequence theorems  *)

Theorem no_empty_seq : forall {S E} (tr : Trans S E) {stm : Stm tr},
    ~(Seq tr []).
Proof.
  intros S E tr stm H.
  inversion H.
Qed.


Theorem seq_reduce_end : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                (l : list S) (s1 s2 : S),
    Seq tr (s2 :: s1 :: l) -> Seq tr (s1 :: l).
Proof.
  intros S E tr stm l s1 s2 H.
  inversion H.
  apply lprf.
Qed.

Theorem seq_first_step_extr : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                     (l : list S) (s1 s2 : S),
    Seq tr (l ++ [s2;s1]) -> Step tr s1 s2.
Proof.
  intros S E tr stm l s1 s2 H.
  induction l as [| s l' IHl].
  - simpl in H. inversion H. apply nprf.
  - apply IHl. simpl in H. destruct l'.
    + simpl. simpl in H. apply seq_reduce_end in H. apply H.
    + simpl. simpl in H. apply seq_reduce_end in H. apply H.
Qed.

Theorem seq_last_step_extr : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                    (l : list S) (s1 s2 : S),
    Seq tr (s2 :: s1 :: l) -> Step tr s1 s2.
Proof.
  intros S E tr stm l s1 s2 H.
  inversion H.
  apply nprf.
Qed.

Theorem seq_extend_before : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                   (l : list S) (s1 s2 : S),
    Seq tr (l ++ [s2]) -> Step tr s1 s2 -> Seq tr (l ++ [s2;s1]).
Proof.
  intros S E tr stm l s1 s2 H1 H2.
  induction l as [| s l' IHl].
  - simpl. apply seq_next.
    + apply seq_one.
    + apply H2.
  - destruct l'.
    + simpl. simpl in H1, IHl. apply seq_next.
      * apply IHl. apply seq_one.
      * apply seq_last_step_extr in H1. apply H1.
    + simpl. simpl in H1, IHl. apply seq_next.
      * apply IHl. apply seq_reduce_end in H1. apply H1.
      * apply seq_last_step_extr in H1. apply H1.
Qed.

Theorem seq_extend_after : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                  (l : list S) (s1 s2 : S),
    Seq tr (s1 :: l) -> Step tr s1 s2 -> Seq tr (s2 :: s1 :: l).
Proof.
  intros S E tr stm l s1 s2 H1 H2.
  apply seq_next.
  - apply H1.
  - apply H2.
Qed.

Theorem seq_reduce_start : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                  (l : list S) (s1 s2 : S),
    Seq tr (l ++ [s2;s1]) -> Seq tr (l ++ [s2]).
Proof.
  intros S E tr stm l s1 s2 H.
  induction l as [| s l' IHl].
  - simpl. apply seq_one.
  - destruct l'.
    + simpl. simpl in H. inversion H. apply seq_next.
      * apply seq_one.
      * apply nprf.
    + simpl. simpl in H, IHl.
      apply seq_extend_after.
      apply IHl.
      apply seq_reduce_end in H. apply H.
      apply seq_last_step_extr in H. apply H.
Qed.

Theorem seq_join : forall {S E} (tr : Trans S E) {stm : Stm tr}
                          (lf : list S) (s : S) (ll : list S),
    Seq tr (s :: lf) -> Seq tr (ll ++ [s]) -> Seq tr (ll ++ (s :: lf)).
Proof.
  intros S E tr stm lf s ll H1 H2.
  induction ll as [| s' ll' IHl].
  - simpl. apply H1.
  - destruct ll'.
    + simpl. simpl in H2. apply seq_extend_after. apply H1.
      apply seq_last_step_extr in H2. apply H2.
    + simpl. simpl in H2, IHl.
      apply seq_extend_after. apply IHl. apply seq_reduce_end in H2. apply H2.
      apply seq_last_step_extr in H2. apply H2.
Qed.

Theorem seq_middle_step_extr : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                      (lf : list S) (s1 s2 : S)
                                      (ll : list S) ,
    Seq tr (ll ++ [s2;s1] ++ lf) -> Step tr s1 s2.
Proof.
  intros S E tr stm lf s1 s2 ll H.
  induction ll as [| s ll' IHl].
  - simpl in H. apply seq_last_step_extr in H. apply H.
  - destruct ll'.
    + simpl in H, IHl. apply IHl. apply seq_reduce_end in H. apply H.
    + simpl in H, IHl. apply IHl. apply seq_reduce_end in H. apply H.
Qed.

Theorem seq_extend_middle : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                   (lf : list S) (s1 s2 s3 : S)
                                   (ll : list S),
    Seq tr (ll ++ [s3;s1] ++ lf) -> Step tr s1 s2 -> Step tr s2 s3 ->
    Seq tr (ll ++ [s3;s2;s1] ++ lf).
Proof.
  intros S E tr stm lf s1 s2 s3 ll H1 H2 H3.
  induction ll as [| s ll' IHl].
  - simpl. simpl in H1. apply seq_next.
    + apply seq_next.
      * apply seq_reduce_end in H1. apply H1.
      * apply H2.
    + apply H3.
  - destruct ll'.
    + simpl. apply seq_next.
      * apply seq_next.
        -- apply seq_next.
           ++ apply seq_reduce_end in H1. apply seq_reduce_end in H1. apply H1.
           ++ apply H2.
        -- apply H3.
      * apply seq_last_step_extr in H1. apply H1.
    + simpl. apply seq_next.
      * simpl in H1, IHl. apply IHl. apply seq_reduce_end in H1. apply H1.
      * simpl in H1. apply seq_last_step_extr in H1. apply H1.
Qed.

Theorem seq_reduce_inside : forall {S E} (tr : Trans S E) {stm : Stm tr}
                                   (lf : list S) (s1 s2 s3 : S)
                                   (ll : list S),
    Seq tr (ll ++ [s3;s2;s1] ++ lf) -> Step tr s1 s3 ->
    Seq tr (ll ++ [s3;s1] ++ lf).
Proof.
  intros S E tr stm lf s1 s2 s3 ll H1 H2.
  induction ll as [| s ll' IHl].
  - simpl. simpl in H1. apply seq_reduce_end in H1.
    apply seq_reduce_end in H1. apply seq_next.
    + apply H1.
    + apply H2.
  - destruct ll'.
    + simpl. simpl in H1, IHl. apply seq_next.
      * apply IHl. apply seq_reduce_end in H1. apply H1.
      * apply seq_last_step_extr in H1. apply H1.
    + simpl. simpl in H1. apply seq_next.
      * apply IHl. apply seq_reduce_end in H1. apply H1.
      * apply seq_last_step_extr in H1. apply H1.
Qed.


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
