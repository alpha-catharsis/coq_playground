From Coq Require Import Lists.List.

Import ListNotations.

From STM Require Import Stm.
From STM Require Import Step.

(* State sequence definition *)

Inductive Seq (S : Type) (E : Type) (stm : Stm S E) : list S -> Prop :=
  | seq_one (ss : S) :  Seq S E stm [ss]
  | seq_next (l : list S) (ss1 : S) (ss2 : S)
      (lprf : Seq S E stm (ss1::l))
      (nprf : Step stm ss1 ss2) : Seq S E stm (ss2::ss1::l).

Arguments Seq {S} {E}.
Arguments seq_one {S} {E}.
Arguments seq_next {S} {E}.

(* State sequence notations *)

Notation "+.. ss" := (seq_one ss) (at level 50).
Notation "ss1 +.+ ss2" := (seq_next ss1 ss2) (at level 60, right associativity).

(* State sequence theorems *)

Theorem no_empty_seq : forall S E (stm : Stm S E) (s : S),
    ~(Seq stm []).
Proof.
  intros S E stm s H.
  inversion H.
Qed.

Theorem two_steps_seq : forall S E (stm : Stm S E) (s1 : S) (s2 : S) (s3 : S),
    Step stm s1 s2 -> Step stm s2 s3 -> Seq stm [s3;s2;s1].
Proof.
  intros S E stm s1 s2 s3 H1 H2.
  apply seq_next.
  - apply seq_next.
    + apply seq_one.
    + apply H1.
  - apply H2.
Qed.

Theorem seq_reduce_end : forall S E (stm : Stm S E) (l : list S)
                                (s1 : S) (s2 : S),
    Seq stm (s2 :: s1 :: l) -> Seq stm (s1 :: l).
Proof.
  intros S E stm l s1 s2 H.
  inversion H.
  apply lprf.
Qed.

Theorem seq_fstep_extr : forall S E (stm : Stm S E) (l : list S)
                                (s1 : S) (s2 : S),
    Seq stm (l ++ [s2;s1]) -> Step stm s1 s2.
Proof.
  intros S E stm l s1 s2 H.
  induction l as [| s' l' IHl'].
  - simpl in H. inversion H. apply nprf.
  - apply IHl'. simpl in H.
    induction l' as [| s'' l'' IHl''].
    + simpl. simpl in H, IHl'. apply seq_reduce_end in H. apply H.
    + simpl. simpl in H, IHl', IHl''.
      apply seq_reduce_end in H. apply H.
Qed.

Theorem seq_lstep_extr : forall S E (stm : Stm S E) (l : list S)
                                (s1 : S) (s2 : S),
    Seq stm (s2 :: s1 :: l) -> Step stm s1 s2.
Proof.
  intros S E stm l s1 s2 H.
  inversion H.
  apply nprf.
Qed.

Theorem seq_extend_before : forall S E (stm : Stm S E) (l : list S)
                                   (s1 : S) (s2 : S),
    Seq stm (l ++ [s2]) -> Step stm s1 s2 -> Seq stm (l ++ [s2;s1]).
Proof.
  intros S E stm l s1 s2 H1 H2.
  induction l as [| s' l' IHl'].
  - simpl. simpl in H1. apply seq_next.
    + apply seq_one.
    + apply H2.
  - simpl. simpl in H1. induction l' as [| s'' l'' IHl''].
    + simpl. simpl in H1, IHl'.
      apply seq_next.
      * apply IHl'. apply seq_one.
      * apply seq_lstep_extr in H1. apply H1.
    + simpl. simpl in H1, IHl', IHl''.
      * apply seq_next.
        -- apply IHl'.
           apply seq_reduce_end in H1. apply H1.
        -- apply seq_lstep_extr in H1. apply H1.
Qed.

Theorem seq_extend_after : forall S E (stm : Stm S E) (l : list S)
                                  (s1 : S) (s2 : S),
    Seq stm (s1 :: l) -> Step stm s1 s2 -> Seq stm (s2 :: s1 :: l).
Proof.
  intros S E stm l s1 s2 H1 H2.
  apply seq_next.
  - apply H1.
  - apply H2.
Qed.

Theorem seq_reduce_beg : forall S E (stm : Stm S E) (l : list S)
                                (s1 : S) (s2 : S),
    Seq stm (l ++ [s2;s1]) -> Seq stm (l ++ [s2]).
Proof.
  intros S E stm l s1 s2 H.
  induction l as [| s' l' IHl'].
  - simpl. apply seq_one.
  - simpl. simpl in H, IHl'.
    induction l' as [| s'' l'' IHl''].
    + simpl. simpl in H, IHl'.
      inversion H.
      apply seq_next.
      * apply seq_one.
      * apply nprf.
    + simpl. simpl in H, IHl', IHl''.
      apply seq_extend_after.
      apply IHl'.
      apply seq_reduce_end in H.
      apply H.
      apply seq_lstep_extr in H.
      apply H.
Qed.

Theorem seq_join : forall S E (stm : Stm S E) (ll : list S) (s : S)
                          (lf : list S),
    Seq stm (s :: lf) -> Seq stm (ll ++ [s]) -> Seq stm (ll ++ (s :: lf)).
Proof.
  intros S E stm ll s lf H1 H2.
  induction ll as [| s' ll' IHl'].
  - simpl. apply H1.
  - simpl. simpl in H2, IHl'.
    induction ll' as [| s'' ll'' IHl''].
    + simpl. simpl in H2, IHl'. apply seq_extend_after. apply H1.
      apply seq_lstep_extr in H2. apply H2.
    + simpl. simpl in H2, IHl', IHl''.
      apply seq_extend_after. apply IHl'. apply seq_reduce_end in H2. apply H2.
      apply seq_lstep_extr in H2. apply H2.
Qed.

Theorem seq_mstep_extr : forall S E (stm : Stm S E) (lf : list S)
                                (ll : list S) (s1 : S) (s2 : S),
    Seq stm (ll ++ [s2;s1] ++ lf) -> Step stm s1 s2.
Proof.
  intros S E stm lf ll s1 s2 H.
  induction ll as [| ls' ll' IHll'].
  - simpl in H. apply seq_lstep_extr in H. apply H.
  - induction ll' as [| ls'' ll'' IHll''].
    + simpl in H, IHll'. apply IHll'. apply seq_reduce_end in H. apply H.
    + simpl in H, IHll', IHll''. apply IHll'. apply seq_reduce_end in H.
      apply H.
Qed.

Theorem seq_extend_middle : forall S E (stm : Stm S E) (lf : list S)
                                   (ll : list S) (s1 : S) (s2 : S) (s3 : S),
    Seq stm (ll ++ [s3;s1] ++ lf) -> Step stm s1 s2 -> Step stm s2 s3 ->
    Seq stm (ll ++ [s3;s2;s1] ++ lf).
Proof.
  intros S E stm lf ll s1 s2 s3 H1 H2 H3.
  induction ll as [| ls' ll' IHl'].
  - simpl. simpl in H1. apply seq_next.
    + apply seq_next.
      * apply seq_reduce_end in H1. apply H1.
      * apply H2.
    + apply H3.
  - induction ll' as [| ls'' ll'' IHl''].
    + simpl. simpl in H1, IHl'. apply seq_next.
      * apply seq_next.
        -- apply seq_next.
           ++ apply seq_reduce_end in H1. apply seq_reduce_end in H1. apply H1.
           ++ apply H2.
        -- apply H3.
      * apply seq_lstep_extr in H1. apply H1.
    + simpl. simpl in H1, IHl', IHl''.
      apply seq_next.
      * apply IHl'. apply seq_reduce_end in H1. apply H1.
      * apply seq_lstep_extr in H1. apply H1.
Qed.

Theorem seq_reduce_inside : forall S E (stm : Stm S E) (lf : list S)
                                   (ll : list S) (s1 : S) (s2 : S) (s3 : S),
    Seq stm (ll ++ [s3;s2;s1] ++ lf) -> Step stm s1 s3 ->
    Seq stm (ll ++ [s3;s1] ++ lf).
Proof.
  intros S E stm lf ll s1 s2 s3 H1 H2.
  induction ll as [| ls' ll' IHl'].
  - simpl. simpl in H1. apply seq_reduce_end in H1.
    apply seq_reduce_end in H1. apply seq_next.
    + apply H1.
    + apply H2.
  - induction ll' as [| ls'' ll'' IHl''].
    + simpl. simpl in H1, IHl'. apply seq_next.
      * apply IHl'. apply seq_reduce_end in H1. apply H1.
      * apply seq_lstep_extr in H1. apply H1.
    + simpl. simpl in H1, IHl', IHl''.
      apply seq_next.
      * apply IHl'. apply seq_reduce_end in H1. apply H1.
      * apply seq_lstep_extr in H1. apply H1.
Qed.
