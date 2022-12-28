From Coq Require Import Lists.List.
Import ListNotations.

Class Enumerable (A : Type) :=
  { enumerated : list A;
    enumerated_all : forall x : A, In x enumerated;
    enumerated_unique : NoDup enumerated }.

From STM Require Import Sem.
Section Example.

  Definition Sem_enumerated : list Sem := [Green ; Yellow ; Red ; Black].

  Theorem Sem_enumerated_all : forall s : Sem, In s Sem_enumerated.
  Proof.
    unfold Sem_enumerated.
    destruct s.
    - simpl. left. reflexivity.
    - simpl. right. left. reflexivity.
    - simpl. right. right. left. reflexivity.
    - simpl. right. right. right. left. reflexivity.
  Qed.

  Theorem Sem_enumerated_unique : NoDup Sem_enumerated.
  Proof.
    unfold Sem_enumerated.
    apply NoDup_cons.
    - intro H. simpl in H. destruct H as [H | [H | [H | H]]].
      + discriminate.
      + discriminate.
      + discriminate.
      + contradiction.
    - apply NoDup_cons.
      + intro H. simpl in H. destruct H as [H | [H | H]].
        * discriminate.
        * discriminate.
        * contradiction.
      + apply NoDup_cons.
        * intro H. simpl in H. destruct H as [H | H].
          -- discriminate.
          -- contradiction.
        * apply NoDup_cons.
          -- intro H. simpl in H. apply H.
          -- apply NoDup_nil.
  Qed.

  Instance Sem_enumerable : Enumerable Sem :=
    { enumerated := Sem_enumerated;
      enumerated_all := Sem_enumerated_all;
      enumerated_unique := Sem_enumerated_unique }.

  Definition Ev_enumerated : list Ev := [Stop ; Next ; Fail].

  Theorem Ev_enumerated_all : forall e : Ev, In e Ev_enumerated.
  Proof.
    unfold Ev_enumerated.
    destruct e.
    - simpl. left. reflexivity.
    - simpl. right. left. reflexivity.
    - simpl. right. right. left. reflexivity.
  Qed.

  Theorem Ev_enumerated_unique : NoDup Ev_enumerated.
  Proof.
    unfold Ev_enumerated.
    apply NoDup_cons.
    - intro H. simpl in H. destruct H as [H | [H | H]].
      + discriminate.
      + discriminate.
      + contradiction.
    -  apply NoDup_cons.
       + intro H. simpl in H. destruct H as [H | H].
         * discriminate.
         * contradiction.
      + apply NoDup_cons.
         * intro H. simpl in H. apply H.
         * apply NoDup_nil.
  Qed.

End Example.
