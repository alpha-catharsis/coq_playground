From Coq Require Import Lists.List.

From STM Require Import Stm.

Inductive FStep S E (stm : Stm S E) : S -> S -> Prop :=
  | fstep (s1 : S) (e : E) (s2 : S)
      (sprf : In (e, s2) (stm s1)) : FStep S E stm s1 s2.

Arguments FStep {S} {E}.
Arguments fstep {S} {E}.
