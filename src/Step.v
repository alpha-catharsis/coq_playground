From Coq Require Import Lists.List.

From STM Require Import Stm.

(* Forward step definition *)

Inductive Step S E (stm : Stm S E) : S -> S -> Prop :=
  | step (s1 : S) (e : E) (s2 : S)
      (sprf : In (e, s2) (stm s1)) : Step S E stm s1 s2.

Arguments Step {S} {E}.
Arguments step {S} {E}.
