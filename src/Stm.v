From Coq Require Import Logic.Decidable.
From Coq Require Import Program.Equality.

(* Transion *)
Definition Trans S E := S -> E -> S -> Prop.

(* State machine class *)
Class Stm {S} {E} (trans : Trans S E) :=
  { trans_funct (s1 : S) (e : E) (s2 : S) (s2' : S)
    : trans s1 e s2 -> trans s1 e s2' -> s2 = s2' }.

(* Decidable state machine class *)
Class DecStm {S} {E} (trans : Trans S E) `{Stm S E trans} :=
  { dec_trans (s1 : S) (e : E) (s2 : S) : decidable (trans s1 e s2) }.

(* Functional transition tactic *)
Ltac functional_transition :=
    intros s1 e s2 s2' H1 H2;
    dependent destruction H1;
    repeat (dependent destruction H2; reflexivity).

(* Decide transition tactic *)
Ltac decide_transition s1 e s2:=
  unfold decidable;
  destruct s1, e, s2;
  repeat ((left; constructor) + (right; intros H; inversion H)).

Section Example.

  Inductive Sem : Set :=
  | Green
  | Yellow
  | Red
  | Black.

  Inductive Ev : Set :=
  | Stop
  | Next
  | Fail.

  Inductive SemTrans : Trans Sem Ev :=
  | green_stop : SemTrans Green Stop Green
  | green_next : SemTrans Green Next Yellow
  | green_fail : SemTrans Green Fail Black
  | yellow_next : SemTrans Yellow Next Red
  | yellow_fail : SemTrans Yellow Fail Black
  | red_stop : SemTrans Red Stop Red
  | red_next : SemTrans Red Next Green
  | red_fail : SemTrans Red Fail Black.

  Theorem SemTrans_funct : forall (s1 : Sem) (e : Ev) (s2 : Sem) (s2' : Sem),
      SemTrans s1 e s2 -> SemTrans s1 e s2' -> s2 = s2'.
  Proof. functional_transition. Qed.

  #[export] Instance SemTrans_Stm_inst : Stm SemTrans :=
    { trans_funct := SemTrans_funct }.

  Definition SemTrans_dec (s1 : Sem) (e : Ev) (s2 : Sem) :
    decidable (SemTrans s1 e s2).
  decide_transition s1 e s2. Defined.

  #[export] Instance SemTrans_DecStm_inst : DecStm SemTrans :=
    { dec_trans := SemTrans_dec }.

End Example.
