Theorem ex34: forall a : Prop,
              (a /\ a) <-> a.
Proof.
  Require Import Coq.Program.Basics.
  split. intro. elim H. apply const.
  intro. split. assumption. assumption.
Qed.

Theorem ex35: forall a : Prop,
             (a \/ a) <-> a.
Proof.
  Require Import Coq.Program.Basics.
  intros. split. intro. elim H.
  apply id. apply id. intro.
  left. assumption.
Qed.