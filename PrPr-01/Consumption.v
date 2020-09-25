Theorem ex36: forall a b : Prop,
              a /\ (a \/ b) <-> a.
Proof.
  split. intro. elim H. intros. assumption.
  intro. split. assumption. left. assumption.
Qed.

Theorem ex37: forall a b : Prop,
              (a \/ a /\ b) <-> a.
Proof.
  Require Import Coq.Program.Basics.
  split. intro. elim H. apply id. intro. elim H0.
  apply const. intro. left. assumption.
Qed.

Theorem ex38: forall a b : Prop,
              a /\ (b \/ ~b) <-> a.
Proof.
  Require Import Classical.
  split. intro. elim H. intros. assumption.
  intro. split. assumption. apply (classic b).
Qed.

Theorem ex39: forall a b : Prop,
              a \/ (b /\ ~b) <-> a.
Proof.
  split. intro. elim H. apply id. intro. elim H0.
  intros. contradiction. intro. left. assumption.
Qed.

Theorem ex40: forall a b : Prop,
              (a /\ b /\ ~b) <-> (b /\ ~b).
Proof.
  split. intro. elim H. intros. apply H1.
  intro. elim H. intros. contradiction.
Qed.

Theorem ex41: forall a b : Prop,
              (a \/ b \/ ~b) <-> (b \/ ~b).
Proof.
  Require Import Classical.
  split. intro. apply (classic b).
  intro. elim H. intros. right. left. assumption.
  intro. right. right. assumption.
Qed.