Theorem ex47: forall a : Prop,
              a <-> a.
Proof.
  Require Import Coq.Program.Basics.
  split. apply id. apply id.
Qed.

Theorem ex48: forall a : Prop,
              a \/ ~a.
Proof.
  Require Import Classical.
  intros. apply (classic a).
Qed.

Theorem ex48_1: forall a b : Prop,
                (a -> b) \/ (b -> a).
Proof.
  intros. apply NNPP. intro. elim H.
  left. intro. elim H. right. intro.
  assumption.
Qed.

Theorem ex49: forall a : Prop,
              ~(a /\ ~a).
Proof.
  intros. intro. elim H. intros. contradiction.
Qed.

