Theorem ex54_7: forall a b c : Prop,
                (a -> b) <-> (~(a -> b) -> c /\ ~c).
Proof.
  Require Import Classical.
  split. intros. split. elim H0. intro.
  apply (H H1). intro. apply H0. assumption.
  intros. apply NNPP. intro. apply H1.
  elim H. intros. contradiction.
  intro. apply H1. apply (H2 H0).
Qed.

Theorem ex54_8: forall a b : Prop,
                (a -> b) <-> (~(a -> b) -> ~a).
Proof.
  Require Import Classical.
  split. intros. contradiction.
  intros. apply NNPP. intro. elim H.
  intro. apply H1. apply (H2 H0).
  assumption.
Qed.

Theorem ex54_9: forall a b : Prop,
                (a -> b) <-> (~(a -> b) -> b).
Proof.
  Require Import Classical.
  split. intros. contradiction.
  intros. apply NNPP. intro. apply H1.
  apply H. intro. apply H1. apply (H2 H0).
Qed.

