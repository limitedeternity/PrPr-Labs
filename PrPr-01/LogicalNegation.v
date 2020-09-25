Theorem ex42: forall a b : Prop,
              ~(a /\ b) <-> (~a \/ ~b).
Proof.
  Require Import Classical.
  split. intro. apply NNPP. intro. elim H0.
  right. apply NNPP. intro. elim H1. intro.
  elim H0. left. apply NNPP. intro. elim H3.
  intro. apply H. split. assumption. assumption.
  intro. elim H. intro. intro. elim H1. intros.
  contradiction. intro. intro. elim H1. intros.
  contradiction.
Qed.

Theorem ex43: forall a b : Prop,
              ~(a \/ b) <-> (~a /\ ~b).
Proof.
  split. intro. split. intro. apply H.
  left. assumption.
  intro. apply H. right. assumption.
  intro. intro. elim H0. intro.
  elim H. intros. contradiction.
  intro. elim H. intros. contradiction.
Qed.

Theorem ex44: forall a b : Prop,
              ~(a -> b) <-> (a /\ ~b).
Proof.
  Require Import Classical.
  split. intro. apply NNPP. intro.
  elim H. intro. apply NNPP. intro.
  elim H0. split. assumption. assumption.
  intro. intro. elim H. intros. apply H2.
  apply (H0 H1).
Qed.

Theorem ex45: forall a b : Prop,
              ~(a <-> b) <-> (a \/ b) /\ ~(a /\ b).
Proof.
  Require Import Classical.
  split. intro. split. apply NNPP. intro.
  elim H. split. intro. elim H0. left. assumption.
  intro. elim H0. right. assumption.
  intro. elim H. elim H0. intros. split.
  refine (fun H1 => H2). refine (fun H2 => H1).
  intro. intro. elim H. intros. elim H1. intro.
  apply H2. split. assumption. apply H0. assumption.
  intro. apply H2. split. apply H0. assumption.
  assumption.
Qed.

(* ---------------- *)

Theorem ex19: forall a b : Prop,
               (a \/ b) <-> ~(~a /\ ~b).
Proof.
  Require Import Classical.
  split. intro. elim H. intro. intro.
  elim H1. intros. contradiction.
  intro. intro. elim H1. intros. contradiction.
  intro. apply NNPP. intro. elim H0. left.
  apply NNPP. intro. apply H. split.
  assumption. intro. apply H0. right. assumption.
Qed.

Theorem ex45_1: forall a b : Prop,
                ~(a <-> b) <-> (a /\ ~b) \/ (~a /\ b).
Proof.
  Require Import Classical.
  Require Import Setoid.
  intros. rewrite (ex19 (a /\ ~b) (~a /\ b)).
  split. intro. intro.
  elim H0. intros. elim H1. split.
  apply NNPP. intro.
  elim H. split. intro. contradiction.
  intro. elim H2. split. assumption.
  assumption. intro.
  elim H. split. intro. assumption.
  intro. apply NNPP. intro. elim H2.
  split. assumption. assumption.
  intro. intro. elim H. split. intro.
  elim H0. intros. elim H1. intros.
  apply H5. apply (H2 H4). intro.
  elim H0. intros. elim H1. intros.
  apply H4. apply (H3 H5).
Qed.

(* ---------------- *)

Theorem ex46: forall a : Prop,
              ~~a <-> a.
Proof.
  Require Import Classical.
  split. intro. apply NNPP. assumption.
  intro. intro. apply H0. assumption.
Qed.

