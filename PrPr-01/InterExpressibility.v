Theorem ex14: forall a b : Prop,
              (a <-> b) <-> (a -> b) /\ (b -> a).
Proof.
  intros. split. split. elim H. intros.
  apply (H0 H2). elim H. intros.
  apply (H1 H2). split. elim H. intros.
  apply (H0 H2). elim H. intros.
  apply (H1 H2).
Qed.

Theorem ex14_1: forall a b : Prop,
                (a <-> b) <-> (a /\ b) \/ (~a /\ ~b).
Proof.
  Require Import Classical.
  Require Import Coq.Program.Basics.
  intros. split. intros. elim H. intros.
  generalize (classic a). intros. elim H2.
  intros. left. split. assumption. apply (H0 H3).
  intros. right. split. assumption. contradict H.
  intro. apply H3. apply (H1 H).
  split. intro. elim H. intro.
  elim H1. refine (fun H0 => id).
  intro. elim H1. intros. contradiction.
  intro. elim H. intro. elim H1. intro.
  refine (fun H0 => H2).
  intro. elim H1. intros. contradiction.
Qed.

Theorem ex15: forall a b : Prop,
               (a -> b) <-> (~a \/ b).
Proof.
  Require Import Classical.
  Require Import Coq.Program.Basics.
  intros. split. intro. generalize (classic a).
  intro. elim H0. intro. right. apply (H H1).
  intro. left. assumption.
  intros. elim H. intro. contradiction. apply id.
Qed.

Theorem ex16: forall a b : Prop,
               (a -> b) <-> ~(a /\ ~b).
Proof.
  Require Import Classical.
  split. intro. intro. elim H0. intros. 
  apply H2. apply (H H1). intros. apply NNPP.
  intro. elim H. split. assumption. assumption.
Qed.

Theorem ex17: forall a b : Prop,
               (a /\ b) <-> ~(~a \/ ~b).
Proof.
  Require Import Classical.
  split. intro. intro. elim H0. elim H. intros.
  contradiction. elim H. intros.
  contradiction. intro. split.
  apply NNPP. intro. contradict H. left. assumption.
  apply NNPP. intro. contradict H. right. assumption.
Qed.

Theorem ex18: forall a b : Prop,
               (a /\ b) <-> ~(a -> ~b).
Proof.
  Require Import Classical.
  split. intro. elim H. intros. intro.
  apply (H2 H0). assumption.
  intro. split.
  apply NNPP. intro. contradict H. intro. contradiction.
  apply NNPP. intro. contradict H. intro. assumption.
Qed.

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

Theorem ex20: forall a b : Prop,
               (a \/ b) <-> (~a -> b).
Proof.
  Require Import Classical.
  intros. split. intros. apply NNPP. intro. elim H.
  intro. contradiction. intro. contradiction. intro.
  apply NNPP. intro. elim H0. right. apply NNPP. intro.
  apply H1. apply H. intro. apply H0. left. assumption.
Qed.

Theorem ex20_1: forall a b : Prop,
                (a \/ b) <-> ((a -> b) -> b).
Proof.
  split. intros. apply NNPP. intro. elim H.
  intro. apply H1. apply (H0 H2). intro. contradiction.
  intro. apply NNPP. intro. apply H0. right. apply NNPP. intro.
  apply H1. apply H. intro. elim H0. left. assumption.
Qed.