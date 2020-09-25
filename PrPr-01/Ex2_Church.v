Theorem ex1: forall p q r : Prop,
             (p -> q) -> (((p -> r) -> q) -> q).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro.
  apply H1. apply H0. intro.
  apply NNPP. intro. apply H1.
  apply (H H2).
Qed.

Theorem ex2: forall p q r s : Prop,
             ((p -> q) -> r) -> ((r -> p) -> (s -> p)).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H2.
  apply H0. apply H. intro. contradiction.
Qed.

Theorem ex3: forall p q r s : Prop,
             ((p -> r) -> (s -> p)) -> 
             (((r -> q) -> p) -> (s -> p)).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H2.
  apply H0. intro. apply NNPP. intro. apply H2.
  apply H. intro. assumption. assumption.
Qed.

Theorem ex4: forall p q r s : Prop,
             ((r -> q) -> (s -> p)) -> 
             ((r -> p) -> (s -> p)).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H2.
  apply H. intro. apply NNPP. intro.
  apply H2. apply (H0 H3).
  assumption.
Qed.

Theorem ex5: forall p q r s : Prop,
             (((r -> p) -> p) -> (s -> p))
             -> (((p -> q) -> r) -> (s -> p)).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H2.
  apply H. intro. apply H3. apply H0.
  intro. contradiction. assumption.
Qed.

Theorem ex6: forall p q r : Prop,
             (((p -> r) -> q) -> q) -> 
             ((q -> r) -> (p -> r)).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H2.
  apply H0. apply H. intro.
  pose proof (H3 H1) as H4. contradiction.
Qed.

Theorem ex7: forall p s : Prop,
             ((p -> s) -> p) -> ((s -> p) -> p) -> p.
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H1. apply H0.
  intro. apply H. intro. (*contradiction.*) 
  assumption. 
Qed.

Theorem ex8: forall a b c : Prop,
             ((a -> b) -> c) -> ((a -> c) -> c).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H1.
  apply H. intro. apply NNPP. intro. apply H1.
  apply (H0 H2).
Qed.
