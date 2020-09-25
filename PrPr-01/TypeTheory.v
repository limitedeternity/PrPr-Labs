Theorem ex50: forall a b c : Prop,
              (a -> b) -> ((b -> c) -> (a -> c)).
Proof.
  intros. apply (H0 (H H1)).
Qed.

Theorem ex50_1: forall a b c : Prop,
                (a <-> b) -> ((b <-> c) -> (a <-> c)).
Proof.
  Require Import Coq.Program.Basics.
  intros. elim H. elim H0. intros. split.
  apply (compose H1 H3). apply (compose H4 H2).
Qed.

Theorem ex50_2: forall a b c : Prop,
                (a -> b) -> ((c -> a) -> (c -> b)).
Proof.
  intros. apply (H (H0 H1)).
Qed.

Theorem ex51: forall a b c : Prop,
              (a -> (b -> c)) <-> (b -> (a -> c)).
Proof.
  split. intros. apply (H H1 H0). intros.
  apply (H H1 H0).
Qed.

Theorem ex52: forall a b c : Prop,
              (a -> (b -> c)) <-> (a /\ b -> c).
Proof.
  split. intros. elim H0. assumption.
  intros. apply H. split. assumption. assumption.
Qed.

Theorem ex53: forall a b : Prop,
              ~a -> (a -> b).
Proof.
  intros. contradiction.
Qed.

Theorem ex53_1: forall a b : Prop,
                ((a -> b) -> a) -> a.
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. cut a. intro.
  contradiction. apply H. intro. contradiction.
Qed.

Theorem ex53_2: forall a b c : Prop,
                (((a -> b) -> c) -> (a -> b)) -> (a -> b).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H1.
  apply H. intro. elim H1. cut b. intro.
  contradiction. apply (H2 H0). assumption.
Qed.

Theorem ex53_3: forall a b : Prop,
                ((((a -> b) -> a) -> a) -> a) -> a.
Proof.
  Require Import Classical.
  intros. apply NNPP. intro.
  apply H0. apply H. intro.
  apply H1. intro. apply NNPP. intro.
  apply H0. assumption.
Qed.

Theorem ex53_4: forall a b : Prop,
                ((((a -> b) -> a) -> a) -> b) -> b.
Proof.
  Require Import Coq.Program.Basics.
  intros. apply H. intros. apply H0. intro.
  refine (apply H (fun H0 => H1)).
Qed.

Theorem ex53_5: forall a b c : Prop,
                ((((((a -> b) -> c) -> c) 
                 -> a) -> a) -> b) -> b.
Proof.
  intros. apply H. intros. apply H0. intros.
  apply H1. intros. apply H.
  intros. assumption.
Qed.

Theorem ex53_6: forall a b c d : Prop,
                ((((((((a -> b) -> c) -> c) -> d)
                    -> d) -> a) -> a) -> b) -> b.
Proof.
  intros. apply H. intros. apply H0. intros.
  apply H1. intros. apply H2. intros.
  apply H. intros. assumption.
Qed.

Theorem ex53_7: forall a b : Prop,
                ((a -> b) -> b) -> ((b -> a) -> a).
Proof.
  intros. apply NNPP. intro.
  apply H1. apply H0. apply H. intro. contradiction.
Qed.