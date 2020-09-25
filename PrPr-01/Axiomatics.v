Theorem ex1: forall a b : Prop,
             a -> (b -> a).
Proof.
  intros. assumption.
Qed.

Theorem ex1_1: forall a : Prop,
               (a -> ~a) -> ~a.
Proof.
  intros. contradict H. intro. 
  apply (H0 H). assumption.
Qed.

Theorem ex1_2: forall a : Prop,
               (~a -> a) -> a.
Proof.
  Require Import Classical.
  intros. apply NNPP. contradict H. intro.
  cut a. intro. contradiction. apply (H0 H).
Qed.

Theorem ex2: forall a b c : Prop,
             (a -> b) -> ((a -> (b -> c)) -> (a -> c)).
Proof.
  intros. apply (H0 H1 (H H1)).
Qed.

Theorem ex3: forall a b : Prop,
             a -> (b -> a /\ b).
Proof.
  intros. split. assumption. assumption.
Qed.

Theorem ex4: forall a b : Prop,
             a /\ b -> a.
Proof.
  intros. elim H. intros. assumption.
Qed.

Theorem ex5: forall a b : Prop,
             a /\ b -> b.
Proof.
  intros. elim H. intros. assumption.
Qed.

Theorem ex6: forall a b : Prop,
             a -> a \/ b.
Proof.
  intros. left. assumption.
Qed.

Theorem ex7: forall a b : Prop,
             b -> a \/ b.
Proof.
  intros. right. assumption.
Qed.

Theorem ex8: forall a b c : Prop,
             (a -> c) -> ((b -> c) -> (a \/ b -> c)).
Proof.
  intros. elim H1. assumption. assumption.
Qed.

Theorem ex8_1: forall a b c : Prop,
               (a \/ b -> c) -> (a -> c) /\ (b -> c).
Proof.
  intros. split. intros. apply H. left. assumption.
  intros. apply H. right. assumption.
Qed.

Theorem ex8_2: forall a b c : Prop,
               (a -> b) -> ((a -> c) -> (a -> b /\ c)).
Proof.
  intros. split. apply (H H1). apply (H0 H1).
Qed.

Theorem ex9: forall a b : Prop,
             (a -> b) -> ((a -> ~b) -> ~a).
Proof.
  intros. intro. apply (H0 H1). apply (H H1).
Qed.

Theorem ex9_1: forall a b : Prop,
               (~a -> b) -> (~(a -> ~b) -> a).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. cut a. intro.
  contradiction. contradict H0. intro. contradiction.
Qed.

Theorem ex9_2: forall a b : Prop,
               a -> (b /\ ~b) -> ~a.
Proof.
  intros. elim H0. intros. contradiction.
Qed.

Theorem ex10: forall a : Prop,
              (~~a -> a).
Proof.
  Require Import Classical.
  intros. apply NNPP. assumption.
Qed.

Theorem ex11: forall a b c : Prop,
              (a -> b) -> ((b -> a) -> (a <-> b)).
Proof.
  intros. split. intros. apply (H H1). assumption.
Qed.

Theorem ex11_1: forall a b c : Prop,
                (a <-> b) -> ((c -> a) <-> (c -> b)).
Proof.
  intros. split. intros. elim H. intros.
  apply (H2 (H0 H1)). intros. elim H.
  intros. apply (H3 (H0 H1)).
Qed.

Theorem ex11_2: forall a b c : Prop,
                (a <-> b) -> ((a -> c) <-> (b -> c)).
Proof.
  intros. split. intros. elim H. intros.
  apply (H0 (H3 H1)). intros. elim H. intros.
  apply (H0 (H2 H1)).
Qed.

Theorem ex12: forall a b : Prop,
              (a <-> b) -> (a -> b).
Proof.
  intros. elim H. intros. apply (H1 H0).
Qed.

Theorem ex13: forall a b : Prop,
              (a <-> b) -> (b -> a).
Proof.
  intros. elim H. intros. apply (H2 H0).
Qed.


