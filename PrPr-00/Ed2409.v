Theorem ex1_4: forall a b c : Prop,
              forall B : (b -> c) -> (a -> b) -> a -> c,
              forall C : (a -> b -> c) -> b -> a -> c,
              forall W : (a -> a -> b) -> a -> b,
              ((a -> b -> c) -> (a -> b) -> a -> c).
Proof.
  intros. apply B. intro. apply C.
  assumption. assumption. assumption. apply W.
  intro. assumption. assumption.
Qed.

Print ex1_4.

Theorem ex2_2: forall A B C D : Prop,
               (A -> B) /\ (C -> D) /\
               (A \/ C) /\ ~(B /\ D) -> 
               (B -> A) /\ (D -> C).
Proof.
  Require Import Coq.Program.Basics.
  intros. split. decompose [and] H.
  elim H1. apply const. intros.
  elim H4. split.
  assumption. apply (H2 H3).
  decompose [and] H. elim H1.
  intros. elim H4.
  split. apply (H0 H3). assumption.
  apply const.
Qed.

Theorem ex3_11: forall P Q R : Prop,
                (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros. repeat apply H || apply H0 || apply H1.
Qed.

Theorem ex3_12: forall P Q R : Prop,
                (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros. repeat apply H || apply H0 || apply H1.
Qed.

Theorem ex3_13: forall P Q R : Prop,
                (P -> R) -> P -> Q -> R.
Proof.
  intros. repeat apply H || apply H0 || apply H1.
Qed.

Theorem ex3_14: forall P Q : Prop,
                (P -> P -> Q) -> P -> Q.
Proof.
  intros. repeat apply H || apply H0 || apply H1.
Qed.

Theorem ex3_15: forall P Q : Prop,
                (P -> Q) -> (P -> P -> Q).
Proof.
  intros. repeat apply H || apply H0 || apply H1.
Qed.

Theorem ex3_16: forall P Q R S : Prop,
                (P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
  intros. repeat apply H || apply H0 || apply H1 || apply H2.
Qed.

Theorem ex3_17: forall P Q : Prop,
                ((((P -> Q) -> P) -> P) -> Q) -> Q.
Proof.
  intros. repeat first [apply H1;intros | apply H0;intros | apply H;intros].
Qed.