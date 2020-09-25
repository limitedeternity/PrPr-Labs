Theorem ex27: forall a b c : Prop,
              a /\ (b \/ c) <-> a /\ b \/ a /\ c.
Proof.
  split. intro. elim H. intros. elim H1. intro.
  left. split. assumption. assumption.
  intro. right. split. assumption. assumption.
  intro. elim H. intro. elim H0. intros.
  split. assumption. left. assumption.
  intro. elim H0. intros. split. assumption.
  right. assumption.
Qed.

Theorem ex28: forall a b c : Prop,
              a \/ (b /\ c) <-> (a \/ b) /\ (a \/ c).
Proof.
  split. intro. elim H. intro. split. left. assumption.
  left. assumption. intro. elim H0. intros. split.
  right. assumption. right. assumption. intro. elim H.
  intros. elim H0. intro. left. assumption. intro.
  elim H1. intro. left. assumption. intro. right. split.
  assumption. assumption.
Qed.

Theorem ex29: forall a b c : Prop,
              a \/ (b -> c) -> (a \/ b) -> (a \/ c).
Proof.
  intros. elim H0. intro. left. assumption.
  elim H. intros. left. assumption.
  intros. right. apply (H1 H2).
Qed.

Theorem ex30: forall a b c : Prop,
              a \/ (b <-> c) -> (a \/ b <-> a \/ c).
Proof.
  intros. split. intro. elim H0. elim H. intro. left. assumption.
  intros. left. assumption. elim H. intros.
  left. assumption. intros. right. apply H1.
  assumption. intro. elim H0. intro. left. assumption.
  elim H. intros. left. assumption.
  intros. right. apply H1. assumption. 
Qed.

Theorem ex30_1: forall a b c : Prop,
                (a -> b) -> (a /\ c) -> (b /\ c).
Proof.
  intros. elim H0. intros. split. apply (H H1).
  assumption.
Qed.

Theorem ex30_2: forall a b c : Prop,
                (a -> b) -> (c /\ a) -> (c /\ b).
Proof.
  intros. elim H0. split. assumption. apply (H H2).
Qed.

Theorem ex30_3: forall a b c : Prop,
                (a <-> b) -> ((c /\ a) <-> (c /\ b)).
Proof.
  intros. split. intro. elim H0. intros.
  elim H. intros. split. assumption.
  apply (H3 H2). intros. elim H0. intros.
  elim H. intros. split. assumption.
  apply (H4 H2).
Qed.

Theorem ex30_4: forall a b c : Prop,
                (a -> b) -> (a \/ c) -> (b \/ c).
Proof.
  intros. elim H0. intros. left. apply (H H1).
  intro. right. assumption.
Qed.

Theorem ex30_5: forall a b c : Prop,
                (a -> b) -> (c \/ a) -> (c \/ b).
Proof.
  intros. elim H0. intros. left. assumption.
  intro. right. apply (H H1).
Qed.

Theorem ex30_6: forall a b c : Prop,
                (a <-> b) -> ((c \/ a) <-> (c \/ b)).
Proof.
  intros. elim H. intros. split. intro.
  elim H2. intro. left. assumption.
  intro. right. apply (H0 H3).
  intro. elim H2. intros. left. assumption.
  intro. right. apply (H1 H3).
Qed.

Theorem ex30_7: forall a b c d : Prop,
                (a -> b) -> (b /\ c -> d) -> (a /\ c -> d).
Proof.
  intros. elim H1. intros. apply H0. split.
  apply (H H2). assumption.
Qed.

Theorem ex30_8: forall a b c d : Prop,
                (a -> b) -> (c /\ d -> a) -> (c /\ d -> b).
Proof.
  intros. elim H1. intros. apply H. apply H0.
  split. assumption. assumption.
Qed.

Theorem ex31: forall a b c d : Prop,
              (a -> b /\ c) <-> (a -> b) /\ (a -> c).
Proof.
  split. intro. split. intro. apply (H H0).
  intro. apply (H H0). intros. elim H.
  intros. split. apply (H1 H0). apply (H2 H0).
Qed.

Theorem ex31_1: forall a b c d : Prop,
                (a -> c) /\ (b -> d) -> (a /\ b -> c /\ d).
Proof.
  intros. elim H. elim H0. intros. split.
  apply (H3 H1). apply (H4 H2).
Qed.

Theorem ex31_2: forall a b c d : Prop,
                (a -> b) /\ (c -> d) -> (a \/ c -> b \/ d).
Proof.
  intros. elim H. elim H0. intros. left. apply (H2 H1).
  intros. right. apply (H3 H1).
Qed.

(* ------------------- *)

Theorem ex20: forall a b : Prop,
               (a \/ b) <-> (~a -> b).
Proof.
  Require Import Classical.
  intros. split. intros. apply NNPP. intro. elim H.
  intro. contradiction. intro. contradiction. intro.
  apply NNPP. intro. elim H0. right. apply NNPP. intro.
  apply H1. apply H. intro. apply H0. left. assumption.
Qed.

Theorem ex32: forall a b c : Prop,
              (a -> b \/ c) <-> (a -> b) \/ (a -> c).
Proof.
  Require Import Setoid.
  Require Import Coq.Program.Basics.
  intros. split. Focus 2. 
  intros. elim H. intro. left. apply (H1 H0).
  intro. right. apply (H1 H0).
  intros. rewrite (ex20 (a -> b) (a -> c)).
  intros. elim H. intro. elim H0. refine (fun H1 => H2).
  apply id. assumption.
Qed.

(* ---------------- *)

Theorem ex32_1: forall a b c : Prop,
                (a \/ b -> c) <-> (a -> c) /\ (b -> c).
Proof.
  intros. split. intro. split. intro. apply H. left.
  assumption. intro. apply H. right. assumption.
  intros. elim H0. elim H. intros.
  apply (H1 H3). elim H. intros. apply (H2 H3).
Qed.

Theorem ex32_2: forall a b c : Prop,
                ((a -> c) \/ (b -> c)) <-> (a /\ b -> c).
Proof.
  Require Import Classical.
  intros. split. intros. elim H0. elim H. intros.
  apply (H1 H2). intros. apply (H1 H3).
  intro. apply NNPP. intro. elim H0. right. intro. elim H0.
  left. intro. apply H. split. assumption. assumption.
Qed.

(* --------------- *)

Theorem ex14: forall a b : Prop,
              (a <-> b) <-> (a -> b) /\ (b -> a).
Proof.
  intros. split. split. elim H. intros.
  apply (H0 H2). elim H. intros.
  apply (H1 H2). split. elim H. intros.
  apply (H0 H2). elim H. intros.
  apply (H1 H2).
Qed.

Theorem ex33: forall a b c : Prop,
              a -> ((b <-> c) <-> ((a -> b) <-> (a -> c))).
Proof.
  Require Import Setoid.
  intros. rewrite ex14. split. intro.
  split. intros. apply H0. apply (H1 H2).
  intros. apply H0. apply (H1 H2).
  split. elim H0. intros. apply H1.
  refine (fun H => H3). assumption.
  elim H0. intros. apply H2.
  refine (fun H => H3). assumption.
Qed.

(* --------------- *)

Theorem ex33_1: forall a b c : Prop,
                (a -> (b -> c)) <-> ((a -> b) -> (a -> c)).
Proof.
  intros. split. intros. apply H. assumption. apply H0. assumption.
  intros. apply H. intro. assumption. assumption.
Qed.

