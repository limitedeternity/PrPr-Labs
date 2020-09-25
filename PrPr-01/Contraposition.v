Theorem ex54: forall a b : Prop,
              (a -> b) <-> (~b -> ~a).
Proof.
  Require Import Classical.
  split. intros. intro. apply H0. apply H.
  assumption. intros. apply NNPP. intro.
  apply H. assumption. assumption.
Qed.

(* ------------------- *)

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

Theorem ex21: forall a b : Prop,
               (a /\ b) <-> (b /\ a).
Proof.
  split. intro. elim H. intros.
  split. assumption. assumption.
  intro. elim H. intros. split. 
  assumption. assumption.
Qed.

Theorem ex46: forall a : Prop,
              ~~a <-> a.
Proof.
  Require Import Classical.
  split. intro. apply NNPP. assumption.
  intro. intro. apply H0. assumption.
Qed.

Theorem ex54_0: forall a b : Prop,
                (a <-> b) <-> (~b <-> ~a).
Proof.
  Require Import Setoid.
  intros. rewrite (ex14_1 (not b) (not a)).
  rewrite (ex14_1 a b).
  split. intro. elim H. intro. right.
  rewrite (ex46 b). rewrite (ex46 a).
  rewrite ex21. assumption.
  intro. left. rewrite ex21. assumption.
  intro. elim H. intro. right. rewrite ex21.
  assumption. rewrite (ex46 b). rewrite (ex46 a).
  intro. left. rewrite ex21. assumption.
Qed.

(* ------------------- *)

Theorem ex54_1: forall a b : Prop,
                (a -> ~b) <-> (b -> ~a).
Proof.
  split. intros. intro. apply H. assumption.
  assumption. intros. intro. apply H.
  assumption. assumption.
Qed.

Theorem ex54_2: forall a b : Prop,
                (~a -> b) <-> (~b -> a).
Proof.
  Require Import Classical.
  split. intros. apply NNPP. intro.
  apply H0. apply H. assumption.
  intros. apply NNPP. intro.
  apply H0. apply H. assumption.
Qed.

Theorem ex54_3: forall a b c : Prop,
                (a /\ b -> c) <-> (a /\ ~c -> ~b).
Proof.
  Require Import Classical.
  Require Import Coq.Program.Basics.
  split. intros. intro. elim H0. intros.
  apply H3. apply H. split. assumption. assumption.
  intros. apply NNPP. intro. apply H.
  split. elim H0. apply const. assumption.
  elim H0. refine (fun _ : a => fun b : b => b).
Qed.

Theorem ex54_4: forall a b c : Prop,
                (a /\ b -> c) -> (~c /\ b -> ~a).
Proof.
  intros. intro. elim H0. intros. apply H2.
  apply H. split. assumption. assumption.
Qed.

(* ------------------- *)

Theorem ex46_copy: forall a : Prop,
              ~~a <-> a.
Proof.
  Require Import Classical.
  split. intro. apply NNPP. assumption.
  intro. intro. apply H0. assumption.
Qed.

Theorem ex54_5: forall a b c : Prop,
                (a /\ ~b -> ~c) -> (a /\ c -> b).
Proof.
  Require Import Setoid.
  intros until c. rewrite (ex54_3 a (not b) (not c)).
  rewrite (ex46_copy c). rewrite (ex46_copy b). intro. assumption.
Qed.

(* ------------------- *)
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

Theorem ex54_6: forall a b c : Prop,
                (c -> a \/ b) -> (~b -> a \/ ~c).
Proof.
  Require Import Setoid.
  intros until c. rewrite ex20. 
  rewrite (ex20 a (not c)).
  intros. intro. apply H0. apply H.
  assumption. assumption.
Qed.

(* ------------------- *)

