Theorem ex24: forall a b c : Prop,
               a /\ (b /\ c) <-> (a /\ b) /\ c.
Proof.
  split. intro. split. split. elim H. intro.
  intro. assumption. elim H. intros.
  elim H1. intros. assumption.
  elim H. intros. elim H1. intros. assumption.
  intro. split. elim H. intros. elim H0.
  intros. assumption. split. elim H. intros.
  elim H0. intros. assumption. elim H. intros.
  assumption.
Qed.

Theorem ex25: forall a b c : Prop,
               a \/ (b \/ c) <-> (a \/ b) \/ c.
Proof.
  split. intro. elim H. intro. left. left. assumption.
  intro. elim H0. intro. left. right. assumption.
  intro. right. assumption.
  intro. elim H. intro. elim H0. intro.
  left. assumption. intro. right. left. assumption.
  intro. right. right. assumption.
Qed.

Theorem ex26: forall a b c : Prop,
               ((a <-> b) <-> c) -> (a <-> (b <-> c)).
Proof.
  Require Import Classical.
  intros. split. intro. split. intro.
  elim H. intros. apply H. split. intro. assumption.
  intro. assumption. intro.
  elim H. intros. apply H3. assumption.
  assumption. 
  intro. elim H0. elim H. intros.
  apply NNPP. intro. elim H2. intros.
  apply H5. apply H7. apply H0. apply H.
  split. intro. apply (H6 H8). assumption.
  apply H. split. intro. contradiction.
  intro. apply H2. apply (H3 H6). assumption.
Qed.

Theorem ex26_1: forall a b c : Prop,
                (a <-> (b <-> c)) -> ((a <-> b) <-> c).
Proof.
  Require Import Classical.
  intros. split. intro. elim H. elim H0. intros.
  apply NNPP. intro. apply H5. apply H3.
  apply H. split. intro. elim H3. intros.
  apply (H7 H6). apply H0. assumption.
  intro. contradiction. apply NNPP. intro.
  elim H3. intros. apply H6. apply H0. apply H. split.
  intro. contradiction. intro. contradiction.
  apply NNPP. intro. apply H7. apply H. split.
  intro. contradiction. intro. contradiction. 
  intro. split. elim H. intros. elim H1. intros.
  apply (H5 H0). assumption. intro. 
  elim H. intros. apply H3. split.
  intro. assumption. intro. assumption.
Qed.