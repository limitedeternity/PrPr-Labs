Theorem ex54_10: forall a b c : Prop,
                 (a -> c) -> (b -> c) -> (a \/ b) -> c.
Proof.
  intros. elim H1. assumption. assumption.
Qed.

Theorem ex54_11: forall a1 a2 b : Prop,
                 (a1 -> b) -> (a2 -> b) -> ((a1 /\ ~a2)
                 \/ (~a1 /\ a2)) -> b.
Proof.
  intros. elim H1. intro. elim H2. intros.
  apply (H H3). intro. elim H2. intros.
  apply (H0 H4).
Qed.

Theorem ex54_12: forall a b c d : Prop,
                 (a -> c) -> (b -> d) -> (a \/ b) 
                 -> (c \/ d).
Proof.
  intros. elim H1. intro. left. apply (H H2).
  intro. right. apply (H0 H2).
Qed.

Theorem ex54_13: forall a b c : Prop,
                 (c -> a) -> (c -> b) -> (~a \/ ~b) 
                 -> ~c.
Proof.
  intros. intro. elim H1. intro. apply H3.
  apply H. assumption. intro. apply H3.
  apply H0. assumption.
Qed.

Theorem ex54_14: forall a b1 b2 : Prop,
                 (a -> b1) -> (a -> b2) -> (~b1 \/ ~b2) 
                 -> ~a.
Proof.
  intros. intro. elim H1. intro. apply H3.
  apply H. assumption. intro. apply H3.
  apply H0. assumption.
Qed.

Theorem ex54_15: forall a b c d : Prop,
                 (c -> a) -> (d -> b) -> (~a \/ ~b) -> 
                 (~c \/ ~d).
Proof.
  intros. elim H1. intro. left. intro.
  apply H2. apply H. assumption.
  intro. right. intro. apply H2. apply H0.
  assumption.
Qed.