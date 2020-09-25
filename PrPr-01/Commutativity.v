Theorem ex21: forall a b : Prop,
               (a /\ b) <-> (b /\ a).
Proof.
  split. intro. elim H. intros.
  split. assumption. assumption.
  intro. elim H. intros. split. 
  assumption. assumption.
Qed.

Theorem ex22: forall a b : Prop,
               (a \/ b) <-> (b \/ a).
Proof.
  split. intro. elim H. intro. right. assumption.
  intro. left. assumption. intro. elim H. intro.
  right. assumption. intro. left. assumption.
Qed.

Theorem ex23: forall a b : Prop,
               (a <-> b) <-> (b <-> a).
Proof.
  split. intro. elim H. intros. split.
  assumption. assumption.
  intro. elim H. intros. split.
  assumption. assumption.
Qed.