Theorem imp_trans: forall P Q R: Prop, 
(P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

Print imp_trans.

Theorem imp_perm: forall P Q R: Prop,
(P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.

Print imp_perm.

Theorem ignore_Q: forall P Q R: Prop,
(P -> R) -> P -> Q -> R.
Proof.
  intros.
  apply H.
  assumption.
Qed.

Print ignore_Q.

Theorem delta_imp: forall P Q: Prop,
(P -> P -> Q) -> P -> Q.
Proof.
  intros.
  apply H.
  assumption.
  assumption.
Qed.

Print delta_imp.

Theorem delta_impR: forall P Q: Prop,
(P -> Q) -> (P -> P -> Q).
Proof.
  intros.
  apply H.
  assumption.
Qed.

Print delta_impR.

Theorem diamond: forall P Q R S: Prop,
(P -> Q) -> (P -> R) -> (Q -> R -> S) -> P -> S.
Proof.
  intros.
  apply H1.
  apply H.
  assumption.
  apply H0.
  assumption.
Qed.

Print diamond.