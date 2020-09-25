Theorem ex3: forall A B: Prop, ((((A->B)->A)->A)->B)->B.
Proof.
  intros.
  apply H.
  intro H0.
  apply H0.
  intro H1.
  apply H.
  intro H2.
  assumption.
Qed.

Print ex3.
Check ex3.