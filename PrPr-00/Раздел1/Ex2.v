Theorem ex2: forall A B D G: Prop, (D->(D->A))->((G->A)->((A->B)->(D->(G->B)))).
Proof.
  intros.
  apply H1.
  apply H0.
  assumption.
Qed.

Print ex2.

Check (fun (A B D G : Prop) 
           (H : D -> D -> A)
           (H0 : G -> A)
           (H1 : A -> B)
           (H2 : D)
           (H3 : G) => H1 (H0 H3)).