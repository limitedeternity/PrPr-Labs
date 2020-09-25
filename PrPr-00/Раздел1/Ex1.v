Theorem ex11: forall A B : Prop, (A->B->B)->A->B->A->B.
Proof.
  tauto.
Qed.

Print ex11.

Theorem ex12: forall A B : Prop, A->(B->A).
Proof.
  intuition.
Qed.

Print ex12.

Theorem ex13: forall A B G : Prop, (A->(B->G))->(A->B)->(A->G).
Proof.
  tauto.
Qed.

Print ex13.

Theorem ex14: forall A B G : Prop, (A->B)->((A->(B->G))->(A->G)).
Proof.
  tauto.
Qed.

Print ex14.

Theorem ex15: forall A B : Prop, (A->(A->B))->(A->B).
Proof.
  tauto.
Qed.

Print ex15.

Theorem ex16: forall A B G : Prop, ((A->B)->(A->G))->(A->(B->G)).
Proof.
  tauto.
Qed.

Print ex16.

Theorem ex17: forall A B : Prop, (A->(A->B))->((A->B)->A)->B.
Proof.
  tauto.
Qed.

Print ex17.

Theorem ex18: forall A B : Prop, ((B->A)->B)->((B->A)->A).
Proof.
  intuition.
Qed.

Print ex18.

Theorem ex19: forall A B : Prop, A->(A->(A->B))->((A->B)->A)->B.
Proof.
  tauto.
Qed.

Print ex19.

Theorem ex20: forall A B : Prop, (A->(B->A)->B)->(((A->B)->B)->B).
Proof.
  intuition.
Qed.

Print ex20.


