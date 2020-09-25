   (* Демонстрация интуиционистских доказательств *)
   (* формул из задачи 1 (раздел 2)               *)
   (* ------------------------------------------- *)
   (* -------------------------------- *)
   (* (P -> Q) -> ((P -> R) -> Q) -> Q *)
   (* -------------------------------- *)
   Theorem s1: forall P Q R : Prop, 
                  (P -> Q) -> (((P /\ ~R) \/ Q) -> Q).
   Proof.
     intros.
     elim H0.
     intros.
     apply H.
     apply H1.
     apply id.
   Qed.

   Print s1.

   (* --------------------------------------- *)
   (* ((P -> Q) -> R) -> (R -> P) -> (S -> P) *)
   (* --------------------------------------- *)
   Theorem s2: forall P Q R S : Prop,
                  (P /\ ~Q \/ R) -> (R -> P) -> (S -> P).
   Proof.
     intros.
     elim H.
     intros.
     apply H2.
     assumption.
  Qed.

  Print s2.

   (* ------------------------------------------------ *)
   (* ((P -> R) -> (S -> P))                           *)
   (*                   -> ((R -> Q) -> P) -> (S -> P) *)
   (* ------------------------------------------------ *)
   Theorem s3: forall P Q R S : Prop,
                  (P /\ ~R \/ (S -> P))
                      -> ((R -> Q) -> P) -> (S -> P).
   Proof.
     intros.
     elim H.
     intros.
     clear H.
     apply H2.
     intros.
     apply (H2 H1).
   Qed.

   Print s3.

   (* ---------------------------------------------- *)
   (* ((R -> Q) -> (S -> P)) -> (R -> P) -> (S -> P) *)
   (* ---------------------------------------------- *)
   Theorem s4: forall P Q R S: Prop,
                  (R /\ ~Q \/ (S -> P))
                                 -> (R -> P) -> (S -> P).
   Proof.
     intros.
     elim H.
     intros.
     apply H0.
     apply H2.
     intros.
     apply (H2 H1).
   Qed.

   Print s4.

   (* ---------------------------------------- *)
   (* (((R -> P) -> P) -> (S -> P))            *)
   (*           -> ((P -> Q) -> R) -> (S -> P) *)
   (* ---------------------------------------- *)
   Theorem s5: forall P Q R S : Prop,
                  ((R -> P) \/ ~S)
                      -> (R \/ P /\ ~Q) -> (S -> P).
   Proof.
     intros.
     elim H.
     intros.
     elim H0.
     assumption.
     intros.
     apply H3.
     intros.
     elim H2.
     assumption.
   Qed.

   Print s5.

   (* ---------------------------------- *)
   (* (((P -> R) -> Q) -> Q)             *)
   (*            -> (Q -> R) -> (P -> R) *)
   (* ---------------------------------- *)
   Theorem s6: forall P Q R : Prop,
                  ((P -> R) \/ Q) -> (Q -> R) -> (P -> R).
   Proof.
      intros.
      elim H.
      intros.
      apply (H2 H1).
      assumption.
   Qed.
