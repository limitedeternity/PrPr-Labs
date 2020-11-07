   (*
   * --------------------
   * Avtor : Bespalov V.
   * Resheno zadach: 13
   * --------------------
   *)

   (* -------------------------------------------------- *)
   (* Доказательство теорем теории моноидов, построенной *)
   (* на основе следующей системы аксиом:                *)
   (*                                                    *)
   (*   x = y -> x = z -> y = z;             (E1)        *)
   (*   x = y -> u = v -> x <*> u = y <*> v; (E2)        *)
   (*                                                    *)
   (*   (x <*> y) <*> z = x <*> (y <*> z);   (Mon1)      *)
   (*   x <*> e     = x;                     (Mon2)      *)
   (*   e <*> x     = x.                     (Mon3)      *)
   (* -------------------------------------------------- *)
   Parameter A  : Type.
   Parameter op : A -> A -> A.
   Parameter e  : A.
   
   Infix "<*>" := op (at level 50, left associativity).

   (* ----------------------------------- *)
   (* Аксиомы равенства в теории моноидов *)
   (* ----------------------------------- *)
   Axiom euclid : forall (x y z : A),
                     x = y -> x = z -> y = z.
   Axiom eq_op  : forall (x y u v : A),
                     x = y -> u = v -> x <*> u = y <*> v. 

   (* ----------------------------------- *)
   (* Аксиомы теории моноидов             *)
   (* ----------------------------------- *)
   Axiom op_assoc        : forall x y z : A, 
                              (x <*> y) <*> z = x <*> (y <*> z).
   Axiom e_neutral_right : forall x : A,
                              x <*> e = x.
   Axiom e_neutral_left  : forall x : A,
                              e <*> x = x.

   (* -------------------------------------------- *)
   (* Доказательства  т е о р е м  теории моноидов *)
   (* -------------------------------------------- *)

   (* --------------------------- *)
   Theorem t_1: forall x : A, x = x.
   Proof.
      intros. generalize (e_neutral_right x).    intro.
              generalize (euclid (x <*> e) x x). intro.
      apply (H0 H H).
   Qed.


   (* ---------------------- *)
   Theorem t_2: forall x y : A,
                   x = y -> y = x.
   Proof.
      intros. generalize (euclid x y x). intro. 
      apply H0. assumption. apply t_1.
   Qed.


   (* ------------------------ *)
   Theorem t_3: forall x y z : A,
                   x = y -> y = z -> x = z.
   Proof.
      intros. generalize (euclid y x z). intro.
      apply H1. rewrite (t_2 x y). apply t_1.
      assumption. assumption. 
   Qed.


   (* ---------------------------- *)
   Theorem t_3_1: forall (x y z : A),
                     x = y -> x <*> z = y <*> z.
   Proof.
      intros. generalize (eq_op x y z z). intro.
      apply H0. assumption. apply t_1.
   Qed.

   (* ---------------------------- *)
   Theorem t_3_2: forall (x y z : A),
                     x = y -> z <*> x = z <*> y.
   Proof.
      intros. generalize (eq_op z z x y). intro.
      apply H0. apply t_1. assumption.
   Qed.

   (* ---------------------------- *)
   Theorem t_3_3: forall a b c d : A,
                     a = b <*> c -> b = d -> a = d <*> c.
   Proof.
      intros. rewrite H. revert H0. apply (t_3_1 b d c).
   Qed.


   (* ---------------------------- *)
   Theorem t_3_4: forall a b c d : A,
                     a = b <*> c -> c = d -> a = b <*> d.
   Proof.
      intros. rewrite H. revert H0. apply (t_3_2 c d b). 
   Qed.


   (* ------------------------------ *)
   Theorem t_3_5: forall a b c d f : A,
                     a = b <*> (c <*> d) -> c = f 
                                    -> a = b <*> (f <*> d).
   Proof.
      intros. rewrite H. rewrite H0. apply t_1.
   Qed.


   (* ------------------------------------ *)
   (* Доказательство единственности правой *)
   (* единицы (слабая форма)               *)
   (* ------------------------------------ *)
   Theorem t_6: forall a : A,
                   (forall x : A, x <*> a = x) -> a = e.
   Proof.
      intros. rewrite <- (H e). rewrite (e_neutral_left a).
      apply t_1.
   Qed.

   (* ----------------------------------- *)
   (* Доказательство единственности левой *)
   (* единицы (слабая форма)              *)
   (* ----------------------------------- *)
   Theorem t_7: forall a : A,
                   (forall x : A, a <*> x = x) -> a = e.
   Proof.
      intros. rewrite <- (H e). rewrite (e_neutral_right a).
      apply t_1.
   Qed.


   (* --------------------------------------------- *)
   (* Доказательство существования и единственности *)
   (* левой единицы                                 *)
   (* --------------------------------------------- *)
   Theorem t_15: exists! x : A, forall a : A, 
                                   x <*> a = a.
   Proof.
      intros. compute. exists e. split. intro. 
      rewrite (e_neutral_left a). apply t_1.
      intros. rewrite <- (H e). rewrite (e_neutral_right x').
      apply t_1.
   Qed.


   (* --------------------------------------------- *)
   (* Доказательство существования и единственности *)
   (* правой единицы                                *)
   (* --------------------------------------------- *)
   Theorem t_15': exists! x : A, forall a : A, 
                                    a <*> x = a.
   Proof.
      intros. compute. exists e. split. intro.
      rewrite (e_neutral_right a). apply t_1.
      intros. rewrite <- (H e). rewrite (e_neutral_left x').
      apply t_1.
   Qed.


   (* ------------------------------------------------ *)
   (* Доказательство совпадения левой и правой единицы *)
   (* ------------------------------------------------ *)
   Theorem t_20: forall (i j : A),
                    (forall (a : A), a <*> i = a)
                 /\ (forall (b : A), j <*> b = b) -> i = j.
   Proof.
      intros. decompose [and] H. generalize (t_6 i). intro.
      generalize (t_7 j). intro. pose proof (H2 H0).
      pose proof (H3 H1). rewrite H4. rewrite H5. apply t_1.
   Qed.
