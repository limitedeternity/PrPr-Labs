   (*
   * --------------------
   * Avtor : Bespalov V.
   * Resheno zadach: 31
   * --------------------
   *)

   (* ------------------------------------*)
   (* Арифметика Дж. Пеано в системе Coq. *)
   (* ------------------------------------*)
   Require Import Coq.Init.Peano.
   Require Import Setoid. (* для rewrite *)

   (* ----------------------------- *)
   (* Аксиомы равенства в теории S  *)
   (* ----------------------------- *)
   Axiom euclid: forall x y z : nat,
                    x = y -> x = z -> y = z.

   (* -------------------------------------- *) 
   (* Начало доказательства  в с е х  теорем *)
   (* Предложений 1 и 2                      *)
   (* -------------------------------------- *)
   Theorem t_a: forall n : nat, n = n.
   Proof.
      intros. rewrite plus_n_O. apply plus_n_O. 
   Qed.

   (* ------------------------------------------ *)
   Theorem t_b: forall (x y : nat), x = y -> y = x.
   Proof.
      intros. rewrite <- H. apply (t_a x). 
   Qed.

   (* --------------------------- *)
   Theorem t_b': forall (x y : nat), 
                    ~(x = y) -> ~(y = x).
   Proof. 
      intros. contradict H. rewrite H. apply (t_a x).
   Qed.

   (* ---------------------------- *)
   Theorem t_c: forall (x y z : nat),
                   x = y -> y = z -> x = z.
   Proof.
      intros. rewrite H0 in H. assumption.
   Qed.

   (* ---------------------------- *)
   Theorem t_d: forall (r t s : nat),
                   r = t -> s = t -> r = s.
   Proof.
      intros. rewrite <- H0 in H. assumption.
   Qed.

   (* ---------------------------- *)
   Theorem t_e: forall (t r s : nat),
                   t = r -> t + s = r + s.
   Proof.
      intros. rewrite H. apply (t_a (r + s)).
   Qed.

   (* ----------------------------------- *)
   Theorem t_f: forall (t : nat), t = 0 + t.
   Proof.
      intros. apply plus_O_n.
   Qed.

   (* -------------------------- *)
   Theorem t_g: forall (t r : nat),
                   S t + r = S (t + r).
   Proof.
      intros. apply plus_Sn_m.
   Qed.

   (* ----------------------------------------- *)
   Theorem t_h: forall (t r : nat), t + r = r + t.
   Proof.
      intros. induction r. rewrite <- (plus_n_O t). apply (plus_O_n t). 
      rewrite <- (plus_n_Sm t r). rewrite (plus_Sn_m r t).
      apply (eq_S (t + r) (r + t)). assumption.
   Qed.

   (* ---------------------------- *)
   Theorem t_i: forall (t r s : nat),
                   t = r -> s + t = s + r.
   Proof.
      intros. rewrite <- H. apply (t_a (s + t)).
   Qed.

   (* ---------------------------- *)
   Theorem t_j: forall (t r s : nat),
                   (t + r) + s = t + (r + s).
   Proof.
      intros. induction t. rewrite (plus_O_n r). rewrite (plus_O_n (r + s)).
      apply t_a. revert IHt. apply eq_S.
   Qed.

   (* ---------------------------- *)
   Theorem t_k: forall (t r s : nat),
                   t = r -> t * s = r * s.
   Proof.
      intros. apply (f_equal2_mult t r s s). assumption. apply t_a.
   Qed.

   (* --------------------------------- *)
   Theorem t_l: forall t : nat, 0 * t = 0.
   Proof.
      intros. rewrite (mult_n_O t) at 2. induction t. apply t_a.
      rewrite <- mult_n_Sm. rewrite <- plus_n_O.
      rewrite <- (mult_n_O (S t)). rewrite (mult_n_O t) at 2.
      assumption.
   Qed.

   (* -------------------------- *)
   Theorem t_m: forall (t r : nat),
                   S t * r = t * r + r.
   Proof.
      intros. induction r. rewrite <- (mult_n_O (S t)).
      rewrite <- (mult_n_O t). compute. apply t_a.
      rewrite <- (mult_n_Sm (S t) r).
      rewrite <- (plus_n_Sm (S t * r) t).
      rewrite <- (plus_n_Sm (t * S r) r). apply eq_S.
      rewrite <- (mult_n_Sm t r). rewrite (t_j (t * r) t r).
      rewrite (t_h t r). rewrite <- (t_j (t * r) r t).
      rewrite (t_e (S t * r) (t * r + r) t). apply t_a.
      apply IHr.
   Qed.

   (* ----------------------------------------- *)
   Theorem t_n: forall (t r : nat), t * r = r * t.
   Proof.
      induction r. rewrite <- (mult_n_O t). rewrite (t_l t).
      apply t_a. rewrite t_m. rewrite <- mult_n_Sm.
      revert IHr. apply t_e.
   Qed.

   (* ---------------------------- *)
   Theorem t_o: forall (t s r : nat),
                   t = r -> s * t = s * r.
   Proof.
      intros. rewrite <- H. apply t_a.
   Qed.

   (* --------------------------------------- *)
   Theorem t_p: forall (t : nat), t + S O = S t.
   Proof.
      intros. induction t. compute. apply t_a.
      rewrite <- IHt at 2. rewrite (plus_Sn_m t 1). 
      apply t_a.
   Qed.

   (* --------------------------------------------- *)
   Theorem t_q: forall (t r : nat), S t + r = t + S r.
   Proof.
      intros. induction t. rewrite plus_O_n.
      rewrite <- (t_p r). apply t_h.
      rewrite <- (t_p (S t)). rewrite <- (t_p t).
      rewrite <- (t_p r). rewrite (t_h r 1). rewrite <- t_j.
      apply t_a.
   Qed.
     
   (* ---------------------------- *)
   Theorem t_r: forall (t r s : nat),
                     S t = r /\ S t = s -> r = s.
   Proof.
      intros. elim H. intros. rewrite <- H0. rewrite <- H1.
      apply t_a.
   Qed.
 
   (* ---------------------------- *)
   Theorem t_s: forall (t r s : nat),
                   t + r = t + s -> r = s.
   Proof.
      intros. induction t. rewrite (plus_O_n r) in H.
      rewrite (plus_O_n s) in H. assumption.
      apply IHt. rewrite (t_q t s) in H.
      rewrite (t_q t r) in H.
      generalize H.
      rewrite <- (plus_n_Sm t r). rewrite <- (plus_n_Sm t s).
      apply eq_add_S.
   Qed.

   (* ----------------------------- *)
   Theorem t_s': forall (t r s : nat),
                    t + s = r + s -> t = r.
   Proof.
      intros. elim H. induction s. rewrite <- (plus_n_O t) in H.
      rewrite <- (plus_n_O r) in H. assumption.
      apply IHs. generalize H.
      rewrite <- (plus_n_Sm t s). rewrite <- (plus_n_Sm r s).
      apply eq_add_S.
   Qed.

   (* -------------------------------- *)
   (* Теорема из Предложения 2         *)
   (* -------------------------------- *)
   Theorem r_distr: forall (t r s : nat),
                       t * (r + s) = t * r + t * s.
   Proof.
      intros. induction t. rewrite (t_l (r + s)).
      rewrite (t_l r). rewrite (t_l s). compute. apply t_a.
      rewrite (t_m t (r + s)). rewrite IHt.
      rewrite <- t_j. rewrite (t_m t r).
      rewrite (t_m t s). rewrite (t_h (t * s) s). 
      rewrite <- t_j. rewrite (t_j (t * r) r s).
      rewrite (t_j (t * r + t * s) r s).
      rewrite (t_j (t * r) (r + s) (t * s)).
      rewrite (t_h (r + s) (t * s)). 
      rewrite <- (t_j (t * r) (t * s) (r + s)).
      apply t_a.
   Qed.

   (* -------------------------------- *)
   (* Теорема из Предложения 2         *)
   (* -------------------------------- *)
   Theorem l_distr: forall (r s t : nat),
                       (r + s) * t = r * t + s * t.
   Proof. 
      intros. rewrite t_n. rewrite (t_n r t).
      rewrite (t_n s t). apply r_distr.
   Qed.

   (* ---------------------------- *)
   Theorem t_t: forall (t r s : nat),
                     (t * r) * s = t * (r * s).
   Proof.
      intros. induction t. rewrite t_l. rewrite t_l.
      apply t_a. rewrite t_m. rewrite t_m. rewrite <- IHt.
      rewrite <- l_distr. apply t_a.
   Qed.

   (* ------------------------- *)
   Lemma t_u': forall (t r : nat),
                  t + r = O -> t = O /\ r = O.
   Proof.
      intros. induction t. split. apply t_a. rewrite plus_O_n in H.
      assumption. split. rewrite t_g in H.
      generalize (O_S (t + r)). intro. apply t_b in H. contradiction.
      generalize (O_S (t + r)). intro. apply t_b in H. contradiction.
   Qed.

   (* -------------------------- *)
   Theorem t_u: forall (t r : nat),
                   t * r = 0 -> t = 0 \/ r = 0.
   Proof.
      intros. induction r. induction t. left. apply t_a. 
      right. apply t_a. left. rewrite <- mult_n_Sm in H.
      apply t_u' in H. elim H. intros. assumption.
   Qed.

   (* -------------------------- *)
   Theorem t_v: forall (t s : nat),
                   t + s = t -> s = 0.
   Proof.
      intros. apply (t_s t s O). rewrite <- plus_n_O. assumption.
   Qed.

   (* ------------------------------------ *)
   Lemma t_v': forall (t : nat), t * S O = t.
   Proof.
      intros. induction t. compute. apply t_a.
      apply (eq_S (t * 1) t). assumption.
   Qed.

   (* -------------------------- *)
   Lemma t_v'': forall (t r : nat),
                   t * S O = r * S O -> t = r.
   Proof.
      intros. rewrite t_v' in H. rewrite t_v' in H. assumption.
   Qed.

   (* -------------------------- *)
   Theorem ex42: forall a b : Prop,
              ~(a /\ b) <-> (~a \/ ~b).
   Proof.
      Require Import Classical.
      split. intro. apply NNPP. intro. elim H0.
      right. apply NNPP. intro. elim H1. intro.
      elim H0. left. apply NNPP. intro. elim H3.
      intro. apply H. split. assumption. assumption.
      intro. elim H. intro. intro. elim H1. intros.
      contradiction. intro. intro. elim H1. intros.
      contradiction.
   Qed.

   Theorem t_w: forall (t r : nat),
                   ~ (t = 0) \/ ~ (r = 0) -> ~ (t + r = 0).
   Proof.
      intros. elim H. intro. intro. generalize (t_u' t r). intro.
      pose proof (H2 H1). rewrite <- ex42 in H. contradiction.
      rewrite <- ex42 in H. generalize (t_u' t r). intro.
      intro. intro. pose proof (H0 H2). contradiction.
   Qed.

   (* -------------------------- *)
   Theorem ex43: forall a b : Prop,
              ~(a \/ b) <-> (~a /\ ~b).
   Proof.
      split. intro. split. intro. apply H.
      left. assumption.
      intro. apply H. right. assumption.
      intro. intro. elim H0. intro.
      elim H. intros. contradiction.
      intro. elim H. intros. contradiction.
   Qed.

   Theorem t_x: forall (t r : nat),
                   ~ (t = 0) /\ ~ (r = 0) -> ~ (t * r = 0).
   Proof.
      intros. elim H. intros. intro. generalize (t_u t r).
      intro. pose proof (H3 H2). rewrite <- ex43 in H. contradiction.
   Qed.

   (* --------------------------------------- *)
   (* Все задачи из Предложений 1 и 2 решены! *)
   (* --------------------------------------- *)