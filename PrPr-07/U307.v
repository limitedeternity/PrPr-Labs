   (*
   * --------------------
   * Avtor : Bespalov V.
   * Resheno zadach: 22
   * --------------------
   *)

Require Import Arith.

(* 0.1 *)
   Inductive beautiful : nat -> Prop :=
      | b_0   : beautiful 0
      | b_3   : beautiful 3
      | b_5   : beautiful 5
      | b_sum : forall n m, beautiful n -> beautiful m
                                        -> beautiful (n + m).

   Theorem three_is_beautiful: beautiful 3.
   Proof.
      apply b_3.
   Qed.

   Theorem eight_is_beautiful: beautiful 8.
   Proof.
      apply (b_sum 3 5). apply b_3. apply b_5.
   Qed.

   Theorem beautiful_plus_eight:
                   forall n, beautiful n -> beautiful (8 + n).
   Proof.
      intro. apply (b_sum 8 n). apply eight_is_beautiful.
   Qed.

   Theorem b_times2: forall n, beautiful n -> beautiful (2 * n).
   Proof.
      intros. apply b_sum. assumption. rewrite <- plus_n_O. assumption.
   Qed.

   Theorem b_timesm: forall n m, beautiful n -> beautiful (n * m).
   Proof.
      intros. induction m. rewrite mult_comm. rewrite mult_0_l.
      apply b_0. rewrite mult_succ_r. apply b_sum. assumption.
      assumption. 
   Qed.

(* 0.2 *)
   Inductive gorgeous : nat -> Prop :=
      | g_0    : gorgeous 0
      | g_plus3: forall n, gorgeous n -> gorgeous (3 + n)
      | g_plus5: forall n, gorgeous n -> gorgeous (5 + n).
 
   Theorem gorgeous_plus13:
                     forall n, gorgeous n -> gorgeous (13 + n).
   Proof.
      intros. apply g_plus5. apply g_plus5. apply g_plus3. assumption.
   Qed.
 
   Theorem gorgeous_beautiful:
                     forall n, gorgeous n -> beautiful n.
   Proof.
      intros. induction H. apply b_0. apply b_sum. apply b_3. assumption.
      apply b_sum. apply b_5. assumption.
   Qed.
 
   Theorem gorgeous_sum: forall n m, gorgeous n -> gorgeous m
                                                -> gorgeous (n + m).
   Proof.
      intros. induction H. rewrite plus_O_n. assumption.
      apply (g_plus3 (n + m)). assumption. apply (g_plus5 (n + m)).
      assumption.
   Qed.
 
   Theorem beautiful_gorgeous: forall n, beautiful n -> gorgeous n.
   Proof.
      intros. induction H. apply g_0. apply g_plus3. apply g_0.
      apply g_plus5. apply g_0. apply gorgeous_sum. assumption. assumption.
   Qed.

   Theorem g_times2: forall n, gorgeous n -> gorgeous (2 * n).
   Proof.
      intros. induction H. rewrite mult_0_r. apply g_0.
      rewrite mult_plus_distr_l. apply gorgeous_sum.
      simpl. apply g_plus3. apply g_plus3. apply g_0.
      assumption. rewrite mult_plus_distr_l. apply gorgeous_sum.
      simpl. apply g_plus5. apply g_plus5. apply g_0. assumption.
   Qed.

(* 1.1 *)
Fixpoint pred n :=
   match n with
      | 0   => 0
      | S u => u
   end.

Eval simpl in pred 0.
Eval simpl in pred 4.
Eval simpl in pred 12.

(* 1.2 *)
Fixpoint pow n m :=
   match m with
      | 0   => 1
      | S m => n * (pow n m)
   end.

Eval simpl in pow 2 5.
Eval simpl in pow 3 2.
Eval simpl in pow 4 0.
Eval simpl in pow 0 1.
Eval simpl in pow 1 3.

(* 1.3 *)
Fixpoint max n m :=
   match n, m with
      | _, 0    => n
      | 0, _    => m
      | S n, S m => S (max n m)
   end.

Eval simpl in max 5 2.
Eval simpl in max 5 0.
Eval simpl in max 0 10.
Eval simpl in max 5 5.

(* 1.4 *)
Fixpoint min n m :=
   match n, m with
      | _, 0    => 0
      | 0, _    => 0
      | S n, S m => S (min n m)
   end.

Eval simpl in min 5 2.
Eval simpl in min 5 0.
Eval simpl in min 0 10.
Eval simpl in min 5 5.

(* 1.5 *)
Fixpoint divmod x y q u :=
   match x with
      | 0    => (q, u)
      | S x' => match u with
                   | 0    => divmod x' y (S q) y
                   | S u' => divmod x' y   q   u'
                end
   end.

Definition div x y :=
   match y with
      | 0    => y
      | S y' => fst (divmod x y' 0 y')
   end.

Eval simpl in div 4 2.
Eval simpl in div 2 50.
Eval simpl in div 140 20.
Eval simpl in div 1 1.

(* 1.6 *)
Definition mod' x y :=
   match y with
     | 0    => y
     | S y' => y' - snd (divmod x y' 0 y')
   end.

Eval simpl in mod' 5 5.
Eval simpl in mod' 8 3.
Eval simpl in mod' 3 15.

(* 1.7 *)
Fixpoint gcd a b :=
   match a with
     | O    => b
     | S a' => gcd (b mod (S a')) (S a')
   end.

Eval simpl in gcd 28 42.

(* 1.8 *)
Definition lcm a b := 
   match a, b with
     | 0, 0 => 0
     | _, _ => (div a (gcd a b)) * b
   end.

Eval simpl in lcm 28 21.

(* 1.9 *)
Fixpoint sqrt_iter k p q r :=
   match k with
     | O    => p
     | S k' => match r with
                 | O    => sqrt_iter k' (S p)
                                        (S (S q))
                                        (S (S q))
                 | S r' => sqrt_iter k' p q r'
               end
   end.

Definition sqrt n := 
   match n with
     | 0 => 0
     | 1 => 1
     | _ => sqrt_iter n 0 0 0
   end.

Eval simpl in sqrt 121.
Eval simpl in sqrt 122.

(* 1.10 *)
Fixpoint log2_iter k p q r :=
   match k with
     | O    => p
     | S k' => match r with
                 | O    => log2_iter k' (S p) (S q) q
                 | S r' => log2_iter k'   p   (S q) r'
               end
   end.

Definition log2 n := 
   match n with
     | 1 => 0
     | _ => log2_iter (pred n) 0 1 0
   end.

Eval simpl in log2 1.
Eval simpl in log2 2.
Eval simpl in log2 4.
Eval simpl in log2 5.

(* 2.1 *)
Fixpoint sum n m :=
   match n with
      | 0   => m
      | S n => S (sum n m)
   end.

Theorem sum_a: forall (n m : nat),
               sum n m = sum m n.
Proof.
   intros. induction n. simpl. apply plus_n_O.
   simpl. rewrite <- plus_n_Sm. rewrite IHn.
   f_equal.
Qed.

Theorem sum_b: forall (n m : nat),
               sum 0 m = m.
Proof.
   intros. simpl. reflexivity.
Qed.

Theorem sum_b': forall (n m : nat),
                sum n 0 = n.
Proof.
   intros. rewrite sum_a. simpl. reflexivity.
Qed.

(* 2.3 *)
Fixpoint mult n m :=
   match n with
      | 0   => 0
      | S p => sum m (mult p m)
   end.

Theorem mult_a: forall (n m : nat), mult n m = mult m n.
Proof.
   intros. induction n. simpl. rewrite <- mult_n_O.
   reflexivity. simpl. rewrite IHn. rewrite <- mult_n_Sm.
   rewrite plus_comm. f_equal.
Qed.

Theorem mult_b: forall (n m : nat), mult 0 m = 0.
Proof.
   intros. induction m. rewrite <- mult_n_O. reflexivity.
   simpl. reflexivity.
Qed.

Theorem mult_b': forall (n m : nat), mult n 0 = 0.
Proof.
   intros. induction n. rewrite <- mult_n_O. reflexivity.
   simpl. rewrite mult_a. apply (mult_b m n).
Qed.

(* 3.1 *)
Fixpoint equ n m : bool :=
   match n, m with
      | 0, 0       => true
      | 0, S _     => false
      | S _, 0     => false
      | S n, S m => equ n m
   end.

Eval simpl in equ 0 0.
Eval simpl in equ 0 1.
Eval simpl in equ 1 0.
Eval simpl in equ 1 1.

(* 3.2 *)
Fixpoint less_or_equal n m : bool :=
   match n, m with
      | 0, 0       => true
      | 0, S _     => true
      | S _, 0     => false
      | S n, S m   => less_or_equal n m
   end.

Eval simpl in less_or_equal 0 0.
Eval simpl in less_or_equal 0 1.
Eval simpl in less_or_equal 1 0.
Eval simpl in less_or_equal 100 1.
Eval simpl in less_or_equal 100 100.

(* 3.3 *)
Fixpoint less n m : bool :=
  match n, m with
    | 0, 0       => false
    | 0, S _     => true
    | S _, 0     => false
    | S n, S m   => less n m
  end.

Eval simpl in less 0 0.
Eval simpl in less 0 1.
Eval simpl in less 1 0.
Eval simpl in less 100 1.
Eval simpl in less 100 100.

(* 3.4 *)
Fixpoint even n : bool :=
   match n with
      | 0        => true
      | 1        => false
      | S (S n) => even n
   end.

Eval simpl in even 0.
Eval simpl in even 1.
Eval simpl in even 2.

(* 3.5 *)
Fixpoint odd n : bool :=
   match n with
      | 0        => false
      | 1        => true
      | S (S n) => odd n
   end.

Eval simpl in odd 0.
Eval simpl in odd 1.
Eval simpl in odd 2.

(* 4.1.1 *)
(* 2^k *)
Fixpoint f1 k :=
   match k with
      | 0   => 1
      | S m => 2 * (f1 m)
   end.

Theorem f1': forall k: nat, f1 k = pow 2 k.
Proof.
   intros. induction k. simpl. reflexivity.
   unfold f1. fold f1. unfold pow. fold pow.
   rewrite IHk. reflexivity.
Qed.

(* 4.1.2 *)
(* k+1 *)
Fixpoint f2 k :=
   match k with
      | 0   => 1
      | S m => 1 + (f2 m)
   end.

Theorem f2': forall k: nat, f2 k = 1 + k.
Proof.
   intros. induction k. simpl. reflexivity.
   simpl. apply eq_S. rewrite IHk. simpl. reflexivity.
Qed.

(* 4.1.3 *)
(* k! *)
Fixpoint f3 k :=
   match k with
     | 0   => 1
     | S m => k * (f3 m)
   end.

Fixpoint fact n :=
   match n with
      | 0 => 1
      | S n => n * fact n
   end.

Axiom f3': forall k: nat, f3 k = fact k.

Eval simpl in f3 0.
Eval simpl in f3 2.
Eval simpl in f3 3.

(* 4.1.4 *)
(* 2k + 1 *)
Fixpoint f4 k :=
   match k with
      | 0   => 1
      | S m => 2 + (f4 m)
   end.

Theorem f4': forall k: nat, f4 k = 2 * k + 1.
Proof.
   intro. induction k. reflexivity.
   unfold f4. fold f4. rewrite mult_succ_r.
   rewrite (plus_comm (2 * k) 2).
   rewrite IHk. rewrite plus_assoc. reflexivity.
Qed.

(* 4.1.5 *)
(* 1 *)
Fixpoint f5 k :=
   match k with
      | 0   => 1
      | S m => (f5 m)
   end.

Theorem f5': forall k: nat, f5 k = 1.
Proof.
   intro. induction k. simpl. reflexivity.
   simpl. assumption.
Qed.

(* 4.1.6 *)
(* 5^k *)
Fixpoint f6 k :=
   match k with
      | 0   => 1
      | S m => 5 * (f6 m)
   end.

Theorem f6': forall k: nat, f6 k = pow 5 k.
Proof.
   intro. induction k. simpl. reflexivity.
   unfold f6. fold f6. unfold pow. fold pow.
   rewrite IHk. reflexivity.
Qed.

(* 4.1.7 *)
(* простые числа? *)
Fixpoint f7 k :=
   match k with
      | 0   => 1
      | S m => 2 * (f7 m) + 5
   end.

Eval simpl in f7 0.
Eval simpl in f7 1.
Eval simpl in f7 2.
Eval simpl in f7 3.