(* 
* --------------------
* Avtor : Bespalov V.
* Sessii: 
  1. 2020-10-22T18:00:10.172Z - 2020-10-12T18:40:12.256Z
* Resheno zadach: 16
* -------------------- 
*)

(* 2_1 *)
Theorem Ex_ar: (1 + 2) * 2 = 6.
Proof.
   compute. reflexivity.
Qed.

(* 2_2 *)
Theorem tr: forall x y z: Type,
               x = y -> y = z -> x = z.
Proof.
   (*intros. rewrite H. assumption.*)
   intros. transitivity y. assumption. assumption.
Qed.

(* 2_3 *)
Variable f: nat -> nat.
Hypothesis f00: f 0 = 0.
Hypothesis f10: f 1 = f 0.
(* ---------------------------------------------------- *)
Theorem Ex_f1     : forall k : nat, k=0 \/ k=1 -> f k = 0.
Proof.
  intros. decompose [or] H. rewrite H0. apply f00.
  rewrite H0. rewrite f10. apply f00.
Qed.
Theorem Ex_f2     : f (f 1) = f 1.
Proof.
  rewrite f10. rewrite f00. apply f00.
Qed.
Theorem Ex_compute: f (5 - 2 * 2) = f (3 - 3).
Proof.
  compute. apply f10.
Qed.

(* 2_4 *)
Variable U : Set.
Variable m : U -> U -> U.
(* ------------------------------------------ *)
Hypothesis com: forall x y : U,   m x y = m y x.
Hypothesis ass: forall x y z : U, m (m x y) z = m x (m y z).
Hypothesis idp: forall x : U,     m x x = x.
(* ------------------------------------------------ *)
Theorem XYX_XY: forall (x y : U), m (m x y) x = m x y.
Proof.
  intros. rewrite ass. rewrite com. rewrite ass. rewrite idp.
  rewrite com. reflexivity.
Qed.

Theorem ex2_5_1: forall t: Type, t = t.
Proof.
   intros. reflexivity.
Qed.

Theorem ex2_5_2: forall x y: Type,
                 x = y -> y = x.
Proof.
   intros. symmetry. assumption.
Qed.

Theorem ex2_5_3: forall x y z: Type, 
                 x = y -> (y = z -> x = z).
Proof.
   intros. transitivity y. assumption. assumption.
Qed.

Theorem ex2_5_4: forall x y z: Type,
                 x = y -> (x = z -> y = z).
Proof.
   intros. transitivity x. symmetry. assumption. assumption.
Qed.

Theorem ex2_5_5 : forall (x y: Type)
                  (A: Type -> Prop),
                  x = y -> (A x <-> A y).
Proof.
   intros. split. rewrite H. apply id.
   rewrite H. apply id.
Qed.

Theorem ex2_5_6: (
                  (forall x: Type, x = x) /\
                  (forall x y: Type, x = y -> y = x) /\
                  (forall x y z: Type, x = y -> (y = z -> x = z))
                 ) <-> (
                  (forall x: Type, x = x) /\
                  (forall x y z: Type, x = y -> (x = z -> y = z))
                 ).
Proof.
   split. intros. split. reflexivity.
   intros. transitivity x. symmetry.
   assumption. assumption.
   split. reflexivity. split. intros. symmetry.
   assumption. intros. transitivity y.
   assumption. assumption.
Qed.

Theorem ex2_6_1: forall (x: Type),
                 forall (B: Type -> Prop),
                 B x <-> (exists y: Type, x = y  /\ B y).
Proof.
   intros. split. intro. exists x. split. reflexivity.
   assumption. intro. elim H. intros. elim H0. intros.
   rewrite H1. assumption.
Qed.

Theorem ex2_6_2: forall (x: Type),
                 forall (B: Type -> Prop),
                 B x <-> (forall y: Type, x = y -> B y).
Proof.
   intros. split. intros. rewrite H0 in H. assumption.
   intro. apply H. reflexivity.
Qed.

Theorem ex2_6_3: forall x: Type,
                 exists y: Type, x = y.
Proof.
   intros. exists x. reflexivity.
Qed.

Theorem ex3_1_1: forall (T: Type)
                        (P: T -> Prop)
                        (t: T),
                 exists! x: T, t = x.
Proof.
   intros. compute. exists t. split. reflexivity.
   intros. assumption.
Qed.

Theorem ex3_1_2: forall (T: Type)
                        (A: T -> Prop)
                        (r s: T),
                 exists x: T, (A x /\ (forall y : T, A y -> x = y)) -> 
                 (A r -> A s -> r = s).
Proof.
   intros. exists r. intros. elim H. intros.
   apply (H3 s). assumption.
Qed.

Theorem ex3_1_3: forall (T: Type)
                        (A: T -> Prop),
                 (exists x: T, forall y: T, A y <-> x = y)
                 -> exists x: T, A x.
Proof.
   intros. elim H. intros. exists x. apply H0. reflexivity.
Qed.
