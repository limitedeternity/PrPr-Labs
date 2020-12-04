(*
 * --------------------
 * Avtor : Bespalov V.
 * Resheno zadach: 21
 * --------------------
*)

Require Import List.
Require Import Arith.
Require Import Setoid.
Open Scope list_scope.

Theorem simpl_succ: forall n: nat, S n = 1 + n.
Proof.
  intros. compute. reflexivity.
Qed.

Theorem O_is_min: forall n: nat, 0 <= n.
Proof.
  intros. induction n. apply (le_O_n 0). rewrite simpl_succ.
  apply (le_plus_trans 0 1 n).
  rewrite plus_n_O. apply le_plus_r.
Qed.

Theorem app_assoc: forall (A: Type) (l m n: list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l. simpl. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_nil_r: forall (A : Type) (l: list A), l ++ nil = l.
Proof.
  intros. induction l. simpl. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

(* 1_1 *)
Theorem app_ge_0: forall (A : Type)
                         (l : list A),
                     0 <= length l.
Proof.
  intros. apply O_is_min.
Qed.

(* 1_2 *)
Theorem app_length: forall (A : Type)
                           (l l' : list A),
             length (l ++ l') = length l + length l'.
Proof.
  intros. induction l. simpl. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem Свойство_1: forall ls1 ls2 ls3 : list Set,
                       app (app ls1 ls2) ls3
                               = app ls1 (app ls2 ls3).
Proof.
  intros. induction ls1. simpl. reflexivity.
  rewrite <- app_assoc. reflexivity.
Qed.

Theorem Свойство_2: forall (x  : Set)
                           (ls : list Set),
                       app (cons x nil) ls = cons x ls.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem Свойство_3: forall (ys  : list Set)
                           (x z : Set),
                       app (z :: ys) (x :: nil)
                          = z :: (app ys (x :: nil)).
Proof.
  intros. reflexivity.
Qed.

Theorem rev_length': forall (A : Type)
                            (l : list A),
                        length (rev l) = length l.
Proof.
  intros. induction l. simpl. reflexivity.
  simpl. rewrite app_length.
  simpl. rewrite IHl. rewrite (simpl_succ (length l)).
  rewrite (plus_comm 1 (length l)). reflexivity.
Qed.

Theorem distr_rev': forall (A : Type)
                           (x y : list A),
                       rev (x ++ y) = rev y ++ rev x.
Proof.
  intros. induction x. simpl. rewrite app_nil_r. reflexivity.
  simpl. rewrite IHx. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive': forall (A : Type)
                                (l : list A),
                            rev (rev l) = l.
Proof.
  intros. induction l. simpl. reflexivity.
  simpl. rewrite distr_rev'. rewrite IHl.
  simpl. reflexivity.
Qed.

Theorem rev_one': forall {A : Type}
                         (x : A),
                     rev (x :: nil) = x :: nil.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem rev_unit': forall (A : Type)
                          (l : list A)
                          (a : A),
                      rev (l ++ a :: nil) = a :: rev l.
Proof.
  intros. rewrite distr_rev'. simpl. reflexivity.
Qed.

Theorem rev_append_rev: forall (A : Type)
                               (l l' : list A),
                         rev_append l l' = rev l ++ l'.
Proof.
  intros until l. induction l. simpl. reflexivity. 
  intro. simpl. rewrite <- app_assoc. simpl. 
  apply (IHl (a :: l')).
Qed.

Theorem rev_alt: forall (A : Type)
                        (l : list A),
                    rev l = rev_append l nil.
Proof.
  intros. rewrite rev_append_rev. rewrite app_nil_r. reflexivity.
Qed.

Theorem map_app': forall (A B : Type)
                         (f : A -> B)
                         (l l' : list A),
                  map f (l ++ l') = map f l ++ map f l'.
Proof.
  intros. induction l; induction l'. simpl. reflexivity.
  simpl. reflexivity. simpl. rewrite app_nil_r. rewrite app_nil_r.
  reflexivity. simpl. rewrite IHl. simpl. reflexivity.
Qed.
  
Theorem map_map': forall (A B C : Type)
                         (f : A -> B)
                         (g : B -> C)
                         (l : list A),
         map g (map f l) = map (fun x : A => g (f x)) l.
Proof.
  intros. induction l. simpl. reflexivity. simpl.
  rewrite IHl. reflexivity.
Qed.

Theorem map_ext': forall (A B : Type)
                         (f g : A -> B),
            (forall a : A, f a = g a)
                -> forall l : list A, map f l = map g l.
Proof.
  intros. induction l. simpl. reflexivity. 
  simpl. rewrite (H a). rewrite IHl. reflexivity.
Qed.

Theorem map_length': forall (A B : Type)
                            (f : A -> B)
                            (l : list A),
                        length (map f l) = length l.
Proof.
  intros. induction l. simpl. reflexivity. simpl.
  rewrite IHl. reflexivity.
Qed.

Theorem map_rev: forall (A B : Type)
                        (f   : A -> B)
                        (ls  : list A),
                    map f (rev ls) = rev (map f ls).
Proof.
  intros. induction ls. simpl. reflexivity.
  simpl. rewrite map_app'. rewrite IHls.
  simpl. reflexivity.
Qed.

Theorem foldСвойство_1: forall (A B : Type)
                         (l : list B)
                         (e : A)
                         (x : B)
                         (f : B -> A -> A), 
                    fold_right f e (x :: nil) = f x e.
Proof.
  intros. unfold fold_right. reflexivity.
Qed.

Theorem fold_right_length: forall (A : Type)
                                  (l : list A),
              fold_right (fun (_ : A) (x : nat) => S x)
                         0
                         l
                  = length l.
Proof.
  intros. induction l. simpl. reflexivity.
  simpl. rewrite IHl. reflexivity.
Qed.

Theorem fold_right_app': forall (A B : Type)
                                (f : A -> B -> B)
                                (l l' : list A)
                                (i : B),
         fold_right f i (l ++ l')
                  = fold_right f (fold_right f i l') l.
Proof.
  intros. induction l. simpl. reflexivity. 
  simpl. rewrite <- IHl. reflexivity.
Qed.

Theorem foldСвойство_2: forall (A : Type)
                           (g : A -> A)
                           (l : list A)
                           (e : A),
      map g l = fold_right (fun (x : A)
                                (y : list A) => g x :: y)
                           nil
                           l.
Proof.
  intros. induction l. simpl. reflexivity. 
  simpl. rewrite IHl. reflexivity.
Qed.
