(* 
* --------------------
* Avtor : Bespalov V.
* Sessii: 
  1. 2020-10-12T18:13:10.044Z - 2020-10-12T22:14:33.430Z
* Resheno zadach: 18
* -------------------- 
*)

Require Import Coq.Program.Basics.

Theorem ex0_1_1: forall a b g : Type,
                 ((a -> b) -> g) -> b -> g.
Proof.
  refine (fun _ _ _ f x => _).
  refine (f (fun P => x)).
Qed.

Theorem ex0_1_2: forall a b g : Type,
                 (a -> a -> b) -> (g -> a) -> (g -> b).
Proof.
  refine (fun _ _ _ f x y => _).
  refine (f (x y) (x y)).
Qed.

Theorem ex0_1_3: forall a b g : Type,
                 (a -> g) -> (g -> a -> b) -> (a -> b).
Proof.
  refine (fun _ _ _ f t x => _).
  refine (t (f x) x).
Qed.

Theorem ex0_1_4: forall a b : Type,
                 ((b -> a -> b) -> a) -> a.
Proof.
  refine (fun _ _ f => _).
  refine (f const).
Qed.

Theorem ex0_1_5: forall a b g d : Type,
                 ((a -> b) -> g -> d) -> g -> b -> d.
Proof.
  refine (fun _ _ _ _ f x y => _).
  refine (f (fun _ => y) x).
Qed.

Theorem ex0_1_6 : forall a b : Type,
                  ((a -> a) -> b) -> b.
Proof.
  refine (fun _ _ f => _).
  refine (f id).
Qed.

Theorem ex0_1_7: forall a b g : Type,
                 ((a -> b -> a) -> g) -> g.
Proof.
  refine (fun _ _ _ f => _).
  refine (f const).
Qed.

Theorem ex0_1_8: forall a b g d : Type,
                 (((a -> b -> g) -> (b -> a -> g)) -> d) -> d.
Proof.
  refine (fun _ _ _ _ f => _).
  refine (f flip).
Qed.

Definition S : forall a b g : Type,
          (a -> b -> g) -> (a -> b) -> a -> g.
Proof.
  refine (fun _ _ _ f t x => _).
  refine (f x (t x)).
Defined.

Theorem ex0_1_9: forall a b g d : Type,
                 (((a -> b -> g) -> (a -> b) -> (a -> g)) -> d) -> d.
Proof.
  refine (fun _ _ _ _ f => _).
  refine (f (S a b g)).
Qed.

Theorem ex0_1_10: forall a b g : Type,
                  ((a -> b) -> g) -> ((b -> g) -> a -> b) -> g.
Proof.
  refine (fun _ _ _ f t => _).
  refine (f (t (fun _ => _))).
  refine (f (fun _ => _H)).
Qed.

Theorem ex0_1_11: forall a b : Type,
                  ((a -> b) -> (b -> a)) -> (b -> a).
Proof.
  refine (fun _ _ f x => _).
  refine (f (fun _ => x) x).
Qed.

Theorem ex1_1_1: forall a b: Type,
                 (a -> (a -> (a -> b)) -> ((a -> b) -> a) -> b).
Proof.
   refine (fun _ _ x y f => _).
   refine (y x x).
Qed.

Definition P : forall a b g : Type, 
           (a -> a -> g) -> (b -> a) -> b -> b -> g.
Proof.
  refine (fun _ _ _ f t x y => _).
  refine ((f (t x)) (t y)).
Defined.

Theorem ex1_1_2: forall a b g: Type,
                 (a -> a -> g) -> (b -> a) -> b -> b -> g.
Proof.
   refine P.
Qed.

Theorem ex2_1_1: forall d: Type,
                 (forall a: Type, a) -> d.
Proof.
   refine (fun _ f => _).
   refine (f d).
Qed.
 
Theorem ex2_1_2: forall d t: Type,
                 d -> (d -> (forall a: Type, a)) -> t.
Proof.
   refine (fun _ _ f m => _).
   refine (m f t).
Qed.

Theorem ex2_1_3: forall d t: Type,
                 (d -> t) -> (d -> t -> (forall a: Type, a)) -> 
                 d -> (forall a: Type, a).
Proof.
   refine (fun _ _ x y z => _).
   refine (y z (x z)).
Qed.

Theorem ex2_1_4: forall d: Type,
                 d -> (d -> (forall a: Type, a)) -> 
                 (forall a: Type, a).
Proof.
   refine (fun _ x y => _).
   refine (y x).
Qed.

Theorem ex2_2_1: forall b: Type,
                 (forall a: Type, a -> b) -> b.
Proof.
   refine (fun _ x => _).
   refine (x (b -> b) _). (* cut *)
   refine id.
Qed.

Theorem ex2_2_2: forall b: Type,
                 (forall g: Type, g -> g -> b) -> b.
Proof.
   refine (fun _ x => _).
   refine (x (b -> b) _ _).
   refine id.
   refine id.
Qed.

Theorem ex2_2_3: forall b: Type,
                 (forall a: Type, a -> forall g: Type,
                 g -> b) -> b.
Proof.
   refine (fun _ x => _).
   refine (x (b -> b) _ (b -> b) _).
   refine id.
   refine id.
Qed.

Theorem ex2_2_4: forall b: Type,
                 (forall a: Type, a -> forall g: Type, g) -> b.
Proof.
   refine (fun _ x => _).
   refine (x (b -> b) _ b).
   refine id.
Qed.