(* 
* --------------------
* Avtor : Bespalov V.
* Sessii: 
  1. 2020-10-12T18:13:10.044Z - 2020-10-12T22:14:33.430Z
* Resheno zadach: 18
* -------------------- 
*)

Require Import Coq.Program.Basics.

Theorem ex0_1_1: forall a b g : Prop,
                 ((a -> b) -> g) -> b -> g.
Proof.
  refine (fun _ _ _ f x => _).
  refine (f (fun P => x)).
Qed.

Theorem ex0_1_2: forall a b g : Prop,
                 (a -> a -> b) -> (g -> a) -> (g -> b).
Proof.
  refine (fun _ _ _ f x y => _).
  refine (f (x y) (x y)).
Qed.

Theorem ex0_1_3: forall a b g : Prop,
                 (a -> g) -> (g -> a -> b) -> (a -> b).
Proof.
  refine (fun _ _ _ f g x => _).
  refine (g (f x) x).
Qed.

Theorem ex0_1_4: forall a b : Prop,
                 ((b -> a -> b) -> a) -> a.
Proof.
  refine (fun _ _ f => _).
  refine (f const).
Qed.

Theorem ex0_1_5: forall a b g d : Prop,
                 ((a -> b) -> g -> d) -> g -> b -> d.
Proof.
  refine (fun _ _ _ _ f x y => _).
  refine (f (fun _ => y) x).
Qed.

Theorem ex0_1_6 : forall a b : Prop,
                  ((a -> a) -> b) -> b.
Proof.
  refine (fun _ _ f => _).
  refine (f id).
Qed.

Theorem ex0_1_7: forall a b g : Prop,
                 ((a -> b -> a) -> g) -> g.
Proof.
  refine (fun _ _ _ f => _).
  refine (f const).
Qed.

Theorem ex0_1_8: forall a b g d : Prop,
                 (((a -> b -> g) -> (b -> a -> g)) -> d) -> d.
Proof.
  refine (fun _ _ _ _ f => _).
  refine (f flip). (* задачи на распознавание комбинаторов? *)
Qed.

Definition S : forall a b g : Prop,
          (a -> b -> g) -> (a -> b) -> a -> g.
Proof.
  refine (fun _ _ _ f g x => _).
  refine (f x (g x)).
Defined.

Theorem ex0_1_9: forall a b g d : Prop,
                 (((a -> b -> g) -> (a -> b) -> (a -> g)) -> d) -> d.
Proof.
  refine (fun _ _ _ _ f => _).
  refine (f (S P P0 P1)).
Qed.

Theorem ex0_1_10: forall a b g : Prop,
                  ((a -> b) -> g) -> ((b -> g) -> a -> b) -> g.
Proof.
  refine (fun _ _ _ f g => _).
  refine (f (g (fun _ => _))).
  refine (f (fun _ => p)).
Qed.

Theorem ex0_1_11: forall a b : Prop,
                  ((a -> b) -> (b -> a)) -> (b -> a).
Proof.
  refine (fun _ _ f x => _).
  refine (f (fun _ => x) x).
Qed.

Theorem ex1_1_1: forall a b: Prop,
                 (a -> (a -> (a -> b)) -> ((a -> b) -> a) -> b).
Proof.
   refine (fun _ _ x y f => _).
   refine (y x x).
Qed.

Definition P : forall a b g : Prop, 
           (a -> a -> g) -> (b -> a) -> b -> b -> g.
Proof.
  refine (fun _ _ _ f g x y => _).
  refine ((f (g x)) (g y)).
Defined.

Theorem ex1_1_2: forall a b g: Prop,
                 (a -> a -> g) -> (b -> a) -> b -> b -> g.
Proof.
   refine P.
Qed.

Theorem ex2_1_1: forall d: Prop,
                 (forall a: Type, a) -> d.
Proof.
   refine (fun _ f => _).
   refine (f P).
Qed.
 
Theorem ex2_1_2: forall d t: Prop,
                 d -> (d -> (forall a: Type, a)) -> t.
Proof.
   refine (fun _ _ f g => _).
   refine ((g f) P0).
Qed.

Theorem ex2_1_3: forall d t: Prop,
                 (d -> t) -> (d -> t -> (forall a: Type, a)) -> 
                 d -> (forall a: Type, a).
Proof.
   refine (fun _ _ x y z => _).
   refine (y z (x z)).
Qed.

Theorem ex2_1_4: forall d: Prop,
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
   refine (x (T -> T) _). (* cut *)
   refine id.
Qed.

Theorem ex2_2_2: forall b: Prop,
                 (forall g: Type, g -> g -> b) -> b.
Proof.
   refine (fun _ x => _).
   refine (x (P -> P) _ _).
   refine id.
   refine id.
Qed.

Theorem ex2_2_3: forall b: Prop,
                 (forall a: Type, a -> forall g: Type,
                 g -> b) -> b.
Proof.
   refine (fun _ x => _).
   refine (x (P -> P) _ (P -> P) _).
   refine id.
   refine id.
Qed.

Theorem ex2_2_4: forall b: Prop,
                 (forall a: Type, a -> forall g: Type, g) -> b.
Proof.
   refine (fun _ x => _).
   refine (x (P -> P) _ P).
   refine id.
Qed.