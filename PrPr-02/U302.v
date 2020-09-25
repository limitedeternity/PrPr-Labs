(* 
* --------------------
* Avtor : Bespalov V.
* Sessii: 
  1. 2020-09-23T19:36:53Z - 2020-09-23T23:22:11Z
  2. 2020-09-24T11:32:04Z - 2020-09-24T14:30:16Z
  3. 2020-09-24T18:31:58Z - 2020-09-24T19:33:12Z
* Resheno zadach: 45 + 3 = 48
* -------------------- 
*)

Theorem ex55: forall A : Prop -> Prop,
              (forall x, A x) <-> (forall y, A y).
Proof.
  split. intro. apply H.
  intro. apply H.
Qed.

Theorem ex56: forall A : Prop -> Prop,
              (exists x, A x) <-> (exists y, A y).
Proof.
  split. intro. apply H.
  intro. apply H.
Qed.

Theorem ex57: forall A : Prop -> Prop -> Prop,
              (forall x y, A x y) <-> (forall y x, A y x).
Proof.
  split. intro. apply H. intro. apply H.
Qed.

Theorem ex58: forall A : Prop -> Prop -> Prop,
              (exists x, exists y, A x y) <->
              (exists y, exists x, A y x).
Proof.
  split. intro. apply H. intro. apply H.
Qed.

Theorem ex59: forall A : Prop -> Prop,
              ~(forall x, A x) <-> (exists x, ~A x).
Proof.
  Require Import Classical.
  split. intro. apply NNPP. intro. apply H.
  intros. apply NNPP. intro. apply H0.
  exists x. intro. contradiction.
  intro. elim H. intros. intro.
  apply H0. apply H1.
Qed.

Theorem ex60: forall A : Prop -> Prop,
              ~(exists x, A x) <-> (forall x, ~A x).
Proof.
  split. intros. intro. apply H. exists x.
  assumption. intro. intro. elim H0.
  intros. elim (H x). assumption.
Qed.

Theorem ex61: forall A : Prop -> Prop,
              (forall x, A x) <-> ~(exists x, ~A x).
Proof.
  Require Import Classical.
  split. intro. intro. elim H0. intros.
  apply H1. apply H. intro. intro. apply NNPP.
  intro. apply H. exists x. assumption.
Qed.

Theorem ex62: forall A : Prop -> Prop,
              (exists x, A x) <-> ~(forall x, ~A x).
Proof.
  Require Import Classical.
  split. intro. intro. elim H. intros. apply H0 with x.
  assumption. intro. apply NNPP. intro.
  elim H. intro. intro. apply H0. exists x.
  assumption.
Qed.

Theorem ex63: forall A B : Prop -> Prop,
              (forall x, (A x) /\ (B x)) <-> 
              (forall x, A x) /\ (forall x, B x).
Proof.
  Require Import Coq.Program.Basics.
  split. intro. split. intro. elim H with x.
  apply const. intro. elim H with x.
  refine (fun _ => id). intro. 
  decompose [and] H. intro. split. 
  apply H0. apply H1.
Qed.

Theorem ex64: forall A : Prop -> Prop,
              forall E : Prop,
              (forall x, E /\ (A x)) <->
              (E /\ (forall x, A x)).
Proof.
  Require Import Coq.Program.Basics.
  split. intro. split. apply (H E). intro. 
  elim H with x. refine (fun _ => id).
  intro. decompose [and] H. intro.
  split. assumption. apply H1.
Qed.

Theorem ex65: forall A : Prop -> Prop,
              forall E : Prop,
              (forall x, E \/ (A x)) <->
              (E \/ (forall x, A x)).
Proof.
  Require Import Classical.
  split. intro. apply NNPP. intro.
  apply H0. right. intro. apply NNPP. intro.
  apply H0. left. apply NNPP. intro. elim H with x.
  intro. contradiction. intro. contradiction.
  intro. decompose [or] H. intro. left. assumption.
  intro. right. apply H0.
Qed.

Theorem ex66: forall A B : Prop -> Prop,
              (exists x, (A x) \/ (B x)) <->
              (exists x, A x) \/ (exists x, B x).
Proof.
  split. intro. elim H. intros. decompose [or] H0.
  left. exists x. assumption. 
  right. exists x. assumption.
  intro. decompose [or] H. elim H0. intros.
  exists x. left. assumption.
  elim H0. intros. exists x. right. assumption.
Qed.

Theorem ex67: forall A : Prop -> Prop,
              forall E : Prop,
              (exists x, E \/ (A x)) <->
              E \/ (exists x, A x).
Proof.
  split. intro. elim H. intros. decompose [or] H0.
  left. assumption. right. exists x. assumption.
  intro. decompose [or] H.
  exists E. left. assumption.
  elim H0. intros. exists x. right. assumption.
Qed.

Theorem ex68: forall A : Prop -> Prop,
              forall E : Prop,
              (exists x, E /\ (A x)) <->
              E /\ (exists x, A x).
Proof.
  split. intros. elim H. intros. elim H0.
  intros. split. assumption. exists x.
  assumption. intro. elim H. intros.
  elim H1. intros. exists x. split.
  assumption. assumption.
Qed.

Theorem ex69: forall E : Prop,
              (forall x: Prop, E) <-> E.
Proof.
  Require Import Coq.Program.Basics.
  split. intro. apply (H E). apply const.
Qed.

Theorem ex70: forall E: Prop,
              (exists x: Prop, E) <-> E.
Proof.
  Require Import Coq.Program.Basics.
  split. intro. elim H. refine (fun _: Prop => id).
  intro. exists E. assumption.
Qed.

Theorem ex71: forall A : Prop -> Prop,
              forall E : Prop,
              (exists x, E -> (A x)) <->
              (E -> (exists x, A x)).
Proof.
  Require Import Classical.
  split. intros. elim H. intros. exists x.
  apply (H1 H0). intro. apply NNPP. intro.
  apply H0. elim H. intros. exists x.
  refine (fun _ => H1). apply NNPP. intro.
  apply H0. exists E. intro. contradiction.
Qed.

Theorem ex72: forall A : Prop -> Prop,
              forall E : Prop,
              (exists x, (A x) -> E) <->
              ((forall x, A x) -> E).
Proof.
  Require Import Classical.
  split. intros. elim H. intros.
  apply H1. apply H0. intros.
  apply NNPP. intro. apply H0.
  exists E. intro. apply NNPP. intro.
  apply H2. apply H. intro. apply NNPP.
  intro. apply H0. exists x. intro.
  contradiction.
Qed.

Theorem ex73: forall A B : Prop -> Prop,
              (exists x, (A x) -> (B x)) <->
              ((forall x, A x) -> (exists x, B x)).
Proof.
  Require Import Classical.
  split. intros. elim H. intros. exists x.
  apply H1. apply H0. intros.
  apply NNPP. intro. elim H. intros.
  apply H0. exists x. intro. assumption.
  intro. apply NNPP. intro. apply H0.
  exists x. intro. contradiction.
Qed.

Theorem ex74: forall A : Prop -> Prop,
              forall E : Prop,
              (forall x, (A x) -> E) <->
              ((exists x, A x) -> E).
Proof.
  split. intros. elim H0. intros. apply H with x.
  assumption. intros. apply H. exists x. assumption.
Qed.

Theorem ex75: forall A : Prop -> Prop,
              forall E : Prop,
              (forall x, E -> (A x)) <->
              (E -> (forall x, A x)).
Proof.
  split. intros. apply H. assumption.
  intros. apply (H H0).
Qed.

Theorem ex75_1: forall A B : Prop -> Prop,
                (forall x, (A x) -> (B x)) ->
                ((forall x, A x) -> (forall x, B x)).
Proof.
  intros. apply H. apply H0.
Qed.

Theorem ex75_2: forall A B : Prop -> Prop,
                (forall x, (A x) -> (B x)) ->
                ((exists x, A x) -> (exists x, B x)).
Proof.
  intros. elim H0. intros. exists x. apply H.
  assumption.
Qed.

Theorem ex75_3: forall P Q : Prop -> Prop,
                (forall x, (P x) -> (~Q x)) <->
                ~(exists x, (P x) /\ (Q x)).
Proof.
  split. intro. compute. intro. elim H0.
  intros. elim H1. intros. elim (H x).
  assumption. assumption.
  compute. intros. apply H.
  exists x. split. assumption. assumption.
Qed.

Theorem ex75_4: forall P Q : Prop -> Prop,
                forall E : Prop,
                (forall x, (Q x) -> (P x) -> E) <->
                ((exists x, (P x) /\ (Q x)) -> E).
Proof.
  split. intros. elim H0. intros. elim H1. intros.
  apply (H x). assumption. assumption.
  intros. apply H. exists x. split.
  assumption. assumption.
Qed.

Theorem ex75_5: forall P Q : Prop -> Prop,
                (forall x, (P x) <-> (Q x)) ->
                ((forall x, P x) <-> (forall x, Q x)).
Proof.
  intros. split. intros. apply (H x).
  apply H0. intros. apply (H x). apply H0.
Qed. 

Theorem ex75_6: forall P Q : Prop -> Prop,
                (forall x, (P x) <-> (Q x)) ->
                ((exists x, P x) <-> (exists x, Q x)).
Proof.
  intros. split. intros. elim H0. intros.
  exists x. elim H with x. intros. apply (H2 H1). 
  intro. elim H0. intros. exists x.
  elim H with x. intros. apply (H3 H1).
Qed.

Theorem ex76: forall A : Prop -> Prop,
              forall x, A x -> exists x, A x.
Proof.
  intros. exists x. assumption.
Qed.

Theorem ex77: forall A : Prop -> Prop -> Prop,
              (exists x, forall y, A x y) ->
              (forall y, exists x, A x y).
Proof.
  intros. elim H. intros. exists x. apply H0.
Qed.

Theorem ex78: forall A B : Prop -> Prop,
              (exists x, (A x) /\ (B x)) ->
              ((exists x, A x) /\ (exists x, B x)).
Proof.
  split. elim H. intros. elim H0. intros. 
  exists x. assumption. elim H. intros. 
  elim H0. intros. exists x. assumption.
Qed.

Theorem ex78_1: forall P Q : Prop -> Prop,
                (exists x, (P x) /\ (~Q x)) <->
                ~(forall x, (P x) -> (Q x)).
Proof.
  Require Import Classical.
  split. intro. intro. elim H. intros.
  elim H1. intros. apply H3. apply H0.
  assumption. intro. apply NNPP.
  intro. apply H. intros. apply NNPP. intro.
  apply H0. exists x. split.
  assumption. assumption.
Qed.

Theorem ex78_2: forall P Q : Prop -> Prop,
                forall E : Prop,
                (exists x, (Q x) /\ (P x) /\ E) <->
                (E /\ (exists x, (Q x) /\ (P x))).
Proof.
  split. intro. elim H. intros.
  decompose [and] H0. split.
  assumption. exists x. split.
  assumption. assumption.
  intro. elim H. intros. elim H1.
  intros. elim H2. intros. exists x.
  split. assumption. split.
  assumption. assumption.
Qed.

Theorem ex79: forall A B : Prop -> Prop,
              ((forall x, A x) \/ (forall x, B x)) ->
              (forall x, (A x) \/ (B x)).
Proof.
  intros. decompose [or] H. left. apply H0.
  right. apply H0.
Qed.

Theorem ex80: forall A B : Prop -> Prop,
              ((exists x, A x) -> (forall x, B x)) ->
              (forall x, (A x) -> (B x)).
Proof.
  intros. apply H. exists x. assumption.
Qed.

Theorem ex80_1: forall A B : Prop -> Prop,
                forall x : Prop,
                ((exists x, A x) -> (exists x, B x)) ->
                (exists x, (A x) -> (B x)).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. apply H0.
  elim H. intros. exists x0. intro.
  assumption. generalize (classic x). intro.
  elim H1. intro. exists x. apply NNPP. intro.
  apply H0. exists x. intro. contradiction.
  intro. exists (not x). apply NNPP. intro.
  apply H0. exists (not x).
  intro. contradiction.
Qed.

Theorem ex81: forall A : Prop -> Prop -> Prop,
              (forall x, forall y, A x y) ->
              (forall x, A x x).
Proof.
  intros. apply H.
Qed.

Theorem ex82: forall A : Prop -> Prop -> Prop,
              (exists x, A x x) -> (exists x, exists y, A x y).
Proof.
  intros. elim H. intros. exists x. exists x. assumption.
Qed.

Theorem ex83: forall A : Prop -> Prop,
              forall t : Prop,
              (forall x, A x) -> A t.
Proof.
  intros. apply H.
Qed.

Theorem ex84: forall A : Prop -> Prop,
              forall t : Prop,
              A t -> (exists x, A x).
Proof.
  intros. exists t. assumption.
Qed.

Theorem ex85: forall A : Prop -> Prop,
              forall x : Prop,
              (exists x, A x) \/ (exists x, ~A x).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro. 
  apply H. left. apply NNPP. intro. 
  apply H. right. apply NNPP. intro. 
  apply H1. exists x. intro. 
  apply H0. exists x. assumption.
Qed.

Theorem ex86: forall P Q : Prop -> Prop,
              forall R : Prop -> Prop -> Prop,
              (exists x, (P x) /\
                (exists y, (Q y) /\ (R x y))) <->
              (exists y, (Q y) /\
                (exists x, (P x) /\ (R x y))).
Proof.
  intros. split. intro. elim H. intros.
  elim H0. intros. elim H2. intros. elim H3.
  intros. exists x0. split. assumption. exists x.
  split. assumption. assumption. intros.
  elim H. intros. elim H0. intros. elim H2.
  intros. elim H3. intros. exists x0.
  split. assumption. exists x. split. 
  assumption. assumption.
Qed.

Theorem ex87: forall P Q : Prop -> Prop,
              forall R : Prop -> Prop -> Prop,
              (exists x, (P x) /\
                (forall y, (Q y) -> (R x y))) ->
              (forall y, (Q y) ->
                (exists x, (P x) /\ (R x y))).
Proof.
  intros. elim H. intros. elim H1. intros.
  exists x. split. assumption. apply H3. assumption.
Qed.

(* ===================== *)

Theorem ex2_1a: forall A : Prop,
                (A \/ A) <-> (A /\ A).
Proof.
  Require Import Coq.Program.Basics.
  Require Import Setoid.

  Theorem ex34: forall a : Prop,
                (a /\ a) <-> a.
  Proof.
    Require Import Coq.Program.Basics.
    split. intro. elim H. apply const.
    intro. split. assumption. assumption.
  Qed.

  Theorem ex35: forall a : Prop,
               (a \/ a) <-> a.
  Proof.
    Require Import Coq.Program.Basics.
    intros. split. intro. elim H.
    apply id. apply id. intro.
    left. assumption.
  Qed.

  intro. rewrite (ex34 A).
  rewrite (ex35 A).
  split. apply id. apply id. 
Qed.

(* ex46 *)
Theorem ex2_2a: forall A : Prop,
                ~(~A) <-> A.
Proof.
  Require Import Classical.
  split. intro. apply NNPP. assumption.
  intro. intro. apply H0. assumption.
Qed.

Theorem ex2_3a: forall A B C : Prop -> Prop,
                (forall x, (A x \/ B x) -> C x) -> 
                 (forall x, ((A x -> C x) /\ (B x -> C x))).
Proof.
  intros. split. intro. apply H. left. assumption.
  intro. apply H. right. assumption.
Qed.

(* ====================== *)

Theorem ex3_11: forall P Q : Prop -> Prop,
                forall x : Prop,
                ((forall x, P x) -> (forall x, Q x)) ->
                (exists x, (P x) -> (Q x)).
Proof.
  Require Import Classical.
  intros. apply NNPP. intro.
  apply H0. exists x. intro. apply H.
  intros. apply NNPP. intro.
  apply H0. exists x0. intro.
  contradiction. 
Qed.

Theorem ex3_12: forall P Q : Prop -> Prop,
                ~(exists x, P x) ->
                 (forall x, (P x) -> (Q x)).
Proof.
  intros until Q. compute. intro.
  intros. elim H. exists x. assumption.
Qed.

Theorem ex3_13: forall P : Prop -> Prop,
                (forall x, P x) <->
                (forall x, forall y, (P x) /\ (P y)).
Proof.
  Require Import Coq.Program.Basics.
  split. intros. split. apply H. apply H.
  intros. elim H with x x. apply const.
Qed.
