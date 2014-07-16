
(** 
    In this section we will include any definitions concerning the logic
    that we will work with.
    In particular, we need probably need 'exists'.
**)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(**
    Next, we want to introduce the type of 'Sets' that we're 
    going to use. I've chosen Ensemble. This may be subject
    to change in more advanced versions.
**)

Require Import Ensembles.

(** 
    Parity structures are the basic data for a Parity Complex 
    without the required axioms. We call them preParity.
**)

Check Ensemble.

Class preParity 

      { U : Type }
      { C : Ensemble U }
      { ind : U -> nat }
      { pos neg : U -> U -> Prop }        

      : Prop := {
 
      dom_pos_rel : forall ( x y : U ), In U C x /\ In U C y /\ pos x y -> ind y = S (ind x);
      dom_neg_rel : forall ( x y : U ), In U C x /\ In U C y /\ neg x y -> ind y = S (ind x)

}.

(**
    neg x y is the statement "x is a negative face of y"
**)

Generalizable Variables U C ind pos neg T R.

(**
    We need a type for subsets of a preParity.
**)

Class subset
     `{X : preParity U C } 
     (T : Ensemble U)   : Prop := {
     subs_cond: Included U T C
}. 

(**
    We need a type for elements of a preParity.
**)

Class elem 
     `{X : preParity U C } 
     (x : U)   : Prop := {
     elem_cond: In U C x
}. 

(** Definition of $S^+$ for a subset of a parity structure **)
Definition setpos `{X : preParity U C} (T : Ensemble U) (A : subset T) : Ensemble U :=
 (fun (u : U) => exists (v : U), In U T v /\ pos u v).

(** Definition of $S^-$ for a subset of a parity structure **)
Definition setneg `{X : preParity U C} (T : Ensemble U) (A : subset T): Ensemble U :=
 (fun (u : U) => exists (v : U), In U T v /\ neg u v).

(** Definition of $S^\plusminus$ for a subset of a parity structure **)
Definition setposneg `{X : preParity U C} (T : Ensemble U) (A : subset T): Ensemble U :=
 Intersection U (setneg T A) (Complement U (setpos T A)).

(** Definition of $S^\minusplus$ for a subset of a parity structure **)
Definition setnegpos `{X : preParity U C} (T : Ensemble U) (A : subset T): Ensemble U :=
 Intersection U (setpos T A) (Complement U (setneg T A)).

Definition el_pos `{X : preParity U C} (x : U) (A : elem x) : Ensemble U. Admitted.
(* :=
 (setpos (Singleton U x) ). *)

Definition el_neg `{X : preParity U C} (x : U) (A : elem x) : Ensemble U. Admitted. (* :=
 (fun (x : U) => setneg (Singleton U x)). *)

(** Orthogonality of subsets **)
Definition setorth `{X : preParity U C } (R T: Ensemble U) (A : subset R) (B : subset T) : Prop :=
  Same_set U (Empty_set U) (Union U (Intersection U (setneg R A) (setneg T B)) (Intersection U (setpos R A) (setpos T B))).

(** Orthogonality of elements **)
Definition el_orth `{X : preParity U C } (x y : U) : Prop. Admitted.
(* := setorth (Singleton U x) (Singleton U y). **)

(** Definition of well-formedness from p.318 **)
Definition well_formed `{X : preParity U C} (S : Ensemble U) (A : subset S): Prop :=
  forall x : U, In U S x /\ ind x = O -> Same_set U S (Singleton U x)
 /\
  forall x y : U, In U S x /\ In U S y /\ ind x = ind y /\ ind x > O -> ~ ( x = y ) -> (el_orth x y).

(*
~
~
~
~
~
~
~
~
~
~
~
~
~
~
~
~
~
~
*)

(** Definition of 'less than' from p.318 **)
Definition el_lt `{X : preParity U C} : elem U -> elem U -> Prop :=
(fun (A : elem U x) => (fun (B : elem U y) => exists z, In U (Intersection (el_pos A x) (el_neg U y)))).

(** The transitive, reflexive closure of a relation **)
Inductive rtClose {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  reflAx : forall {a : A}, rtClose R a a
| transAx : forall {a b c : A}, R a b -> rtClose R b c -> rtClose R a c. 


Notation "x << y" := ( rtClose el_lt x y)
(at level 50, left associativity) 
                       : nat_scope .

Notation "x == y" := ( x = y )
(at level 50, left associativity) 
                       : nat_scope .


Class ParityComplex `{X : preParity U C} : Prop := 
{ 
  axiom1  : forall (n : nat) (x : C (S (S n))),
    union (setneg (el_neg x)) (setpos (el_pos x)) == union (setpos (el_neg x)) (setneg (el_pos x)) ;
  axiom2  : forall (n : nat) (x : C (S n)), 
    well_formed (el_neg x) /\ well_formed (el_pos x);
  axiom3a : forall (n : nat) (x y: C (S n)), 
    (x << y) /\ (y << x) -> x = y ;
  axiom3b : forall (n : nat) (x y: C (S n)), 
    (x << y) /\ False 
}.

Proposition Prop_1_1 `{X : preParity U C} : forall (n : nat) (x : C (S (S n))),
  is_empty (Intersection (setpos (el_pos x)) (setneg (el_neg x))) /\
  is_empty (Intersection (setpos (el_neg x)) (setpos (el_neg x))) /\
  Intersection (setneg (el_neg x)) (setneg (el_pos x)) == setnegpos (el_neg x) /\
  Intersection (setneg (el_neg x)) (setneg (el_pos x)) == setnegpos (el_pos x) /\
  Intersection (setneg (el_neg x)) (setneg (el_pos x)) == setposneg (el_neg x) /\
  Intersection (setpos (el_neg x)) (setpos (el_pos x)) == setposneg (el_pos x) .
Admitted.

Proposition Prop_1_2 `{X : preParity U C} : 
   forall (n : nat) (x : C (S (S n))) (u v : C (S n)),
   (u << v) /\ (pos (S n) x v) -> is_empty (Intersection (el_neg u) (setpos (el_neg x))).
Admitted.

(** Proposition Prop_1_3 `{X : preParity U C} : ?? . 
Admitted.
**)

Definition moves `{X : preParity U C} (T M P: Type) : Prop := 
 ( P == Intersection (union M (setpos T)) (complement (setneg T)) ) /\  
 ( M == Intersection (union P (setneg T)) (complement (setpos T)) ) .

Proposition Prop_2_1 `{X : preParity U C} :
   forall (T M : Type), exists (P : Type), 
   moves T M P   <->   (setnegpos T = M) /\ is_empty (Intersection M (setpos T)).
Admitted.

Proposition Prop_2_2 `{X : preParity U C} :
   forall (T A B X: Type),
   (moves T A B) /\ (X = A) /\ is_empty (Intersection (setnegpos T) X) ->
   forall (Y : Type),
   is_empty (Intersection Y (setneg T)) /\ is_empty (Intersection Y (setpos T)) -> 
   (moves T (Intersection (union A Y) (complement X)) (Intersection (union B Y) (complement X))).
Admitted.

 


