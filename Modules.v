
(* Written by Mitchell Buckley 11/11/2013 *)
(* A proposed Module structure to describe Parity Complexes *)

Require Import Ensembles.
Require Import Setoid.
Require Import Utf8_core.


(* Implicits *)

Arguments In : default implicits.
Arguments Setminus : default implicits.
Arguments Disjoint : default implicits.
Arguments Inhabited : default implicits.
Arguments Intersection : default implicits.
Arguments Union : default implicits.
Arguments Same_set : default implicits.
Arguments Included : default implicits.
Arguments Complement : default implicits.


(* Notation *)

Notation "A == B" := (Same_set A B) (at level 61).
Notation "A ∪ B" := (Union A B) (at level 61).
Notation "A ∩ B" := (Intersection A B) (at level 61).
Notation "A ⊆ B" := (Included A B) (at level 61).
Notation "x ∈ A" := (In A x) (at level 61).
Notation "√ A"   := (Complement A) (at level 61).


(* misc from Dom's earlier stuff *)

Definition decidable {A : Type} (X : Ensemble A) : Prop :=
  forall (x : A), (In X x) \/ ~(In X x).

Definition rel (A : Type) : Type := A -> A -> Prop.

Definition decidable_rel {A : Type} (R : rel A) : Prop :=
  forall (x y : A), (R x y) \/ ~(R x y).

Inductive Fin : nat -> Type :=
| fO : forall (n : nat), Fin (S n)
| fS : forall (n : nat), Fin n -> Fin (S n).

Record bijection (A B : Type) : Type :=
  {
    f : A -> B;
    f' : B -> A;
    left_inverse_ax : forall (x : A), f' (f x) = x;
    right_inverse_ax : forall (y : B), f (f' y) = y
  }.

Record finite_cardinality (A : Type) : Type :=
  {
    card : nat;
    card_bij : bijection A (Fin card)
  }.

(** We use subset types { x | In X x } to turn Ensembles into types.         **
 ** That the following is the correct definition ultimately relies on        **
 ** proof irrelevance                                                        **)

Definition finite_set {A : Type} (X : Ensemble A) : Type := 
  finite_cardinality { x | In X x }.

(** Inductive definition of the reflexive transitive closure of a relation  **)

Inductive rt_closure {A : Type} (R : rel A) : rel A :=
  | rt_refl : forall (x : A), rt_closure R x x
  | rt_cons : forall (x y z : A), 
                 R x y -> rt_closure R y z -> rt_closure R x z.

Lemma rt_trans : 
  forall {A : Type} (R : rel A) (x y z : A),
    rt_closure R x y -> rt_closure R y z -> rt_closure R x z.
Proof.
  intros A R x y z H.
  revert z.
  induction H as [ | x w y H K IH ].
  trivial.
  intros z L.
  apply (rt_cons _ x w z).
  trivial.
  apply IH.
  trivial.
Qed.
  
(** But Ross' definitions need us to consider reflexive transitive closures  **
 ** of relations restricted to some subset. We use subset types to turn      **
 ** Ensembles into types.                                                    **)

Definition rest_rel 
           {A : Type} (X : Ensemble A) (R : rel A) : rel { x | In X x }. 
  compute.
  intros H K.
  destruct H as [x p].
  destruct K as [y q].
  apply (R x y).
Defined.

Definition unrest_rel 
           {A : Type} {X : Ensemble A} (R : rel { x | In X x }) : rel A :=
  fun (x y : A) => 
    exists (p : In X x) (q : In X y), R (existT _ x p) (existT _ y q).

Definition rt_closure_ens {A : Type} (X : Ensemble A) (R : rel A) :=
  unrest_rel (rt_closure (rest_rel X R)).

Lemma nat_eq_decidable : forall (n m : nat), (n = m) \/ ~(n = m).
Proof.
  intros n; induction n; intro m; case m; auto.
  intro n'; destruct (IHn n'); auto.
Qed.

Lemma finite_is_decidable {U : Type} : 
  forall (S : Ensemble U), finite_set S -> decidable S.
Proof.
  admit. (* This should be done at some point? *)
Qed.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Pre-Parity Complexes and associated results          *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Module Type PreParity.

  Parameter carrier : Type.
  Parameter dim : carrier -> nat.
  Parameter plus minus : carrier -> Ensemble carrier.

  Axiom plus_minus_disjoint : forall (y : carrier), Disjoint (plus y) (minus y).
  Axiom plus_dim : forall (x y : carrier), In (plus y) x -> S(dim x) = dim y. 
  Axiom minus_dim : forall (x y : carrier), In (minus y) x -> S(dim x) = dim y. 
  Axiom plus_dec : forall (x : carrier), decidable (plus x).
  Axiom minus_dec : forall (x : carrier), decidable (minus x).

End PreParity.

Module PreParityTheory (M : PreParity).

  Import M.

  Definition Plus (X : Ensemble carrier) : Ensemble carrier :=
    fun (y : carrier) => (exists (x : carrier), (In X x) /\ (In (plus x) y)).
  Definition Minus (X : Ensemble carrier) : Ensemble carrier :=
    fun (y : carrier) => (exists (x : carrier), (In X x) /\ (In (minus x) y)). 

  Definition PlusMinus (X : Ensemble carrier) : Ensemble carrier :=
    Setminus (Plus X) (Minus X).
  Definition MinusPlus (X : Ensemble carrier) : Ensemble carrier :=
    Setminus (Minus X) (Plus X).

  Definition Perp (X Y : Ensemble carrier) : Prop :=
    (Disjoint (Plus X) (Plus Y)) /\ (Disjoint (Minus X) (Minus Y)).
  Definition perp (x y : carrier) : Prop :=
    (Disjoint (plus x) (plus y)) /\ (Disjoint (minus y) (minus y)).

  Definition less (x y : carrier) : Prop :=
    (Inhabited (Intersection (plus x) (minus y))).
  Definition curly_less (x y : carrier) : Prop :=
    (In (minus y) x) \/ (In (plus x) y). 
  
  Definition triangle (S : Ensemble carrier) : rel carrier := 
    rt_closure_ens S less.
  Definition solid_triangle (S : Ensemble carrier) : rel carrier := 
    rt_closure_ens S curly_less.

  Definition cells (n : nat) : Ensemble carrier :=
    fun (x : carrier) => (dim x = n).

  Definition moves (S M P : Ensemble carrier) : Prop :=
    P == (Intersection (Union (M) (Plus S)) (Complement (Minus S))) /\
    M == (Intersection (Union (P) (Minus S)) (Complement (Plus S))).

  Definition well_formed (X : Ensemble carrier) : Prop :=
    (forall (x y : carrier), dim x = O -> dim y = 0 -> x = y )
    /\
    (forall (n : nat) (x y : carrier), dim x = S n -> dim y = S n -> not (perp x y) -> x = y).


(* Basic results for Preparity Complexes *)

  Lemma Prop_2_4 :
    forall (T Z M P : Ensemble carrier),
    moves (Union T Z) M P -> 
    Included (PlusMinus Z) P ->
    Perp T Z ->
    exists N, moves T M N /\ moves Z N P.
  Proof. admit. Qed.

End PreParityTheory.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Parity Complexes                                     *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Module Type ParityComplex.
  Declare Module C : PreParity.
  Import C.
  Module PPT := PreParityTheory C.
  Import PPT.

  Axiom axiom1 :
    forall (x : carrier), Union (Plus (plus x)) (Minus (minus x)) == Union (Plus (minus x)) (Minus (plus x)).

  Axiom axiom2 :
    forall x, well_formed (plus x) /\ well_formed (minus x).

  Axiom axiom3a:
    forall x y   : carrier, triangle (Full_set _) x y -> triangle (Full_set _) y x -> x = y.

  Axiom axiom3b:
    forall x y z : carrier, 
    triangle (Full_set _) x y ->
    (not (In (plus z) x /\ In (minus z) y) /\ not (In (plus z) y /\ In (minus z) y)).

End ParityComplex.

Module ParityComplexTheory (M : ParityComplex).

Import M.
Import C.
Import PPT. 

(* Section 3 material goes here. *)

Record cell : Type :=
{
  M : Ensemble _;
  P : Ensemble _;
  M_moves : moves M M P;
  P_moves : moves P M P
}.

End ParityComplexTheory.                                    

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* The one-point type : the zero cell                   *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Inductive One :=
| star : One.

Lemma decidable_eq_One : decidable_rel (eq (A := One)).
Proof.
  compute.
  intro x; case x; intro y; case y.
  left; trivial.
Qed.

(* Empty sets are decidable and have cardinality 0 *)

Lemma decidable_empty : forall (A : Type), decidable (Empty_set A).
Proof.
  compute; intros.
  right; intro H; inversion H.
Qed.

Lemma cardinality_empty : forall (A : Type), finite_set (Empty_set A).
Proof.
  compute. intro A.
  apply (Build_finite_cardinality _ 0).
  assert (f : { x | Empty_set A x } -> Fin 0).
  intro H; destruct H as [x p]; inversion p.
  assert (f' : Fin 0 -> { x | Empty_set A x}).  
  intro H; inversion H.
  apply (Build_bijection _ _ f f').
  intro x. destruct x as [x' p]. inversion p.
  intro y. inversion y.
Qed.

(* Zero is a Pre Parity Complex *)

Module ZeroPre <: PreParity.

  Definition carrier := One.

  Definition decidable_eq_carrier := decidable_eq_One.

  Definition dim (x : One) : nat := 0.

  Definition plus (x : One) : Ensemble carrier := Empty_set _.
  Definition minus (x : One) : Ensemble carrier := Empty_set _.

  Lemma plus_dec : forall (x : One), decidable (plus x).
  Proof.
    intro x.
    unfold plus.
    apply decidable_empty.
  Qed.
  
  Lemma minus_dec : forall (x : One), decidable (minus x).
  Proof.
    intro x.
    unfold minus.
    apply decidable_empty.
  Qed.

  Lemma plus_fin : forall (x : carrier), finite_set (plus x).
  Proof.
    intro x. case x. compute.
    apply cardinality_empty.
  Qed.

  Lemma minus_fin : forall (x : carrier), finite_set (minus x).
  Proof.
    intro x. case x. compute.
    apply cardinality_empty.
  Qed.
  
  Lemma plus_dim : forall (x y : One), In (plus y) x -> S(dim x) = dim y.
  Proof.
    intros x y H.
    unfold plus in H.
    inversion H.
  Qed.
  
  Lemma minus_dim : forall (x y : One), In (minus y) x -> S(dim x) = dim y.
  Proof.
    intros x y H.
    unfold plus in H.
    inversion H.
  Qed.

  Lemma plus_minus_disjoint : forall (y : carrier), Disjoint (plus y) (minus y).
  Proof.
    intros. constructor. unfold not. unfold In. 
    intros. inversion H. unfold In in H0. inversion H0.
  Qed.

End ZeroPre.

(* Zero is a ParityComplex *)

Module ZeroCell <: ParityComplex.

  Module C := ZeroPre. 
  Import C.
  Module PPT := PreParityTheory ZeroPre.
  Import PPT.

  Lemma axiom1 :
    forall (x : carrier), Union (Plus (plus x)) (Minus (minus x)) == Union (Plus (minus x)) (Minus (plus x)).
  Proof.
    intros.
    unfold Same_set.
    split;
    unfold Included;
    intros;
    destruct x;
    inversion H;
    inversion H0;
    inversion H2;
    inversion H3.       
  Qed.

  Lemma axiom2 :
    forall x, well_formed (plus x) /\ well_formed (minus x).
  Proof.
    intros. unfold well_formed. 
    split. 
    split. 
    intros. destruct x0. destruct y. reflexivity. 
    intros. destruct x0. inversion H.
    split. 
    intros. destruct x0. destruct y. reflexivity. 
    intros. destruct x0. inversion H.  
  Qed.

  Lemma axiom3a:
    forall x y : carrier, triangle (Full_set _) x y -> triangle (Full_set _) y x -> x = y.
  Proof.
    intros. destruct x. destruct y. auto. 
  Qed.

  Lemma axiom3b:
    forall x y z : carrier, 
    triangle (Full_set _) x y ->
    (not (In (plus z) x /\ In (minus z) y) /\ not (In (plus z) y /\ In (minus z) y)).
  Proof.
    intros.
    split; unfold not; intros B; inversion B as [K J]; unfold In in K; unfold In in J;
    inversion K.
  Qed.

  
End ZeroCell.

Module ZeroPreTheory := PreParityTheory ZeroPre.
Module ZeroCellTheory := ParityComplexTheory ZeroCell. 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Section Test.

  Import ZeroPre.
  Import ZeroPreTheory.
  Import ZeroCell.
  Import ZeroCellTheory.

  Print minus_dim.
  Print cell.

End Test.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


















