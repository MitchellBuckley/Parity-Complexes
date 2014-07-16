Require Import Ensembles.

Arguments In : default implicits.
Arguments Setminus : default implicits.
Arguments Disjoint : default implicits.
Arguments Inhabited : default implicits.
Arguments Intersection : default implicits.
Arguments Union : default implicits.
Arguments Same_set : default implicits.
Arguments Included : default implicits.
Arguments Complement : default implicits.

(** I'm going to assume that everything is extensional so that I don't    ** 
 ** need to worry about setoids.                                          **)

Axiom prop_ext : forall (P Q : Prop), 
  (P <-> Q) -> P = Q.

Axiom func_ext_dep : forall (A:Type) (B:A->Type) (f g : forall x, B x),
  (forall x, f x = g x) -> f = g.

(** The following result actually follows from the extensionality principles **
 ** postulated above, but we'll just adopt it as an axiom here.              **
 ** Proof irrelevance means that every proposition only has one proof.       **)

Axiom proof_irrelevance : forall (P : Prop) (p q : P), p = q.

(** We can talk about why this is important and what it means for some of    **
 ** the definitions below when we chat next week.                            **)

(** We could do without this extensionality stuff using setoids, or maybe    **
 ** for the very "discrete" kinds of structures we are thinking of here we   **
 ** might even be able to get away without those                             **)

(** Some useful definitions **)

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

(** Our Module type which declares the "signature" which all pre-parity **
 ** complex Modules must implement                                      **)

Module Type PreParity.

  Parameter carrier : Type.

  (** It will probably be important for the equality on the carrier to be decidable **)

  Axiom decidable_eq_carrier : decidable_rel (eq (A := carrier)).

  Parameter dim : carrier -> nat.

  Parameter plus minus : carrier -> Ensemble carrier.

  (*
  Record faces (p : carrier -> Ensemble carrier) : Prop :=
    {
      dec_ax : forall (x : carrier), decidable _ (p x);
      dim_ax : forall (x y : carrier), In _ (p y) x -> S (dim x) = dim y
    }.

  Axiom plus_ax : faces plus.
  Axiom minus_ax : faces minus.
  *)

  Axiom plus_dec : forall (x : carrier), decidable (plus x).
  Axiom minus_dec : forall (x : carrier), decidable (minus x).

  Axiom plus_fin : forall (x : carrier), finite_set (plus x).
  Axiom minus_fin : forall (x : carrier), finite_set (minus x).

  Axiom plus_dim : forall (x y : carrier), In (plus y) x -> S(dim x) = dim y. 
  Axiom minus_dim : forall (x y : carrier), In (minus y) x -> S(dim x) = dim y. 

End PreParity.

Lemma nat_eq_decidable : forall (n m : nat), (n = m) \/ ~(n = m).
Proof.
  intros n; induction n; intro m; case m; auto.
  intro n'; destruct (IHn n'); auto.
Qed.

(** The following "functor" defines some functions and proves some theorems **
 ** which apply to any PreParity module.                                    **)

Module PreParityDefns (M : PreParity).

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

  Lemma cells_decidable : forall (n : nat), decidable (cells n).
  Proof.
    compute; intros; apply nat_eq_decidable.
  Qed.

  Definition moves (S M P : Ensemble carrier) : Prop :=
    Same_set P (Intersection (Union (M) (Plus S)) (Complement (Minus S))) /\
    Same_set M (Intersection (Union (P) (Minus S)) (Complement (Plus S))).

  Lemma Obs_p321 : forall (S : Ensemble carrier), moves S (MinusPlus S) (PlusMinus S).
  Proof.
  intros S. unfold moves.
   split. unfold PlusMinus. unfold MinusPlus.
   split. unfold Included. intros x H. 


   admit. admit. admit.
  Qed.

  Lemma Same_set_trans : forall (A B C : Ensemble carrier), 
      Same_set A B -> Same_set B C -> Same_set A C.
  Proof.
    intros A B C. compute.
    intros H K. inversion H as [HA HB]. inversion K as [KA KB].
    split.
    intros y J. apply KA. apply HA. apply J.
    intros y J. apply HB. apply KB. apply J.
  Qed.

  Lemma Union_Included : forall (A B C : Ensemble carrier), 
      Same_set (C) (Union A B) -> Included A C.
  Proof.
    intros A B C. compute. intros H. inversion H as [HA HB].
    intros y J. apply HB. apply Union_introl. unfold In. apply J.
  Qed.

  Lemma Union_symm : forall (A B : Ensemble carrier), 
     Union A B = Union B A.
  Admitted.

  Lemma Same_set_Included : forall (A B C : Ensemble carrier), 
      Same_set (A) (B) -> Included C A -> Included C B.
  Proof.
     intros A B C. compute. intros H K. inversion H as [HA HB].
     intros y J. apply HA. apply K. apply J.
  Qed.

  Lemma Same_set_refl : forall (A B : Ensemble carrier), 
      Same_set (A) (B) -> Same_set (B) (A).
  Proof.
     admit.
  Qed.

  Lemma Distribute_r : forall (A B C : Ensemble carrier),
     Same_set (Intersection (Union A B) (C)) (Union (Intersection (A) (C)) (Intersection (B) (C))).
  Proof.
    intros A B C. split. 
    compute. intros y H. 
    admit. admit.
  Qed.

  Lemma Setminus_Intersection_complement : forall (A B : Ensemble carrier),
     Same_set (Setminus A B) (Intersection A (Complement B)).
  Proof.
    intros A B. compute. split. 
    admit. admit.
  Qed.

  Lemma Prop_2_1 : forall (S M : Ensemble carrier), 
     (exists (P : Ensemble carrier), moves S M P) 
   <->
     Included (MinusPlus S) M /\ Disjoint M (Plus S).
  Proof.
    intros S M. split. 
    intros H. inversion H as [wP hP].
    unfold moves in hP. inversion hP as [hPA hPB].
    split.
    apply Union_Included with (B := Intersection wP (Complement (Plus S))).
    unfold MinusPlus.
    apply (Same_set_trans M (Union (Intersection (Minus S) (Complement (Plus S))) (Intersection wP (Complement (Plus S)))) _ ).
    assert (Same_set 
  (Union (Intersection (Minus S) (Complement (Plus S))) (Intersection wP (Complement (Plus S))))
  (Intersection (Union (Minus S) (wP)) (Complement (Plus S)))). apply Same_set_refl. apply Distribute_r. apply Same_set_refl in H0.
    apply (Same_set_trans M (Intersection (Union (Minus S) wP) (Complement (Plus S))) _ ). 
    rewrite (Union_symm (Minus S) wP). apply hPB.
    apply H0. admit.
    admit.
    admit.
  Qed.

End PreParityDefns.

(** The one point type **)

Inductive One :=
| star : One.

Lemma decidable_eq_One : decidable_rel (eq (A := One)).
Proof.
  compute.
  intro x; case x; intro y; case y.
  left; trivial.
Qed.

(** Empty sets are always decidable and have cardinatily 0 **)

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

(** Now let's define a module which implements the PreParity interface     **
 ** which we do by providing definitions for all the functions and proofs  **
 ** for all the axioms defined there                                       **)

Module ZeroCell <: PreParity.

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

End ZeroCell.

(** And we can construct an associated module of definitions and lemmas **
 ** using the PreParityDefns functor                                    **)

Module ZeroCellDefns := PreParityDefns ZeroCell.

(** We can use the definitions in ZeroCell and ZeroCellDefns by Importing    **
 ** those modules into a scope. Here we do this within a section, so that    **
 ** these definition don't "escape" to pollute all of the rest of our theory **)

Section Test.

  Import ZeroCell.
  Import ZeroCellDefns.

  (** So all of the definitions in ZeroCell and ZeroCellDefns are 
      available here **)

  Print minus_dim.

End Test.

(** But they are no longer available here **)