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


Lemma example_1 : forall P Q R : Ensemble nat,
  Included P Q -> Included P (Union Q R).
Proof.
  auto with v62.
Qed.

Hint Unfold In.
Hint Constructors Intersection and.

Lemma example_11 : forall P Q R : Ensemble nat, forall x, 
  In (Intersection P Q) x -> In P x.
Proof.
  intuition. eauto 60 with *.
Qed.


Ltac invertexists := 
  match goal with
    H1: exists x, ?P |- _ => inversion H1; clear H1
  end.

Ltac invertconj :=
  match goal with
    H1: ?P /\  ?Q |- _ => inversion H1; clear H1
  end.

Ltac invertInters H :=
  inversion H as [?a L K ?b]; subst; unfold In in K; unfold In in L; clear H.

Ltac unfold_all := 
  match goal with 
    H1: _ |- _ => autounfold with sets in H1
  end; autounfold with sets.

Ltac big_guy := 
  match goal with
    | H1: In ?P ?X |- _ => unfold In in H1
    | H1: (Intersection ?P ?Q) ?X |- _ => inversion H1 as [y A B C]; clear H1; clear C; clear y; unfold In in A; unfold In in B
    | H: _ |- (Intersection ?P ?Q) ?X => constructor; unfold In  
    | H1: ?P ?X, H2: (Complement ?P) ?X |- _ => unfold Complement in H2; unfold In in H2; apply H2 in H1; inversion H1
  end.

Lemma example_2 : forall P Q R S: Ensemble nat,
  Included P Q -> Included R S -> Included (Intersection P R) (Intersection Q S).
Proof.
  autounfold with sets. 
  intros.
  repeat (try big_guy).
  auto.
  big_guy;
  auto.
intros.
  autounfold with sets in H.
  autounfold with sets in H0.
  
  unfold_all. 
  unfold_In.
 unfold In in H2.
  left... auto...
  right... auto...

Hint Constructors and.

Lemma example_3 : forall P Q R S: Prop,
  (P -> Q) -> (R -> S) -> ((P /\ R) -> (Q /\ S)).
Proof.
  intros.
  inversion H1. eauto.
  unfold Included. unfold In. intros. inversion H1. auto with sets. 
  Abort.
