
(* Written by Mitchell Buckley 12/11/2013 *)

Require Import Ensembles.
Require Import Finite_sets.
Require Import Relations.
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
Arguments Finite : default implicits.

(* Hints *)

Hint Unfold Setminus.
Hint Constructors Disjoint.

(* Notation *)

Notation "A == B" := (Same_set A B) (at level 79).
Notation "A ∪ B" := (Union A B) (at level 61).
Notation "A ∩ B" := (Intersection A B) (at level 61).
Notation "A ⊆ B" := (Included A B) (at level 79).
Notation "x ∈ A" := (In A x) (at level 71).
Notation "√ A"   := (Complement A) (at level 51).
Notation "A == B == C" := ((A == B) /\ (B == C)) (at level 79, B at next level).
Notation "A ⊆ B ⊆ C" := ((A ⊆ B) /\ (B ⊆ C)) (at level 79, B at next level).


(* omega categories *)

one_glob : Type ?
two_glob :Type ?
is_a_one_category : one_glob -> Prop ?
is_a_two_category : two_glob -> Prop ? 

Record omega_category {A : Type} : Type :=
  {
    C : nat -> Ensemble A;
    src : forall (n : nat), { x | In (C (S n)) x} -> { x | In (C n) x};
    tgt : forall (n : nat), { x | In (C (S n)) x} -> { x | In (C n) x};
    unit : forall (n : nat), { x | In (C n) x}     -> { x | In (C n) x};
    (* mult : forall (n : nat), { (f, g) | In (C (S n)) f /\ In (C (S n)) g /\ s n g = t n f} -> { x | In (C (S n)) x}; *)
    unit_l : forall (n : nat) f , 
                mult n (f, unit n (src f)) = f;
    unit_r : forall (n : nat) f , 
                mult n (unit n (tgt f), f) = f;
    assoc  : forall (n : nat) f g h, 
                src n f = tgt n g /\ src n g = tgt n h ->
                mult n (mult n (f, g), h) = mult n (f, mult n (g, h));
    assoc  : 
  }. 
