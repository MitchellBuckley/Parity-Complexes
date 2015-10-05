
(** 

  Written by Mitchell Buckley, 2015.

  This is an attempt to implement an example of a parity complex. 
  The example is that of cubes.

**)

(** Import libraries **)


Require Import Utf8_core.
Require Import Ensembles.
Require Import Relations.
Require Import Ensembles_setoids.
Require Import Arith.
Require Import Setoid.
Require Import basic_nat.
Require Import Finite_Ensembles.
Require Import PreparityComplexes.
(* Require Import ParityComplexes. *)
Require Import List.
Import List.ListNotations.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Parity Complex Definitions                           *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Definition N : nat := 4.

  Inductive symb : Type :=
  | P : symb
  | M : symb
  | O : symb.

  Definition clist : Type := sum (unit) (prod (list symb) (bool)).

  (* Definition list_count {A} *)

  Lemma symb_dec : (∀ x y : symb, {x = y} + {x ≠ y}).
  Proof with intuition.
    intros x y; induction x, y; 
    (try (left; reflexivity) || (right; intros J; inversion J)).
  Qed.

Definition cdim : (clist) -> nat := 
  fun l => 
    match l with
    | inl e => 0
    | inr l' => 
      match l' with
      | pair l'' b => count_occ symb_dec l'' O +
        match b with
        | true => 0
        | false => 1
        end
      end
    end.

Compute cdim (inr ([P;M;M;O;O;M], true)).

Definition cMinus : clist -> Ensemble clist :=
  fun l =>
    match l with 
    | inl e => Empty_set
    | inr l' => Full_set
    end.

Definition cPlus : clist -> (Ensemble clist) :=
  fun l =>
    match l with 
    | inl e => Empty_set
    | inr l' => Full_set
    end.

Module Orientals_PreParity.

Definition carrier := clist.
Definition dim := cdim. 
Definition plus := cPlus.
Definition minus := cMinus. 

  Theorem carrier_decidable_eq : decidable_eq carrier.
  Proof with intuition.
    unfold decidable_eq.
    unfold not.
    intros a b.
    destruct a, b; [left | right | right | idtac]; intros.
    - induction u, u0; reflexivity.
    - inversion H.
    - inversion H.
    - induction p, p0.
      assert ({b = b0} + {b ≠ b0}). 
        apply Bool.bool_dec...
      assert ({a = l} + {a ≠ l}). 
        apply list_eq_dec; apply symb_dec...
      induction H; [idtac | right].
        induction H0; [left | right]; subst...
          inversion H...
        intros K; inversion K...
  Qed.

  Theorem plus_dim :  forall (x y : carrier), Ensembles.In (plus y) x -> S (dim x) = dim y.
  Proof.
  

  Admitted.

  Theorem minus_dim :   forall (x y : carrier), Ensembles.In (minus y) x -> S (dim x) = dim y.
    Proof.
  Admitted.

  (* face-sets are disjoint, finite and non-empty *)

  Theorem plus_Finite :         forall (x : carrier),   Finite (plus x).
  Proof.
  Admitted.
  Theorem minus_Finite :        forall (x : carrier),   Finite (minus x).
  Proof.
  Admitted.
  Theorem plus_Inhabited :      forall (x : carrier),   dim x > 0 -> (Inhabited (plus x)).
  Proof.
  Admitted.
  Theorem minus_Inhabited :     forall (x : carrier),   dim x > 0 -> (Inhabited (minus x)).
  Proof.
  Admitted.
  Theorem plus_zero:            forall (x : carrier),   (dim x) = 0 ->  plus x == Empty_set.
  Proof.
  Admitted.
  Theorem minus_zero:           forall (x : carrier),   (dim x) = 0 -> minus x == Empty_set.
  Proof.
  Admitted.
  Theorem plus_minus_Disjoint : forall (y : carrier),   Disjoint (plus y) (minus y).
  Proof.
  Admitted.

End Orientals_PreParity.

Module Orientals_PreParityTheory := PreParityTheory(Orientals_PreParity).

Module Orientals_ParityComplex.

(*  Definition C := Orientials_PreParity. *)

  Theorem axiom1 :
    forall (x : carrier),
      (Plus (plus x)) ∪ (Minus (minus x)) == (Plus (minus x)) ∪ (Minus (plus x)).
  Proof.
  Admitted.

  Theorem axiom2a :
    forall x, well_formed (plus x).
  Proof.
  Admitted.

  Theorem axiom2b :
    forall x, well_formed (minus x).
  Proof.
  Admitted.

  Theorem axiom3a:
    forall x y : carrier,
      triangle x y -> triangle y x -> x = y.
  Proof.
  Admitted.

  Theorem axiom3b:
    forall x y z : carrier,
    triangle x y ->
    (~ (In (plus z) x /\ In (minus z) y) /\ ~ (In (plus z) y /\ In (minus z) x)).
  Proof.
  Admitted.

End Orientals_ParityComplex.
