
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
Require Import Vector.
Import VectorNotations.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Parity Complex Definitions                           *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Definition N : nat := 4.

  Inductive symb : Type :=
  | P : symb
  | M : symb
  | O : symb.

  Definition clist : Type := t symb N.

  (* Definition list_count {A} *)

  Lemma symb_dec : (∀ x y : symb, {x = y} + {x ≠ y}).
  Proof with intuition.
    intros x y; induction x, y;
    (try (left; reflexivity) || (right; intros J; inversion J)).
  Qed.

  Definition symb_eq : symb -> symb -> bool :=
  fun a => match a with
           | M => fun b => match b with
                           | M => true
                           | _ => false
                           end
           | P => fun b => match b with
                           | P => true
                           | _ => false
                           end
           | O => fun b => match b with
                           | O => true
                           | _ => false
                           end
           end.

  Fixpoint Vcount_occ {M : nat} (j : symb) (l : t symb M) : nat :=
    match l with
    | nil => 0
    | cons h M' tl => match (symb_eq j h) with
       | true => S (Vcount_occ j tl)
       | false =>  Vcount_occ j tl
      end
    end.

  Definition cdim : (clist) -> nat :=
    fun l => Vcount_occ O l.

  Lemma vector_dec : forall {A}, (forall (a b : A), {a = b} + {a <> b}) ->
    forall n, (forall (a b : t A n), {a = b} + {a <> b}).
  Proof with intuition.
   intros A H.
   apply rect2.
   - left...
   - intros.
     specialize H with a b.
     induction H.
     + subst.
       destruct H0.
        * left; subst...
        * right... admit.
     + clear H0. right...
       inversion H...
  Qed.

Compute cdim [P;M;O;M].

Inductive differl {a b : nat} : t symb (a + 1 + b) -> t symb (a + 1 + b) -> Prop :=
| fff : forall (A : t _ a) (B : t _ b), differl (append (append A [O]) B) (append (append A [M]) B).

Definition differr (l l' : clist) (m : Fin.t N): Prop :=
  forall k, (m=k  -> nth l k = O /\ nth l k = P )
    /\
                  (m<>k -> nth l k = nth l' k).

Definition is_even {n : nat} : Fin.t (S n) -> Prop. Admitted.
Definition is_odd  {n : nat} : Fin.t (S n) -> Prop. Admitted.

Definition even : nat -> Prop. Admitted.
Definition odd  : nat -> Prop. Admitted.

Definition cMinus : clist -> clist -> Prop :=
forall l l', exists a b, N = a + 1 + b /\ even a /\ (differl l l').

| oddcasesM : forall l l' k, (is_odd k /\ differr l l' k) -> cMinus l l'.

Inductive cPlus : clist -> clist -> Prop :=
| evencasesP : forall l l' k, (is_even k /\ differr l l' k) -> cPlus l l'
| oddcasesP : forall l l' k, (is_odd k /\ differl l l' k) -> cPlus l l'.

Module Orientals_PreParity.

Definition carrier := clist.
Definition dim := cdim.
Definition plus := cPlus.
Definition minus := cMinus.

  Theorem carrier_decidable_eq : decidable_eq carrier.
  Proof with intuition.
    admit.
  Qed.

  Theorem plus_dim :  forall (x y : carrier), Ensembles.In (plus y) x -> S (dim x) = dim y.
  Proof with intuition.
  unfold plus, dim...
  induction H...
  unfold differr in H1...
  unfold cdim...

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
