
(**
    Written by Mitchell Buckley. Started on 25/11/2013 while a
    PhD student at Macquarie University.

    This file contains some basic lemmas concerning natural
    numbers that I could not find in the standard library,
    and were required for a formalisation of the theory
    of Parity Complexes.
  **)

Require Import Utf8_core.
Require Import Arith.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Independent Lemmas concerning nat                    *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  (* Strong mathematical induction *)
  Lemma strong_induction :
    forall P : nat -> Prop,
    P O ->
    (forall n : nat, (forall m, m <= n -> P m) -> P (S n)) ->
    forall n : nat, P n.
  Proof with intuition.
    intros P.
    set (Q := fun n => (forall m, m <= n -> P m)).

    intros.
    assert (Q 0) as A.
      unfold Q... inversion H1...
    assert (forall l, Q l -> Q (S l)) as B.
      unfold Q...
      inversion H2...
    assert (Q n) as C.
      apply (nat_ind Q)...
    apply (C n).
    left.
  Qed.

  (* Less-than-or-equal-to is a total relation *)
  Lemma le_total : forall n m, (n <= m) \/ (m <= n).
  Proof with intuition.
    apply NPeano.Nat.le_ge_cases.
  Qed.

  (* A four case comparison of two natural numbers *)
  Lemma lt_eq_eq_lt_dec: forall k m, {k < m} + {k = m} + {k = S m} + {S m < k}.
  Proof with intuition.
    intros.
    pose (lt_eq_lt_dec k m)...
    unfold lt in b.
    apply le_lt_eq_dec in b...
  Qed.

  (* Three basic contradictions on less-than *)
  Lemma lt_Sn : forall n, (S n < n) -> False.
  Proof with intuition.
    intros n.
    induction n...
    apply (lt_n_0) in H...
  Qed.

  Lemma lt_SSn : ∀ n : nat, S (S n) < n -> False.
  Proof with intuition.
    intros n.
    induction n...
      inversion H...
  Qed.

  Lemma lt_SSSn : ∀ n : nat, S (S (S n)) < n -> False.
  Proof with intuition.
    intros n.
    induction n...
      inversion H...
  Qed.

  (* Two basic contradictions on less-than-or-equal-to *)
  Lemma le_SSn : ∀ n : nat, S (S n) <= n -> False.
  Proof with intuition.
    intros n.
    induction n...
      inversion H...
  Qed.

  Lemma le_SSSn : ∀ n : nat, S (S (S n)) <= n -> False.
  Proof with intuition.
      intros n.
    induction n...
      inversion H...
  Qed.

  (* A basic contradictions on equality *)
  Lemma SSn_n : forall n, S (S n) = n -> False.
  Proof with intuition.
    intros...
    induction n...
    inversion H...
  Qed.

  (* A basic property of the successor function *)
  Lemma Sn_minus_1 : forall n, (S n - 1 = n).
  Proof with intuition.
    simpl...
  Qed.

  Hint Resolve SSn_n le_SSn.
