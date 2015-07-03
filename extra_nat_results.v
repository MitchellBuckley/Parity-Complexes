
Require Import Utf8_core.
Require Import Arith.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Independent Lemmas concerning nat                    *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

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

  Lemma le_total : forall n m, (n <= m) \/ (m <= n).
  Proof with intuition.
    apply NPeano.Nat.le_ge_cases.
  Qed.

  Lemma lt_eq_eq_lt_dec: forall k m, {k < m} + {k = m} + {k = S m} + {S m < k}.
  Proof with intuition.
   intros.
   pose (lt_eq_lt_dec k m)...
   unfold lt in b.
   apply le_lt_eq_dec in b...
  Qed.

  Lemma lt_Sn_n : forall n, (S n < n) -> False.
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

  Lemma le_SSn : ∀ n : nat, S (S n) <= n -> False.
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

  Lemma le_SSSn : ∀ n : nat, S (S (S n)) <= n -> False.
  Proof with intuition.
     intros n.
    induction n...
      inversion H...
  Qed.

  Lemma SSn_n : forall n, S (S n) = n -> False.
  Proof with intuition.
    intros...
    induction n...
    inversion H...
  Qed.

  Lemma le_SSn_n : forall n, S (S n) <= n -> False.
  Proof with intuition.
    intros...
    induction n...
    inversion H...
  Qed.

  Hint Resolve SSn_n le_SSn_n.

  Lemma Sn_minus_1 : forall n, (S n - 1 = n).
  Proof.
    intros.
    simpl.
    symmetry.
    apply minus_n_O.
  Qed.
