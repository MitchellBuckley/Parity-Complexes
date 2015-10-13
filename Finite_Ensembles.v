(**

  Written by Mitchell Buckley. Started on 25/11/2013 while a
  PhD student at Macquarie University

  This collection began as a set of results needed for dealing with Finite sets
  among parity complexes.
  That is still its primary function, but it now presents a different definition
  than the standard library and covers a wide range of rewrite rules.

**)

(** Import libraries **)

  Require Import Utf8_core.
  Require Import basic_nat.
  Require Import Ensembles.
  Require Import Ensembles_setoids.
  Require Import Setoid.
  Require Import Arith.

(* Borrow some tactics from Ensembles_setoids *)

  Ltac finitecrush :=
   repeat (repeat (conj || disj || neg || misc); intuition); intuition.

  (* New definitions of Finite and Cardinal with extra constructor *)

  Inductive Finite {U : Type} : Ensemble U -> Prop :=
  |  Finite_Empty_set : Finite (Empty_set)
  |  Finite_Add : forall A : Ensemble U, Finite A ->
                   forall x : U, ~(x ∈ A) ->
                    Finite (Add U A x)
  |  Finite_Same_set : forall T, Finite T ->
                        forall S, S == T ->
                         Finite S.

  Inductive Cardinal {U : Type} : Ensemble U -> nat -> Prop :=
  | Cardinal_Empty_set : Cardinal (Empty_set) 0
  | Cardinal_Add : forall (A : Ensemble U) (n : nat),
                     Cardinal A n ->
                      forall x : U, ~ x ∈ A ->
                       Cardinal (Add U A x) (S n)
  | Cardinal_Same_set : forall A n, Cardinal A n ->
                         forall B, A == B ->
                          Cardinal B n.

  Hint Constructors Finite Cardinal.

  (** SETOID MORPHISMS **)

  (* Iff is stable under decidable, Finite, Cardinal *)
  Add Parametric Morphism U : (@Finite U) with
    signature (@Same_set U) ==> (@iff) as Finite_mor.
  Proof with intuition.
    intros...
    apply (Finite_Same_set x)...
    apply (Finite_Same_set y)...
  Qed.

  Add Parametric Morphism U : (@decidable U) with
    signature (@Same_set U) ==> (@iff) as decidable_mor.
  Proof with intuition.
    unfold Same_set, Included, decidable...
    specialize H with (x0 := x0)...
    specialize H with (x  := x0)...
  Qed.

  Add Parametric Morphism U : (@Cardinal U) with
    signature (@Same_set U) ==> (@eq nat) ==> (@iff) as Cardinal_mor.
  Proof with intuition.
    intros...
    + inversion H0; clear H0; subst.
      - apply (Cardinal_Same_set Empty_set)...
      - apply (Cardinal_Same_set (Add U A x0))...
      - apply (Cardinal_Same_set x)...
        apply (Cardinal_Same_set A)...
    + inversion H0; clear H0; subst.
      - apply (Cardinal_Same_set Empty_set)...
      - apply (Cardinal_Same_set (Add U A x0))...
      - apply (Cardinal_Same_set y)...
        apply (Cardinal_Same_set A)...
  Qed.

  (** COMPATIBILITY WITH UNION ETC. **)

  Definition decidable_eq (U : Type) : Prop :=
    forall (a b : U), (a = b \/ ~(a = b)).

  (* Finite sets are decidable sets if the type has decidable equality *)

  Lemma Finite_are_decidable {U : Type}:
    decidable_eq U ->
      forall (T : Ensemble U), Finite T -> decidable T.
  Proof with intuition.
    intros dec_eq.
    unfold decidable...
    induction H.
    + right... inversion H.
    + intuition.
      assert (x = x0 \/ ~(x = x0))...
        apply dec_eq.
      - left. crush.
      - right. crush.
    + rewrite H0...
  Qed.

  Hint Resolve Finite_are_decidable.

  (* Finite sets are closed under Intersection and Union *)

  Lemma Finite_Intersection {U : Type} : forall (S: Ensemble U), Finite S -> forall T, decidable T -> Finite (T ∩ S).
  Proof with finitecrush.
    intros S SFin.
    induction SFin...
      - apply (Finite_Same_set Empty_set)...
      - assert ((x ∈ T) \/ (¬x ∈ T))...
          apply H0.
        + apply (Finite_Same_set (Add U (T ∩ A) x))...
          constructor...
          crush.
        + apply (Finite_Same_set (T ∩ A))...
          crush.
      - rewrite H...
  Qed.

  Lemma Finite_Union {U : Type} : forall (S T : Ensemble U), decidable S -> Finite T -> Finite S -> Finite (S ∪ T).
  Proof with finitecrush.
    intros...
    induction H0; intros.
      - apply (Finite_Same_set S)...
      - assert ((x ∈ S) \/ (~x ∈ S))...
          apply H.
        + assert (S ∪ Add U A x == S ∪ A).
            crush.
          rewrite H3...
        + assert (S ∪ Add U A x == Add U (S ∪ A) x).
            crush.
          rewrite H3...
          constructor...
      - rewrite H2...
  Qed.

  Hint Resolve Finite_Union Finite_Intersection.

  (* If set B is finite, A is a subset of B and ... then A is also finite *)
  Lemma Finite_Setminus_Included {U : Type} :
  (* \ref{arxiv.org/pdf/math/9405204} for proof I followed *)
     forall (B: Ensemble U),
       Finite B ->
     forall A,
       A ⊆ B ->
       B == A ∪ (B \ A) ->
       Finite A.
  Proof with finitecrush.
    intros B BFinite.

    induction BFinite as [ | B' B'Finite IndHyp p | B BFinite IndHyp C eqHyp]; intros A Hyp2 Hyp1.
      - apply (Finite_Same_set _ (Finite_Empty_set) _).
        apply (Included_Empty_set _ _ Hyp2)...
      - assert (Finite (A ∩ B')) as AB'Finite.
          apply IndHyp.
          crush.
          unfold Same_set, Included...
          assert (x ∈ (A ∪ Setminus (Add U B' p) A)) as J'.
            rewrite <- Hyp1.
            crush.
          inversion J' as [a K |a K]; clear J'; subst.
            left...
            unfold Setminus, In at 1 in K...
            right...
        assert (p ∈ (A ∪ Setminus (Add U B' p) A)) as J.
          rewrite <- Hyp1...
        inversion J as [a G | a G]; clear J; subst.
        + assert (A == Add U (A ∩ B') p).
            unfold Add, Same_set, Included...
            assert (In (Add U B' p) x).
              apply Hyp2...
            unfold Add in H1.
            inversion H1; clear H1; subst; [left | right]...
          rewrite H0...
          constructor...
        + assert (A == (A ∩ B')).
            unfold Same_set, Included...
            assert (In (Add U B' p) x). apply Hyp2...
            crush.
          apply (Finite_Same_set _ AB'Finite)...
      - apply IndHyp;
        rewrite <- eqHyp...
  Qed.

  (* This is essentially the same as the previous Lemma, the statement is just different *)
  Lemma Finite_Included {U : Type} :
     forall (B: Ensemble U),
       Finite B ->
     forall A,
       A ⊆ B -> (forall x, x ∈ B -> ((x ∈ A) \/ ~(x ∈ A))) -> Finite A.
  Proof with intuition.
    intros.
    apply (Finite_Setminus_Included B)...
    crush.
    assert (x ∈ A ∨ (x ∈ A → False))...
  Qed.

  Hint Resolve Finite_Included Finite_Setminus_Included.

  (** CARDINALITY **)

  (* Sets are finite precisely when they have a cardinality *)

  Lemma Cardinality_exists {U : Type} :
    forall (T : Ensemble U), Finite T -> exists n, Cardinal T n.
  Proof with finitecrush.
    intros T TFin.
    induction TFin.
      - exists 0...
      - inversion IHTFin; clear IHTFin. exists (S x0)...
      - inversion IHTFin; clear IHTFin. exists (x). rewrite H...
  Qed.

  Lemma Cardinal_are_Finite {U : Type} :
    forall n (T : Ensemble U), Cardinal T n -> Finite T.
  Proof with finitecrush.
    intros n T Tcard.
    induction Tcard...
      rewrite <- H...
  Qed.

  (* A set is empty precisely when it has cardinality zero *)

  Lemma Cardinality_zero_Empty_set {U : Type} :
    forall (T : Ensemble U), Cardinal T 0 -> T == (Empty_set).
  Proof with finitecrush.
    remember 0 as n.
    intros T cardT.
    induction cardT...
      inversion Heqn.
      rewrite <- H...
  Qed.

  Lemma Cardinality_Empty_set_is_zero {U : Type} :
    forall (T : Ensemble U), T == (Empty_set) -> Cardinal T 0.
  Proof with finitecrush.
    intros.
    rewrite H...
  Qed.

  (* A set is a singleton precisely when it has cardinality one *)

  Lemma Cardinality_one_Singleton {U : Type} :
    forall (T : Ensemble U), Cardinal T 1 -> exists x, T == (Singleton x).
  Proof with finitecrush.
    remember 1 as n.
    intros. induction H.
      - inversion Heqn.
      - inversion Heqn.
        subst. exists x...
        clear IHCardinal.
        assert (A == Empty_set) as K.
          apply Cardinality_zero_Empty_set...
        rewrite K.
        unfold Same_set, Included...
      - apply IHCardinal in Heqn.
        inversion Heqn.
        exists x... rewrite <- H0...
  Qed.

  Lemma Cardinality_Singleton_is_one {U : Type} :
    forall (x : U), Cardinal (Singleton x) 1.
  Proof with finitecrush.
    intros.
    apply (Cardinal_Same_set (Add U (Empty_set) x))...
    unfold Same_set, Included...
  Qed.

  (* Finite sets are either empty or Inhabited *)

  Lemma Finite_Empty_or_Inhabited {U : Type} :
    forall A : (Ensemble U), Finite A -> ((A == Empty_set) \/ (Inhabited A)).
  Proof with intuition.
    intros.
    induction H...
      left; rewrite H0...
      right; rewrite H0...
  Qed.

  Hint Resolve Finite_Empty_or_Inhabited.

  (* Singletons are finite *)

  Lemma Finite_Singleton {U : Type} :
    forall x : U, Finite (Singleton x).
  Proof with finitecrush.
    intros...
    apply (Finite_Same_set (Add U (Empty_set) x))...
    crush.
  Qed.

  Hint Resolve Finite_Singleton.

  (* some basic sets of natural numbers are finite *)

  (* {x | x <  n} is finite for all n *)
  Lemma lt_n_is_Finite : forall n, Finite (fun m => (m < n)).
  Proof with intuition.
    intros.
    induction n.
    + apply (Finite_Same_set (Empty_set))...
      unfold Same_set, Included, In...
      inversion H...
    + apply (Finite_Same_set (Add _ (fun m => (m < n)) n ))...
      - constructor...
        unfold In in H.
        apply (le_not_lt n n (le_n n))...
      - crush.
        unfold In in H...
        inversion H...
  Qed.

  (* {x | x <= n} is finite for all n *)
  Lemma le_n_is_Finite : forall n, Finite (fun m => (m <= n)).
  Proof with intuition.
    intros.
    induction n.
    + apply (Finite_Same_set (Singleton 0)).
      apply Finite_Singleton.
      unfold Same_set, Included, In; intuition; inversion H...
    + apply (Finite_Same_set (Add _ (fun m => (m <= n)) (S n) ))...
      - apply Finite_Add...
        unfold In in H...
        apply le_Sn_n in H...
      - unfold Same_set, Included...
        * unfold In in H... inversion H...
        * crush.
  Qed.

  (* Finite non-empty sets of natural numbers have maximum and minimum elements *)
  Lemma Finite_nat_have_maximum_le_element :
    forall (T : Ensemble nat), Finite T -> Inhabited T ->
      exists u, ((u ∈ T) /\ (forall v, (v ∈ T) -> v <= u)).
  Proof with finitecrush.
    intros.
    induction H.
      - inversion H0...
      - assert ((A == Empty_set) \/ (Inhabited A)).
          apply Finite_Empty_or_Inhabited...
        inversion H2; clear H2.
        + exists x... rewrite H3 in H4...
        + apply IHFinite in H3.
          inversion H3 as [z]; clear H3...
          assert (((x) <= (z)) \/ ((z) <= (x)))...
            apply le_total.
          * exists z...
          * exists x... apply (le_trans _ z)...
      - rewrite H1 in H0.
        apply IHFinite in H0...
        inversion H0; clear H0...
        exists x...
        rewrite H1...
        apply H3. rewrite <- H1...
  Qed.

  Lemma Finite_nat_have_minimum_le_element :
    forall (T : Ensemble nat), Finite T -> Inhabited T ->
      exists u, ((u ∈ T) /\ (forall v, (v ∈ T) -> u <= v)).
  Proof with finitecrush.
    intros.
    induction H.
      - inversion H0...

      - assert ((A == Empty_set) \/ (Inhabited A)).
          apply Finite_Empty_or_Inhabited...
        inversion H2; clear H2.
        + exists x... rewrite H3 in H4...
        + apply IHFinite in H3.
          inversion H3 as [z]; clear H3...
          assert (((z) <= (x)) \/ ((x) <= (z)))...
            apply le_total.
          * exists z...
          * exists x... apply (le_trans _ z)...

      - rewrite H1 in H0.
        apply IHFinite in H0...
        inversion H0; clear H0.
        exists x... rewrite H1...  apply H3.  rewrite <- H1...
  Qed.

  (* decidable sets of natural numbers have minimum elements *)

  Lemma decidable_nat_have_minimum_le_element :
    forall (T : Ensemble nat), decidable T -> Inhabited T ->
      exists u, ((u ∈ T) /\ (forall v, (v ∈ T) -> u <= v)).
  Proof with finitecrush.

  assert (forall P: nat -> Prop,
            (forall n, ((P n) \/ ~(P n))) ->
            (forall n, ((forall m, m <= n -> P m) \/ ~(forall m, m <= n -> P m)))) as THM.
    intros...
    induction n...
      pose (H 0)... left... inversion H1...
      pose (H (S n))... left... inversion H2...

  intros T decT inhabT.
  inversion inhabT as [w winT]; clear inhabT.
  set (Z := fun s => T s /\ s <= w).
  assert (Z ⊆ T) as K.
    unfold Z, Included, In at 1...
  assert (∃ u : nat, u ∈ Z ∧ (∀ v : nat, v ∈ Z → u <= v)).
    apply Finite_nat_have_minimum_le_element...
    apply (Finite_Same_set (Intersection T (fun s => s <= w)))...
    apply Finite_Intersection...
      apply le_n_is_Finite.
    unfold Z, Same_set, Included... unfold In at 1 in H...
    exists w... unfold Z, In at 1...
  inversion H as [m mMin]; clear H...
  exists m...
  assert ({v <= w} + {w < v})...
    apply le_lt_dec.
  apply H0... unfold Z, In at 1...
  apply (le_trans _ w)... apply H0... unfold Z, In at 1...
  Qed.

  (* Finite sets are inhabited precisely when they have non-zero cardinality *)

  Lemma Cardinal_Sn {U : Type} : forall (T : Ensemble U) n, Cardinal T (S n) -> Inhabited T.
  Proof with intuition.
    intros.
    remember (S n) as W.
    induction H...
      inversion HeqW.
      rewrite <- H0...
  Qed.

  Lemma Finite_Inhabited_Cardinal_Sn {U : Type} : forall (X : Ensemble U),
    Finite X -> Inhabited X ->
      exists n, Cardinal X (S n).
  Proof with intuition.
    intros.
    apply Cardinality_exists in H...
    inversion H as [n J]; clear H...
    destruct n...
      exfalso. apply Cardinality_zero_Empty_set in J...
      inversion H0; clear H0... rewrite J in H; inversion H...

      exists n...
  Qed.

  (* Setminus reduces cardinality by one *)

  Lemma Cardinal_Setminus {U : Type} :
    decidable_eq U ->
      forall n (T : Ensemble U), Cardinal T n ->
         forall u, u ∈ T -> Cardinal (T \ (Singleton u)) (pred n).
  Proof with intuition.
    intuition.
    induction H0...
    - inversion H1...
    - subst.
      assert ((x = u) \/ ~(x = u))...
        apply H...
      + apply (Cardinal_Same_set A)...
        crush.
        exfalso...
      + apply (Cardinal_Same_set (Add U (Setminus A (Singleton u)) x))...
          destruct n...
            exfalso. apply Cardinality_zero_Empty_set in H0. rewrite H0 in H1...
            rewrite Add_Empty_is_Singleton in H1. inversion H1...
            apply Cardinal_Add...
            apply IHCardinal. revert H1; crush.
            revert H3; crush.
        crush.
    - rewrite H2 in *...
  Qed.

  (* Inclusion of finite sets implies ordering of cardinality *)

  Lemma Cardinal_le {U : Type} :
    decidable_eq U ->
    forall (T : Ensemble U) n, Cardinal T n ->
      forall (R : Ensemble U) m, Cardinal R m ->
        T ⊆ R ->
          n <= m.
  Proof with intuition.
    intros Udec T n Tcard.
    generalize dependent T.
    induction n...
    destruct m...
    - exfalso.
      apply Cardinality_zero_Empty_set in H.
      apply Cardinal_Sn in Tcard...
      inversion Tcard...
      assert (In Empty_set x)...
      rewrite <- H. apply H0... inversion H2...
    - apply le_n_S.
      assert (Inhabited T).
        apply Cardinal_Sn in Tcard...
      inversion H1; clear H1.
      set (T' := Setminus T (Singleton x)).
      set (R' := Setminus R (Singleton x)).
      apply IHn with T' R'; unfold T', R'.
      apply (Cardinal_Setminus Udec (S n))...
      apply (Cardinal_Setminus Udec (S m))...
      crush.
  Qed.

  (* For all decidable propositions P and finite sets W,
     W either contains an element satisfying P, or it does not *)

  Lemma Finite_decidable_existence {U : Type}:
    forall W, Finite W ->
      forall P : U -> Prop, (forall c, P c \/ ~(P c)) ->
        ((exists x, x ∈ W /\ P x) \/ ~((exists x, x ∈ W /\ P x))).
  Proof with intuition.
    intros W WFin.
    induction WFin...
      - right... inversion H0... inversion H2...

      - assert (P x ∨ (P x → False))...
        + left... exists x...
        + assert ((∃ x : U, x ∈ A ∧ P x) ∨ ((∃ x : U, x ∈ A ∧ P x) → False))...
      left... inversion H3 as [ a D]; exists a...
      right... apply H3... inversion H1 as [ a D]; exists a...
      unfold Add in H4. apply Union_inv in H4... exfalso. inversion H6... rewrite <- H4 in H5...

      - assert ((∃ x : U, x ∈ T ∧ P x) ∨ ((∃ x : U, x ∈ T ∧ P x) → False))...
        + left... inversion H2 as [a A]; exists a... rewrite H...
        + right... apply H2. inversion H1 as [ a A]; exists a... rewrite <- H...
  Qed.

  (* Among finite sets of equal cardinality, inclusion implies same_set *)

  Lemma Cardinal_eq_Included_Same_set {U : Type} :
    decidable_eq U ->
    forall n (Z : Ensemble U), Cardinal Z n ->
        forall X, Cardinal X n ->
            Z ⊆ X -> X == Z.
  Proof with intuition.
    intros Udec n Z Zcard.
    induction Zcard...
      - apply Cardinality_zero_Empty_set...
      - unfold Same_set...
        unfold Add, Included...
        assert (X == Add U (Setminus X (Singleton x)) x).
          apply Add_Setminus_Singleton. apply Udec...
          apply H1...
        assert (Setminus X (Singleton x) == A).
          apply IHZcard...
          apply (Cardinal_Setminus Udec (S n))... unfold Included...
          assert ((x1 = x) \/ ~(x1 = x))... apply Udec...
            + exfalso. apply H... rewrite <- H6...
            + unfold Setminus, In at 1... inversion H5... +
        rewrite H3 in H2.
        rewrite H4 in H2.
        unfold Add in H2...
      - rewrite <- H. apply IHZcard... rewrite H...
  Qed.

  (* Finite sets are closed under Setminus *)

  Lemma Setminus_Finite {U : Type} :
    decidable_eq U ->
    forall (A : Ensemble U), Finite A ->
    forall (B : Ensemble U), Finite B ->
      Finite (A ∩ (√ B)).
  Proof with intuition.
    intros Udec...
    induction H...
    - apply (Finite_Same_set Empty_set)...
    - unfold Add.
      rewrite I_U_dist_r.
      apply Finite_Union...
      assert (x ∈ B \/ ~(x ∈ B))...
        apply Finite_are_decidable...
      + apply (Finite_Same_set Empty_set)...
        crush.
      + apply (Finite_Same_set (Singleton x))...
        crush.
    - rewrite H1...
  Qed.

  Lemma Setminus_Finite' {U : Type} :
    decidable_eq U ->
    forall (A : Ensemble U), Finite A ->
    forall (B : Ensemble U), Finite B ->
      Finite (A \ B).
  Proof with intuition.
    intros.
    rewrite Setminus_is_Intersection_Complement.
    apply Setminus_Finite...
  Qed.
