
Require Import Ensembles Constructive_sets.
Require Import Relations.
Require Import mySetoids.
Require Import Setoid.
Require Import Utf8_core.
Require Import Arith.

  Ltac myfinitetactic := 
  match goal with
    | H: _ |- Disjoint ?P ?Q => constructor
    | H: Disjoint ?P ?Q |- _ => inversion H; clear H
    | H: exists x, ?P |- _ => inversion H; clear H
    | H: In (Intersection ?S ?T) ?x |- _ => apply In_Intersection in H
    | H: _ |- In (Intersection ?S ?T) ?x  => apply In_Intersection
    | H: In (Union _ _) _ |- _ => apply In_Union in H
    | H: In ?P ?X, K: In (Complement ?P) ?X |- _ => unfold Complement in K; unfold In in K; unfold not in K; apply K in H; contradiction
    | H: In ?P ?x |- In (Union ?P ?Q) ?x => left
    | H: In ?Q ?x |- In (Union ?P ?Q) ?x => right
    | H: ?x ∈ Add ?U ?A ?y |- _ => unfold Add in H
    | H: _ |- ?x ∈ Add ?U ?A ?y => unfold Add
    | H: ?x ∈ Singleton ?U ?y |- _ => inversion H; clear H
    | H: In (Empty_set) _ |- _ => inversion H
  end.

  Ltac finitecrush := 
    repeat (myfinitetactic; intuition) || intuition.

  Inductive Finite {U : Type} : Ensemble U -> Prop :=
  |  Finite_Empty_set : Finite (Empty_set)
  |  Finite_Add : ∀ A : Ensemble U, Finite A → 
                       ∀ x : U, ¬x ∈ A -> Finite (Add U A x)
  |  Finite_Same_set : forall T, Finite T -> 
                          forall S, S == T -> Finite S.

  Inductive Cardinal {U : Type} : Ensemble U -> nat -> Prop :=
  | Cardinal_Empty_set : Cardinal (Empty_set) 0
  | Cardinal_Add : forall (A : Ensemble U) (n : nat),
               Cardinal A n ->
               forall x : U, ~ In A x -> Cardinal (Add U A x) (S n)
  | Cardinal_Same_set : forall A n, Cardinal A n -> forall B, A == B -> Cardinal B n.

  Inductive Dardinal {U : Type} : Ensemble U -> nat -> Prop :=
  | Dardinal_Empty_set : Dardinal (Empty_set) 0
  | Dardinal_Add : forall (A : Ensemble U), 
                   forall x : U, ~ In A x -> 
                   forall n, Dardinal A n ->
                     Dardinal (Add U A x) (S n)
  | Dardinal_Same_set : forall A B, A == B -> 
                        forall n, Dardinal A n -> 
                          Dardinal B n.

  Hint Constructors Finite Cardinal.

  Lemma strong_induction : 
    forall P : nat -> Prop, 
       P 0 -> 
       (forall n, (forall m, m <= n -> P m) -> P (S n)) -> 
       (forall n, P n) .
  Proof with intuition.
  intros P.
  set (Q := fun n => (forall m, m <= n -> P m)).
  pose (nat_ind Q).
  intros.
  assert (Q 0); unfold Q...
    inversion H1...
  assert ((∀ n : nat, Q n → Q (S n))); unfold Q...
    inversion H4...
  assert (Q n)...
  Qed.
  
  (** SETOID MORPHISMS **)

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
    unfold Same_set, Included, decidable.
    intros...
    specialize H with (x0 := x0). inversion H; clear H...
    specialize H with (x  := x0). inversion H; clear H...
  Qed.

  Add Parametric Morphism U : (@Cardinal U) with 
    signature (@Same_set U) ==> (@eq nat) ==> (@iff) as Cardinal_mor.
  Proof with intuition.
    intros...

    inversion H0; clear H0; subst.
    apply (Cardinal_Same_set Empty_set).
    apply (Cardinal_Empty_set).
    assumption.
    eapply Cardinal_Same_set.
    apply (Cardinal_Add).
    apply H1.
    apply H2.
    assumption.
    apply (Cardinal_Same_set x).
    apply (Cardinal_Same_set A).
    assumption.
    assumption.
    assumption.

    inversion H0; clear H0; subst.
    apply (Cardinal_Same_set Empty_set).
    apply (Cardinal_Empty_set).
    symmetry in H... 
    eapply Cardinal_Same_set.
    apply (Cardinal_Add).
    apply H1.
    apply H2.
    symmetry in H...
    apply (Cardinal_Same_set y).
    apply (Cardinal_Same_set A).
    assumption.
    assumption.
    symmetry in H... 
  Qed.

  (** COMPATIBILITY WITH UNION ETC. **)

  Definition decidable_eq (U : Type) : Prop :=
   forall (a b : U), (a = b \/ ~(a = b)).

  Lemma Finite_are_decidable {U : Type}: 
    decidable_eq U -> 
      forall (T : Ensemble U), Finite T -> decidable T.
  Proof with intuition.
    intros dec_eq.
    intros; unfold decidable...
    
    induction H.

    right... inversion H.
    
    inversion IHFinite; clear IHFinite.
    left...
    assert (x = x0 \/ ~(x = x0)). apply dec_eq.
    inversion H2; clear H2; [left | right]; subst.
      unfold Add; right. constructor.
    intros. unfold Add in H2. inversion H2; clear H2.
    subst...
    subst... inversion H4... 

    inversion IHFinite; [left | right]. 
      rewrite H0...
      intros; apply H1. rewrite <- H0; assumption.
  Qed. 


  Lemma Finite_Included {U : Type} : 
    (forall (A : Ensemble U), decidable A) -> 
     forall (S : Ensemble U), Finite S -> 
     forall T, Included T S -> Finite T.
  Proof with finitecrush. 

    intros alldec S SFinite.
    induction SFinite...
      - assert (T == Empty_set)... 
        apply (Finite_Same_set _ (Finite_Empty_set) T)...

      - assert (x ∈ T \/ ¬x ∈ T)... 
          apply alldec.
        + assert (T == Add U (Setminus T (Singleton U x)) x) as J.  
            apply add_subtract...
          rewrite J...   
          constructor.
          apply IHSFinite. 
          unfold Included... 
          unfold Setminus, In at 1 in H1... apply H0 in H3... 
          idtac... 
          unfold In, Setminus in H1...
        + apply IHSFinite...
          unfold Included...
          assert (In (Add U A x) x0)... exfalso. subst...
      
      - apply IHSFinite...
        rewrite <- H...
  Qed.

  Lemma Finite_Included' {U : Type} :  
  (* \ref{arxiv.org/pdf/math/9405204} for proof I followed *)
     forall (B: Ensemble U), 
       Finite B -> 
     forall A, 
       A ⊆ B -> B == Union A (Setminus B A) -> Finite A.
  Proof with finitecrush.
    intros B BFinite.

    induction BFinite as [ | B' B'Finite IndHyp p | B BFinite IndHyp C eqHyp]; intros A Hyp2 Hyp1.
      - apply (Finite_Same_set _ (Finite_Empty_set) _). 
        apply (Included_Empty_set _ _ Hyp2)... 

      - assert (Finite (Intersection A B')) as AB'Finite. 
          apply IndHyp. 
          unfold Included...
          rewrite Setminus_is_Intersection_Complement. 
          unfold Same_set, Included...
          assert (x ∈ (A ∪ Setminus (Add U B' p) A)) as J'.
          rewrite <- Hyp1.
          unfold Add; left...
          inversion J' as [a K |a K]; clear J'; subst.
            left...
            unfold Setminus, In at 1 in K...
            right... 
            unfold Complement, not, In at 1... 
            right...
          apply In_Complement... 

        assert (p ∈ (A ∪ Setminus (Add U B' p) A)) as J.
          rewrite <- Hyp1...

      inversion J as [a G | a G]; clear J; subst.
        +
        assert (A == Add U (Intersection A B') p). 
          unfold Add, Same_set, Included...
          assert (In (Add U B' p) x). apply Hyp2... 
          unfold Add in H1.  
          inversion H1; clear H1; subst; [left | right]...
          rewrite <- H0...
          rewrite H0... 
          constructor.
        inversion H0; clear H0... subst...

        +
        assert (A == (Intersection A B')). 
          unfold Same_set, Included... 
          assert (In (Add U B' p) x). apply Hyp2... 
          unfold Add in H1.  
          inversion H1; clear H1... subst...
          unfold Setminus, In at 1 in G... intuition.
        apply (Finite_Same_set _ AB'Finite)...

      - apply IndHyp;
      rewrite <- eqHyp...
  Qed.

  Lemma Finite_Included'' {U : Type} : 
     forall (B: Ensemble U), 
       Finite B -> 
     forall A, 
       A ⊆ B -> (forall x, x ∈ B -> ((x ∈ A) \/ ~(x ∈ A))) -> Finite A.
  Proof with intuition. 
    intros. 
    apply (Finite_Included' B)...
    unfold Same_set, Included...
    assert (x ∈ A ∨ (x ∈ A → False)). apply H1... 
    inversion H3; clear H3...
    inversion H2... subst. unfold Setminus, In at 1 in H3...
  Qed.

  Lemma Finite_Union {U : Type} : forall (S T : Ensemble U), decidable S -> Finite T -> Finite S -> Finite (Union S T).
  Proof with finitecrush.
    intros...
    induction H0; intros.
      - eapply (Finite_Same_set S)...

      -
      assert ((x ∈ S) \/ (¬x ∈ S))... apply H.
      + 
        assert (S ∪ Add U A x == S ∪ A). unfold Same_set; unfold Included...
        subst... 
        rewrite H3... 

      + 
        assert (S ∪ Add U A x == Add U (S ∪ A) x). unfold Same_set; unfold Included...
        rewrite H3...
        eapply Finite_Add... 

      - rewrite H2...
  Qed.

  Lemma Finite_Intersection {U : Type} : forall (S: Ensemble U), Finite S -> forall T, decidable T -> Finite (Intersection T S).
  Proof with finitecrush.
    intros S SFin.
    induction SFin; intros.
      - eapply Finite_Same_set. apply Finite_Empty_set. 
        unfold Same_set; unfold Included... 

      - 
      assert ((x ∈ T) \/ (¬x ∈ T))... apply H0.
      +
        assert ((T ∩ Add U A x) == (Add U (T ∩ A) x)).
        unfold Same_set; unfold Included... subst... 
        rewrite H1... constructor...
      + 
        assert ((T ∩ Add U A x) == (T ∩ A)).
        unfold Same_set; unfold Included... subst... 
        rewrite H1... 

      - rewrite H... 
  Qed.

  (** CARDINALITY **)

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

  Lemma Cardinality_one_Singleton {U : Type} : 
    forall (T : Ensemble U), Cardinal T 1 -> exists x, T == (Singleton _ x).
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
    forall (x : U), Cardinal (Singleton U x) 1.
  Proof with finitecrush.
    intros. 
    apply (Cardinal_Same_set (Add U (Empty_set) x))...  
    unfold Same_set, Included... 
  Qed.

  Lemma Finite_Empty_or_Inhabited {U : Type} : 
    forall A : (Ensemble U), Finite A -> ((A == Empty_set) \/ (Inhabited A)).
  Proof with intuition.  
    intros.
    induction H... 
      left. rewrite H0... 
      right. rewrite H0... 
  Qed.

  Lemma Finite_Singleton {U : Type} : 
    forall x, Finite (Singleton U x).
  Proof with finitecrush. 
    intros...
    apply (Finite_Same_set (Add U (Empty_set) x))... 
    unfold Same_set, Included...
  Qed.

  Lemma lt_n_is_Finite : forall n, Finite (fun m => (m < n)). 
  Proof with intuition.
    intros. 
    induction n.
      apply (Finite_Same_set (Empty_set)).
      apply Finite_Empty_set. 
      unfold Same_set, Included, In... inversion H... 
      
      eapply (Finite_Same_set (Add _ (fun m => (m < n)) n ))...
      apply Finite_Add...
      unfold In in H... 
      apply (le_not_lt n n (le_n n))... 

      unfold Same_set, Included...
        unfold In in H... inversion H... 
        unfold Add in H...
        apply In_Union in H... inversion H0; clear H0... 
  Qed.

  Lemma le_n_is_Finite : forall n, Finite (fun m => (m <= n)). 
  Proof with intuition.
    intros. 
    induction n.
      apply (Finite_Same_set (Singleton nat 0)).
      apply Finite_Singleton. 
      unfold Same_set, Included, In... inversion H... inversion H...
      
      eapply (Finite_Same_set (Add _ (fun m => (m <= n)) (S n) ))...
      apply Finite_Add...
      unfold In in H... apply le_Sn_n in H... 

      unfold Same_set, Included...
        unfold In in H... inversion H... 
        unfold Add in H...
        apply In_Union in H... inversion H0; clear H0... 
  Qed.

  Lemma le_total : forall n m, (n <= m) \/ (m <= n).
  Proof with intuition.
    intros n. 
    induction n. 
      - intros. left... 
      - induction m. 
        + right... 
        + specialize IHn with (m := m). 
          inversion IHn; clear IHn...
  Qed.

  Lemma Finite_nat_have_maximum_le_element : 
    forall (T : Ensemble nat), Finite T -> Inhabited T -> 
      exists u, ((In T u) /\ (forall v, (In T v) -> v <= u)).
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
          * exists z... rewrite <- H2... 
          * exists x... apply (le_trans _ z)...

      - rewrite H1 in H0. 
        apply IHFinite in H0... 
        exists x... rewrite H1...  apply H3.  rewrite <- H1... 
  Qed. 

  Lemma Finite_nat_have_minimum_le_element : 
    forall (T : Ensemble nat), Finite T -> Inhabited T -> 
      exists u, ((In T u) /\ (forall v, (In T v) -> u <= v)).
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
          * exists z... rewrite <- H2... 
          * exists x... apply (le_trans _ z)...

      - rewrite H1 in H0. 
        apply IHFinite in H0... 
        exists x... rewrite H1...  apply H3.  rewrite <- H1... 
  Qed. 


  Lemma decidable_nat_have_minimum_le_element : 
    forall (T : Ensemble nat), decidable T -> Inhabited T -> 
      exists u, ((In T u) /\ (forall v, (In T v) -> u <= v)).
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
  assert (Included Z T) as K. 
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

  Lemma Cardinal_Sn {U : Type} : forall T n, @Cardinal U T (S n) -> Inhabited T.
  Proof with intuition.
    intros.
    remember (S n) as W.
    induction H...
      inversion HeqW.
      rewrite <- H0...
  Qed.

  Lemma Finite_Inhabited_Cardinal_Sn {U : Type} : forall X,
    @Finite U X -> Inhabited X ->
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

  Lemma Cardinal_le {U : Type} : 
    forall T n, @Cardinal U T n -> 
      forall R m, @Cardinal U R m -> 
        Included T R -> 
          n <= m.
  Proof with intuition.
  Admitted.

  Lemma Cardinal_Setminus {U : Type} : 
    decidable_eq U -> 
      forall n T, @Cardinal U T (S n) -> 
         forall u, In T u -> Cardinal (Setminus T (Singleton U u)) n.
  Proof with finitecrush. 
  Admitted.

  Lemma Finite_decidable_existence {U : Type}: 
    forall W, Finite W -> 
      forall P : U -> Prop, (forall c, P c \/ ~(P c)) -> 
        ((exists x, In W x /\ P x) \/ ~((exists x, In W x /\ P x))).
  Proof with intuition. 
    intros W WFin.
    induction WFin... 
      - right... inversion H0... inversion H2... 

      - assert (P x ∨ (P x → False))...
        + left... exists x...
        + assert ((∃ x : U, x ∈ A ∧ P x) ∨ ((∃ x : U, x ∈ A ∧ P x) → False))...
      left... inversion H3 as [ a D]; exists a...
      right... apply H3... inversion H1 as [ a D]; exists a... 
      unfold Add in H4. apply In_Union in H4... exfalso. inversion H6... rewrite <- H4 in H5... 

      - assert ((∃ x : U, x ∈ T ∧ P x) ∨ ((∃ x : U, x ∈ T ∧ P x) → False))... 
        + left... inversion H2 as [a A]; exists a... rewrite H...
        + right... apply H2. inversion H1 as [ a A]; exists a... rewrite <- H...
  Qed.

  Lemma Setminus_Finite' {U : Type} :
   ∀ A : Ensemble U,
     Finite A → ∀ B : Ensemble U, Finite B → Finite (Setminus A B). Admitted. 

  
  Lemma Finite_Same_set' {U : Type} : decidable_eq U -> forall S T, S == T -> @Finite U S -> Finite T.
  Proof with intuition.
    intros...
    induction H1.
  Qed.
