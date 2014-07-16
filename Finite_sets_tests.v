

Require Import Ensembles.

Section Ensembles_finis.

  Variable U : Type.

  Inductive Finite (A : Ensemble U) : Type :=
    | Empty_is_finite : forall (A : Ensemble U),
        Same_set U A (Empty_set U) -> Finite A
    | Union_is_finite : forall (A : Ensemble U),
        Finite A -> forall x:U, ~ In U A x -> Finite (Add U A x).

  Fixpoint cardinal (T : Ensemble U) (P : Finite T) : nat := 
    match P with
      | Empty_is_finite H Q => 0
      | Union_is_finite H Q _ _ => S (cardinal H Q)
    end.

End Ensembles_finis.

  Definition HHH : Ensemble nat := Add _ (Add _ (Add _ (Empty_set _) 4) 9 ) 11.
  
  Lemma KKK : (Finite _ HHH).
  Proof with auto.
    unfold HHH.
    right. right. right. left. admit. 
    unfold not. intros. unfold In in H. inversion H. 
    unfold not. intros. unfold In in H. inversion H. 
    inversion H0. unfold In in H0. inversion H0.  
    unfold not. intros. unfold In in H. inversion H.
    inversion H0. inversion H2. unfold In in H2. inversion H2.
    inversion H0.
  Qed.

  Lemma dec (U : Type) : forall S, (Finite U S) -> forall x, ((In U S x) \/ ~(In U S x)).
  Proof.
    eapply (Finite_ind U).
    intros. 
    Finite_ind
    intros. 
    induction X.
    right. unfold not. intros. unfold Same_set in s. inversion s.
    unfold Included in H0. apply H0 in H. inversion H.
    inversion IHX. left. unfold Add. unfold In. constructor. assumption. unfold Union.
  Qed.

  Lemma asdf (U : Type) : forall S R, (Included U S R) -> Finite _ R -> Finite _ S.
  Proof.
    intros.
    unfold Included in H. 
    induction X.
      left. unfold Same_set; split; unfold Included. unfold Same_set in s.
      inversion s. unfold Included in H0. intros. auto. intros. inversion H0.
      assert
      induction X.
         subst.
      apply IHX. intros. apply H in H0. unfold In in H0. unfold Add in H0.
      inversion H0; subst. assumption. inversion H1. subst.   
  Qed.

Hint Resolve Empty_is_finite Union_is_finite: sets v62.
Hint Resolve card_empty card_add: sets v62.

Require Import Constructive_sets.

Section Ensembles_finis_facts.
  Variable U : Type.

  Lemma cardinal_invert :
    forall (X:Ensemble U) (p:nat),
      cardinal U X p ->
      match p with
        | O => X = Empty_set U
        | S n =>
          exists A : _,
            (exists x : _, X = Add U A x /\ ~ In U A x /\ cardinal U A n)
      end.

  Lemma cardinal_elim :
    forall (X:Ensemble U) (p:nat),
      cardinal U X p ->
      match p with
        | O => X = Empty_set U
        | S n => Inhabited U X
      end.

End Ensembles_finis_facts.
