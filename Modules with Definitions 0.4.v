
(* Written by Mitchell Buckley 12/11/2013 *)

Require Import Ensembles Constructive_sets.
Require Import myFiniteDefs.
Require Import Relations.
Require Import mySetoids.
Require Import Utf8_core.
Require Import Max Le.
Require Import Arith.
Require Import Setoid.

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
Arguments Add : default implicits.
Arguments Singleton : default implicits.
Arguments Empty_set {U} _.
Arguments Full_set {U} _.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Preliminary definitions                              *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Definition restrict {A : Type} (X : Ensemble A) (R : relation A) : relation A :=
   (fun x => (fun y => In X x /\ In X y /\ R x y)).

Definition is_singleton {A : Type} (X : Ensemble A) : Prop :=
  exists x, X == Singleton x.

Hint Unfold decidable : sets v62. 

Transparent In.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Pre-Parity Complex Definitions                       *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Module Type PreParity.

  Parameter carrier : Type.
  Parameter dim : carrier -> nat.
  Parameter plus minus : carrier -> Ensemble carrier.

  Axiom plus_dim :  forall (x y : carrier), In (plus y) x -> S(dim x) = dim y.
  Axiom minus_dim : forall (x y : carrier), In (minus y) x -> S(dim x) = dim y. 
  Axiom plus_fin :  forall (x : carrier),   Finite (plus x).
  Axiom minus_fin : forall (x : carrier),   Finite (minus x).
  Axiom plus_non_empty : forall (x : carrier),  dim x > 0 -> (Inhabited (plus x)).
  Axiom minus_non_empty : forall (x : carrier),  dim x > 0 -> (Inhabited (minus x)).
  Axiom plus_minus_disjoint : forall (y : carrier), Disjoint (plus y) (minus y).
  Axiom zero_faces: forall (x : carrier),   (dim x) = 0 -> (plus x == Empty_set /\ minus x == Empty_set).
  Axiom all_decidable : forall (S : Ensemble carrier), decidable S. 

End PreParity.

Module PreParityTheory (M : PreParity).

  Import M.

  Definition sub (S : Ensemble carrier) (n : nat) : Ensemble carrier := 
    fun (x : carrier) => (In S x /\ dim x  = n).
  Definition sup (S : Ensemble carrier) (n : nat) : Ensemble carrier := 
    fun (x : carrier) => (In S x /\ dim x <= n).
    
  Definition setdim (S : Ensemble carrier) (n : nat) : Prop :=
    forall x, (In S x) -> dim x <= n.

  Definition Plus (X : Ensemble carrier) : Ensemble carrier :=
    fun (y : carrier) => (exists (x : carrier), (In X x) /\ (In (plus x) y)).
  Definition Minus (X : Ensemble carrier) : Ensemble carrier :=
    fun (y : carrier) => (exists (x : carrier), (In X x) /\ (In (minus x) y)). 

  Definition PlusMinus (X : Ensemble carrier) : Ensemble carrier := 
    Intersection (Plus X) (Complement (Minus X)).
  Definition MinusPlus (X : Ensemble carrier) : Ensemble carrier :=
    Intersection (Minus X) (Complement (Plus X)).

  Definition Perp (X Y : Ensemble carrier) : Prop :=
    (Intersection (Plus X) (Plus Y) == Empty_set) /\ (Intersection (Minus X) (Minus Y) == Empty_set).
  Definition perp (x y : carrier) : Prop :=
    (Intersection (plus x) (plus y) == Empty_set) /\ (Intersection (minus x) (minus y) == Empty_set).

  Definition less (x y : carrier) : Prop :=
    (Inhabited (Intersection (plus x) (minus y))).
  Definition curly_less (x y : carrier) : Prop :=
    (In (minus y) x) \/ (In (plus x) y). 
  
  Definition triangle : relation carrier := 
    clos_refl_trans_1n _ (less).
  Definition solid_triangle : relation carrier := 
    clos_refl_trans_1n _ (curly_less).
  Definition triangle_rest (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans_1n _ (restrict S less).
  Definition solid_triangle_rest (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans_1n _ (restrict S curly_less).
    
  Definition is_a_segment (S T : Ensemble carrier) : Prop :=
       S ⊆ T /\
       forall x y z, (less x y) /\ (triangle_rest T y z) ->
       x ∈ S /\ z ∈ S ->
       y ∈ S. 

  Definition is_initial_segment (S T : Ensemble carrier) : Prop :=
       S ⊆ T /\
       forall y z, (triangle_rest T y z) ->
       z ∈ S ->
       y ∈ S. 

  Definition is_final_segment (S T : Ensemble carrier) : Prop :=
       S ⊆ T /\
       forall y z, (triangle_rest T y z) ->
       y ∈ S ->
       z ∈ S. 

  Hint Unfold PlusMinus MinusPlus Perp perp less curly_less triangle solid_triangle
     triangle_rest solid_triangle_rest Plus Minus sup sub: sets v62.

  Definition moves_def (S M P : Ensemble carrier) : Prop :=
    P == (Intersection (Union (M) (Plus S)) (Complement (Minus S))) /\
    M == (Intersection (Union (P) (Minus S)) (Complement (Plus S))).

  Notation "S 'moves' M 'to' P" := (moves_def S M P) (at level 89).

  Definition well_formed (X : Ensemble carrier) : Prop :=
    (forall (x y : carrier), In X x /\ In X y 
        -> (dim x = O -> dim y = 0 -> x = y))
    /\
    (forall (x y : carrier), In X x /\ In X y 
        -> (forall (n : nat), dim x = S n -> dim y = S n -> not (perp x y) -> x = y)).

  Definition tight (R : Ensemble carrier) : Prop :=
    forall u v, 
      triangle u v ->  In R v -> Intersection (minus u) (PlusMinus R) == (Empty_set).

  Hint Unfold moves_def well_formed tight : sets v62.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Basic results direct from definitions                *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Ltac basic := 
  match goal with
    | H: ?P /\ ?Q |- _ => inversion H; clear H
    | H: _ |- ?P /\ ?Q => split
    | H: ?P, K: ?P -> False |- _ => contradiction
    | H: _ |- Disjoint ?P ?Q => constructor
    | H: Disjoint ?P ?Q |- _ => inversion H; clear H
    | H: exists x, ?P |- _ => inversion H; clear H
    | H: _ |- forall x, ?P => intros
    | H: In (Intersection ?S ?T) ?x |- _ => apply In_Intersection in H
    | H: _ |- In (Intersection ?S ?T) ?x  => apply In_Intersection
    | H: In (Union ?S ?T) ?x |- _ => apply In_Union in H
    | H: _ |- ?P == ?P => reflexivity
    | H: _ |- Included ?P ?P => reflexivity
    | H: _ |- ~ (?P) => unfold not; intros
    | H: Perp ?S ?T |- _ => unfold Perp in H
    | H: In ?P ?X, K: In (Complement ?P) ?X |- _ => unfold Complement in K; unfold In in K; unfold not in K; apply K in H; contradiction
    | H: In ?P ?x |- In (Union ?P ?Q) ?x => left
    | H: In ?Q ?x |- In (Union ?P ?Q) ?x => right
    | H: _ |- decidable _ => apply all_decidable
  end.

  Ltac subsuptac := 
  match goal with
    | H: In (sub ?P ?n) ?x |- _ => unfold In at 1 in H; unfold sub in H
    | H: In (sup ?P ?n) ?x |- _ => unfold In at 1 in H; unfold sup in H
    | H: _ |- In (sub ?P ?n) ?x => unfold In, sub
    | H: _ |- In (sup ?P ?n) ?x => unfold In, sup
  end.

Ltac disj := 
  match goal with
    | H: ?P \/ ?Q |- _ => inversion H; clear H
    | H: (?P ∪ ?Q) ?x |- _ => inversion H as [a K aeq | b K beq]; [clear H aeq a | clear H beq b]; unfold In in K
  end.

Ltac conj := 
  match goal with
    | H: (?P ∩ ?Q) ?x |- _ => inversion H as [a H1 H2 aeq]; clear H a aeq
    | H: ?P /\ ?Q |- _ => inversion H; clear H
    | H: _ |- (?P ∩ ?Q) ?x => split; unfold In in *
    | H: _ |- (?P /\ ?Q) => split; unfold In in *
  end; unfold In in *.

Ltac neg :=
  match goal with
    | H: (√(?P)) ?x |- _ => unfold Complement in H; unfold In, not in H
    | H: _ |- (√(?P)) ?x => unfold Complement; unfold In, not
  end.

Ltac misc :=
  match goal with
    | H: (Empty_set) ?x |- _   => contradiction
    | H: (Full_set) ?x |- _    => clear H
    | H: _ |- (Full_set) ?x    => constructor
    | H: _ |- (Empty_set) ?x   => exfalso
    | H: ?a = ?b |- _          => subst
    | H: Singleton ?a ?a |- _  => clear a
    | H: Singleton ?a ?b |- _ =>   inversion H as [K]; clear H; try rewrite K in *; clear K
    | H: Disjoint ?a ?b |- _   => inversion H as [L]; clear H; unfold not, In in L 
    | H: _ |- Disjoint ?a ?b   => constructor; unfold In, not; intros
    | H: Inhabited ?S |- _       => inversion H; clear H
    | H: ?S ?x |- Inhabited ?S   => exists x
end.

  Ltac crush := 
   autounfold with *;
   intuition; 
   repeat (conj || disj || neg || misc); 
   auto.
 
  Ltac splits := 
    match goal with 
      | H: _ |- _ /\ _ => split; try splits
    end. 

  (** SETOID MORPHISMS **)

  Add Parametric Morphism : (@Plus) with 
    signature (@Same_set carrier) ==> (@Same_set carrier) as Plus_Same_set.
  Proof with crush.
    crush. inversion H. exists x1...
    inversion H. exists x1... 
  Qed.

  Add Parametric Morphism : (@Minus) with 
    signature (@Same_set carrier) ==> (@Same_set carrier) as Minus_Same_set.
  Proof with crush.
    crush. inversion H. exists x1...
    inversion H. exists x1... 
  Qed.

  Add Parametric Morphism : (sub) with 
    signature (@Same_set carrier) ==> (@eq nat) ==> (@Same_set carrier) as sub_Same_set.
  Proof with intuition.
    crush.
  Qed.

  Add Parametric Morphism : (sup) with 
    signature (@Same_set carrier) ==> (@eq nat) ==> (@Same_set carrier) as sup_Same_set.
  Proof with intuition.
    crush.
  Qed.

  Add Parametric Morphism : (@moves_def) with 
    signature (@Same_set carrier) ==> (@Same_set carrier) ==> (@Same_set carrier) ==> (@iff) as moves_def_mor.
  Proof with intuition.
    unfold moves_def...
    rewrite <- H, <- H0, <- H1...
    rewrite <- H, <- H0, <- H1...
    rewrite H, H0, H1...
    rewrite H, H0, H1...
  Qed.

  (** PLUS AND MINUS PROPERTIES **)

  Lemma Plus_Union_compat : forall S T,
     Plus (Union S T) == Union (Plus S) (Plus T).
  Proof with intuition. 
    autounfold with *...
    inversion H... inversion H1; [left |right]; unfold In; exists x0...
    inversion H; subst;
    unfold In in H0; inversion H0; exists x0... 
    left... right...
  Qed.

  Lemma Minus_Union_compat : forall S T,
     Minus (Union S T) == Union (Minus S) (Minus T).
  Proof with repeat basic; unfold In; auto.
    intros. autounfold with sets. unfold Minus...
    inversion H.
      left... exists x0...
      right... exists x0...
    inversion H.
      unfold In in H0. inversion H0. exists x1... left...
      unfold In in H0. inversion H0. exists x1... right...
  Qed.

  Lemma Minus_Singleton : forall x, Minus (Singleton x) == minus x.
  Proof with intuition.
    autounfold with *... inversion H... inversion H1... exists x...
  Qed.
  
  Lemma Plus_Singleton : forall x, Plus (Singleton x) == plus x.
  Proof with intuition.
    autounfold with *... inversion H... inversion H1... exists x...
  Qed.

  Lemma PlusMinus_Singleton : forall x, PlusMinus (Singleton x) == plus x.
  Proof with crush. 
    crush... 
    inversion H1... exists x... inversion H0...
    assert (dim x1 > 0 \/ dim x1 = 0).
      destruct (dim x1). right... left...
    inversion H1; clear H1.
    assert (Disjoint (plus x1) (minus x1)). 
      apply plus_minus_disjoint...
    inversion H1. apply (H4 x0)...
    apply zero_faces in H2...
    assert (In Empty_set x0).
    rewrite <- H4... 
    unfold In in *... 
  Qed.

  Lemma MinusPlus_Singleton : forall x, MinusPlus (Singleton x) == minus x.
  Proof with crush. 
    crush... 
    inversion H1... exists x... inversion H0...
    assert (dim x1 > 0 \/ dim x1 = 0).
      destruct (dim x1). right... left...
    inversion H1; clear H1.
    assert (Disjoint (plus x1) (minus x1)). 
      apply plus_minus_disjoint...
    inversion H1. apply (H4 x0)...
    apply zero_faces in H2... 
    assert (In Empty_set x0).
    rewrite <- H4... 
    unfold In in *...
  Qed.

  (** SUB AND SUP PROPERTIES **)

  Lemma sub_Included : forall T n, Included (sub T n) T.
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Included...
  Qed.

  Lemma sup_Included : forall T n, Included (sup T n) T.
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Included...
  Qed.

  Lemma sub_sup_Included : forall T n, Included (sub T n) (sup T n).
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Included...
    rewrite H1...
  Qed.

  Lemma sup_Union : forall T R n, sup (Union T R) n == Union (sup T n) (sup R n).
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Same_set; unfold Included...
    inversion H0; [left | right]...
    inversion H; [left | right]...
    inversion H; inversion H0...
  Qed.

  Lemma sub_Union : forall T R n, sub (Union T R) n == Union (sub T n) (sub R n).
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Same_set; unfold Included...
    inversion H0; [left | right]...
    inversion H; [left | right]...
    inversion H; inversion H0...
  Qed.

  Lemma sub_Included_compat {U : Type} : forall S T, S ⊆ T -> forall m, (sub S m) ⊆ (sub T m).
  Proof.
    autounfold with *. intuition.
  Qed.

  Lemma sup_Included_compat {U : Type} : forall S T, S ⊆ T -> forall m, (sup S m) ⊆ (sup T m).
  Proof.
    autounfold with *. intuition.
  Qed.

  Lemma sup_Intersection : forall T R n, sup (Intersection T R) n == Intersection (sup T n) (sup R n).
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Same_set; unfold Included...
  Qed.

  Lemma sub_Intersection : forall T R n, sub (Intersection T R) n == Intersection (sub T n) (sub R n).
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Same_set; unfold Included...
  Qed.

  Lemma sub_idemp : forall n S, sub (sub S n) n == sub S n.
  Proof with intuition.
    autounfold with *...
  Qed. 

  Lemma sup_idemp : forall n S, sup (sup S n) n == sup S n.
  Proof with intuition.
    autounfold with *...
  Qed. 

  Lemma sub_Minus : forall n T, sub (Minus T) n == Minus (sub T (S n)).
  Proof with intuition.
    autounfold with *. 
    intros. split.
    intros... 
    inversion H0. exists x0... subst. symmetry. apply minus_dim...
    intros.
    inversion H; clear H...
    exists x0...
    apply minus_dim in H1... rewrite H2 in H1... 
  Qed.

  Lemma sup_Plus : forall T n, sup (Plus T) n == Plus (sup T (S n)).
  Proof with repeat (basic || subsuptac); auto.
    unfold Same_set.
    intros.
    unfold Included...
    unfold Plus in H0. unfold In in H0. inversion H0. clear H0...
    unfold Plus. unfold In. exists x0... unfold sup... apply plus_dim in H2.
    rewrite <- H2. apply le_n_S...
    generalize dependent n.
    unfold Plus. unfold Included...
    unfold In in H. inversion H. clear H...
    unfold In. exists x0... unfold sup in H...
    unfold In in H. inversion H. clear H...
    apply le_S_n. apply plus_dim in H1. rewrite H1...
  Qed.

  Lemma sub_sup_Empty_set : forall n k, n < k -> forall S, sub (sup S n) k == Empty_set.
  Proof with intuition.
    autounfold with *... 
    subst. exfalso. 
    apply (le_Sn_n n).
    apply (le_trans _ (dim x))...
  Qed. 

  (** WELL_FORMED PROPERTIES **)
  
  Lemma well_formed_Included : 
    forall S T, Included S T -> well_formed T -> well_formed S.
  Proof with intuition.
    autounfold with *...
    eapply H2.
    split; apply H; assumption.
    apply H0. assumption.
    idtac... 
  Qed.

  Lemma well_formed_Singleton : 
    forall x, well_formed (Singleton x).
  Proof with intuition.
    intros x.
    unfold well_formed...
    inversion H2; inversion H3; subst...
    inversion H0; inversion H1; subst...
  Qed.

  (** RESULTS ABOUT TRIANGLE **)

  Lemma equal_dim : forall x y, triangle x y -> (dim x = dim y). 
  Proof with repeat basic; auto.
    unfold triangle.
    eapply (clos_refl_trans_1n_ind carrier).
      intros... 
      intros... 
      inversion H; clear H. rename x0 into w...
      apply plus_dim in H. apply minus_dim in H3. rewrite <- H1. rewrite <- H3.
      rewrite <- H...
  Qed.

  Lemma rest_implies_full : forall S x y, triangle_rest S x y -> triangle x y.
  Proof with repeat basic; auto.
    unfold triangle.
    unfold triangle_rest.
    intros S.
    eapply Relation_Operators.clos_refl_trans_1n_ind; intros.
      left.
      inversion H...
      eapply Relation_Operators.rt1n_trans. apply H5. assumption.
  Qed.

  (** FINITES SETS HAVE MAXIMAL ELEMENTS **)

  Lemma Finite_carrier_have_max_dim_element : 
    forall (T : Ensemble carrier), Finite T -> Inhabited T -> exists u, ((In T u) /\ 
      (forall v, (In T v) -> dim v <= dim u)).
  Proof with repeat basic; auto.
    intros.
    induction H.
      inversion H0. inversion H. 
      
      assert ((A == Empty_set) \/ (Inhabited A)). apply Finite_Empty_or_Inhabited. assumption.
           inversion H2. 
           exists x... apply Add_intro2. unfold Add in H4... inversion H4.
           rewrite H3 in H5. inversion H5. apply Singleton_inv in H5.        
           subst. apply le_refl. 
           apply IHFinite in H3. inversion H3 as [z]. 
           assert (((dim x) <= (dim z)) \/ ((dim z) <= (dim x))). apply le_total.
           inversion H5; [exists z | exists x]... left... unfold Add in H4...
           inversion H4... apply Singleton_inv in H10; subst...
           right... apply Singleton_intro... unfold Add in H4...
           inversion H4... apply (le_trans _ (dim z) _)... 
           apply Singleton_inv in H10; subst...

      assert (Inhabited T). inversion H0. eapply (Inhabited_intro _ _ x). 
      rewrite <- H1... 
      apply IHFinite in H2. inversion H2. exists x...
      symmetry in H1. rewrite <- H1... 
      apply H5. rewrite <- H1...  
  Qed. 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Section 2                                            *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma Observation_p321 : 
    forall (S : Ensemble carrier), S moves (MinusPlus S) to (PlusMinus S).
  Proof with intuition.
    unfold moves_def, PlusMinus, MinusPlus...

    rewrite U_I_dist_r.
    rewrite Full_set_property.
    rewrite Full_set_ident_right.
    rewrite I_U_dist_r.
    rewrite Empty_set_property.
    rewrite Empty_set_ident_left.
    reflexivity. 
    apply all_decidable.

    rewrite U_I_dist_r.
    rewrite Full_set_property.
    rewrite Full_set_ident_right.
    rewrite I_U_dist_r.
    rewrite Empty_set_property.
    rewrite Empty_set_ident_left.
    reflexivity. 
    apply all_decidable.
  Qed.

  Lemma Prop_2_1 : forall (S M : Ensemble carrier), 
     (exists (P : Ensemble carrier), S moves M to P) 
     <->
     (MinusPlus S) ⊆ M /\ Disjoint M (Plus S).
  Proof with repeat basic; auto.
    unfold moves_def; unfold PlusMinus; unfold MinusPlus. 
    intros S M; split; intros. 
    inversion H as [P]; clear H.
    intuition.

    rewrite H1.
    apply Intersection_Included_compat. unfold Included... reflexivity.

    constructor. unfold not; intros. apply In_Intersection in H0. intuition.
    rewrite H1 in H2...

    exists ((M ∪ Plus S) ∩ √Minus S).
    split; try reflexivity.
    rewrite U_I_dist_r.
    rewrite Full_set_property.
    rewrite Full_set_ident_right.
    rewrite I_U_dist_r. 
    rewrite I_U_dist_r.
    rewrite Empty_set_property.
    rewrite Empty_set_ident_right.
    inversion H; clear H.
    assert ((M ∩ √Plus S) == M). eapply Intersection_Included_left.
    apply Disjoint_property_right. apply Disjoint_sym. assumption. 
    rewrite H; clear H.
    symmetry. rewrite Union_sym.
    apply Union_Included_left. apply H0.
    apply all_decidable.
  Qed.

  Lemma Prop_2_1' : forall (S M : Ensemble carrier), 
     S moves M to ((M ∪ (Plus S)) ∩ √(Minus S)) 
     <->
     (MinusPlus S) ⊆ M /\ Disjoint M (Plus S).
  Proof with intuition. 
    intros. split; intros.
    apply Prop_2_1.
    exists ((M ∪ Plus S) ∩ √Minus S). assumption.
    apply Prop_2_1 in H.
    inversion H as [P K]. 
    unfold moves_def in *...
    rewrite <- H0...
  Qed.

  Lemma Prop_2_1_dual : forall (S P : Ensemble carrier), 
     (exists (M : Ensemble carrier), S moves M to P) 
     <->
     (PlusMinus S) ⊆ P /\ Disjoint P (Minus S).
  Proof with repeat basic; auto.
    unfold moves_def; unfold PlusMinus; unfold MinusPlus. 
    intros S P; split; intros. 
    inversion H as [M]; clear H.
    intuition.

    rewrite H. 
    apply Intersection_Included_compat. unfold Included... reflexivity.

    constructor. unfold not; intros. apply In_Intersection in H0. intuition.
    rewrite H in H2... 

    exists ((P ∪ Minus S) ∩ √Plus S).
    split; try reflexivity.
    rewrite U_I_dist_r.
    rewrite Full_set_property.
    rewrite Full_set_ident_right.
    rewrite I_U_dist_r. 
    rewrite I_U_dist_r.
    rewrite Empty_set_property.
    rewrite Empty_set_ident_right.
    inversion H; clear H.
    assert ((P ∩ √Minus S) == P). eapply Intersection_Included_left.
    apply Disjoint_property_right. apply Disjoint_sym. assumption. 
    rewrite H; clear H.
    symmetry. rewrite Union_sym.
    apply Union_Included_left. apply H0.
    apply all_decidable.
  Qed.

  Lemma Prop_2_2 : 
    forall (S A B X: Ensemble carrier),
    S moves A to B -> X ⊆ A -> Disjoint (MinusPlus S) X 
    -> 
    forall (Y : Ensemble carrier),  
    Disjoint Y (Plus S) -> Disjoint Y (Minus S) 
    ->
    S moves ((A ∪ Y) ∩ (√X)) to ((B ∪ Y) ∩ (√X)).
  Proof.
    intros...
    unfold moves_def in H. inversion H; clear H.
    assert (exists (P : Ensemble carrier), S moves ((A ∪ Y) ∩ √X) to P).
      apply Prop_2_1.
      split.
        apply Included_trans with (T:=(A ∩ √X)).
          rewrite H5. 
          rewrite <- (Intersection_idemp (MinusPlus S)).
          apply Intersection_Included_compat.
          unfold MinusPlus. 
          apply Intersection_Included_compat.
          apply Union_Included_cancel_left. reflexivity. reflexivity.
          apply Disjoint_property_left. apply H1.
          apply Intersection_Included_compat.
          apply Union_Included_cancel_right; reflexivity. reflexivity.
          
        apply Disjoint_intersection_condition.
        rewrite Intersection_trans. rewrite (Intersection_sym _ (Plus S)).
        rewrite <- Intersection_trans.
        rewrite I_U_dist_r. assert (Disjoint Y (Plus S)). apply H2. 
        apply Disjoint_intersection_condition in H. rewrite H.
        rewrite Empty_set_ident_right.
        rewrite H5. rewrite (Intersection_trans _ _ (Plus S)).
        rewrite (Intersection_sym _ (Plus S)). rewrite Empty_set_property.
        rewrite Empty_set_zero. rewrite Intersection_sym.
        rewrite Empty_set_zero. reflexivity.

    inversion H as [P].
    assert (P == (B ∪ Y) ∩ √X).
    Focus 2. unfold moves_def. unfold moves_def in H6. inversion H6; clear H6. 
    split; rewrite <- H7; assumption.
    clear H.
    inversion H6; clear H6.
    rewrite H, H4.
    repeat rewrite U_I_dist_r.
    rewrite Union_trans.
    rewrite (Union_sym Y).
    rewrite <- Union_trans.
    repeat rewrite Intersection_trans.
    rewrite Intersection_Same_set_compat; try reflexivity.
    rewrite (Union_sym _ Y). 
    rewrite (Union_Included_left Y _).
    rewrite (Union_sym). 
    rewrite (Union_Included_left).
    apply Intersection_sym. 
    apply Complement_Included_flip. apply (Included_trans _ _ _ H0).
    rewrite H5. apply Intersection_Included_cancel_left. reflexivity.
    apply Disjoint_property_left. apply H3.
  Qed.

  Lemma Prop_2_3 : 
    forall (S M P T Q : Ensemble carrier),
    S moves M to P -> T moves P to Q -> (Disjoint (Minus S) (Plus T) ) 
    ->
    (S ∪ T) moves M to Q.
  Proof with repeat basic; auto.
    intros.
    unfold moves_def in *.  intuition. 
    
    rewrite H. 
    assert (Plus T == Intersection (Plus T) (Complement (Minus S))).
      symmetry. apply Intersection_Included_left. apply Disjoint_property_right. assumption. 
    rewrite H0.
    rewrite H2.
    rewrite <- I_U_dist_r.
    assert ((√Minus S ∩ √Minus T) == (√Minus(Union S T))). 
    rewrite Minus_Union_compat. rewrite Union_Complement_compat...
    rewrite <- H5.
    rewrite <- Intersection_trans.
    assert ((Plus S ∪ Plus T) == (Plus (S ∪ T))). 
    rewrite Plus_Union_compat...
    rewrite <- H6.
    rewrite <- Union_trans...

    rewrite H3. 
    assert (Minus S == Intersection (Minus S) (Complement (Plus T))).
      symmetry. apply Intersection_Included_left. apply Disjoint_property_right. 
      apply Disjoint_sym. assumption. 
    rewrite H0.
    rewrite H4.
    rewrite <- I_U_dist_r.
    assert ((√Plus T ∩ √Plus S) == (√Plus(Union S T))). 
    rewrite Plus_Union_compat. rewrite Union_Complement_compat... rewrite Union_sym...
    rewrite <- H5.
    rewrite <- Intersection_trans.
    assert ((Minus T ∪ Minus S) == (Minus (S ∪ T))). 
    rewrite Minus_Union_compat... rewrite Union_sym...
    rewrite <- H6.
    rewrite <- Union_trans...
  Qed.

 
  Lemma Prop_2_4 :
    forall (T Z M P : Ensemble carrier),
    (Union T Z) moves M to P -> 
    Included (PlusMinus Z) P ->
    Perp T Z ->
    exists N N', (N == N') /\ (T moves M to N) /\ (Z moves N' to P).
  Proof with repeat basic; auto.
    intros T Z M P. 
    remember (Union T Z) as S.
    intros.
    unfold moves_def in H...
    
    assert (exists N, Z moves N to P). 
    apply Prop_2_1_dual. 
      split; try assumption.
      assert (Included (Minus Z) (Minus S)). 
        rewrite HeqS. rewrite Minus_Union_compat. apply Union_Included_cancel_left. reflexivity.
      apply Disjoint_intersection_condition. eapply (Included_Empty_set). eapply Intersection_Included_compat.
      reflexivity. apply H1. 
      rewrite H2. rewrite Intersection_trans. rewrite (Intersection_sym _ (Minus S)). 
      rewrite Empty_set_property. rewrite Empty_set_zero. reflexivity.      
    inversion H1 as [N']; clear H1.

    assert (exists N', T moves M to N').        
    apply Prop_2_1. split.
      assert (K1: Plus T == (Plus S) ∩ √(Plus Z)). 
        rewrite HeqS. rewrite Plus_Union_compat. rewrite I_U_dist_r.
        rewrite Empty_set_property. rewrite Empty_set_ident_right.
        apply Disjoint_result... 
      assert (K2: Minus T == (Minus S) ∩ √(Minus Z)). rewrite HeqS. 
        rewrite Minus_Union_compat. rewrite I_U_dist_r.
        rewrite Empty_set_property. rewrite Empty_set_ident_right.
        apply Disjoint_result...  
      assert ((MinusPlus T) == (MinusPlus S ∩ √(Minus Z)) ∪ (Minus S ∩ (PlusMinus Z)) ). 
        unfold MinusPlus, PlusMinus. rewrite K1, K2.
        rewrite (Intersection_Complement_compat).
        rewrite (Complement_Complement_compat).
      unfold Same_set; unfold Included...
        inversion H7... left... right... 
        inversion H1. apply In_Intersection in H6... apply In_Intersection in H6... 
        inversion H1. apply In_Intersection in H6... apply In_Intersection in H6... 
        inversion H1; apply In_Intersection in H6...  
        apply all_decidable. apply all_decidable.

      assert (M == (Union M (Intersection (Minus S) P))).
      unfold Same_set; unfold Included...
        inversion H6... symmetry in H3. rewrite <- H3...
        rewrite H2 in H9... 

      rewrite H1, H6. rewrite H3.
      unfold MinusPlus.
      unfold Included...
      inversion H7. left... right... 

      (* apply Disjoint_intersection_condition.  *)
      constructor... rewrite H3 in H6...
      rewrite HeqS in H8. assert ((√Plus (T ∪ Z)) == ((√ Plus T ∩ √ Plus Z))).
      rewrite Plus_Union_compat. rewrite Union_Complement_compat...
      rewrite H6 in H8...

    inversion H1 as [N]; clear H1. 
    exists N. exists N'...
    
    unfold moves_def in H5. inversion H5. clear H5.
    unfold moves_def in H6. inversion H6. clear H6.
    rewrite H7, H5. 
    assert ((Plus T) == (Intersection (Plus S) (Complement (Plus Z)))).
      rewrite HeqS. rewrite Plus_Union_compat. rewrite I_U_dist_r.
      rewrite Empty_set_property. rewrite Empty_set_ident_right.
      apply Disjoint_result. assumption.
    assert ((Minus T) == (Intersection (Minus S) (Complement (Minus Z)))).
      rewrite HeqS. rewrite Minus_Union_compat. rewrite I_U_dist_r.
      rewrite Empty_set_property. rewrite Empty_set_ident_right.
      apply Disjoint_result. assumption. 
    rewrite H6, H9. 
    rewrite Intersection_Complement_compat. 
    rewrite Complement_Complement_compat.
    rewrite U_I_dist_l. 
    rewrite Intersection_trans. 
    rewrite (Intersection_sym (M ∪ √Plus Z) _).
    rewrite <- Intersection_trans. 
    rewrite (I_U_dist_l (M ∪ Plus S)). 
    rewrite <- H2.
    assert ((Minus Z) ⊆ Union (MinusPlus S) (Plus S)).
      assert ((Union (MinusPlus S) (Plus S)) == (Union (Minus S) (Plus S))).
        unfold MinusPlus. rewrite U_I_dist_r. rewrite Full_set_property. rewrite Full_set_ident_right...
        apply all_decidable.
      rewrite H10. rewrite HeqS. rewrite Minus_Union_compat. left; right...
    assert ((MinusPlus S ∪ Plus S) ⊆ (Union M (Plus S))). 
      unfold MinusPlus. rewrite H3. apply Union_Included_compat. 
      apply Intersection_Included_compat. apply Union_Included_cancel_left. 
      reflexivity. reflexivity. reflexivity.
    assert (Minus Z ⊆ M ∪ Plus S). 
      eapply Included_trans. apply H10... assumption.
    assert (((M ∪ Plus S) ∩ Minus Z) == (Minus Z)).
      unfold Same_set; unfold Included... rewrite H13.
    assert ((M ∪ √Plus Z) == (√Plus Z)).
      apply Union_Included_left.
      rewrite H3. apply Intersection_Included_cancel_left.
      apply Complement_Included_flip. rewrite HeqS. 
      rewrite Plus_Union_compat. apply (Included_trans _ (Plus T ∪ Plus Z) _).
      unfold Included; intros; right... apply Complement_closure.
    rewrite H14...
    apply all_decidable.
    apply all_decidable.
  Qed.

End PreParityTheory.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Parity Complex Definitions                           *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Module Type ParityComplex.
 
  Declare Module C : PreParity.
  Import C.
  Module PPT := PreParityTheory C.
  Import PPT.

  Axiom axiom1 :
    forall (x : carrier), 
      Union (Plus (plus x)) (Minus (minus x)) == Union (Plus (minus x)) (Minus (plus x)).

  Axiom axiom2 :
    forall x, 
      well_formed (plus x) /\ well_formed (minus x).

  Axiom axiom3a:
    forall x y : carrier, 
      triangle x y -> triangle y x -> x = y.

  Axiom axiom3b:
    forall x y z : carrier, 
    triangle x y ->
    (~ (In (plus z) x /\ In (minus z) y) /\ ~ (In (plus z) y /\ In (minus z) x)).
  (* This last condition somewhat awkwardly phrased, this might become tricky later *)

End ParityComplex.

Module ParityComplexTheory (M : ParityComplex).

  Import M.
  Import C.
  Import PPT. 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Basic results direct from definitions                *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
 
  (* empty *)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Section 1                                            *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma Prop_1_1 : 
    forall x, 
    (Plus (plus x)) ∩ (Minus (minus x)) == (Empty_set) == (Plus (minus x)) ∩ (Minus (plus x))
    /\
    (MinusPlus (minus x)) == Intersection (Minus (minus x)) (Minus (plus x)) == (MinusPlus (plus x))
    /\
    (PlusMinus (minus x)) == Intersection (Plus (minus x)) (Plus (plus x))   == (PlusMinus (plus x)).
  Proof with repeat basic; auto.
    remember axiom3b as axiom3b. clear Heqaxiom3b.
    assert (H: forall x y, (In (Plus (plus x)) y /\ In (Minus (minus x)) y) -> False).
      intros... rename y into u.
      unfold Plus, In in H0.  
      unfold Minus, In in H1...
      rename x0 into v. rename x1 into w. 
      assert (less w v).
        unfold less. eapply Inhabited_intro... apply H3... apply H2... 
      assert (triangle w v). 
        eapply (Relation_Operators.rt1n_trans).
        apply H. left... 
      eapply axiom3b in H4... unfold not in H5. apply H5... 
      apply H0.
      apply H1. 

    assert (K: forall x y, (In (Minus (plus x)) y /\ In (Plus (minus x)) y) -> False).
      intros... rename y into u.
      unfold Plus in H2. unfold In in H2. 
      unfold Minus in H1. unfold In in H1...
      rename x0 into v. rename x1 into w. 
      assert (less v w).
        unfold less. eapply Inhabited_intro... apply H3... apply H4... 
      assert (triangle v w). 
        eapply (Relation_Operators.rt1n_trans).
        apply H0. left... 
      eapply axiom3b in H5... unfold not in H7. apply H7... 
      apply H1.
      apply H2. 

    intros; split; split.
    apply Disjoint_intersection_condition.
    constructor. unfold not. intros... apply (H x x0)...
    symmetry.
    apply Disjoint_intersection_condition.
    constructor. unfold not. intros... apply (K x x0)...
 
    split; unfold MinusPlus, Same_set, Included... rename x0 into y.
    assert (In (Union (Plus (minus x)) (Minus (plus x))) y).
      rewrite <- (axiom1 x)... apply In_Union in H0... inversion H0... 
    apply In_Complement... apply (K x x0)...

    unfold Same_set, Included...
    apply In_Complement... apply (H x x0)...
    pose (axiom1 x).
    assert (In (Plus (plus x) ∪ Minus (minus x)) x0).
    symmetry in s.
    rewrite <- s... apply In_Union in H0... inversion H0... 

    split; unfold PlusMinus, Same_set, Included...
    pose (axiom1 x).
    assert (In (Plus (plus x) ∪ Minus (minus x)) x0).
    symmetry in s.
    rewrite <- s... apply In_Union in H0... inversion H0...
    apply In_Complement... apply (H x x0)...
    
    unfold Same_set; unfold Included...
    apply In_Complement... apply (K x x0)...
    assert (In (Union (Plus (minus x)) (Minus (plus x))) x0).
    rewrite <- (axiom1 x)... apply In_Union in H0... inversion H0... 
  Qed.

  Lemma Prop_1_2 :
    forall u v x,
    triangle u v ->
    In (plus x) v ->
    (minus u) ∩ (Plus (minus x)) == Empty_set.
  Proof with repeat basic; auto.
    intros.
    unfold Same_set; unfold Included... 
    unfold Plus in H3. unfold In in H3... rename x1 into w. 
    assert (less w u). unfold less. apply (Inhabited_intro _ _ x0)... 
    assert (triangle w v). unfold triangle. 
    eapply Relation_Operators.rt1n_trans. apply H1. apply H. eapply axiom3b in H5... 
    unfold not in H7. exfalso. apply H7... apply H0. apply H3. inversion H1. inversion H1.
  Qed.

  Lemma Prop_1_3 : 
    forall R S', 
      tight R -> well_formed S' -> R ⊆ S' -> is_a_segment R S'.
  Proof with repeat basic; auto.
    unfold is_a_segment.
    unfold tight.
    unfold well_formed.
    unfold triangle. intros... 
    assert (exists m, (dim x = S m)) as K.
      inversion H4... apply plus_dim in H8. exists (dim x0). auto.  
    rename x into w. rename y into u. rename z into v.
    assert (dim w = dim u) as J. apply equal_dim. unfold triangle. eapply Relation_Operators.rt1n_trans. 
      apply H4. left. 
    inversion H4 as [y]...
    assert (minus u ∩ PlusMinus R == Empty_set) as L.
      apply (H u v). eapply rest_implies_full. apply H7.
      assumption.  
    assert (~(In (PlusMinus R) y)) as M.
      unfold not; intros... assert (In (Empty_set) y). 
      rewrite <- L... inversion H11. unfold not in M.
    assert (In (Plus R) y) as N.
      unfold Plus. unfold In. exists w...
    assert (In (Minus R) y) as P. 
      assert (y ∈ Minus R \/ ~(y ∈ Minus R)). apply all_decidable...
      inversion H0. assumption. exfalso. apply M.
      unfold PlusMinus...
    inversion P as [z]...
    assert (u = z).
      eapply H3...   
      assert (forall T u' v', In T v' -> triangle_rest T u' v' -> In T u') as Q.
        unfold triangle_rest.
        unfold restrict.
        intros...
        induction H13. 
          assumption.
          apply H13.
      apply (Q _ u v)...
      rewrite <- J. apply H8. 
      apply minus_dim in H12. rewrite <- H12. rewrite <- H8.
      apply plus_dim in H9...
      unfold perp in H0...
      apply Disjoint_intersection_condition in H14. 
      inversion H14. apply (H0 y)...
      rewrite H0...
  Qed.

  Lemma xplus_is_tight :
    forall x, tight (plus x).
  Proof with repeat basic; auto.
    unfold tight; intros.
    assert (Intersection (minus u) (Plus (minus x)) == Empty_set). 
      apply (Prop_1_2 u v)...
    assert (Plus (minus x) ∩ Plus (plus x) == PlusMinus (plus x)). 
      eapply Prop_1_1. 
    rewrite <- H2. 
    rewrite <- Intersection_trans. 
    rewrite H1.
    unfold Same_set, Included; split; intros... inversion H3. 
  Qed.

  (* Section 2 ?*)
  
  Lemma Observation_p322 :
    forall (T Z : Ensemble carrier),
    well_formed (Union T Z) ->
    Disjoint T Z ->
    Perp T Z. 
  Proof with repeat basic; auto.
    intros T Z WF Disj. remember (Union T Z) as S'.
    unfold well_formed in WF... 
    rename H into WF0.
    rename H0 into WFSn. 
    rename H1 into Disj.
    unfold Perp...

    apply Disjoint_intersection_condition. constructor. unfold not in *. 
    intros... rename H0 into PT. rename H1 into PZ.
    unfold Plus in PT. unfold In in PT.
    unfold Plus in PZ. unfold In in PZ...
    assert (dim x0 = S (dim x)). symmetry. apply plus_dim. unfold In...
    assert (dim x1 = S (dim x)). symmetry. apply plus_dim. unfold In...
    assert (x0 = x1). 
    eapply WFSn. split; rewrite HeqS'. right... left... 
    apply H. assumption. 
    unfold perp. intros...
    apply Disjoint_intersection_condition in H6. 
    inversion H6 as [J]; clear H6; unfold not in J; apply (J x)...
    subst.
    apply (Disj x1)...
 
    apply Disjoint_intersection_condition. constructor. unfold not in *. 
    intros... rename H0 into PT. rename H1 into PZ.
    unfold Minus in PT. unfold In in PT.
    unfold Minus in PZ. unfold In in PZ...
    assert (dim x0 = S (dim x)). symmetry. apply minus_dim. unfold In...
    assert (dim x1 = S (dim x)). symmetry. apply minus_dim. unfold In...
    assert (x0 = x1). 
    eapply WFSn. split; rewrite HeqS'. right... left... 
    apply H. assumption. 
    unfold perp. intros...
    apply Disjoint_intersection_condition in H7. 
    inversion H7 as [J]; clear H6; unfold not in J; apply (J x)...
    subst.
    apply (Disj x1)...
  Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Cells                                                *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Definition Same_pair (A B: Ensemble carrier * Ensemble carrier) : Prop.
  inversion A as [M  P ].
  inversion B as [M' P'].
  exact (M == M' /\ P == P').
  Defined.

  Hint Unfold Same_pair.

  Notation " F === G" := (Same_pair F G) (at level 89).

  Definition is_a_cell (G : Ensemble carrier * Ensemble carrier) : Prop.
  inversion G as [M P]. 
  exact ( Inhabited M  /\ Inhabited P /\
    well_formed M /\ well_formed P /\
    Finite M /\ Finite P /\
    (M moves M to P) /\ (P moves M to P)).
  Defined.

  Definition celldim (G : Ensemble carrier * Ensemble carrier) (n : nat) : Prop.
    inversion G as [M P]. 
    exact (setdim (Union M P) n).
  Defined.

  Definition source (n : nat) (G : Ensemble carrier * Ensemble carrier) : Ensemble carrier * Ensemble carrier.
    inversion G as [M P]. exact ( sup M n , sub M n ∪ sup P (n-1)).
  Defined.

  Definition target (n : nat) (G : Ensemble carrier * Ensemble carrier) : Ensemble carrier * Ensemble carrier.
    inversion G as [M P]. exact ( sub P n ∪ sup M (n-1) , sup P n ).
  Defined.

  Definition composable (n : nat) (A B : Ensemble carrier * Ensemble carrier) : Prop :=
    target n A === source n B. 

  Definition composite (n : nat) (A B : Ensemble carrier * Ensemble carrier) : Ensemble carrier * Ensemble carrier.
   inversion A as [M P].
   inversion B as [N Q].
   exact ((M ∪ (N ∩ √(sub N n))), ((P ∩ √(sub P n)) ∪ Q)).
  Defined.

  Definition receptive (S : Ensemble carrier) : Prop :=
    (forall x, (Plus (minus x)) ∩ (Plus (plus x)) ⊆ S ->
       (Inhabited (S ∩ (Minus (minus x))) -> False) ->
       (Inhabited (S ∩ (Minus (plus x))) -> False))  /\ 
    (forall x, (Minus (plus x)) ∩ (Minus (minus x)) ⊆ S ->
       (Inhabited (S ∩ (Plus (plus x))) -> False) ->
       (Inhabited (S ∩ (Plus (minus x))) -> False)).

  Definition cell_receptive (G : Ensemble carrier * Ensemble carrier) : Prop.
    inversion G as [M P].
    exact (receptive M /\ receptive P).
  Qed.

  Hint Unfold is_a_cell.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Basic results direct from definitions                *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma cell_has_dim : forall M P, is_a_cell (M, P) -> exists m, celldim (M, P) m.
  Proof with repeat basic; auto.
    intros.
    unfold is_a_cell in H...
    assert (Finite (Union M P)). 
    apply Finite_Union.
    apply all_decidable. 
    assumption.
    assumption. 
    apply Finite_carrier_have_max_dim_element in H6.
    inversion H6 as [m]; clear H6... 
    exists (dim m).
    unfold celldim. 
    unfold setdim.
    intros...
    inversion H8; apply H9...
    inversion H0. 
    apply (Inhabited_intro _ _ x). 
    left...
  Qed.

  Lemma source_is_a_cell : forall (n : nat) (M P : Ensemble carrier), 
    is_a_cell (M, P) -> celldim (M, P) (S n) -> is_a_cell (source (S n) (M, P)).
  Proof with intuition.
    intros n M P MPcell MPdim.
    unfold source.
    assert (S n - 1 = n) as JK. admit. rewrite JK; clear JK.
    unfold is_a_cell in *...

    unfold celldim, setdim in MPdim.
    inversion H as [j]; exists j.
    repeat subsuptac...

    unfold celldim, setdim in MPdim.
    unfold moves_def in *...
    inversion H1 as [j]; exists j.
    assert (In ((M ∪ Plus M) ∩ √Minus M) j). rewrite <- H6...
    basic. inversion H10; clear H10. 
    assert (dim j <= S n). apply MPdim... 
    inversion H10; clear H10. 
    inversion H11; clear H11.
    left... unfold Plus in H10. unfold In at 1 in H10.
    inversion H10 as [d G]; clear H10...
    apply plus_dim in H11.
    assert (dim d <= S n). apply MPdim...
    rewrite H14 in H11. rewrite <- H11 in H15. apply le_Sn_n in H15... 
    right...

    unfold well_formed in *...
      apply H6... 
      repeat subsuptac...
      repeat subsuptac...
      eapply H8... 
      repeat subsuptac...
      repeat subsuptac...
      apply H2... assumption.

    unfold well_formed in *...
      inversion H12; clear H12... 
      inversion H13; clear H13; subst...
      apply H6... 
      repeat subsuptac...
      repeat subsuptac...
      repeat subsuptac... rewrite H10 in H14; inversion H14.
      inversion H13; clear H13; subst...
      repeat subsuptac... rewrite H11 in H15; inversion H15.
      apply H0... 
      repeat subsuptac...
      repeat subsuptac...
      inversion H10; clear H10... 
      inversion H11; clear H11; subst...
      eapply H8... 
      repeat subsuptac...
      repeat subsuptac...
      apply H2. assumption.
      repeat subsuptac...
      rewrite H2 in H15; inversion H15; subst.
      rewrite H12 in H16. apply le_Sn_n in H16...
      inversion H11; clear H11; subst...
      repeat subsuptac...
      rewrite H12 in H16; inversion H16; subst.
      rewrite H2  in H15. apply le_Sn_n in H15...
      eapply H9...
      repeat subsuptac...
      repeat subsuptac...
      apply H2. assumption.

    (**) eapply Finite_Included. apply all_decidable. apply H3. 
      apply sup_Included.
    (**) apply Finite_Union... apply all_decidable...  
      eapply Finite_Included. apply all_decidable. apply H4. apply sup_Included.
      eapply Finite_Included. apply all_decidable. apply H3. apply sub_Included.  

    (**)
    assert (forall S M P, S moves M to P <-> S moves M to ((Intersection (Union (M) (Plus S)) (Complement (Minus S))))) as big_help.
      admit. 
    assert (M moves M to (Intersection (Union (M) (Plus M)) (Complement (Minus M)))).
      unfold moves_def in *... rewrite <- H6...
    apply Prop_2_1' in H6...
    apply big_help.
    apply Prop_2_1'...
    unfold MinusPlus, sup, Minus, Plus, Included, In; intros.
    inversion H6; clear H6. subst.
    unfold In in H10, H11.
    inversion H10 as [z K]; clear H10...
    assert (not ((Plus M) x)) as II.
    unfold Plus, not...
    unfold Complement in H11. apply H11.
    unfold In. inversion H6 as [w]. exists w...
    apply H8. unfold MinusPlus... split... exists z... 
    (* true because of minus_dim *) admit.
    
    apply Disjoint_intersection_condition.
    apply (Included_Empty_set _ (M ∩ Plus M)). 
    apply Intersection_Included_compat. 
      unfold sup, Included, In...
      unfold Plus, sup, Included, In... inversion H6 as [z F]. exists z...
    apply Disjoint_intersection_condition...

    (**)
    assert (forall S M P, S moves M to P <-> S moves M to ((Intersection (Union (M) (Plus S)) (Complement (Minus S))))) as big_help.
      admit. 
    assert (P moves M to (Intersection (Union (M) (Plus P)) (Complement (Minus P)))).
      unfold moves_def in *... rewrite <- H5...
    assert (M moves M to (Intersection (Union (M) (Plus M)) (Complement (Minus M)))).
      unfold moves_def in *... rewrite <- H8...
    apply Prop_2_1' in H6...
    apply Prop_2_1' in H8...
    apply big_help.
    apply Prop_2_1'...
    unfold MinusPlus.
    rewrite Plus_Union_compat, Minus_Union_compat.
    rewrite <- Union_Complement_compat.
    unfold sup, sub, Minus, Plus, Complement, Included, In; intros.
    inversion H8; clear H8; subst.
    inversion H13; clear H13; subst. 
    unfold In in *.
    inversion H12; clear H12. subst.
    unfold In in H13. inversion H13 as [r T]; clear H13... 
    apply H6. unfold MinusPlus. split. exists r...
    unfold Complement, In, not...
    apply H8. exists r...
    admit. (* problems here, not sorted out yet *)
    apply minus_dim in H13. (* true *) admit. 
    subst.
    unfold In in H13. inversion H13 as [r T]; clear H13... 
    apply H9. unfold MinusPlus. split. exists r...
    unfold Complement, In, not...
    apply H14. exists r...
    admit. (* problems here, not sorted out yet *)
    apply minus_dim in H13. (* true *) admit. 
    
    apply Disjoint_intersection_condition.
    rewrite Plus_Union_compat.
    rewrite I_U_dist_l.  
    apply (Included_Empty_set _ (Union Empty_set Empty_set)).
    apply Union_Included_compat.
    apply (Included_Empty_set _ (M ∩ Plus M)).
    apply Intersection_Included_compat.
      unfold sup, Included, In...
      unfold Plus, sub, Included, In... inversion H8 as [z F]. exists z...
    apply Disjoint_intersection_condition...
    apply (Included_Empty_set _ (M ∩ Plus P)).
    apply Intersection_Included_compat.
      unfold sup, Included, In...
      unfold Plus, sup, Included, In... inversion H8 as [z F]. exists z...
    apply Disjoint_intersection_condition...
    rewrite Empty_set_ident_left...

Qed.

  Lemma target_is_a_cell : forall (n : nat) (M P : Ensemble carrier), 
    is_a_cell (M, P) -> is_a_cell (target n (M, P)).
  Admitted.


(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Section 3                                            *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma Prop_3_1 :
    forall x M P, 
      (plus x) moves M to P ->
      receptive M ->
      (minus x) moves M to P.
  Proof with repeat basic; auto.
    intros. assert (exists P', plus x moves M to P'). exists P... 
    apply Prop_2_1 in H1...
    assert (MinusPlus (minus x) == MinusPlus (plus x)).
      remember (Prop_1_1 x) as prop_1_1. clear Heqprop_1_1...
      eapply Same_set_trans. apply H6... assumption.
    assert (MinusPlus (minus x) ⊆ M). unfold Included...
      unfold Included in H2. apply H2. rewrite <- H3... clear H3.
    assert (Disjoint M (Plus(minus x))).
      unfold receptive in H0... apply (H5 x). 
      Focus 3. eapply (Inhabited_intro)... apply H6. assumption.
      Focus 2. intros... inversion H0; clear H0... 
       unfold moves_def in H... rewrite H10 in H0...
      unfold moves_def in H... unfold Included...
        assert ((In (Plus (plus x)) x1) \/ ~(In (Plus (plus x)) x1)). apply all_decidable.
        inversion H. pose (Prop_1_1 x)... assert (In (Empty_set) x1). rewrite <- H14...
        inversion H12. symmetry in H8. rewrite <- H8...
    assert (exists Y, minus x moves M to Y). apply Prop_2_1. 
    constructor; assumption. inversion H5 as [P']. clear H5.
    assert (P == P'). unfold moves_def in H6. inversion H6. clear H6. rewrite H5. 
      symmetry. rewrite I_U_dist_r. remember (Prop_1_1 x). clear Heqa... 
      unfold PlusMinus in H8. rewrite H8. inversion H; clear H. rewrite H3.
      rewrite I_U_dist_r.
      assert ((Plus (plus x) ∩ √Minus (plus x)) == (Plus (minus x) ∩ Plus (plus x))).        
        unfold Same_set; unfold Included...
        assert (x0 ∈ (Plus (plus x) ∪ Minus (minus x))). left. assumption. 
        rewrite (axiom1 x) in H... inversion H...
        apply In_Complement... assert (In (Plus (minus x) ∩ Plus (plus x)) x0).
        do 2 basic. assumption. assumption. rewrite H11 in H17.
        unfold PlusMinus in H17...
      assert ((M ∩ √Minus (plus x)) == (M ∩ √Minus (plus x) ∩ √Plus (minus x))). 
        unfold Same_set; unfold Included... apply In_Complement... unfold not in H6. 
        apply (H6 x0)...
      assert ((M ∩ √Minus (minus x)) == (M ∩ √Minus (minus x) ∩ √Plus (plus x))). 
        unfold Same_set; unfold Included... apply In_Complement... 
        rewrite H14 in H17...
      rewrite H15. rewrite H16. 
      rewrite H.
      repeat rewrite (Intersection_trans M _ _). repeat rewrite Union_Complement_compat.
      rewrite (Union_sym (Minus (minus x)) _). rewrite (axiom1 x).
      rewrite (Union_sym _ (Minus (plus x))).
      reflexivity.        
      
    unfold moves_def. unfold moves_def in H6. rewrite <- H5 in H6. 
    assumption. 
  Qed.

  Definition is_a_cell' (S T : Ensemble carrier) := is_a_cell (S, T). 

  Hint Unfold is_a_cell'.

  Add Parametric Morphism : (well_formed) with
    signature (@Same_set carrier) ==> (iff) as well_formed_Same_set.
  Proof with intuition.
    autounfold with *...
    eapply H3...
    apply H... assumption.
    eapply H3...
    apply H... assumption.
  Qed.

  Add Parametric Morphism : (is_a_cell') with 
    signature (@Same_set carrier) ==> (@Same_set carrier) ==> (iff) as is_a_cell_Same_set.
  Proof with intuition.
    intuition. 
    symmetry in H.
    symmetry in H0.
    unfold is_a_cell', is_a_cell, moves_def in *...
    rewrite H...
    rewrite H0...
    rewrite H... 
    rewrite H0...
    apply (Same_set_is_finite _ H5 _ H). 
    apply (Same_set_is_finite _ H6 _ H0).
    rewrite H, H0...
    rewrite H, H0...
    rewrite H, H0...
    rewrite H, H0...

    unfold is_a_cell', is_a_cell, moves_def in *...
    rewrite H...
    rewrite H0...
    rewrite H... 
    rewrite H0...
    apply (Same_set_is_finite _ H5 _ H). 
    apply (Same_set_is_finite _ H6 _ H0).
    rewrite H, H0...
    rewrite H, H0...
    rewrite H, H0...
    rewrite H, H0...
  Qed.

  Lemma is_a_cell_Same_set_compat : forall (S S': Ensemble carrier), 
    S == S' -> forall T T', T == T' -> (is_a_cell (S, T) <-> is_a_cell (S', T')).
  Proof.
    intros.
    fold (is_a_cell' S T).
    fold (is_a_cell' S' T').
    rewrite H, H0.
    intuition. 
  Qed.

  Lemma dim_1_properties : forall x, dim x = 1 -> 
    ( Plus  (minus x) == Empty_set /\
      Plus  (plus  x) == Empty_set /\
      Minus (minus x) == Empty_set /\
      Minus (plus  x) == Empty_set ). 
  Proof with intuition.
    intros x H... 
    crush... inversion H0 as [j]...
    assert (dim j = 0). apply minus_dim in H2. rewrite H in H2. auto. 
    assert (plus j == Empty_set). apply zero_faces. assumption. fold (In (plus j) x0) in H3. rewrite H4 in H3; unfold In in H3...
    crush... inversion H0 as [j]...
    assert (dim j = 0). apply plus_dim in H2. rewrite H in H2. auto. 
    assert (plus j == Empty_set). apply zero_faces. assumption. fold (In (plus j) x0) in H3. rewrite H4 in H3; unfold In in H3...
    crush... inversion H0 as [j]...
    assert (dim j = 0). apply minus_dim in H2. rewrite H in H2. auto. 
    assert (minus j == Empty_set). apply zero_faces. assumption. fold (In (minus j) x0) in H3. rewrite H4 in H3; unfold In in H3...
    crush... inversion H0 as [j]...
    assert (dim j = 0). apply plus_dim in H2. rewrite H in H2. auto. 
    assert (minus j == Empty_set). apply zero_faces. assumption. fold (In (minus j) x0) in H3. rewrite H4 in H3; unfold In in H3...
  Qed.

  Lemma Prop_3_3 : (forall M P : Ensemble carrier, is_a_cell (M, P) -> cell_receptive (M, P)).
  Admitted.  

  (* This is not trivial, needs to be finished, need help with this *)
  Lemma maximal_exists :
    forall n X, Included X (sub Full_set n) -> Finite X -> Inhabited X
      -> exists x, In X x /\ (forall y, In X y -> (triangle x y -> x = y)).
  Proof with intuition.
    intros. 
    induction H0.
      (* X empty *)
      apply Inhabited_not_empty in H1. exfalso; apply H1. trivial. 

      (* X Add *)
      apply Finite_Empty_or_Inhabited in H0.
      inversion H0; clear H0.
        (* A Empty *)
        exists x...
        unfold Add in H0. apply In_Union in H0. inversion H0; clear H0. 
        rewrite H3 in H5. inversion H5.
        inversion H5. trivial.
        (* A Inhabited *)
        assert (∃ x : carrier, x ∈ A ∧ (∀ y : carrier, y ∈ A → triangle x y → x = y)) as Q.
          apply IHFinite.
          apply (Included_trans _ (Add A x) _)...
          assumption.
        clear IHFinite.
        inversion Q as [z]; clear Q...
        assert (triangle z x \/ ~(triangle z x)) as choice. admit.
        inversion choice; clear choice. 
          exists x. admit.
          exists z...
            unfold Add in H6. apply In_Union in H6. inversion H6; clear H6. apply H5...
            inversion H8; clear H8. rewrite H6 in *. clear H6. exfalso. apply H0...
      (* X Same_set *)
      symmetry in H2.
      assert (∃ x : carrier, x ∈ T ∧ (∀ y : carrier, y ∈ T → triangle x y → x = y)). 
        apply IHFinite; clear IHFinite.
        rewrite H2...
        rewrite H2...
      inversion H3 as [z].
      exists z...
      rewrite <- H2...
      apply (H6 y)...
      symmetry in H2.
      rewrite <- H2...
  Qed.

  Lemma less_decidable : forall x y, ((less x y) \/ ~(less x y)).
  Proof with intuition.
    intros.
    assert (Finite (Intersection (plus x) (minus y))).
    apply Finite_Intersection. apply minus_fin.
    apply all_decidable.
    apply Finite_Empty_or_Inhabited in H.
    inversion H; [right | left].
    unfold not; intros. unfold less in H1.
    rewrite H0 in H1.
    inversion H1. inversion H2.
    unfold less...
  Qed.

  Lemma maximal_property :
    forall n X, Included X (sub Full_set n) -> Finite X -> Inhabited X
      -> exists x, In X x /\ Disjoint (plus x) (Minus X).
  Proof with intuition.
  Admitted. (*
    intros n X hyp1 hyp2 hyp3.
    induction hyp2.
      (* X Empty *)
      inversion hyp3 as [x J]. inversion J. 
      (* X Add *)
      assert (A == Empty_set \/ Inhabited A). apply Finite_Empty_or_Inhabited.
      apply hyp2. inversion H0; clear H0.
       exists x...
          apply Disjoint_intersection_condition. unfold Add.
              rewrite Minus_Union_compat.
              rewrite Minus_Singleton. rewrite H1.
              assert (Minus Empty_set == Empty_set). unfold Same_set, Included, Minus, In...
              inversion H0; clear H0...
              rewrite H0. rewrite Empty_set_ident_left...
          apply Disjoint_intersection_condition.
          apply plus_minus_disjoint. 
      assert (exists x, In A x /\ (forall y, In A y -> (triangle x y -> x = y))) as hyp4.
      apply (maximal_exists n).
      apply (Included_trans _ (Add A x))...
      assumption. assumption. 
      inversion hyp4 as [x']; clear hyp4...
      assert (triangle x' x \/ ~(triangle x' x)) as choice. admit.
      inversion choice; clear choice.
        exists x...
          constructor...
          basic. basic. unfold Add in H6. 
          rewrite (Minus_Union_compat _ _) in H6.
          basic.
          inversion H6; clear H6.
            unfold Minus in H4. unfold In at 1 in H4. 
            inversion H4 as [a]; clear H4. apply (H3 a)...
            assert (triangle x a). admit.  
            admit.
            rewrite (Minus_Singleton _) in H4. admit.          
        exists x'...
          apply Disjoint_intersection_condition. unfold Add.
              rewrite Minus_Union_compat.
              rewrite Minus_Singleton.
          apply Disjoint_intersection_condition. 
          constructor...
          basic. basic. basic.
          inversion H6; clear H6.
          unfold In, Minus in H4.
          inversion H4 as [z]; clear H4.
            apply (H3 z)...
            eapply Relation_Operators.rt1n_trans.
              unfold less. exists x0. basic... apply H7.
              apply Relation_Operators.rt1n_refl.
            apply H0...
            eapply Relation_Operators.rt1n_trans.
              unfold less. exists x0. basic... apply H4.
              apply Relation_Operators.rt1n_refl.
      (* X Same_set *)
      assert (∃ x : carrier, x ∈ T ∧ Disjoint (plus x) (Minus T)) as K.
      apply IHhyp2.
        rewrite <- H...
        rewrite <- H...
      inversion K as [x Kx]... exists x...
      symmetry in H. rewrite H...
      rewrite <- H in H1... *)
  
  Lemma cell_dim_n_property : 
    forall M P, is_a_cell (M, P) -> forall n, celldim (M, P) n -> sub M n == sub P n.
  Proof with intuition.
    intros M P K n J.
    unfold is_a_cell in K... unfold moves_def in *...
    unfold sub, Same_set, Included, In...

    fold (In P x). rewrite H6.
    repeat basic. left... apply In_Complement. unfold not... 
    unfold In, Minus in H7. inversion H7; clear H7... apply minus_dim in H13.
    assert (dim x0 <= n). unfold celldim, setdim in *. apply J...
    rewrite <- H13 in H12. rewrite H11 in H12. apply (le_Sn_n n)...

    fold (In M x). rewrite H9.
    repeat basic. left... apply In_Complement. unfold not... 
    unfold In, Plus in H7. inversion H7; clear H7... apply plus_dim in H13.
    assert (dim x0 <= n). unfold celldim, setdim in *. apply J...
    rewrite <- H13 in H12. rewrite H11 in H12. apply (le_Sn_n n)...
  Qed.     

  Definition Lemma_3_2_b_st : nat -> nat -> Prop := 
    (fun n => (fun m => 
    forall (X : Ensemble carrier), 
    cardinal X m ->
    (forall M P, (is_a_cell (M, P) /\ celldim (M, P) n) ->
    ((X ⊆ (sub (Full_set) (S n))) /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n))) ->
    is_a_cell ( (sup M (n - 1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)), (sup P (n - 1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)) )
    /\ (Minus X ∩ (sub M n)) == Empty_set))).

  Definition Lemma_3_2_c_st : nat -> nat -> Prop := 
    (fun n => (fun m => 
    forall (X : Ensemble carrier), 
    cardinal X m ->
    (forall M P, (is_a_cell (M, P) /\ celldim (M, P) n) ->
    ((X ⊆ (sub (Full_set) (S n))) /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n))) ->
    is_a_cell ( (sup M (n - 1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)) ∪ X, (sup P (n - 1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)) ∪ X)
    ))).

  Lemma Lemma_3_2_b_n_0 : forall n, Lemma_3_2_b_st n 0.
  Proof with intuition.
    intros n.
    unfold Lemma_3_2_b_st.
    intros X Xcard. 
    assert (X == Empty_set) as XEmpty. 
      apply cardinality_zero_Empty_set; assumption.
    assert (Finite X) as XFinite.
      apply (cardinal_are_Finite 0)...
    intros M P H. 
    inversion H as [MPcell MPdim]; clear H. 
    intros H.
    inversion H as [Xdim K]; clear H. 
    inversion K as [Xwf Xcond]; clear K. 
    split. 

    (* is_a_cell *)
    assert (Minus X == Empty_set) as MXE. 
      rewrite XEmpty.
      unfold Minus, Same_set, Included, In... inversion H...
    assert (Plus X == Empty_set) as PXE. 
      rewrite XEmpty.
      unfold Plus, Same_set, Included, In... inversion H...
    assert (sup M (n - 1) ∪ ((sub M (n) ∪ Minus X) ∩ √Plus X) == M) as MM. 
      rewrite MXE, PXE. 
      rewrite Complement_Empty_set. 
      rewrite Empty_set_ident_right. 
      rewrite Full_set_ident_right.
      unfold sup, sub, Same_set, Included, In...
        inversion H. crush. crush.
        assert (dim x <= (n)).
          unfold celldim in *...
        inversion H0; [right | left]... admit.
    assert (sup P (n - 1) ∪ ((sub M (n) ∪ Minus X) ∩ √Plus X) == P) as PP.
      rewrite MXE, PXE. 
      rewrite Complement_Empty_set. 
      rewrite Empty_set_ident_right. 
      rewrite Full_set_ident_right.
      rewrite (cell_dim_n_property M P).
      unfold sup, sub, Same_set, Included, In...
        inversion H. crush. crush.
        assert (dim x <= (n)).
          unfold celldim in *...
        inversion H0; [right | left]... admit.
    assumption. 
    assumption. 
    eapply (is_a_cell_Same_set_compat). 
    apply MM. apply PP. apply MPcell.

    (* Disjoint *)
    apply Disjoint_intersection_condition.
    constructor. 
    unfold not; intros. 
    basic...
    unfold In, Minus in H0...
    inversion H0 as [z J]...
    assert (In Empty_set z). rewrite <- XEmpty... 
    inversion H3.
  Qed.

  Lemma Lemma_3_2_b_0_1 : Lemma_3_2_b_st 0 1.
  Proof with intuition.
    unfold Lemma_3_2_b_st.
    intros X Xcard M P J K.
    inversion J as [MPcell MPdim]; clear J.
    inversion K as [Xdim L]; clear K.
    inversion L as [Xwf Xcond]; clear L.
    apply cardinality_one_Singleton in Xcard. 
    inversion Xcard as [x Xsing]; clear Xcard.
    set (Y := ((sub M 0 ∪ Minus X) ∩ √Plus X)).
    
    assert (dim x = 1) as dimx. 
      rewrite Xsing in Xdim.
      autounfold with * in Xdim... apply Xdim... 
    assert (sub M 0 == plus x) as subM0. 
      admit. (* by well_formed M *)
    assert (Y == minus x) as Ydef. 
      unfold Y. 
      rewrite Xsing, subM0, Plus_Singleton, Minus_Singleton.
      rewrite I_U_dist_r.
      rewrite Empty_set_property.
      rewrite Empty_set_ident_left.
      apply Intersection_Included_left.
      apply Disjoint_property_right.
      apply plus_minus_disjoint.
    assert (sup M (0 - 1) == Empty_set) as supM0. admit. (* this is really a coding issue *)
    assert (sup P (0 - 1) == Empty_set) as supP0. admit. (* this is really a coding issue *)
    assert (sup M (0 - 1) ∪ Y == minus x) as HypA.
      unfold is_a_cell in MPcell...
      rewrite supM0, Ydef. 
      rewrite Empty_set_ident_left.
      reflexivity.
    assert (sup P (0 - 1) ∪ Y == minus x) as HypB.
      unfold is_a_cell in MPcell...
      rewrite supP0, Ydef. 
      rewrite Empty_set_ident_left.
      reflexivity.

    split.

    eapply is_a_cell_Same_set_compat.
    apply HypA. 
    apply HypB.      
    unfold is_a_cell... 
        apply minus_non_empty. rewrite dimx. auto.
        apply minus_non_empty. rewrite dimx. auto. 
        apply axiom2. 
        apply axiom2. 
        apply minus_fin. 
        apply minus_fin. 
        apply dim_1_properties in dimx...
        unfold moves_def; split; rewrite H, H0;
          rewrite Empty_set_ident_right; rewrite Complement_Empty_set;
          rewrite Full_set_ident_right; reflexivity.
        apply dim_1_properties in dimx...
        unfold moves_def; split; rewrite H, H0;
          rewrite Empty_set_ident_right; rewrite Complement_Empty_set;
          rewrite Full_set_ident_right; reflexivity.

      rewrite Xsing, Minus_Singleton, subM0.
      apply Disjoint_intersection_condition.
      apply Disjoint_sym. apply plus_minus_disjoint.
  Qed.

  Lemma Lemma_3_2_Step_1' :
    forall n m, (Lemma_3_2_b_st n m) -> (Lemma_3_2_c_st n m).
  Proof with intuition.
    unfold Lemma_3_2_b_st, Lemma_3_2_c_st. 
    intros n m Hyp1 X Xcard M P J K. 
    assert (is_a_cell
               (sup M (n - 1) ∪ ((sub M n ∪ Minus X) ∩ √Plus X),
               sup P (n - 1) ∪ ((sub M n ∪ Minus X) ∩ √Plus X))
             ∧ Minus X ∩ sub M n == Empty_set) as Hyp2.
    apply Hyp1...
    intuition.
    set (Y := ((sub M n ∪ Minus X) ∩ √Plus X))...

    unfold is_a_cell in *... 

    apply (Inhabited_Included (sup M (n - 1) ∪ Y)). assumption. 
    apply Union_Included_cancel_right. reflexivity.


      (*
    apply (Inhabited_Included P). assumption. 
    apply Union_Included_cancel_right. reflexivity.
      
    (**)
    unfold well_formed in *...
    inversion H28; clear H28. inversion H29; clear H29.
      apply H8... 
      subst. apply H1 in H28. unfold sub, In at 1 in H28... 
        rewrite H30 in H27. inversion H27.
      subst. apply H1 in H11. unfold sub, In at 1 in H11... 
        rewrite H30 in H26. inversion H26.
          
subst. apply H3 in H12. unfold sub, In at 1 in H12... rewrite H31 in H27. inversion H27.
        inversion H27; clear H27. inversion H28; clear H28.
          subst. eapply H24... apply H12. assumption. 
          admit. 
        inversion H28; clear H28. 
          admit.
          subst. eapply H22... apply H12. assumption.
      
      unfold well_formed in *...
        inversion H29; clear H29. inversion H30; clear H30.
          apply H10... 
          subst. apply H3 in H29. unfold sub, In at 1 in H29... rewrite H31 in H28. inversion H28.
          subst. apply H3 in H12. unfold sub, In at 1 in H12... rewrite H31 in H27. inversion H27.
        inversion H27; clear H27. inversion H28; clear H28.
          subst. eapply H25... apply H12. assumption.
          admit. 
        inversion H28; clear H28. 
          admit.
          subst. eapply H22... apply H12. assumption. *)
      (* apply Finite_Union... apply all_decidable.
      apply Finite_Union... apply all_decidable.

 admit. 
      admit.*)
  Admitted.

  Lemma Lemma_3_2_Step_2' :
    forall n, ((Lemma_3_2_b_st n 1) -> (forall m, Lemma_3_2_b_st n (S m))).
  Proof with repeat basic; auto.
    intros n hypothesis_for_1 m.
    induction m.
      assumption. 
    unfold Lemma_3_2_b_st in *. 
    intros X Xcard M P H J.
    inversion H as [MPcell MPdim]; clear H.
    inversion J as [Xdim K]; clear J.
    inversion K as [Xwf Xcond]; clear K.

    assert (exists x, In X x /\ Disjoint (plus x) (Minus X)) as R. 
      admit. (* maximal *)
    inversion R as [x xcond]; clear R. 
    inversion xcond as [xinX disj]; clear xcond.
    assert (plus x ⊆ sub M n). 
      apply (Included_trans _ (PlusMinus X)).
        unfold PlusMinus. rewrite <- (Intersection_idemp (plus x)).
        apply Intersection_Included_compat.
          unfold Included, Plus, In... exists x...
        apply Disjoint_property_left. assumption. 
    assumption. 

    assert (is_a_cell
                 (sup M (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x)),
                 sup P (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x)))
               ∧ Minus (Singleton x) ∩ sub M n == Empty_set).
        apply hypothesis_for_1...
        apply cardinality_Singleton_is_one.
        unfold Included... inversion H1; subst... 
        apply well_formed_Singleton. 
        rewrite PlusMinus_Singleton...
    
    set (N :=  sup M (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x))).
    set (Q :=  sup P (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x))). 
    set (Z := Intersection X (Complement (Singleton x))).
    set (Y' := (sub N n ∪ (Minus Z)) ∩ √Plus Z).
    set (Y  := (sub M n ∪ (Minus X)) ∩ √Plus X).

    assert (is_a_cell ((sup N (n - 1)  ∪ Y'), (sup Q (n - 1) ∪ Y')) /\ Minus Z ∩ sub N n == Empty_set).
      eapply (IHm Z).
        (* Z is the right size *) admit. 
        split.
        apply H0.
        (* correct dimensions, already proved this somewhere *) admit.
        split.
        apply (Included_trans _ X _). unfold Z. unfold Included... assumption.
        split.
        unfold Z. apply (well_formed_Included _ X). unfold Included... assumption.

          assert (sub N n == Intersection (Union (sub M n) (minus x)) (Complement (plus x))).
            unfold N. 
            rewrite sub_Union.
            rewrite sub_Intersection. rewrite sub_Union.
            rewrite sub_sup_Empty_set. rewrite Empty_set_ident_left...
            rewrite sub_idemp.
            rewrite Minus_Singleton.
            rewrite Plus_Singleton.
            unfold Same_set, Included...
              inversion H4; clear H4... 
              right. 
              unfold sub, In at 1 in H3...
              unfold sub, In at 1 in H5...
              inversion H4; clear H4... 
              right. 
              unfold sub, In at 1... (* true *) admit.
              inversion H4; clear H4... 
              unfold sub, In at 1... (* true *) admit.
              unfold sub, In at 1... (* true *) admit.
              (* true *) admit.
          rewrite H1.
Admitted.
(*
      admit. 

(*        assert (PlusMinus Z == Intersection (Union (PlusMinus X) (minus x)) (Complement (plus x))). 
          assert (X == Union Z (Singleton x)) as XZrel. admit. 
          unfold PlusMinus. 
          rewrite XZrel.
          rewrite Plus_Union_compat. 
          rewrite Minus_Union_compat.
          rewrite Plus_Singleton. 
          rewrite Minus_Singleton. 
          rewrite <- Union_Complement_compat.
          rewrite I_U_dist_r.
          rewrite I_U_dist_r.
          rewrite I_U_dist_r.
          unfold Same_set, Included...
          left. left... Z
          left... idtac...
*)

      assert (sup N (n-1) == sup M (n-1)) as J1.
        unfold N, sup...
        crush. inversion K; clear K. crush. basic. inversion H5; clear H5...
        unfold In in H16... erewrite (Minus_Singleton x) in H16.
        apply minus_dim in H16. exfalso. 
        assert (dim x = S n). admit.
        rewrite H5 in H16. inversion H16. rewrite H18 in H15. (* again n>0 *)
        (* inversion on H15 *) admit.
        left... unfold In... 
      assert (sup Q (n-1) == sup P (n-1)) as J2.
        unfold Q, Same_set, Included, sub, sup, In...
        crush. inversion K; clear K. crush. basic. inversion H5; clear H5...
        unfold In in H16... admit. erewrite (Minus_Singleton x) in H16.
        apply minus_dim in H16. exfalso. assert (dim x = S n). admit. 
        rewrite H5 in H16. inversion H16. rewrite H18 in H15. (* again n>0 *)
        (* inversion on H15 *) admit.
        left... unfold In... 
      assert (Y == Y') as J3. 
        unfold Y, Y', N.    
        assert (X == Union (Singleton x) Z). 
          unfold Z. rewrite Union_sym. rewrite U_I_dist_r. 
          rewrite Full_set_property. rewrite Full_set_ident_right. 
          unfold Same_set, Included... inversion H5... inversion H14. rewrite <- H15...
          apply all_decidable. 
        rewrite H2.
        rewrite Minus_Union_compat.
        rewrite Plus_Union_compat.
        rewrite <- Union_Complement_compat.
        rewrite sub_Union. rewrite sub_sup_Empty_set.
        rewrite Empty_set_ident_left.
        rewrite sub_Intersection. rewrite sub_Union. rewrite sub_idemp. rewrite sub_Minus.
        rewrite <- Intersection_trans.
        rewrite <- Union_trans.
        rewrite I_U_dist_r.
        assert (sub (Singleton x) (S n) == (Singleton x)) as WW. admit.
        rewrite WW. 
          unfold Same_set, Included... 
          inversion H15; clear H15... inversion H15; clear H15... 
          left... unfold sub, In at 1...
          admit.
          left... unfold sub, In at 1... admit.
          inversion H15; clear H15... inversion H15; clear H15... 
          left... 
          unfold sub, In at 1 in H17... left...
          unfold sub, In at 1 in H17... right... 
          (* x is maximal *) admit. 
          (* n > 0 *) admit.

      split.
      eapply is_a_cell_Same_set_compat. 
      rewrite <- J1, J3. reflexivity.   
      rewrite <- J2, J3. reflexivity.
      apply H1.
      clear J1 J2 J3.

      assert ((sub N n ∪ (plus x)) ∩ √minus x == sub M n) as K0.
        unfold N. rewrite sub_Union. rewrite sub_Intersection. 
        rewrite sub_sup_Empty_set. rewrite Empty_set_ident_left. 
        rewrite sub_Union. rewrite sub_idemp.
        unfold Same_set, Included...
          inversion H14; clear H14...
          inversion H14; clear H14...
          unfold sub, In at 1 in H5...
          unfold sub, In at 1... 
          exfalso. unfold Complement, not, In at 1 in H15. 
          apply H15. rewrite (Minus_Singleton x) in H14...
          left... unfold sub, In at 1... unfold sub, In at 1 in H5...
          apply In_Complement.
          unfold not; intros. 
          (* ?? *) admit. 
          admit. apply In_Complement.
          unfold not; intros. (* ?? *) admit.
          (* n > 0 *) admit.
      assert (((((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x))) ∪ (plus x)) ∩ √minus x == sub M n) as KK0. 
        rewrite Minus_Singleton. rewrite Plus_Singleton. rewrite U_I_dist_r.
        rewrite Full_set_property. rewrite Full_set_ident_right.
        rewrite I_U_dist_r.
        rewrite I_U_dist_r. rewrite Empty_set_property.
        rewrite Empty_set_ident_right.
        rewrite Union_Included_right. rewrite Intersection_Included_left.
        reflexivity. apply Disjoint_property_left.
        apply Disjoint_intersection_condition. (* ?? *) admit. 
        apply Intersection_Included_compat. assumption. reflexivity. 
        apply all_decidable. clear KK0.
      rewrite <- K0. 
      assert (X == Union Z (Singleton x)) as K1. unfold Z. rewrite U_I_dist_r.
        rewrite Full_set_property. rewrite Full_set_ident_right. 
        symmetry. apply Union_Included_right. unfold Included. intros.
        inversion H2. rewrite <- H3. apply xcond. apply all_decidable. 
      rewrite K1. 
      rewrite Minus_Union_compat. rewrite Minus_Singleton.
      rewrite <- Intersection_trans. 
      rewrite I_U_dist_r. rewrite I_U_dist_l.
      rewrite I_U_dist_l. 
      assert (minus x ∩ plus x == Empty_set) as K2. rewrite <- Disjoint_intersection_condition. 
      apply Disjoint_sym. apply plus_minus_disjoint.
      rewrite K2. rewrite Empty_set_ident_right. 
      assert ((Minus Z ∩ sub N n) == Empty_set) as K3. apply H1.
      rewrite K3. rewrite (Union_sym Empty_set). rewrite Empty_set_ident_right.
      assert (minus x ∩ sub N n == Empty_set) as K4. (* ?? *) admit. 
      rewrite K4. rewrite Empty_set_ident_right.
      clear K0 K1 K2 K3 K4. 
      unfold Same_set, Included; split; intros. 
      idtac...
      exfalso. (* by maximality of x *) admit.
      inversion H2.
  



 Qed.
*)

  Lemma Lemma_3_2_Step_3' :
    forall n, (forall m , Lemma_3_2_b_st n (S m)) -> (Lemma_3_2_b_st n 1).  
  Proof with repeat basic; auto.
    intros n Hyp1.

    induction n.
    (* n = 0 *)
    apply Lemma_3_2_b_0_1.

    (* n > 0 *)
    unfold Lemma_3_2_b_st in *.
    intros X Xcard M P K L.
    inversion K as [MPcell MPdim]; clear K.
    inversion L as [Xdim J]; clear L.
    inversion J as [Xwf Xcond]; clear J.
    assert (Finite X) as XFin. admit.

    apply cardinality_one_Singleton in Xcard.
    inversion Xcard as [x Xsing]; clear Xcard.

    assert (plus x ⊆ sub M (S n)) as plusxdim.
      assert (PlusMinus X == plus x) as K. 
        unfold PlusMinus. rewrite Xsing. 
        rewrite Plus_Singleton, Minus_Singleton. 
        apply Intersection_Included_left. apply Disjoint_property_left.
        apply plus_minus_disjoint.
      rewrite <- K. assumption.  
    set (Y := (sub M (S n) ∪ Minus X) ∩ √Plus X).
  
    assert (exists S' T, (sub M (S n)) == S' ∪ (plus x) ∪ T) as J. admit.
    inversion J as [S' K]; clear J.   
    inversion K as [T DisjUnion]; clear K.
    assert (exists A B, (S' moves (sub M n) to A) /\ ((plus x) moves A to B) /\ (T moves B to (sub P n))) as J.
      admit.
    inversion J as [A K]; clear J.
    inversion K as [B D]; clear K...

    set (tM := sub P (n) ∪ sup M (n - 1)).
    set (tP := sup P (n)).
    assert (is_a_cell (tM, tP)) as tMPcell.
      unfold tM, tP. apply target_is_a_cell... 
    assert (celldim (tM, tP) (n)) as tMPdim. 
      admit.

    assert (is_a_cell ((sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) ∪ T, tP ∪ T)).

  Admitted.

  Lemma Lemma_3_2_b :
    forall n m, (Lemma_3_2_b_st n m).
  Proof.
    intros n m.
    destruct m.
      (* m = 0 *) apply Lemma_3_2_b_n_0.
    generalize dependent m.
    induction n.
      assert (Lemma_3_2_b_st 0 1) as true_at_0_1.
        (* m = 1, n = 0 *) apply Lemma_3_2_b_0_1.
      destruct m; try assumption.
        (* n = 0 : use step 2 *) apply Lemma_3_2_Step_2'; assumption.
      assert (Lemma_3_2_b_st n 1) as true_at_1.
        (* m = 1 : use step 3 *) apply Lemma_3_2_Step_3'. assumption.
      destruct m; try assumption.
        (* all m, n : use step 2 *) apply Lemma_3_2_Step_2'; assumption.
  Qed.

  Lemma Lemma_3_2_Step_1 :
    forall (n : nat) M P, (is_a_cell (M, P) /\ celldim (M, P) n) ->
    forall X, (X ⊆ (sub (Full_set) (S n))) /\ Finite X /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n)) ->
    (is_a_cell (((sup M (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X))), ((sup P (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)))) 
    /\ (Minus X ∩ (sub M n) == Empty_set) -> (is_a_cell ((((sup M (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X))) ∪ X), (P ∪ X)))).
  Proof with intuition.
    intros n M P K X. 
    set (Y := ((sub M n ∪ Minus X) ∩ √Plus X))...
    unfold is_a_cell in *... 
      apply (Inhabited_Included (sup M (n - 1) ∪ Y)). assumption. apply Union_Included_cancel_right. reflexivity.
      apply (Inhabited_Included P).  assumption. apply Union_Included_cancel_right. reflexivity.
      (**)
      unfold well_formed in *...
        inversion H29; clear H29. inversion H30; clear H30.
          apply H9... 
          subst. apply H3 in H29. unfold sub, In at 1 in H29... rewrite H31 in H28. inversion H28.
          subst. apply H3 in H12. unfold sub, In at 1 in H12... rewrite H31 in H27. inversion H27.
        inversion H27; clear H27. inversion H28; clear H28.
          subst. eapply H24... apply H12. assumption. 
          admit. 
        inversion H28; clear H28. 
          admit.
          subst. eapply H22... apply H12. assumption.
      (**)
      unfold well_formed in *...
        inversion H29; clear H29. inversion H30; clear H30.
          apply H10... 
          subst. apply H3 in H29. unfold sub, In at 1 in H29... rewrite H31 in H28. inversion H28.
          subst. apply H3 in H12. unfold sub, In at 1 in H12... rewrite H31 in H27. inversion H27.
        inversion H27; clear H27. inversion H28; clear H28.
          subst. eapply H25... apply H12. assumption.
          admit. 
        inversion H28; clear H28. 
          admit.
          subst. eapply H22... apply H12. assumption.
      apply Finite_Union... apply all_decidable.
      apply Finite_Union... apply all_decidable.

 admit. 
      admit.
  Qed.


 
  Lemma Lemma_3_2_Step_2 :
    (forall (X : Ensemble carrier), cardinal X 1 /\ Finite X ->
    forall (n : nat) M P, (is_a_cell (M, P) /\ celldim (M, P) n) ->
    ((X ⊆ (sub (Full_set) (S n))) /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n)) ->
    is_a_cell (((sup M (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X))), ((sup P (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)))) 
    /\ (Minus X ∩ (sub M n) == Empty_set))) ->

    (forall (m : nat) (X : Ensemble carrier), cardinal X m /\ Finite X ->
    forall (n : nat) M P, (is_a_cell (M, P) /\ celldim (M, P) n) ->
    ((X ⊆ (sub (Full_set) (S n))) /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n)) ->
    is_a_cell (((sup M (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X))), ((sup P (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)))) 
    /\ (Minus X ∩ (sub M n) == Empty_set))).
  Proof with repeat basic; auto.
    intros hypothesis_for_1 m. 
    destruct m.
      (* m = 0 *) 
      admit.
    induction m.
      (* m = 1 *)
      assumption.
     
      (* m > 1 *)
      intros X X_cond n M P MPcond othercond.
      assert (exists x, In X x /\ Disjoint (plus x) (Minus X)) as R. admit. (* maximal *)
      inversion R as [x xcond]; clear R. 
      assert (plus x ⊆ sub M n). 
        apply (Included_trans _ (PlusMinus X)).
        unfold PlusMinus. rewrite <- (Intersection_idemp (plus x)).
        apply Intersection_Included_compat.
          unfold Included, Plus, In... exists x...
        apply Disjoint_property_left. apply xcond. 
      apply othercond. 
     
      assert (is_a_cell
                 (sup M (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x)),
                 sup P (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x)))
               ∧ Minus (Singleton x) ∩ sub M n == Empty_set).
        apply hypothesis_for_1...
        apply cardinality_Singleton_is_one.
        apply Finite_Singleton. 
        unfold Included... inversion H1; subst... 
        apply well_formed_Singleton. 
        rewrite PlusMinus_Singleton...
      set (N :=  sup M (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x))).
      set (Q :=  sup P (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x))).
      
      set (Z := Intersection X (Complement (Singleton x))).
      set (Y' := (sub N n ∪ (Minus Z)) ∩ √Plus Z).
      set (Y  := (sub M n ∪ (Minus X)) ∩ √Plus X).
      assert (is_a_cell ((sup N (n - 1)  ∪ Y'), (sup Q (n - 1) ∪ Y')) /\ Minus Z ∩ sub N n == Empty_set).
        eapply (IHm Z _ n N Q ).
        split.
        apply H0.
        assert (dim x = S n) as UU. 
          inversion othercond. inversion xcond. apply H1 in H3. unfold sub, In in H3...
        unfold celldim, N, Q, setdim...
          inversion H3; clear H3... inversion H12; clear H12... 
            eapply (le_trans _ (n-1)). unfold sup, In in H3... 
            destruct n; try reflexivity. apply le_S. simpl. rewrite minus_n_O. reflexivity.
          inversion H12; clear H12... 
            unfold sub, In in H3... 
            rewrite H14; reflexivity. 
          rewrite (Minus_Singleton x) in H3.
          apply minus_dim in H3. apply le_S_n. rewrite H3. rewrite UU. reflexivity.
          inversion H12; clear H12... 
            eapply (le_trans _ (n-1)). unfold sup, In in H3... 
            destruct n; try reflexivity. apply le_S. simpl. rewrite minus_n_O. reflexivity.
          inversion H12; clear H12... 
            unfold sub, In in H3... 
            rewrite H14; reflexivity. 
          rewrite (Minus_Singleton x) in H3.
          apply minus_dim in H3. 
          apply le_S_n. rewrite H3. rewrite UU. reflexivity.
        split. 
          apply (Included_trans _ X _). unfold Z. unfold Included... apply othercond. 
        split. 
          unfold Z. apply (well_formed_Included _ X). unfold Included... apply othercond.
          assert (PlusMinus Z == Intersection (Union (PlusMinus X) (minus x)) (Complement (plus x))). 
              assert (X == Union Z (Singleton x)). admit. 
              unfold PlusMinus. rewrite H1.
              rewrite Plus_Union_compat. rewrite Minus_Union_compat.
              rewrite Plus_Singleton. rewrite Minus_Singleton. 
              rewrite <- Union_Complement_compat.
              rewrite I_U_dist_r.
            admit.
          assert (sub N n == Intersection (Union (sub M n) (minus x)) (Complement (plus x))).
            unfold N. rewrite (sub_Union).
            rewrite sub_Intersection. rewrite sub_Union.
            rewrite sub_sup_Empty_set. rewrite Empty_set_ident_left...
            rewrite sub_idemp.
            unfold Same_set, Included...
              inversion H13... 
              right. unfold sub, In at 1 in H4...
              rewrite (Minus_Singleton x) in H15...
              unfold sub, In at 1 in H14...
              apply In_Complement. unfold not; intros. 
              rewrite -> (In_Complement _ x0) in H4. unfold not in H4.
              apply H4. admit. (* bug here ? *)
              inversion H13...
              (* use H4, right *) admit.
              (* use H14, inversion on H13, dimension conditions in each case *) admit.
            (* not true, comes from sub_sup, maybe need global assertion that n>0 *) admit.
          rewrite H1, H2.
          apply Intersection_Included_compat.
          apply Union_Included_compat.
          apply othercond. reflexivity. reflexivity.
      
      assert (sup N (n-1) == sup M (n-1)) as J1.
        unfold N, Same_set, Included, sub, sup, In...
        crush. inversion K; clear K. crush. basic. inversion H5; clear H5...
        unfold In in H16... erewrite (Minus_Singleton x) in H16.
        apply minus_dim in H16. exfalso. 
        assert (dim x = S n). admit.
        rewrite H5 in H16. inversion H16. rewrite H18 in H15. (* again n>0 *)
        (* inversion on H15 *) admit.
        left... unfold In... 
      assert (sup Q (n-1) == sup P (n-1)) as J2.
        unfold Q, Same_set, Included, sub, sup, In...
        crush. inversion K; clear K. crush. basic. inversion H5; clear H5...
        unfold In in H16... admit. erewrite (Minus_Singleton x) in H16.
        apply minus_dim in H16. exfalso. assert (dim x = S n). admit. 
        rewrite H5 in H16. inversion H16. rewrite H18 in H15. (* again n>0 *)
        (* inversion on H15 *) admit.
        left... unfold In... 
      assert (Y == Y') as J3. 
        unfold Y, Y', N.    
        assert (X == Union (Singleton x) Z). 
          unfold Z. rewrite Union_sym. rewrite U_I_dist_r. 
          rewrite Full_set_property. rewrite Full_set_ident_right. 
          unfold Same_set, Included... inversion H5... inversion H14. rewrite <- H15...
          apply all_decidable. 
        rewrite H2.
        rewrite Minus_Union_compat.
        rewrite Plus_Union_compat.
        rewrite <- Union_Complement_compat.
        rewrite sub_Union. rewrite sub_sup_Empty_set.
        rewrite Empty_set_ident_left.
        rewrite sub_Intersection. rewrite sub_Union. rewrite sub_idemp. rewrite sub_Minus.
        rewrite <- Intersection_trans.
        rewrite <- Union_trans.
        rewrite I_U_dist_r.
        assert (sub (Singleton x) (S n) == (Singleton x)) as WW. admit.
        rewrite WW. 
          unfold Same_set, Included... 
          inversion H15; clear H15... inversion H15; clear H15... 
          left... unfold sub, In at 1...
          admit.
          left... unfold sub, In at 1... admit.
          inversion H15; clear H15... inversion H15; clear H15... 
          left... 
          unfold sub, In at 1 in H17... left...
          unfold sub, In at 1 in H17... right... 
          (* x is maximal *) admit. 
          (* n > 0 *) admit.

      split.
      eapply is_a_cell_Same_set_compat. 
      rewrite <- J1, J3. reflexivity.   
      rewrite <- J2, J3. reflexivity.
      apply H1.
      clear J1 J2 J3.

      assert ((sub N n ∪ (plus x)) ∩ √minus x == sub M n) as K0.
        unfold N. rewrite sub_Union. rewrite sub_Intersection. 
        rewrite sub_sup_Empty_set. rewrite Empty_set_ident_left. 
        rewrite sub_Union. rewrite sub_idemp.
        unfold Same_set, Included...
          inversion H14; clear H14...
          inversion H14; clear H14...
          unfold sub, In at 1 in H5...
          unfold sub, In at 1... 
          exfalso. unfold Complement, not, In at 1 in H15. 
          apply H15. rewrite (Minus_Singleton x) in H14...
          left... unfold sub, In at 1... unfold sub, In at 1 in H5...
          apply In_Complement.
          unfold not; intros. 
          (* ?? *) admit. 
          admit. apply In_Complement.
          unfold not; intros. (* ?? *) admit.
          (* n > 0 *) admit.
      assert (((((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x))) ∪ (plus x)) ∩ √minus x == sub M n) as KK0. 
        rewrite Minus_Singleton. rewrite Plus_Singleton. rewrite U_I_dist_r.
        rewrite Full_set_property. rewrite Full_set_ident_right.
        rewrite I_U_dist_r.
        rewrite I_U_dist_r. rewrite Empty_set_property.
        rewrite Empty_set_ident_right.
        rewrite Union_Included_right. rewrite Intersection_Included_left.
        reflexivity. apply Disjoint_property_left.
        apply Disjoint_intersection_condition. (* ?? *) admit. 
        apply Intersection_Included_compat. assumption. reflexivity. 
        apply all_decidable. clear KK0.
      rewrite <- K0. 
      assert (X == Union Z (Singleton x)) as K1. unfold Z. rewrite U_I_dist_r.
        rewrite Full_set_property. rewrite Full_set_ident_right. 
        symmetry. apply Union_Included_right. unfold Included. intros.
        inversion H2. rewrite <- H3. apply xcond. apply all_decidable. 
      rewrite K1. 
      rewrite Minus_Union_compat. rewrite Minus_Singleton.
      rewrite <- Intersection_trans. 
      rewrite I_U_dist_r. rewrite I_U_dist_l.
      rewrite I_U_dist_l. 
      assert (minus x ∩ plus x == Empty_set) as K2. rewrite <- Disjoint_intersection_condition. 
      apply Disjoint_sym. apply plus_minus_disjoint.
      rewrite K2. rewrite Empty_set_ident_right. 
      assert ((Minus Z ∩ sub N n) == Empty_set) as K3. apply H1.
      rewrite K3. rewrite (Union_sym Empty_set). rewrite Empty_set_ident_right.
      assert (minus x ∩ sub N n == Empty_set) as K4. (* ?? *) admit. 
      rewrite K4. rewrite Empty_set_ident_right.
      clear K0 K1 K2 K3 K4. 
      unfold Same_set, Included; split; intros. 
      idtac...
      exfalso. (* by maximality of x *) admit.
      inversion H2.
  Admitted.
 
  Lemma Lemma_3_2_b : 
    (forall (X : Ensemble carrier), Finite X ->
    forall (n : nat) M P, (is_a_cell (M, P) /\ celldim (M, P) n) ->
    ((X ⊆ (sub (Full_set) (S n))) /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n)) ->
    is_a_cell (((sup M (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X))), ((sup P (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)))) 
    /\ (Minus X ∩ (sub M n) == Empty_set))).
  Proof with repeat basic; auto.
    intros X XFin.
    assert (exists m, cardinal X m). apply cardinality_exists. assumption.
    inversion H as [m card_X]; clear H.
    destruct m. 
      apply Lemma_3_2_m_is_0.
      split; assumption. 
    eapply Lemma_3_2_Step_2.
    Focus 2. split. apply card_X. assumption.
    clear.

    intros X Xcond. inversion Xcond; clear Xcond.
    apply cardinality_one_Singleton in H.
    inversion H; clear H.
    intros. 
    inversion H2; clear H2. 
    inversion H4; clear H4. 
    assert (plus x ⊆ sub M n).
      assert (PlusMinus X == plus x). 
        unfold PlusMinus. rewrite H1. 
        rewrite Plus_Singleton. rewrite Minus_Singleton. 
        apply Intersection_Included_left. apply Disjoint_property_left.
        apply plus_minus_disjoint.
      rewrite <- H4. assumption.  
    clear H5.
    inversion H; clear H.      
    set (Y := (sub M n ∪ Minus X) ∩ √Plus X).
    
    generalize dependent P.
    generalize dependent M.
    generalize dependent X.
    generalize dependent x.
    induction n; intros.

      (* n = 0 *)      
      assert (dim x = 1) as dimx. admit.
      assert (sub M 0 == plus x) as subM0. admit.
      assert (Y == minus x) as Ydef. admit.
      assert (sup M (0 - 1) == Empty_set) as supM0. admit.
      assert (sup P (0 - 1) == Empty_set) as supP0. admit.
      assert (sup M (0 - 1) ∪ ((sub M 0 ∪ Minus X) ∩ √Plus X) == minus x) as A.
      unfold is_a_cell in H5...
      rewrite supM0, H1, subM0, Plus_Singleton, Minus_Singleton.
      rewrite Empty_set_ident_left.
      rewrite I_U_dist_r.
      rewrite Empty_set_property.
      rewrite Empty_set_ident_left.
      apply Intersection_Included_left.
      apply Disjoint_property_right.
      apply plus_minus_disjoint.
      assert (sup P (0 - 1) ∪ ((sub M 0 ∪ Minus X) ∩ √Plus X) == minus x) as B.
      rewrite supP0, H1, subM0, Plus_Singleton, Minus_Singleton.
      rewrite Empty_set_ident_left.
      rewrite I_U_dist_r.
      rewrite Empty_set_property.
      rewrite Empty_set_ident_left.
      apply Intersection_Included_left.
      apply Disjoint_property_right.
      apply plus_minus_disjoint.
      split.
      eapply is_a_cell_Same_set_compat.
      apply A. apply B.
      
      unfold is_a_cell... 
        apply minus_non_empty. rewrite dimx. auto.
        apply minus_non_empty. rewrite dimx. auto.
        admit. admit. 
        apply minus_fin. 
        apply minus_fin. 
        unfold moves_def; apply dim_1_properties in dimx... 
          rewrite H, H7.
          rewrite Empty_set_ident_right. rewrite Complement_Empty_set.
          rewrite Full_set_ident_right. reflexivity.
          rewrite H, H7.
          rewrite Empty_set_ident_right. rewrite Complement_Empty_set.
          rewrite Full_set_ident_right. reflexivity.
        unfold moves_def; apply dim_1_properties in dimx... 
          rewrite H, H7.
          rewrite Empty_set_ident_right. rewrite Complement_Empty_set.
          rewrite Full_set_ident_right. reflexivity.
          rewrite H, H7.
          rewrite Empty_set_ident_right. rewrite Complement_Empty_set.
          rewrite Full_set_ident_right. reflexivity.

      rewrite H1, Minus_Singleton, subM0.
      apply Disjoint_intersection_condition.
      apply Disjoint_sym. apply plus_minus_disjoint.

      (* n > 0 *)
      assert (exists S' T, (sub M (S n)) == S' ∪ (plus x) ∪ T) as J. admit.
        inversion J as [S' K]; clear J.   
        inversion K as [T L]; clear K.
      assert (exists A B, (S' moves (sub M n) to A) /\ ((plus x) moves A to B) /\ (T moves B to (sub P n))) as J.
        admit.
        inversion J as [A K]; clear J.
        inversion K as [B D]; clear K...

        set (tM := sub P (n) ∪ sup M (n - 1)).
        set (tP := sup P (n)).
        assert (is_a_cell (tM, tP)).
        unfold tM, tP. apply target_is_a_cell... 
        assert (celldim (tM, tP) (n)). admit.

        assert (is_a_cell ((sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) ∪ T, tP ∪ T)).
        eapply Lemma_3_2_Step_1.
        split; assumption.
        (* T has correct dimension, T Finite, T wellformed because M is, 
           final condition because (sub tM n) == sub tP n) and because T is final *) 
        admit. 
        eapply (Lemma_3_2_Step_2 _ _ T _ n).
        split; assumption. (* same as above *) admit.
        (* misc stuff that helps reconcile with Ross's paper *)
        assert (B == ((sub tM n ∪ Minus T) ∩ √Plus T)).
        unfold tM.
        rewrite sub_Union. rewrite sub_sup_Empty_set.
        rewrite sub_idemp. rewrite Empty_set_ident_right.
        unfold moves_def in H9. inversion H9; assumption. admit. 
        assert (sup tM (n-1) == sup M (n-1) ). 
        unfold tM. rewrite sup_Union.
        rewrite sup_idemp. admit. 
        assert (is_a_cell (sup M (n - 1) ∪ (B ∪ T), (sup P n) ∪ T)). admit.
        
        assert (is_a_cell (sup M (n-1) ∪ B , sup P (n-1) ∪ B) /\ celldim (sup M (n-1) ∪ B , sup P (n-1) ∪ B) n). 
        split. 
        

admit.
        assert (is_a_cell
       ((sup (sup M (n - 1) ∪ B) (n - 1)
         ∪ ((sub (sup M (n - 1) ∪ B) n ∪ Minus (plus x)) ∩ √Plus (plus x))) ∪ (plus x),
       (sup P (n - 1) ∪ B) ∪ (plus x))).
        eapply Lemma_3_2_Step_1. 
        assumption.
        admit.
        eapply (Lemma_3_2_Step_2 _ _ (plus x) _ n).
        assumption. admit. 
       
        assert (is_a_cell (sup M (n-1) ∪ A , sup P (n-1) ∪ A) /\ celldim (sup M (n-1) ∪ A , sup P (n-1) ∪ A) n). admit.
        assert (is_a_cell
       ((sup (sup M (n - 1) ∪ A) (n - 1)
         ∪ ((sub (sup M (n - 1) ∪ A) n ∪ Minus S') ∩ √Plus S')) ∪ S',
       (sup P (n - 1) ∪ A) ∪ S')).
        eapply Lemma_3_2_Step_1. 
        assumption.
        admit.
        eapply (Lemma_3_2_Step_2 _ _ S' _ n).
        assumption. admit. 

        assert (minus x moves A to B). 
        apply Prop_3_1. 
        unfold moves_def; split; assumption. 
        admit.

        (* ... *)        

        simpl. rewrite <- (minus_n_O n)...
        admit. admit. admit. admit. admit. admit.
        unfold Y.
        unfold moves_def. split. 
        Admitted.

  Lemma all_receptive : (forall M P : Ensemble carrier, is_a_cell (M, P) -> cell_receptive (M, P)).
  Admitted.  

  Lemma Lemma_3_2_c : 
    forall (n : nat) M P, (is_a_cell (M, P) /\ celldim (M, P) n) ->
      forall X, (X ⊆ (sub (Full_set) (S n))) /\ Finite X /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n)) ->
      is_a_cell ((((sup M (n-1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X))) ∪ X), (P ∪ X)).
  Proof with repeat basic; auto.
  intros.
  apply Lemma_3_2_Step_1. 
  Focus 3.
  apply Lemma_3_2_b...
  assumption. assumption. 
  Qed.

  Lemma Prop_3_4 :
    forall M P, is_a_cell (M, P) ->
    forall z n, dim z = S n ->
    minus z ⊆ P ->
    Minus M ∩ plus z == Empty_set.
  Admitted.

  Lemma Prop_3_5 :
    forall M P N Q, is_a_cell (M, P) /\ is_a_cell (N, Q) ->
    (forall n m, m < n-1 -> (M == N /\ P == Q /\ P = N)) -> 
    (Minus M ∩ Plus N == Empty_set) /\ is_a_cell (M, N).
  Admitted.

  Lemma Theorem_3_6b :
    forall M P N Q (n: nat), 
      is_a_cell (M, P) -> is_a_cell (N, Q) -> 4 = 4 ->
      Minus (M ∪ P) ∩ Plus (N ∪ Q) == Empty_set.
  Admitted. 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* mu and pi                                            *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Definition mu (x : carrier) : Ensemble carrier. Admitted.
  Definition pi (x : carrier) : Ensemble carrier. Admitted.
  
  Notation "'<<' x '>>'" := ((mu x), (pi x)) (at level 85).

  Axiom atom_is_a_cell : forall x, is_a_cell (<< x >>).

  Axiom atom_dim : forall x n, dim x = n -> celldim (<<x>>) n.

  Axiom mu_top : forall x n, dim x = n -> sub (mu x) n == Singleton x. 
  Axiom pi_top : forall x n, dim x = n -> sub (pi x) n == Singleton x. 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Basic results from definitions                       *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma Same_set_is_a_cell : forall S T, 
    is_a_cell (S, T) -> forall S' T', S == S' /\ T == T' -> is_a_cell (S', T').
  Admitted. 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Section 4                                            *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Axiom mu_is_tight : forall x, tight (mu x).

  Lemma Theorem_4_1 :
    forall M P n, is_a_cell (M, P) -> celldim (M, P) n ->
    forall u, u ∈ (sub M n) -> ~((M, P) === << u >>) ->
    exists N Q L R m, 
      is_a_cell (N, Q) /\ 
      is_a_cell (L, R) /\
      (m < n) /\ 
      ~(celldim (N, Q) m) /\ 
      ~(celldim (L, R) m) /\
      ((M, P) === composite m (N, Q) (L, R)).
  Proof with repeat basic; auto.
    intros M P n cellcond dimcond u udim notatomic.  

    (* Find m *)
    set (Z := (fun m => (m < n) /\ ~((sub M (S m), sub P (S m)) === (sub (mu u) (S m), sub (pi u) (S m))))). 
    assert (exists m, (In Z m /\ forall r, In Z r -> r <= m)) as max_exists.
      assert (Inhabited Z /\ Finite Z) as Inhab_Finite. admit. 
      apply Finite_nat_have_maximum_le_element; apply Inhab_Finite.
    inversion max_exists as [m H]; clear max_exists; inversion H as [minZ mmax]; clear H.
    
    assert ((sub M (S m)) == (sub (mu u) (S m)) ∪ ((sub M (S m)) ∩ (sub P (S m)))) as Mcond. 
      unfold Z, In in minZ. inversion minZ as [minZa minZb]; clear minZ. 
      assert ( S m < n \/ S m = n). 
        unfold lt in minZa. inversion minZa. right; trivial. left. unfold lt. apply le_n_S. trivial. 
      inversion H.
        assert ((sub M (S m), sub P (S m)) === (sub (mu u) (S m), sub (pi u) (S m))). 
          admit. (*by maximality*)
        unfold Same_pair in H1; inversion H1; clear H1. 
      (*
        assert (sub M n == sub P n). admit.
        assert (sub (mu u) n ⊆ sub M n). admit.
        rewrite <- H1. rewrite (Intersection_idemp (sub M n)).
        rewrite Union_Included_left. reflexivity. assumption. *) admit. admit.

    assert ((sub P (S m)) == (sub (pi u) (S m)) ∪ ((sub M (S m)) ∩ (sub P (S m)))) as Pcond. 
(*      unfold Z, In in minZ. inversion minZ as [minZa minZb]; clear minZ. 
      assert ( S m < n \/ S m = n). 
        unfold lt in minZa. inversion minZa. right; trivial. left. unfold lt. apply le_n_S. trivial. 
      inversion H.
        assert ((sub M (S m), sub P (S m)) ::: (sub (mu u) (S m), sub (pi u) (S m))). admit. (*by maximality*)
        unfold Same_pair in H1; inversion H1; clear H1. rewrite <- H3.
        unfold Same_set, Included. split; intros.
          left; assumption. apply In_Union in H1. inversion H1. assumption. apply In_Intersection in H4. 
          apply H4.
        rewrite H0. admit. (* just fact here *) *) admit.

    assert (Inhabited ((sub M (S m)) ∩ (sub P (S m)))) as MPInhab.
      assert (((sub M (S m)) ∩ (sub P (S m))) == Empty_set \/ Inhabited ((sub M (S m)) ∩ (sub P (S m)))). 
      apply Finite_Empty_or_Inhabited. eapply (Finite_Included). apply all_decidable. 
      assert (Finite M). apply cellcond. apply H. 
      unfold Included, sub, In; intros. inversion H. apply H0.
      inversion H as [K | K]; clear H; try assumption.
      rewrite K in Mcond, Pcond.
      rewrite Empty_set_ident_right in Mcond, Pcond.
      unfold Z in minZ. unfold In at 1 in minZ. inversion minZ as [AAA BBB]; clear minZ.
      exfalso. apply BBB. constructor; assumption.    
    inversion MPInhab as [w winMP]; clear MPInhab.
    
    set (X := fun k => k ∈ sub M (S m) /\ triangle k w).
    assert (exists x, (In X x /\ forall r, In X r -> triangle x r)) as Xhasmin. 
      admit.
    inversion Xhasmin as [x xismin]; clear Xhasmin.

    set (Y := fun k => k ∈ sub M (S m) /\ triangle w k).
    assert (exists y, (In Y y /\ forall r, In Y r -> triangle r y)) as Yhasmax. 
      admit.    
    inversion Yhasmax as [y yismax]; clear Yhasmax.
    
    assert (~(x ∈ (sub (mu u) (S m))) \/ ~(y ∈ (sub (mu u) (S m)))) as ASD. 
      admit.
    
    assert ((x ∈ ((sub M (S m)) ∩ (sub P (S m)))) \/ (y ∈ ((sub M (S m)) ∩ (sub P (S m))))) as xory. 
      inversion ASD as [WER | WER]; clear ASD; [left | right].
        inversion xismin as [QQQ WWW]; clear xismin. unfold In, X in QQQ. 
        inversion QQQ as [OOO IIII]; clear QQQ. rewrite Mcond in OOO.
        apply In_Union in OOO; inversion OOO; try assumption. contradiction.
        inversion yismax as [QQQ WWW]; clear yismax. unfold In, Y in QQQ. 
        inversion QQQ as [OOO IIII]; clear QQQ. rewrite Mcond in OOO.
        apply In_Union in OOO; inversion OOO; try assumption. contradiction.

    assert ((minus x ⊆ sub M m) /\ (plus y ⊆ sub P m)) as specialcond. split.
      cut (minus x ⊆ sub (MinusPlus M) m); intros. apply (Included_trans _ _ _ H).
      eapply (sub_Included_compat). eapply Prop_2_1. exists P. apply cellcond. 
      unfold Included, sub, MinusPlus, In; intros. 
      split. 
        split.
          unfold Minus; exists x. 
          split. 
            inversion xismin. unfold X, In, sub in H0. apply H0.
            apply H.
          apply In_Complement; unfold not; intros. unfold In, Plus in H0. 
          inversion H0; clear H0. inversion xismin as [RRR TTT].
          assert (triangle x1 x). 
            apply (Relation_Operators.rt1n_trans _ _ _ x).
            unfold less. exists x0...
            apply (Relation_Operators.rt1n_refl).
          assert (triangle x x1). 
            apply TTT. unfold X. unfold In at 1. 
            split. 
              unfold sub. unfold In at 1. 
              split. 
                apply H1. 
                inversion H1. apply plus_dim in H3. apply minus_dim in H. 
                rewrite <- H3. rewrite H. unfold X, In, sub in RRR. inversion RRR.
                apply H4.  
              eapply (Relation_Operators.rt1n_trans _ _ _ x). 
              exists x0. 
              split.  
                apply H1. 
                apply H. 
            apply TTT.
          unfold X; split. 
            apply In_Intersection in winMP. apply winMP. 
            apply (Relation_Operators.rt1n_refl). 
        assert (x = x1). 
          apply axiom3a; assumption.
        subst. remember (plus_minus_disjoint x1) as K.
        inversion K. apply (H3 x0)...
      assert (dim x = S m) as AA. 
        inversion xismin as [A B]; unfold X, In in A;
        inversion A as [C D]; unfold sub in C; apply C. 
      apply minus_dim in H. rewrite AA in H; inversion H; trivial. 

    admit.

    inversion xory.
      (**)
      set (R := (P ∩ (√(Singleton x)))).
      set (L := ((M ∩ √(Singleton x)) ∪ plus x) ∩ √minus x).
      set (Q := ((((sub M m) ∪ (plus x)) ∩ √(minus x))) ∪ (sup P (m-1)) ∪ (Singleton x)).
      set (N := ((sup M m) ∪ ((Singleton x)))).
      exists N. exists Q. exists L. exists R. exists m. 
      split. 
        unfold N, Q. admit.
      split.
        unfold L, R. admit.
      split. admit.
      split. admit.
      split. admit.
      split. admit.
      admit.
      
      (**)
      set (N := (M ∩ (√(Singleton y)))).
      set (Q := ((M ∩ √(Singleton y)) ∪ minus y) ∩ √plus y).
      set (L := ((sup M (m-1) ∪ (((sub P m) ∪ (minus y)) ∩ √(plus y))) ∪ (Singleton y))).
      set (R := ((sup P m) ∪ ((Singleton y)))).
      assert (sup (sup M (m - 1) ∪ sub P m) (m - 1) == sup M (m-1)). admit.
      assert ((sub (sup M (m - 1) ∪ sub P m) m) == sub P m). admit.
      exists N. exists Q. exists L. exists R. exists m. 
      splits.
        unfold N, Q. admit.
        unfold L, R.  
        apply (Same_set_is_a_cell ((sup M (m - 1) ∪ ((sub P m ∪ Minus (Singleton y)) ∩ √Plus (Singleton y))) ∪ Singleton y)
  (sup P m ∪ Singleton y)). 
        eapply Same_set_is_a_cell. 
        Focus 2. split.
        rewrite <- H0. rewrite <- H1 at 2. reflexivity. reflexivity.
        apply (Lemma_3_2_c m (Union (sup M (m-1)) (sub P m)) (sup P m)).
        split. remember (target_is_a_cell m M P cellcond). unfold is_a_cell, target in i.
        apply (Same_set_is_a_cell _ _ i). split. apply Union_sym. reflexivity. admit. 
        admit.
        split.
          rewrite (Minus_Singleton y). rewrite (Plus_Singleton y). reflexivity.
          reflexivity.
  Admitted. 

End ParityComplexTheory.                                    






