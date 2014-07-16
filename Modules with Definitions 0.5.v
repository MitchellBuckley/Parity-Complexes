
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

Hint Unfold decidable : sets v62. 

Transparent In.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Pre-Parity Complex Definitions                       *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Module Type PreParity.

  Parameter carrier : Type.
  Parameter dim : carrier -> nat.
  Parameter plus minus : carrier -> Ensemble carrier.

  Axiom carrier_decidable_eq : decidable_eq carrier.

  Axiom plus_dim :            forall (x y : carrier), In (plus y) x -> S(dim x) = dim y.
  Axiom minus_dim :           forall (x y : carrier), In (minus y) x -> S(dim x) = dim y. 
  Axiom plus_fin :            forall (x : carrier),   Finite (plus x).
  Axiom minus_fin :           forall (x : carrier),   Finite (minus x).
  Axiom plus_non_empty :      forall (x : carrier),  dim x > 0 -> (Inhabited (plus x)).
  Axiom minus_non_empty :     forall (x : carrier),  dim x > 0 -> (Inhabited (minus x)).
  Axiom plus_zero:            forall (x : carrier),   (dim x) = 0 ->  plus x == Empty_set.
  Axiom minus_zero:           forall (x : carrier),   (dim x) = 0 -> minus x == Empty_set.
  Axiom plus_minus_disjoint : forall (y : carrier), Disjoint (plus y) (minus y).
  
  Axiom all_decidable :       forall (S : Ensemble carrier), decidable S. 

  Hint Resolve plus_fin minus_fin plus_dim minus_dim.

  (*
  Lemma all_decidable : forall (S : Ensemble carrier), Finite S -> decidable S. 
  Proof.
    intros.
    apply Finite_are_decidable.
    apply carrier_decidable_eq.
    assumption.
  Qed.  
  *)

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
    | H: In (fun y => _) ?x |- _ => unfold In at 1 in H
    | H: _ |- In (fun y => _) ?x => unfold In at 1
    | [ H:(Same_set ?S ?T), _:(In ?T ?x) |- In ?S ?x ] => rewrite H; assumption
    | [ H:(Same_set ?S ?T), _:(In ?S ?x) |- In ?T ?x ] => rewrite <- H; assumption
  end.

  Lemma Test_basic : True.
  Proof.
    assert True. trivial.
    assert (In (fun z => (z <= 10)) 4). basic. admit.
    basic.
    assert (Empty_set == Singleton 3). admit.
    assert (In (Singleton 3) 4). admit.
    assert (In Empty_set 4).
      basic. 

    constructor.
  Qed.

  Ltac subsuptac := 
  match goal with
    | H: In (sub ?P ?n) ?x |- _ => unfold sub, In at 1 in H
    | H: In (sup ?P ?n) ?x |- _ => unfold sup, In at 1 in H
    | H: _ |- In (sub ?P ?n) ?x => unfold In, sub
    | H: _ |- In (sup ?P ?n) ?x => unfold In, sup
  end.

Ltac disj := 
  match goal with
    | H: (?P ∪ ?Q) ?x |- _ => inversion H as [a K aeq | b K beq]; [clear H aeq a | clear H beq b]; unfold In in K
    | H: ?P ?x |- (?P ∪ _) ?x => left
    | H: ?P ?x |- (_ ∪ ?P) ?x => right
  end.

Ltac conj := 
  match goal with
    | H: (?P ∩ ?Q) ?x |- _ => inversion H as [a H1 H2 aeq]; clear H a aeq; unfold In in H1; unfold In in H2
    | H: _ |- (?P ∩ ?Q) ?x => split; unfold In
  end.

Ltac neg :=
  match goal with
    | H: (√(?P)) ?x |- _ => unfold Complement, In, not in H
    | H: _ |- (√(?P)) ?x => unfold Complement, In, not
  end.

Ltac misc :=
  match goal with
    | H: (Empty_set) ?x |- _   => contradiction
    | H: (Full_set) ?x |- _    => clear H
    | H: _ |- (Full_set) ?x    => constructor
    | H: _ |- (Empty_set) ?x   => try (exfalso; auto)
    | H: ?a = ?b |- _          => subst
    | H: Singleton ?a ?a |- _  => clear a
    | H: Singleton ?a ?b |- _  => inversion H as [K]; clear H; try rewrite K in *; clear K
    | H: Disjoint ?a ?b |- _   => inversion H as [L]; clear H; unfold not, In in L 
    | H: _ |- Disjoint ?a ?b   => constructor; unfold In, not; intros
    | H: Inhabited ?S |- _       => inversion H; clear H
    | H: ?S ?x |- Inhabited ?S   => exists x; unfold In; trivial
end.

  Ltac crush' := 
   autounfold with *;
   intuition; 
   repeat (conj || disj || neg || misc); 
   auto.
 
  Ltac crush := 
   autounfold with *;
   intuition (try (conj || disj || neg || misc); intuition).

  (** SETOID MORPHISMS **)

  Add Parametric Morphism : (@Plus) with 
    signature (@Same_set carrier) ==> (@Same_set carrier) as Plus_Same_set.
  Proof with crush.
    crush. inversion H... exists x1...
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

  Add Parametric Morphism : (triangle_rest) with 
    signature (@Same_set carrier) ==> (@eq carrier) ==> (@eq carrier) ==> (@iff) as triangle_rest_Same_set.
  Proof with intuition.
    intros S T; unfold triangle_rest... 
    induction H0.
      apply rt1n_refl.
      assert (restrict T less x y).
        unfold restrict in *...
        rewrite <- H... rewrite <- H...
      eapply (Relation_Operators.rt1n_trans)... apply H2...
        assumption. 

    induction H0.
      apply rt1n_refl.
      assert (restrict S less x y).
        unfold restrict in *...
        rewrite H... rewrite H...
      eapply (Relation_Operators.rt1n_trans)... apply H2...
        assumption.
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
    apply minus_zero in H2...
    assert (In Empty_set x0).
    rewrite <- H2... 
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
    apply plus_zero in H2... 
    assert (In Empty_set x0).
    rewrite <- H2... 
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

  Hint Resolve sub_Included sup_Included sub_sup_Included.

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
    forall T, well_formed T -> forall S, Included S T -> well_formed S.
  Proof with intuition.
    autounfold with *...
    eapply H1... apply H2. assumption. 
  Qed.

  Lemma well_formed_Singleton : 
    forall x, well_formed (Singleton x).
  Proof with intuition.
    intros x.
    unfold well_formed...
    inversion H2; inversion H3; subst...
    inversion H0; inversion H1; subst...
  Qed.
 
  Hint Resolve well_formed_Singleton well_formed_Included.

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
      apply H5...
  Qed. 

  Hint Resolve Finite_are_decidable carrier_decidable_eq.

  Hint Constructors Finite.

  Lemma Plus_Finite : 
    forall A, Finite A ->
      Finite (Plus A).
  Proof with intuition.
    intros.
    induction H...
      apply (Same_set_is_finite Empty_set)...
      crush. 
      inversion H... 

      unfold Add.
      rewrite Plus_Union_compat.
      rewrite Plus_Singleton.
      apply Finite_Union... 
      
      rewrite H0...
  Qed.

  Lemma Minus_Finite : 
    forall A, Finite A ->
      Finite (Minus A).
  Proof with intuition.
    intros.
    induction H.
      apply (Same_set_is_finite Empty_set)...
      crush. inversion H... 

      unfold Add. 
      rewrite Minus_Union_compat. 
      rewrite Minus_Singleton. 
      apply Finite_Union...
   
      rewrite H0...
  Qed.

  Lemma Setminus_Finite : 
    forall A, @Finite carrier A ->
    forall B, Finite B ->
      Finite (Intersection A (Complement B)).
  Proof with intuition.
    intros.
    induction H.
    apply (Same_set_is_finite Empty_set)...

    unfold Add.
    rewrite I_U_dist_r. 
    apply Finite_Union...
    assert (In B x \/ ~(In B x)). apply all_decidable. 
    inversion H2; clear H2.
      apply (Same_set_is_finite Empty_set).
      constructor.
      unfold Same_set, Included...
      repeat basic. 
      inversion H4; clear H4; subst... unfold Complement, In at 1 in H5...
      inversion H2...
      apply (Same_set_is_finite (Singleton x)).
      apply Finite_Singleton.
      unfold Same_set, Included...
      repeat basic. 
      inversion H4...
      inversion H2; clear H2; subst...

    rewrite H1...
  Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Section 2                                            *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma Observation_p321 : 
    forall (S : Ensemble carrier), Finite S -> S moves (MinusPlus S) to (PlusMinus S).
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
     Finite S ->
     ((exists (P : Ensemble carrier), S moves M to P) 
     <->
     (MinusPlus S) ⊆ M /\ Disjoint M (Plus S)).
  Proof with repeat basic; auto.
    unfold moves_def; unfold PlusMinus; unfold MinusPlus. 
    intros S M SFin; split; intros. 
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
     Finite S ->
     (S moves M to ((M ∪ (Plus S)) ∩ √(Minus S)) 
     <->
     (MinusPlus S) ⊆ M /\ Disjoint M (Plus S)).
  Proof with intuition. 
    intros S M SFin. split; intros.
    apply Prop_2_1...
    exists ((M ∪ Plus S) ∩ √Minus S). assumption.
    apply Prop_2_1 in H...
    inversion H as [P K]. 
    unfold moves_def in *...
    rewrite <- H0...
  Qed.

  Hint Resolve all_decidable Plus_Finite Minus_Finite.

  Lemma Prop_2_1_dual : forall (S P : Ensemble carrier), 
     Finite S ->
     ((exists (M : Ensemble carrier), S moves M to P) 
     <->
     (PlusMinus S) ⊆ P /\ Disjoint P (Minus S)).
  Proof with repeat basic; auto.
    unfold moves_def; unfold PlusMinus; unfold MinusPlus. 
    intros S P SFin; split; intros. 
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
    auto.
  Qed.

  Lemma Prop_2_2 : 
    forall (S A B X: Ensemble carrier),
    Finite S ->
    S moves A to B -> X ⊆ A -> Disjoint (MinusPlus S) X 
    -> 
    forall (Y : Ensemble carrier),  
    Disjoint Y (Plus S) -> Disjoint Y (Minus S) 
    ->
    S moves ((A ∪ Y) ∩ (√X)) to ((B ∪ Y) ∩ (√X)).
  Proof with intuition.
    intros S A B X SFin. intros.
    unfold moves_def in H. inversion H; clear H.
    assert (exists (P : Ensemble carrier), S moves ((A ∪ Y) ∩ √X) to P).
      apply Prop_2_1. assumption.
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
        rewrite (Intersection_sym _ (Plus S)). rewrite Empty_set_property...
        rewrite Empty_set_zero_right...

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
    rewrite <- Union_sym, Union_trans...
  Qed.

 
  Lemma Prop_2_4 :
    forall (T Z M P : Ensemble carrier),
    Finite Z -> Finite T -> (Union T Z) moves M to P -> 
    Included (PlusMinus Z) P ->
    Perp T Z ->
    exists N N', (N == N') /\ (T moves M to N) /\ (Z moves N' to P).
  Proof with repeat basic; auto.
    intros T Z M P ZFin TFin. 
    remember (Union T Z) as S.
    intros.
    assert (Finite S) as SFin. rewrite HeqS. apply Finite_Union...
    unfold moves_def in H...
    
    assert (exists N, Z moves N to P). 
    apply Prop_2_1_dual. assumption.
      split; try assumption.
      assert (Included (Minus Z) (Minus S)). 
        rewrite HeqS. rewrite Minus_Union_compat. apply Union_Included_cancel_left. reflexivity.
      apply Disjoint_intersection_condition. eapply (Included_Empty_set). eapply Intersection_Included_compat.
      reflexivity. apply H1. 
      rewrite H2. rewrite Intersection_trans. rewrite (Intersection_sym _ (Minus S)). 
      rewrite Empty_set_property...
    inversion H1 as [N']; clear H1.

    assert (exists N', T moves M to N').        
    apply Prop_2_1. assumption. split.
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
        auto. auto.

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
        auto.
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
    rewrite H14... auto. auto.
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

  Axiom axiom2a :
    forall x, well_formed (plus x).

  Axiom axiom2b :
    forall x, well_formed (minus x).

  Axiom axiom3a:
    forall x y : carrier, 
      triangle x y -> triangle y x -> x = y.

  Axiom axiom3b:
    forall x y z : carrier, 
    triangle x y ->
    (~ (In (plus z) x /\ In (minus z) y) /\ ~ (In (plus z) y /\ In (minus z) x)).
  (* This last condition somewhat awkwardly phrased, this might become tricky later *)

Hint Resolve axiom2a axiom2b.

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

  Lemma Same_set_is_a_cell : forall S T, 
    is_a_cell (S, T) -> forall S' , S == S' -> forall T', T == T' -> is_a_cell (S', T').
  Admitted. 


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

  Lemma Sn_minus_1 : forall n, (S n - 1 = n).
  Proof. intros. simpl. symmetry. apply minus_n_O. Qed.

  Lemma Finite_sup : forall T, Finite T -> forall n, Finite (sup T n). 
  Proof with intuition.
    intros.
    eapply (Finite_Included).
    apply all_decidable. apply H.
    trivial. 
  Qed.

  Lemma Finite_sub : forall T, Finite T -> forall n, Finite (sub T n). 
  Proof with intuition.
    intros.
    eapply (Finite_Included).
    apply all_decidable. apply H.
    trivial. 
  Qed.

  Hint Resolve Finite_sub Finite_sup.

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

  Lemma M_0_Inhabited : 
    forall M P, 
      is_a_cell (M, P) -> 
      exists z, (sub M 0) == Singleton z.
  Admitted. 

  Lemma sub_sup_0 : forall X, sub X 0 == sup X 0.
  Admitted.

  Hint Resolve Finite_Singleton sub_sup_0.

  Lemma source_is_a_cell : forall (m : nat) (M P : Ensemble carrier), 
    is_a_cell (M, P) -> 
    celldim (M, P) (S m) -> 
    forall n, 
      n <= m -> 
      is_a_cell (source n (M, P)).
  Proof with intuition.
    intros m M P MPcell MPdim n nltm.
    unfold source.
    
    destruct n.
    apply (Same_set_is_a_cell (sub M 0) (sub M 0))... 
      apply M_0_Inhabited in MPcell. 
      inversion MPcell; clear MPcell. 
    apply (Same_set_is_a_cell (Singleton x) (Singleton x))... 
    assert (dim x = 0) as dimx. admit.
    unfold is_a_cell... 
      exists x...
      exists x...
 
      unfold moves_def...
      rewrite Plus_Singleton, Minus_Singleton.
      rewrite plus_zero...
      rewrite minus_zero...
      rewrite Empty_set_ident_right. 
      rewrite Complement_Empty_set. 
      rewrite Full_set_ident_right...
      rewrite Plus_Singleton, Minus_Singleton.
      rewrite plus_zero...
      rewrite minus_zero...
      rewrite Empty_set_ident_right. 
      rewrite Complement_Empty_set. 
      rewrite Full_set_ident_right...

      unfold moves_def...
      rewrite Plus_Singleton, Minus_Singleton.
      rewrite plus_zero...
      rewrite minus_zero...
      rewrite Empty_set_ident_right. 
      rewrite Complement_Empty_set. 
      rewrite Full_set_ident_right...
      rewrite Plus_Singleton, Minus_Singleton.
      rewrite plus_zero...
      rewrite minus_zero...
      rewrite Empty_set_ident_right. 
      rewrite Complement_Empty_set. 
      rewrite Full_set_ident_right...

    assert (sup P (0 - 1) == Empty_set) as AA. admit. (* fix later *)
    rewrite AA. 
    rewrite Empty_set_ident_right...

    rewrite Sn_minus_1. 
    unfold is_a_cell in *...

    unfold celldim, setdim in MPdim.
    (* sup M 0 is inhabited *) 
    admit.

    (* sup P 0 is inhab *)
    admit.

    unfold well_formed in *...
      apply H6... 
      repeat subsuptac...
      repeat subsuptac...
      eapply H8... 
      repeat subsuptac...
      repeat subsuptac...
      apply H2. 
      assumption.

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

    (**) apply Finite_Union...

    (**) admit. admit.
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
    assert (exists Y, minus x moves M to Y). apply Prop_2_1. apply minus_fin.
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
    assert (plus j == Empty_set). apply plus_zero... fold (In (plus j) x0) in H3. rewrite H4 in H3; unfold In in H3...
    crush... inversion H0 as [j]...
    assert (dim j = 0). apply plus_dim in H2. rewrite H in H2. auto. 
    assert (plus j == Empty_set). apply plus_zero... fold (In (plus j) x0) in H3. rewrite H4 in H3; unfold In in H3...
    crush... inversion H0 as [j]...
    assert (dim j = 0). apply minus_dim in H2. rewrite H in H2. auto. 
    assert (minus j == Empty_set). apply minus_zero... fold (In (minus j) x0) in H3. rewrite H4 in H3; unfold In in H3...
    crush... inversion H0 as [j]...
    assert (dim j = 0). apply plus_dim in H2. rewrite H in H2. auto. 
    assert (minus j == Empty_set). apply minus_zero... fold (In (minus j) x0) in H3. rewrite H4 in H3; unfold In in H3...
  Qed.

  Lemma Prop_3_3 : (forall M P : Ensemble carrier, is_a_cell (M, P) -> cell_receptive (M, P)).
  Proof with intuition.
    unfold is_a_cell...
    assert (receptive M /\ receptive P).
    split.

    unfold receptive... 
    remember (dim x) as n.
    destruct n.
    
    (* n = 0 *) 
    assert (Minus (minus x) == Empty_set /\ Minus (plus x) == Empty_set).
    split; unfold Minus, Same_set, Included, In...  
    inversion H10... apply minus_dim in H12. rewrite <- Heqn in H12. inversion H12.
    inversion H10... apply plus_dim in H12. rewrite <- Heqn in H12. inversion H12.
    apply H8... 
    rewrite H11.
    rewrite H12 in H9...
    
    induction n.
    (* n = 1 *)
    assert (Minus (minus x) == Empty_set /\ Minus (plus x) == Empty_set).
    split; apply dim_1_properties; symmetry... 
    apply H8... 
    rewrite H11.
    rewrite H12 in H9...

    (* n > 1 *)
    
  Admitted.

  Lemma triangle_dec : forall T, Finite T -> forall x z, (triangle_rest T z x \/ ~(triangle_rest T z x)).
  Proof with intuition. 
    intros T TFin. 
    induction TFin...
    
      assert (x = z \/ ~(x = z)). apply carrier_decidable_eq.
      inversion H; clear H; [left |right]... 
        rewrite H0. left.
        inversion H; clear H...
        inversion H1; clear H1... inversion H.

      assert (x0 = z \/ ~(x0 = z)). apply carrier_decidable_eq.
      inversion H0; clear H0; subst; [left | idtac]...
        left.
      specialize IHTFin with (x:=x0) (z := z).
      inversion IHTFin; clear IHTFin...
        left... admit.
        (* decide whether you can use x to form a path *) 
      admit.

      specialize IHTFin with (x:=x) (z := z).
      inversion IHTFin; clear IHTFin; [left | right]...
      rewrite H...
      apply H0. rewrite <- H...
  Qed.

  (* This is not trivial, needs to be finished, need help with this *)
  Lemma maximal_exists :
    forall n X, Included X (sub Full_set n) -> Finite X -> Inhabited X
      -> exists x, In X x /\ (forall y, In X y -> (triangle_rest X x y -> x = y)).
  Proof with intuition. 
    intros. 
    induction H0.
      (* X empty *)
      apply Inhabited_not_empty in H1. 
      exfalso; apply H1...

      (* X Add *)
      apply Finite_Empty_or_Inhabited in H0.
      inversion H0; clear H0.
        (* A Empty *)
        exists x...
        unfold Add in H0. 
        apply In_Union in H0. 
        inversion H0; clear H0... 
          rewrite H3 in H5; inversion H5.
        (* A Inhabited *)
        assert (∃ x : carrier, x ∈ A ∧ (∀ y : carrier, y ∈ A → triangle_rest A x y → x = y)) as Q.
          apply IHFinite.
          apply (Included_trans _ (Add A x) _)...
          assumption.
        clear IHFinite.
        inversion Q as [z]; clear Q...
        assert (triangle_rest A z x \/ ~(triangle_rest A z x)) as choice. 
          admit.
        inversion choice; clear choice; [exists x | exists z]... 
          admit.
          unfold Add in H6. 
          apply In_Union in H6. 
          inversion H6; clear H6.  
            apply H5... admit.
            inversion H8; clear H8; subst. 
            exfalso. 
            apply H0... admit.

      (* X Same_set *)
      symmetry in H2.
      assert (∃ x : carrier, x ∈ T ∧ (∀ y : carrier, y ∈ T → triangle_rest T x y → x = y)). 
        apply IHFinite; clear IHFinite; rewrite H2; auto.
      inversion H3 as [z]; clear H3...
      exists z...
      rewrite <- H2...
      apply (H5 y)...
      rewrite H2...
      admit. (* this last is fine really *)
  Qed.

  Lemma less_decidable : forall x y, ((less x y) \/ ~(less x y)).
  Proof with intuition.
    intros.
    assert (Finite (Intersection (plus x) (minus y))).
      apply Finite_Intersection. 
      apply minus_fin.
      apply all_decidable.
    apply Finite_Empty_or_Inhabited in H.
    inversion H; clear H; [right | left]...
      unfold less in H.
      rewrite H0 in H.
      inversion H. 
      inversion H1.
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
    is_a_cell ( (sup M (n - 1)) ∪ (((sub M n) ∪ Minus X) ∩ √(Plus X)) ∪ X, P ∪ X)
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
        crush. crush. crush. 
        assert (dim x <= (n)).
          unfold celldim in *...
        inversion H0; [right | left]... 
          basic... rewrite Sn_minus_1...
    assert (sup P (n - 1) ∪ ((sub M (n) ∪ Minus X) ∩ √Plus X) == P) as PP.
      rewrite MXE, PXE. 
      rewrite Complement_Empty_set. 
      rewrite Empty_set_ident_right. 
      rewrite Full_set_ident_right.
      rewrite (cell_dim_n_property M P).
      unfold sup, sub, Same_set, Included, In...
        crush. crush. crush.
        assert (dim x <= (n)).
          unfold celldim in *...
        inversion H0; [right | left]... 
          basic... rewrite Sn_minus_1...
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

  Lemma Included_Singleton {U : Type} : forall S, @Inhabited U S ->
     forall a, Included S (Singleton a) -> S == (Singleton a).
  Proof with intuition.
    intros.
    unfold Same_set...
    unfold Included...
    inversion H1; clear H1; subst.
    inversion H; clear H.
    assert (x0 ∈ Singleton x). 
    apply H0...
    inversion H...
  Qed.

  Lemma dim_0_Singleton : forall S, Inhabited (sub S 0) -> well_formed S ->
    exists d, sub S 0 == Singleton d. 
  Proof with intuition.
    intros.
    inversion H; clear H.
    exists x.
    unfold Same_set, Included...
    assert (x = x0).
    unfold well_formed in H0...
    repeat subsuptac.
    apply H2...
    subst...
    inversion H... subst...  
  Qed.

  Lemma dim_0_Inhabited : forall M P, (is_a_cell (M, P)) -> Inhabited (sub M 0).
  Proof with intuition.
    unfold is_a_cell...

    assert (forall k, sub M k == Empty_set -> sub M (S k) == Empty_set)...
      assert (Inhabited (sub M (S k)) -> Inhabited (sub M k)). 
        intros.
        assert (Finite (MinusPlus (sub M (S k)))). admit.
        apply Finite_Empty_or_Inhabited in H9.
        inversion H8...
          exfalso. 
          (* Find minimum in sub M (S k) and this belongs in (MinusPlus (sub M)) *)
          admit.
          inversion H11 as [t L]; exists t... (* fine *) admit.
      assert (Finite (sub M (S k))). admit. 
      apply Finite_Empty_or_Inhabited in H9.
      inversion H9... 
        inversion H9 as [h j].
        rewrite H6 in j; inversion j. 
    assert (Finite (sub M 0)). admit. 
    apply Finite_Empty_or_Inhabited in H8.
      inversion H8; clear H8...
    exfalso.
    assert (forall j, sub M j == Empty_set); intros.
      induction j...
    assert (M == Empty_set); unfold Same_set, Included...
      assert (In (sub M (dim x)) x); unfold sub...
        rewrite <- (H8 (dim x))...
      inversion H10.
    inversion H0. rewrite H10 in H11. inversion H11.
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
      assert (exists d, sub M 0 == Singleton d).
      apply dim_0_Singleton. 
      eapply dim_0_Inhabited. apply MPcell.
      apply MPcell. inversion H as [f L]; clear H.
      assert (plus x == Singleton f). apply Included_Singleton.
      apply plus_non_empty. rewrite dimx...
      rewrite <- L.
      assert (PlusMinus X == plus x). 
      unfold PlusMinus. rewrite Xsing.
      assert (Plus (Singleton x) ∩ √Minus (Singleton x) == PlusMinus (Singleton x)).
      unfold PlusMinus...
      rewrite H.
      rewrite PlusMinus_Singleton...
      rewrite <- H... rewrite <- H in L...
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

  Lemma Finite_sup_n : forall M, Finite M -> forall n, Finite (sup M n).
  Proof with intuition.
    intros.
    apply (Finite_Included'' M)...
    unfold sup, Included, In...
    assert ({dim x <= n} + {n < dim x}). apply le_lt_dec.
    inversion H1; clear H1; [left | right]. 
      unfold sup... 
      intros. unfold lt in H2. unfold sup, In in H1... 
      apply (le_Sn_n n). apply (le_trans _ (dim x))...
  Qed.

  Lemma Finite_sub_n : forall M, Finite M -> forall n, Finite (sub M n).
  Proof with intuition.
    intros.
    apply (Finite_Included'' M)...
    unfold sub, Included, In...
    assert ({eq_nat n (dim x)} + {~ eq_nat n (dim x)}). 
      apply eq_nat_decide.
    inversion H1; clear H1; [left | right]...
      apply eq_nat_is_eq in H2...
      apply H2. 
      apply eq_nat_is_eq...
  Qed.

  Lemma Finite_Minus : forall X, Finite X -> Finite (Minus X).
  Proof with intuition.
    intros.
    induction H.
    
    assert (Minus Empty_set == Empty_set).
      unfold Same_set, Minus, Included, In... inversion H...
    rewrite H.
    apply Empty_is_finite.
    
    unfold Add.
    rewrite Minus_Union_compat. 
    rewrite Union_sym. 
    apply Finite_Union... 

    rewrite H0...
  Qed.

  Hint Resolve Finite_sub_n Finite_sup_n Finite_Minus.

  Lemma asdf : forall S T m, Included (S) (sub T m) -> forall x, (In S x -> dim x = m). 
  Proof with crush. 
    unfold setdim...
    apply H...
  Qed.

  Lemma asdf' : forall S m x, In (sub S m) x -> (dim x = m). 
  Proof with crush. 
    crush. 
  Qed.

  Hint Extern 1 (dim _ = _) => 
    match goal with 
      | H: ?X ⊆ (sub _ (?n)), _: In ?X ?x |- (dim ?x = ?n) => apply (asdf _ _ _ H)
      | H: In (sub _ ?n) ?x |- (dim ?x = ?n) => apply (asdf' _ _ _ H) 
      | H: dim ?x = S ?n, K: In (minus ?x) ?y |- (dim ?y = ?n) =>
          apply minus_dim in K; rewrite H in K; inversion K; trivial
    end.

  Lemma asdf'' : forall S m x, In (sup S m) x -> (dim x <= m). 
  Proof with crush. 
    crush. 
  Qed.

  Hint Extern 1 (dim _ <= _) => match goal with | H: In (sup _ ?n) ?x |- (dim ?x <= ?n) => apply (asdf'' _ _ _ H) end.

  Lemma qwer   : forall n, (n-1 <= n). Admitted.
  Lemma qwer'  : forall n, (n-1 <  n). Admitted.
  Lemma qwer'' : forall n, (n <= n-1) -> False. Admitted.

  Hint Resolve asdf asdf' asdf'' qwer qwer' qwer'' le_Sn_n n_Sn.

  Lemma Lemma_3_2_Step_1' :
    forall n m, (Lemma_3_2_b_st n m) -> (Lemma_3_2_c_st n m).
  Proof with intuition.
    unfold Lemma_3_2_b_st, Lemma_3_2_c_st. 
    intros n m Hyp1 X Xcard M P J K. 
    assert (Finite X) as XFin. apply (cardinal_are_Finite m)...
    set (Y := ((sub M n ∪ Minus X) ∩ √Plus X))...
    assert (is_a_cell
               (sup M (n - 1) ∪ ((sub M n ∪ Minus X) ∩ √Plus X),
                sup P (n - 1) ∪ ((sub M n ∪ Minus X) ∩ √Plus X))
             ∧ Minus X ∩ sub M n == Empty_set) as Hyp2.
    apply Hyp1...
    intuition. 
    unfold is_a_cell in *... 
    
    apply (Inhabited_Included (sup M (n - 1) ∪ Y)). assumption. 
    apply Union_Included_cancel_right. reflexivity.

    apply (Inhabited_Included (P)). assumption. 
    apply Union_Included_cancel_right. reflexivity.
      
    (* This whole argument is predicated on the fact that both parts of the union are
       well-formed and that the intersection is (dimenion-wise) empty *)
    unfold well_formed in *...
    apply In_Union in H28... 
    apply In_Union in H29... 
      exfalso. assert (dim y = S n)...
      rewrite H27 in H29. inversion H29.
    apply In_Union in H29... 
      exfalso. assert (dim x = S n)...
      rewrite H26 in H29. inversion H29.
    apply In_Union in H26...
    apply In_Union in H27...
      eapply H23... apply H11. assumption.
      exfalso. 
      assert (dim y = S n)...
      apply In_Union in H30...
        assert (dim x <= n). apply (le_trans _ (n-1))...    
        eauto.
        rewrite H11, <- H28, H27 in H30. apply (le_Sn_n n)... 
        assert (dim x = n). unfold Y in H31. 
        apply In_Intersection in H31... 
        apply In_Union in H30... eauto.
        inversion H31... assert (dim x0 = S n)... 
        rewrite H11, <- H28, H27 in H30... symmetry in H30. apply (n_Sn n)... 
    apply In_Union in H27...
      exfalso. 
      assert (dim x = S n)... 
      apply In_Union in H26...
        assert (dim y <= n). apply (le_trans _ (n-1))...    
        eauto.
        rewrite H28, <- H11, H27 in H26. apply (le_Sn_n n)... 
        assert (dim y = n). unfold Y in H31. 
        apply In_Intersection in H31... 
        apply In_Union in H26... eauto.
        inversion H31... assert (dim x0 = S n)...
        rewrite H28, <- H11, H27 in H26... symmetry in H26. apply (n_Sn n)... 
        eapply H21... apply H11. trivial. 

    (* as above *)
    unfold well_formed in *...
    apply In_Union in H28... 
    apply In_Union in H29...
      assert (dim y = S n)... 
      rewrite H27 in H29. inversion H29.
    apply In_Union in H29...
      assert (dim x = S n)... 
      rewrite H26 in H29. inversion H29.
    apply In_Union in H26... 
    apply In_Union in H27...
      eapply (H24)... apply H11. trivial. 
      exfalso. 
      assert (dim y = S n)... 
      assert (dim x <= n)... assert (dim x = S n)... rewrite H11, <- H28...
      rewrite H32 in H31... apply (le_Sn_n n)...
    apply In_Union in H27...
      exfalso. assert (dim y <= n)... assert (dim x = S n). eauto.
      assert (dim y = S n). rewrite H28, <- H11, H31... rewrite H32 in H27; apply (le_Sn_n n)...
      eapply H21... apply H11. trivial.
      
    apply Finite_Union... 
    apply Finite_Union...
 
  Admitted.


 Hint Constructors cardinal Finite. 

  Lemma maximal_exists' : (forall X, Finite X -> well_formed X -> exists x, In X x /\ Disjoint (plus x) (Minus X)).
  Admitted.

  Lemma cardinal_minus_1 {U : Type} : forall m X, cardinal X (S m) -> forall (x : U), In X x -> cardinal (Intersection X (Complement (Singleton x))) m.
  Admitted.

  Lemma Lemma_3_2_Step_2' :
    forall n, ((Lemma_3_2_b_st n 1) -> (forall m, Lemma_3_2_b_st n (S m))).
  Proof with intuition.
    intros n hypothesis_for_1 m.

    induction m. assumption.
 
    unfold Lemma_3_2_b_st in *. 
    intros X Xcard M P H J.
    inversion H as [MPcell MPdim]; clear H.
    inversion J as [Xdim K]; clear J.
    inversion K as [Xwf Xcond]; clear K.

    assert (exists x, In X x /\ Disjoint (plus x) (Minus X)) as R.  (* maximal *)
      apply maximal_exists'...
      apply (cardinal_are_Finite (S (S m)))...
    inversion R as [x xcond]; clear R. 
    inversion xcond as [xinX disj]; clear xcond.

    assert (dim x = S n) as dimx...

    assert (plus x ⊆ sub M n) as K. 
      apply (Included_trans _ (PlusMinus X))...
        unfold PlusMinus. rewrite <- (Intersection_idemp (plus x)).
        apply Intersection_Included_compat...
          unfold Included, Plus, In... exists x...
        apply Disjoint_property_left...

    assert (is_a_cell
                 (sup M (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x)),
                 sup P (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x)))
               ∧ Minus (Singleton x) ∩ sub M n == Empty_set).
        apply hypothesis_for_1...
        apply cardinality_Singleton_is_one.
        unfold Included... inversion H; subst... 
        rewrite PlusMinus_Singleton...
    inversion H as [LA LB]; clear H.
    
    set (N :=  sup M (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x))).
    set (Q :=  sup P (n - 1) ∪ ((sub M n ∪ Minus (Singleton x)) ∩ √Plus (Singleton x))). 
    set (Z := Intersection X (Complement (Singleton x))).
    set (Y' := (sub N n ∪ (Minus Z)) ∩ √Plus Z).
    set (Y  := (sub M n ∪ (Minus X)) ∩ √Plus X). 
    assert (X == Union (Singleton x) Z) as XZrel. 
      unfold Z. 
      rewrite Union_sym. rewrite U_I_dist_r. 
      rewrite Full_set_property. rewrite Full_set_ident_right. 
      unfold Same_set, Included... apply In_Union in H... inversion H0. rewrite <- H...
      intuition. 

    assert (is_a_cell ((sup N (n - 1)  ∪ Y'), (sup Q (n - 1) ∪ Y')) /\ Minus Z ∩ sub N n == Empty_set) as AA.
      eapply (IHm Z).
        apply cardinal_minus_1...

        split. 
        assumption.

        unfold celldim, N, Q, setdim...
          apply In_Union in H...
          apply In_Union in H0...
            eapply (le_trans _ (n-1))...
          apply In_Intersection in H...
          apply In_Union in H0...
          assert (dim x0 = n)... rewrite H0...
          rewrite (Minus_Singleton x) in H.
          apply minus_dim in H. apply le_S_n. rewrite H. rewrite dimx...
          apply In_Union in H0...
            eapply (le_trans _ (n-1)). repeat subsuptac... idtac...
          apply In_Intersection in H...
          apply In_Union in H0...
          assert (dim x0 = n)... rewrite H0...
          rewrite (Minus_Singleton x) in H.
          apply minus_dim in H. apply le_S_n. rewrite H. rewrite dimx...

        split.
        apply (Included_trans _ X _). unfold Z. 
        apply Intersection_Included_cancel_right... assumption.

        split.
        unfold Z. apply (well_formed_Included X)...
        apply Intersection_Included_cancel_right...

        assert (sub N n == Intersection (Union (sub M n) (minus x)) (Complement (plus x))) as JA.
            unfold N. 
            rewrite sub_Union.
            rewrite sub_Intersection. rewrite sub_Union.
            rewrite sub_sup_Empty_set... rewrite Empty_set_ident_left...
            rewrite sub_idemp.
            rewrite Minus_Singleton.
            rewrite Plus_Singleton.
            unfold Same_set, Included;
              repeat basic...
              right. 
              repeat subsuptac... 
              repeat subsuptac... 
              repeat subsuptac... 
        assert (PlusMinus Z ⊆ Intersection (Union (PlusMinus X) (minus x)) (Complement (plus x))) as JB. 
          unfold PlusMinus.
          rewrite XZrel.
          rewrite Plus_Union_compat. 
          rewrite Minus_Union_compat.
          rewrite Plus_Singleton. 
          rewrite Minus_Singleton.
          rewrite <- Union_Complement_compat.
          unfold Included; repeat (basic; intuition). 
          assert ((In (minus x) x0) \/ ~(In (minus x) x0))... 
            assert (Finite (minus x))... assert (decidable (minus x))... apply H3. 
            apply In_Complement; unfold not... 
            unfold Plus, Z, In at 1 in H1. 
            inversion H1 as [d SS]...
            apply In_Intersection in H3...
            unfold well_formed in Xwf...
            assert (x = d). 
            eapply H7... apply dimx. intuition. unfold perp in H8... 
            assert (In Empty_set x0). rewrite <- H9. apply In_Intersection... inversion H8. rewrite H8 in H6. 
            apply In_Complement in H6; unfold not in H6... 
        
      rewrite JA, JB.
        apply Intersection_Included_compat...
        apply Union_Included_compat...

      assert (sup N (n-1) == sup M (n-1)) as J1.
        unfold N.
        rewrite Minus_Singleton, Plus_Singleton.
        rewrite sup_Union, sup_idemp.
        unfold Same_set, Included...
          apply In_Union in H1... 
        repeat subsuptac...
        apply In_Intersection in H1... 
        apply In_Union in H2... 
        repeat subsuptac...
        apply minus_dim in H1. rewrite dimx in H1. inversion H1. 
        rewrite H5 in H3. exfalso... eauto.

      assert (sup Q (n-1) == sup P (n-1)) as J2.
        unfold Q.
        rewrite Minus_Singleton, Plus_Singleton.
        rewrite sup_Union, sup_idemp.
        unfold Same_set, Included...
          apply In_Union in H1... 
        repeat subsuptac...
        apply In_Intersection in H1... 
        apply In_Union in H2... 
        assert (dim x0 = n)...  rewrite H2 in H3. exfalso. eauto. 
        apply minus_dim in H1. rewrite dimx in H1. inversion H1. 
        rewrite H5 in H3. exfalso... eauto.

      assert (Y == Y') as J3. 
        unfold Y, Y', N.    
        rewrite XZrel.
        rewrite Minus_Union_compat.
        rewrite Plus_Union_compat.
        rewrite <- Union_Complement_compat.
        rewrite sub_Union. 
        rewrite sub_sup_Empty_set...
        rewrite Empty_set_ident_left.
        rewrite sub_Intersection. rewrite sub_Union. rewrite sub_idemp. rewrite sub_Minus.
        rewrite <- Intersection_trans.
        rewrite <- Union_trans.
        rewrite I_U_dist_r.
        assert (sub (Singleton x) (S n) == (Singleton x)) as WW. 
          unfold Same_set, Included... subsuptac... subsuptac...
          inversion H1. rewrite <- H2...
        rewrite WW. clear WW.
        rewrite Minus_Singleton, Plus_Singleton.
          unfold Same_set, Included... 
            repeat (basic; intuition). 
            left... left... 
            repeat (basic; intuition). 
            left... apply In_Intersection... repeat subsuptac...
            left... apply In_Intersection... repeat subsuptac...
            right... apply In_Intersection... 
            unfold Z in H1. unfold Minus, In at 1 in H1. 
            inversion H1 as [z T]; clear H1... 
            apply In_Complement; unfold not... 
            assert (less x z). exists x0... admit. (* x is maximal *)
      eapply is_a_cell_Same_set_compat. 
      rewrite <- J1, J3. reflexivity.   
      rewrite <- J2, J3. reflexivity.
      apply AA.

      (* it relies on the fact that ((sub M n) ∩ (minus x)) is empty, but why should it be? *)
   admit.

 Qed.

  Lemma sub_Sn_sup_n : forall M n, (Union (sub M (S n)) (sup M n)) == sup M (S n).
  Proof with intuition.
   crush. 
   rewrite H0; crush.
   inversion H1; clear H1; [left | right]; crush.
  Qed.

    Lemma well_formed_Union : 
      forall A, well_formed A ->
      forall B, well_formed B ->
        (forall x y, x ∈ A /\ y ∈ B -> ~ (dim x = dim y)) ->
        well_formed (Union A B).
    Proof with intuition.
      unfold well_formed...
        inversion H7; clear H7; subst...
        inversion H8; clear H8; subst...
          exfalso; apply (H2 x y)... rewrite H5, H6... 
        inversion H8; clear H8; subst...
          exfalso; apply (H2 y x)... rewrite H5, H6...
        inversion H5; clear H5; subst...
        inversion H6; clear H6; subst...
          eapply H1... apply H... assumption. 
          exfalso; apply (H2 x y)... rewrite H, H7...
        inversion H6; clear H6; subst...
          exfalso; apply (H2 y x)... rewrite H, H7...
          eapply H4... apply H... assumption.
    Qed.

  Hint Constructors Singleton.

  Lemma target_dim : forall M P, is_a_cell (M, P) -> forall m, 
    celldim (target m (M, P)) m.
  Proof with intuition.
    intros...
    unfold target, celldim, setdim...
    repeat (basic; intuition).
    assert (dim x = m)... rewrite H1...
    apply (le_trans _ (m-1))...
  Qed.

  Lemma source_dim : forall M P, is_a_cell (M, P) -> forall m, 
    celldim (source m (M, P)) m.
  Proof with intuition.
    intros...
    unfold source, celldim, setdim...
    repeat (basic; intuition).
    assert (dim x = m)... rewrite H1...
    apply (le_trans _ (m-1))...
  Qed.

  Hint Constructors Full_set.

  Lemma Lemma_3_2_Step_3' :
    forall n, (forall m , Lemma_3_2_b_st (n - 1) m) -> (Lemma_3_2_b_st n 1).  
  Proof with intuition.
    intros n Hyp1.

    induction n.
    (* n = 0 *)
    apply Lemma_3_2_b_0_1.

    (* n > 0 *)
    assert (S n - 1 = n) as II. simpl. symmetry. apply minus_n_O. 
    rewrite II in *. clear II.
    intros X Xcard M P K L.
    inversion K as [MPcell MPdim]; clear K.
    inversion L as [Xdim J]; clear L.
    inversion J as [Xwf Xcond]; clear J.
    assert (Finite X) as XFin. apply (cardinal_are_Finite 1)...

    apply cardinality_one_Singleton in Xcard.
    inversion Xcard as [x Xsing]; clear Xcard.
    assert (In X x) as xinX. rewrite Xsing...

    assert (plus x ⊆ sub M (S n)) as plusxdim.
      assert (PlusMinus X == plus x) as K. 
        unfold PlusMinus. rewrite Xsing. 
        rewrite Plus_Singleton, Minus_Singleton. 
        apply Intersection_Included_left. apply Disjoint_property_left.
        apply plus_minus_disjoint.
      rewrite <- K... 
    set (Y := (sub M (S n) ∪ Minus X) ∩ √Plus X).

    set (S' := (fun z => exists w, In (plus x) x /\ triangle_rest (sub M (S n)) z w /\ ~(In (sub M (S n)) z))).
    set (T  := Setminus (sub M (S n)) S'). 
    assert ((sub M (S n)) == S' ∪ (plus x) ∪ T) as DisjUnion. admit.
    assert (Disjoint (sub M (S n)) S') as DisjMS'. admit.
    assert (Disjoint (sub M (S n)) T) as DisjMT. admit.
    assert (Disjoint T S') as DisjTS'. admit.
    assert (is_initial_segment S' (sub M (S n))) as S'initial. admit.
    assert (is_final_segment T (sub M (S n))) as Tfinal. admit.
    assert (Finite T) as TFin. admit.
    assert (Finite S') as S'Fin. admit.
    set (A := @Full_set carrier).
    set (B := @Full_set carrier).
    assert (S' moves (sub M n) to A) as moves1. admit.
    assert ((plus x) moves A to B) as moves2. admit.
    assert (T moves B to (sub P n)) as moves3. admit.

    assert (dim x = S (S n)) as xdim.... apply Xdim in xinX.

    set (tM := sub P (n) ∪ sup M (n - 1)).
    set (tP := sup P (n)).
    assert (is_a_cell (tM, tP)) as tMPcell.
      unfold tM, tP. apply target_is_a_cell... 
    assert (celldim (tM, tP) (n)) as tMPdim. 
      apply target_dim...
(*
    assert (is_a_cell ((sup M (n - 1) ∪ B ∪ T          , sup P (n) ∪ T))        ).
    assert (is_a_cell ((sup M (n - 1) ∪ B              , sup P (n - 1) ∪ B))    ).
    assert (is_a_cell ((sup M (n - 1) ∪ A ∪ (plus x)   , sup P (n) ∪ (plus x))) ).
    assert (is_a_cell ((sup M (n - 1) ∪ A              , sup P (n - 1) ∪ A))    ).
    assert (is_a_cell ((sup M (n - 1) ∪ (sub M n) ∪ S' , sup P (n) ∪ S'))       ).
    assert (is_a_cell ((sup M (n - 1) ∪ (sub M n)      , sup P (n - 1) ∪ (sub M n))) ).
  *)  
    assert (B == ((sub tM n) ∪ Minus T) ∩ √Plus T) as Bdef.
      assert (sub tM n == sub P n) as K. 
        unfold tM. 
        rewrite sub_Union. rewrite sub_idemp. rewrite sub_sup_Empty_set...
      rewrite K. 
      apply moves3.
    
    assert (exists mT, cardinal T mT). apply cardinality_exists. assumption.
      inversion H as [mT Tcard]; clear H.
    
    assert (is_a_cell ((sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) ∪ T, tP ∪ T)) as T1.
      eapply (Lemma_3_2_Step_1' _ mT)...
      unfold Included... subsuptac... 
      assert (In (sub M (S n)) x0). rewrite DisjUnion. right...
      subsuptac...
      apply (well_formed_Included M)... apply MPcell.
      apply (Included_trans _ ((S' ∪ plus x) ∪ T))... 
      rewrite <- DisjUnion... 
      unfold tM.
      rewrite sub_Union. left. rewrite sub_idemp.
      assert (PlusMinus T ⊆ (sub P n)). apply Prop_2_1_dual... 
      exists B... apply H0...

    assert (is_a_cell ((sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)  , sup tP (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T))) 
       /\ (Minus T) ∩ sub tM n == Empty_set) as T2.
      apply (Hyp1 mT)...
      unfold Included... subsuptac... 
      assert (In (sub M (S n)) x0). rewrite DisjUnion. right...
      subsuptac...
      apply (well_formed_Included M)... apply MPcell.
      apply (Included_trans _ ((S' ∪ plus x) ∪ T))... 
      rewrite <- DisjUnion... 
      unfold tM.
      rewrite sub_Union. left. rewrite sub_idemp.
      assert (PlusMinus T ⊆ (sub P n)). apply Prop_2_1_dual... 
      exists B... apply H0...

    assert (exists mplusx, cardinal (plus x) mplusx). 
      apply cardinality_exists...
      inversion H as [mplusx plusxcard]; clear H.

    assert (is_a_cell ((sup ((sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) ∪ T) (n - 1) ∪ ((sub ((sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) ∪ T) n ∪ Minus (plus x)) ∩ √Plus (plus x))) ∪ (plus x), (tP ∪ T) ∪ (plus x))) as plusx1.
      eapply (Lemma_3_2_Step_1' _ (mplusx))... 
      admit.
      unfold Included... 
      rewrite <- Bdef.
      assert (sub ((sup tM (n - 1) ∪ B) ∪ T) n == B). admit.
      rewrite H1.
      apply Prop_2_1_dual...
      exists A...  

    assert (is_a_cell
               (sup (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1) ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n ∪ Minus (plus x)) ∩ √Plus (plus x)),
               sup (sup tP (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1) ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n ∪ Minus (plus x)) ∩ √Plus (plus x)))
             ∧ Minus (plus x) ∩ sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n == Empty_set) as plusx2.
      eapply Hyp1...
      apply plusxcard.
      admit.
      unfold Included... 
      rewrite <- Bdef.
      assert (sub ((sup tM (n - 1) ∪ B)) n == B). admit.
      rewrite H1.
      apply Prop_2_1_dual...
      exists A...  
    
    assert (A == (B ∪ Minus (plus x)) ∩ √Plus (plus x)) as Adef. apply moves2. 

    assert (exists mS', cardinal S' mS'). 
      apply cardinality_exists...
    inversion H as [mS' S'card]; clear H.

    assert (is_a_cell
        ((sup (sup (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1)
            ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n
                ∪ Minus (plus x)) ∩ √Plus (plus x))) (n - 1) ∪ ((sub (sup (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1)
            ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n
                ∪ Minus (plus x)) ∩ √Plus (plus x))) n ∪ Minus S') ∩ √Plus S')) ∪ S', (sup (sup tP (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1)
           ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n
               ∪ Minus (plus x)) ∩ √Plus (plus x))) ∪ S')) as S'1.
      apply (Lemma_3_2_Step_1' _ mS')...
      admit. 
      unfold Included... subsuptac...
      assert (In (sub M (S n)) x0). rewrite DisjUnion. left; left...
      subsuptac...
      apply (well_formed_Included M)...       apply MPcell.
      apply (Included_trans _ ((S' ∪ plus x) ∪ T))... 
      rewrite <- DisjUnion...
      rewrite <- Bdef.
      unfold Included; intros. 
      rewrite sub_Union at 1. right.
      assert (PlusMinus S' ⊆ A). apply Prop_2_1_dual...
      exists (sub M n)... apply H4 in H3; clear H4.
      rewrite Adef in H3...
      unfold sub at 1, In at 1...  assert ((sub (sup tM (n - 1) ∪ B) n == B)). admit.
      rewrite H4... admit. 

    assert (is_a_cell
        (sup (sup (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1)
            ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n
                ∪ Minus (plus x)) ∩ √Plus (plus x))) (n - 1) ∪ ((sub (sup (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1)
            ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n
                ∪ Minus (plus x)) ∩ √Plus (plus x))) n ∪ Minus S') ∩ √Plus S'),
        sup (sup (sup tP (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1)
           ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n
               ∪ Minus (plus x)) ∩ √Plus (plus x))) (n - 1) ∪ ((sub (sup (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1)
            ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n
                ∪ Minus (plus x)) ∩ √Plus (plus x))) n ∪ Minus S') ∩ √Plus S'))
      ∧ Minus S' ∩ sub (sup (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) (n - 1)
            ∪ ((sub (sup tM (n - 1) ∪ ((sub tM n ∪ Minus T) ∩ √Plus T)) n
                ∪ Minus (plus x)) ∩ √Plus (plus x))) n == Empty_set)
    as S'2.
      eapply Hyp1...
      apply S'card.
      admit.
      unfold Included... subsuptac...
      assert (In (sub M (S n)) x0). rewrite DisjUnion. left; left...
      subsuptac...
      apply (well_formed_Included M)...       apply MPcell.
      apply (Included_trans _ ((S' ∪ plus x) ∪ T))... 
      rewrite <- DisjUnion...
      rewrite <- Bdef.
      rewrite sub_Union.
      rewrite sub_sup_Empty_set... rewrite Empty_set_ident_left.
      assert (sub ((sub (sup tM (n - 1) ∪ B) n ∪ Minus (plus x)) ∩ √Plus (plus x)) n == (B ∪ Minus (plus x)) ∩ √Plus (plus x)).
      admit. rewrite H3. rewrite <- Adef.
      apply Prop_2_1_dual...
      exists (sub M n)...

    assert ((minus x) moves A to B) as moves4.
      apply Prop_3_1. assumption. admit. (* receptivity condition? *)

    assert ((S' ∪ (minus x)) moves (sub M n) to B) as moves5.
    eapply Prop_2_3. apply moves1. assumption. 
     (* big lot of work here *) admit.

    assert (((minus x) ∪ T) moves A  to (sub P n)) as moves6.
    eapply Prop_2_3. apply moves4. assumption. 
     (* big lot of work here *) admit.

    assert (((S' ∪ (minus x)) ∪ T) moves (sub M n) to (sub P n)) as moves7.
      eapply Prop_2_3. apply moves5. assumption.
      apply Disjoint_intersection_condition.
      rewrite Minus_Union_compat.
      rewrite I_U_dist_r.
      (* first empty because S initial and T final *) 
      (* second was proved when we did moves6 *)
      admit.

    assert (well_formed (S' ∪ (minus x))) as WF1.
      (* disjoint union, so enough to show each part WF *)
      (* well_formed S' because subset of M *)
      (* well_formed (minus x) by axiom *) 
      admit.

    assert (well_formed ((minus x) ∪ T)) as WF2.
      (* disjoint union, so enough to show each part WF *)
      (* well_formed T because subset of M *)
      (* well_formed (minus x) by axiom *) 
      admit.

    assert (well_formed ((S' ∪ minus x) ∪ T)) as WF3.
      (* disjoint union, so enough to show each part WF *)
      admit.

    assert (Y == (S' ∪ minus x) ∪ T) as Ycond.
      unfold Y. 
      rewrite DisjUnion. 
      rewrite Xsing.
      rewrite Minus_Singleton, Plus_Singleton.
      repeat (rewrite I_U_dist_r).
      (* all of these are empty, or the not plus goes away by disjointness *)
      admit. 

    unfold is_a_cell...

    (* Y Should be inhabited because (minus x) is inhabited *) 
    rewrite Ycond. apply (Inhabited_Included (minus x)). 
      apply minus_non_empty. rewrite xdim. admit. 
      unfold Included; intros; right;left;right...

    (* Y Should be inhabited because (minus x) is inhabited *) 
    rewrite Ycond. apply (Inhabited_Included (minus x)). 
      apply minus_non_empty. rewrite xdim. admit. 
      unfold Included; intros; right;left;right...

    apply well_formed_Union... 
    apply (well_formed_Included M). 
    apply MPcell. idtac...
    rewrite Ycond...
    unfold Y in H8. rewrite (Sn_minus_1 n) in H7. assert (dim x0 <= n)... 
    apply In_Intersection in H8...
    apply In_Union in H9...
    assert (dim y = S n)... rewrite H6, H9 in H5... apply le_Sn_n in H5...
    assert (dim y = S n)... unfold Minus, In at 1 in H8... inversion H8; clear H8... 
    assert (dim x1 = S (S n))... rewrite H6, H9 in H5... apply le_Sn_n in H5...

    apply well_formed_Union... 
    apply (well_formed_Included P). 
    apply MPcell. idtac...
    rewrite Ycond...
    unfold Y in H8. rewrite (Sn_minus_1 n) in H7. assert (dim x0 <= n)... 
    apply In_Intersection in H8...
    apply In_Union in H9...
    assert (dim y = S n)... rewrite H6, H9 in H5... apply le_Sn_n in H5...
    assert (dim y = S n)... unfold Minus, In at 1 in H8... inversion H8; clear H8... 
    assert (dim x1 = S (S n))... rewrite H6, H9 in H5... apply le_Sn_n in H5...

    rewrite (Sn_minus_1 n). 
    rewrite Ycond... 
    repeat (apply Finite_Union)...
    apply Finite_sup_n... apply MPcell.

    rewrite (Sn_minus_1 n). 
    rewrite Ycond... 
    repeat (apply Finite_Union)...
    apply Finite_sup_n... apply MPcell.

    (* there is some condition about splitting dimensions that should make this work *)
    admit. 
    admit.

    rewrite Xsing. rewrite Minus_Singleton.
    rewrite DisjUnion.
    repeat (rewrite I_U_dist_l).
    (* second is obvious *)
    (* first and third not so clear *)
    admit.
  Qed.

  Lemma Lemma_3_2_b_0_m :
    forall m, (Lemma_3_2_b_st 0 m).
  Proof with intuition. 
    unfold Lemma_3_2_b_st. 
    intros.
    assert (exists z, (sub M 0) == Singleton z).
      apply dim_0_Singleton.
      eapply dim_0_Inhabited. apply H0. apply H0.
    inversion H2 as [z K]; clear H2.
    assert (PlusMinus X == Singleton z). 
      admit. (* ???? *) 

    split.

    assert (sup M (0 - 1) == Empty_set) as JA. admit. (* error, sort this out later *)
    assert (sup P (0 - 1) == Empty_set) as JB. admit. (* error, sort this out later *)
    assert ((sub M 0) ∩ √(Plus X) == Empty_set). 
      unfold Same_set, Included...
      exfalso. apply In_Intersection in H5... 
      rewrite K in H7; inversion H7; clear H7.
      assert (In (PlusMinus X) x).
        rewrite <- H5, H2... unfold PlusMinus in H7. apply In_Intersection in H7...
      inversion H5.
    assert (exists w, MinusPlus X == Singleton w). admit. (* ???? *)
    inversion H4 as [w E]; clear H4.
    assert (dim w = 0). admit. (* ???? *)
    apply (Same_set_is_a_cell (Singleton w) (Singleton w)). 
    unfold is_a_cell...
      exists w...
      exists w...
      unfold moves_def. 
        split; rewrite Plus_Singleton, Minus_Singleton, plus_zero, minus_zero, Empty_set_ident_right, Complement_Empty_set, Full_set_ident_right...
      unfold moves_def. 
        split; rewrite Plus_Singleton, Minus_Singleton, plus_zero, minus_zero, Empty_set_ident_right, Complement_Empty_set, Full_set_ident_right...
     
    rewrite JA, I_U_dist_r, H3, <- E, Empty_set_ident_left, Empty_set_ident_left...

    rewrite JB, I_U_dist_r, H3, <- E, Empty_set_ident_left, Empty_set_ident_left...

    unfold Same_set, Included...
      exfalso.
      apply In_Intersection in H5...
      rewrite K in H8. rewrite <- H2 in H8. unfold PlusMinus in H8.
    apply In_Intersection in H8...
    inversion H5... 
  Qed. 

  Lemma Lemma_3_2_b :
    forall n m, (Lemma_3_2_b_st n m).
  Proof.
    intros n.
    induction n.
      apply Lemma_3_2_b_0_m.
    destruct m.
      apply Lemma_3_2_b_n_0.
    apply Lemma_3_2_Step_2'.
    apply Lemma_3_2_Step_3'.
    simpl. rewrite <- (minus_n_O).
    apply IHn.
  Qed.
 
  Lemma all_receptive : (forall M P : Ensemble carrier, is_a_cell (M, P) -> cell_receptive (M, P)).
  Admitted.  

  Lemma Lemma_3_2_c :
    forall n m, (Lemma_3_2_c_st n m).
  Proof.
    intros.
    apply Lemma_3_2_Step_1'.
    apply Lemma_3_2_b.
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
  Proof with intuition.
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
        admit. admit.
    
    assert ((sub P (S m)) == (sub (pi u) (S m)) ∪ ((sub M (S m)) ∩ (sub P (S m)))) as Pcond. 
      admit. 

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
        apply In_Union in OOO; inversion OOO...
        inversion yismax as [QQQ WWW]; clear yismax. unfold In, Y in QQQ. 
        inversion QQQ as [OOO IIII]; clear QQQ. rewrite Mcond in OOO.
        apply In_Union in OOO; inversion OOO... 
    clear ASD.

    assert ((minus x ⊆ sub M m) /\ (plus y ⊆ sub P m)) as specialcond. split.
      cut (minus x ⊆ sub (MinusPlus M) m); intros. apply (Included_trans _ _ _ H).
      eapply (sub_Included_compat). eapply Prop_2_1.
      apply cellcond. exists P. apply cellcond. 
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

    inversion xory; clear xory.
      (**)
      set (R := (P ∩ (√(Singleton x)))).
      set (L := ((M ∩ √(Singleton x)) ∪ plus x) ∩ √minus x).
      set (Q := ((((sub M m) ∪ (plus x)) ∩ √(minus x))) ∪ (sup P (m-1)) ∪ (Singleton x)).
      set (N := ((sup M m) ∪ ((Singleton x)))).
      exists N. exists Q. exists L. exists R. exists m. 
      split. 
        unfold N, Q. 
        admit.
      split.
        unfold L, R. 
        admit.
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
      split.
        unfold N, Q. admit.


      (* L and R case *)
      assert (dim y = S m) as ydim.
        inversion yismax; clear yismax.
        unfold Y, In, sub in H2. apply H2.

      split.
        unfold L, R.  
        apply (Same_set_is_a_cell ((sup M (m - 1) ∪ ((sub P m ∪ Minus (Singleton y)) ∩ √Plus (Singleton y))) ∪ Singleton y)
  (sup P m ∪ Singleton y))... 
        apply (Same_set_is_a_cell ((sup (sup M (m - 1) ∪ sub P m) (m - 1)
    ∪ ((sub (sup M (m - 1) ∪ sub P m) m ∪ Minus (Singleton y))
       ∩ √Plus (Singleton y))) ∪ Singleton y) (sup P m ∪ Singleton y))... 
        apply (Lemma_3_2_c _ 1). 
        apply cardinality_Singleton_is_one. 
        split. remember (target_is_a_cell m M P cellcond). unfold target in i.
        apply (Same_set_is_a_cell _ _ i). apply Union_sym. reflexivity.
        unfold celldim, setdim...
          inversion H8; clear H8; subst.
          inversion H9; clear H9; subst.
          apply (le_trans _ (m-1)). apply H8. admit.
          unfold sub, In at 1 in H8...
          rewrite H10; left. 
          apply H9.
        split.
        unfold Included... 
          inversion H8; clear H8; subst.
          unfold In, sub... 
          constructor.
        split.
        apply well_formed_Singleton.
        rewrite sub_Union.
        rewrite sub_idemp.
        rewrite sub_sup_Empty_set.
        rewrite Empty_set_ident_left.
        unfold Included...
          unfold sub, In at 1...
          assert (PlusMinus M ⊆ P) as FF. admit.
          apply FF. (* ?? *) admit. 
          rewrite PlusMinus_Singleton in H8. 
          apply plus_dim in H8.
          rewrite ydim in H8. 
          inversion H8...
        admit.
        rewrite H0, H1... 
        rewrite (Minus_Singleton y), (Plus_Singleton y)...
        split.
        unfold Z, In in minZ...
        split. 
          unfold not; intros.
          unfold N, Q in H2. admit.
        split. 
          unfold not; intros.
          unfold L, R in H2. admit.
        unfold composite, L, R, N, Q. split. 
        repeat (rewrite sub_Union).
        rewrite sub_sup_Empty_set.
        assert ( sub (Singleton y) m == Empty_set) as HH. 
          admit.
        rewrite HH. clear HH.
        rewrite Empty_set_ident_left.
        rewrite Empty_set_ident_right.
        assert (sub ((sub P m ∪ minus y) ∩ √plus y) m == ((sub P m ∪ minus y) ∩ √plus y) ) as BB.
          unfold sub at 1, Same_set, Included... 
          unfold In at 1 in H8; inversion H8; assumption.
          unfold In at 1... 
          inversion H8; clear H8; subst.
          inversion H9; clear H9; subst.
          unfold sub, In in H8...
          apply minus_dim in H8. rewrite ydim in H8.
          inversion H2... 
        rewrite BB.
        set (KK := ((sub P m ∪ minus y) ∩ √plus y)).
        unfold Same_set, Included... 
          assert (x0 = y ∨ x0 ≠ y) as JJ. 
            apply carrier_decidable_eq.
          inversion JJ; [right | left]; clear JJ...
          subst. 
          apply In_Intersection... 
          apply In_Complement; unfold not... 
          unfold KK in H9. rewrite <- BB in H9.
          unfold sub at 1, In at 1 in H9... rewrite ydim in H11. 
          apply (n_Sn m)... 
          apply In_Intersection... 
          apply In_Complement; unfold not...
          inversion H10; subst...
          apply In_Union in H8...
          apply In_Intersection in H9...
          apply In_Intersection in H9...
          apply In_Union in H8...
          apply In_Union in H9...
          unfold sup, In at 1 in H8... 
          exfalso. unfold Complement, In at 1 in H10... 
          inversion H9; clear H9. rewrite <- H8.
          unfold Y, In at 1 in H4. apply H4.
          admit. 
    admit.

  Admitted. 

End ParityComplexTheory.                                    





