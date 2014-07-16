
(* Written by Mitchell Buckley 12/11/2013 *)

Require Import Ensembles.
Require Import Finite_sets.
Require Import Relations.
Require Import mySetoids.
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

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Basic definitions                                    *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Definition decidable {A : Type} (X : Ensemble A) : Prop :=
  forall (x : A), (In X x) \/ ~(In X x).

Definition restrict {A : Type} (X : Ensemble A) (R : relation A) : relation A.
  compute.
  intros x y.
  apply (In X x /\ In X y /\ R x y).
Defined.

Definition is_singleton {A : Type} (X : Ensemble A) : Prop :=
  forall x y, (In X x /\ In X y) -> x = y.

Definition is_a_segment {A : Type} (S T : Ensemble A) : Prop :=
  4=4.

Hint Unfold decidable : sets v62. 

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Pre-Parity Complexes and associated results          *)
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
  Axiom plus_minus_disjoint : forall (y : carrier), dim y > 0 ->  Disjoint (plus y) (minus y).
  Axiom zero_faces: forall (x : carrier),   (dim x) = 0 -> (plus x == minus x == Empty_set _).
  Axiom all_decidable : forall (S : Ensemble carrier), decidable S. 

End PreParity.

Module PreParityTheory (M : PreParity).

  Import M.

  Definition elem_at_dim (n : nat) : Ensemble carrier :=
    fun (x : carrier) => (dim x = n).

  Definition Plus (X : Ensemble carrier) : Ensemble carrier :=
    fun (y : carrier) => (exists (x : carrier), (In X x) /\ (In (plus x) y)).
  Definition Minus (X : Ensemble carrier) : Ensemble carrier :=
    fun (y : carrier) => (exists (x : carrier), (In X x) /\ (In (minus x) y)). 

  Definition PlusMinus (X : Ensemble carrier) : Ensemble carrier := 
    Intersection (Plus X) (Complement (Minus X)).
  Definition MinusPlus (X : Ensemble carrier) : Ensemble carrier :=
    Intersection (Minus X) (Complement (Plus X)).

  Definition Perp (X Y : Ensemble carrier) : Prop :=
    (Disjoint (Plus X) (Plus Y)) /\ (Disjoint (Minus X) (Minus Y)).
  Definition perp (x y : carrier) : Prop :=
    (Intersection (plus x) (plus y) == Empty_set _) /\ (Intersection (minus x) (minus y) == Empty_set _).

  Definition less (x y : carrier) : Prop :=
    (Inhabited (Intersection (plus x) (minus y))).
  Definition curly_less (x y : carrier) : Prop :=
    (In (minus y) x) \/ (In (plus x) y). 
  
  Definition triangle (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans _ (less).
  Definition solid_triangle (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans _ (curly_less).
  Definition triangle_rest (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans _ (restrict S less).
  Definition solid_triangle_rest (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans _ (restrict S curly_less).
    
  Hint Unfold PlusMinus MinusPlus Perp perp less curly_less triangle solid_triangle
     triangle_rest solid_triangle_rest : sets v62.
(* we could introduce notations for triangle and solid_triangle *)

  Definition moves_def (S M P : Ensemble carrier) : Prop :=
    P == (Intersection (Union (M) (Plus S)) (Complement (Minus S))) /\
    M == (Intersection (Union (P) (Minus S)) (Complement (Plus S))).

  Notation "S 'moves' M 'to' P" := (moves_def S M P) (at level 89).
  (* this notation could maybe be improved, see p321 *)

  Definition well_formed (X : Ensemble carrier) : Prop :=
    (forall (x y : carrier), dim x = O -> dim y = 0 -> x = y ) (* sufficient? *)
    /\
    (forall (n : nat) (x y : carrier), dim x = S n -> dim y = S n -> not (perp x y) -> x = y).
    (* 
       "not (perp x y) -> x = y"
       is the contrapositive of the condition given by Ross
       we might need to be careful with this 
    *)

  Definition tight (R : Ensemble carrier) : Prop :=
    forall u v, 
      triangle (Full_set _) u v ->  In R v -> Intersection (minus u) (PlusMinus R) == (Empty_set _).

  Hint Unfold moves_def well_formed tight : sets v62.

  (* Section 2 *)

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
  end.
  
  Ltac myUnfold := unfold moves_def; unfold PlusMinus; unfold MinusPlus.

  Lemma Observation_p321 : 
    forall (S : Ensemble carrier), S moves (MinusPlus S) to (PlusMinus S).
  Proof with repeat (try basic); auto.
    unfold moves_def; unfold PlusMinus; unfold MinusPlus...
    intros...
    unfold Same_set; unfold Included...
    inversion H0...
    unfold Same_set; unfold Included...
    inversion H0...
  Qed.

  Lemma Prop_2_1 : forall (S M : Ensemble carrier), 
     (exists (P : Ensemble carrier), S moves M to P) 
     <->
     (MinusPlus S) ⊆ M /\ Disjoint M (Plus S).
  Proof with repeat basic; auto.
    unfold moves_def; unfold PlusMinus; unfold MinusPlus...
    intros. split...

    eapply Included_Same_set_compat. reflexivity. symmetry. apply H1.
    unfold Included... 
    apply (In_Same_set' _ _ H1) in H2...

    exists ((M ∪ Plus S) ∩ √Minus S).
    split; try reflexivity.
    rewrite U_I_dist_r.
    rewrite Full_set_property.
    rewrite Full_set_ident_right.
    rewrite I_U_dist_r.
    unfold Same_set; unfold Included...
    left... apply In_Complement...  
    unfold Same_set; unfold Included;
    repeat (split; intros)...
    unfold not in H. apply (H x)...
    inversion H1; clear H1; subst...
    inversion H1; clear H1; subst...
    unfold Included in H0.  apply H0...
    apply all_decidable.
  Qed.

  Lemma Prop_2_1_dual : forall (S P : Ensemble carrier), 
     (exists (M : Ensemble carrier), S moves M to P) 
     <->
     (PlusMinus S) ⊆ P /\ Disjoint P (Minus S).
  Proof with repeat basic; auto.
    unfold moves_def; unfold PlusMinus; unfold MinusPlus...
    intros. split...

    eapply Included_Same_set_compat. reflexivity. symmetry. apply H.
    unfold Included... apply (In_Same_set' _ _ H) in H2... 
    
    exists ((P ∪ Minus S) ∩ √Plus S)...
    rewrite U_I_dist_r.
    rewrite Full_set_property.
    rewrite Full_set_ident_right.
    rewrite I_U_dist_r.
    unfold Same_set; unfold Included...
    left... apply In_Complement...  
    unfold Same_set; unfold Included;
    repeat (split; intros)...
    unfold not in H. apply (H x)...
    inversion H1; clear H1; subst...
    inversion H1; clear H1; subst...
    unfold Included in H0.  apply H0...
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
  Proof with repeat basic; auto.
    intros...
    unfold moves_def in H...
    assert (exists (P : Ensemble carrier), S moves ((A ∪ Y) ∩ √X) to P).
    apply Prop_2_1.
    split.
    apply Included_trans with (T:=(A ∩ √X)).
      unfold Included; intros... unfold MinusPlus in H...
      unfold Same_set in H5; unfold Included in H5. inversion H5; clear H5.
    apply H8. clear H H8...
    apply In_Complement... unfold not in H2. apply (H2 x)...
    unfold Included...
    
    constructor...
    inversion H; clear H...
    unfold Same_set in H5; unfold Included in H5. inversion H5; clear H5.
    apply H in H6; clear H...
    unfold not in H3; apply (H3 x)...

    inversion H as [P].
    assert (P == (B ∪ Y) ∩ √X).
    Focus 2. unfold moves_def. unfold moves_def in H6. inversion H6; clear H6. 
    split.
    rewrite <- H7; assumption.
    rewrite <- H7; assumption.
    clear H.
    inversion H6; clear H6.
    rewrite H.
    rewrite U_I_dist_r.
    rewrite  H1.
    rewrite  U_I_dist_r.
    unfold Same_set; unfold Included...
      inversion H6... inversion H8. left; left...
      right... left; right...
      inversion H10... apply In_Complement...
      unfold Included in H0. apply H0 in H11.
      unfold Same_set in H5. unfold Included in H5. apply H5 in H11... 
      inversion H6... inversion H8. left; left...
      right... left; right...
      inversion H10... apply In_Complement... unfold not in H4. apply (H4 x)...
  Qed.

  Lemma Plus_Union_compat : forall S T,
     Plus (Union S T) == Union (Plus S) (Plus T).
  Proof with repeat basic; unfold In; auto.
    intros. autounfold with sets. unfold Plus...
    inversion H.
      left... exists x0...
      right... exists x0...
    inversion H.
      unfold In in H0. inversion H0. exists x1... left...
      unfold In in H0. inversion H0. exists x1... right...
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

  Lemma Union_Complement_compat {U : Type} : forall (S T : Ensemble U),
    (√S ∩ √T) == (√(Union S T)).
  Proof with try repeat match goal with H: In ?P ?X |- _ => unfold In in H end; auto.
    intros. autounfold with sets...
    unfold Complement. unfold not. unfold In.
    split; intros.
      inversion H... subst. inversion H0...
    split; intros; unfold In.
      intros; apply H. left...
      intros; apply H. right... 
  Qed.

  Lemma Prop_2_3 : 
    forall (S M P T Q : Ensemble carrier),
    S moves M to P -> T moves P to Q -> Disjoint (Minus S) (Plus T) 
    ->
    (S ∪ T) moves M to Q.
  Proof with repeat basic; auto.
    intros...
    unfold moves_def in H...
    unfold moves_def in H0...
    unfold moves_def...
    
    rewrite H. 
    assert (Plus T == Intersection (Plus T) (Complement (Minus S))).
    unfold Same_set; unfold Included... apply In_Complement... unfold not in H2. apply (H2 x)...
    rewrite H0.
    rewrite H1.
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
    unfold Same_set; unfold Included... apply In_Complement... unfold not in H2. apply (H2 x)...
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

Lemma Empty_set_ident {U : Type} : forall (S : Ensemble U), (Union S (Empty_set _)) == S.
  Proof with auto.
    intros.
    unfold Same_set; unfold Included...
    split; intros...
      inversion H...
        inversion H0.
      left...
  Qed. 

Lemma Intersection_idemp {U : Type} : forall (S : Ensemble U), (Intersection S S) == S.
  Proof with auto.
    intros.
    unfold Same_set; unfold Included...
    split; intros...
      inversion H...
      constructor...
  Qed. 

Lemma Intersection_sym {U : Type} : forall (S T: Ensemble U), (Intersection S T) == (Intersection T S).
  Proof with auto.
    intros.
    unfold Same_set; unfold Included.
    split; intros x H; inversion H; subst;
      constructor...
  Qed.

Lemma Intersection_Complement_compat {U : Type} : forall (S T: Ensemble U), decidable S -> √(Intersection S T) == (Union (√S) (√T)).
  Proof with unfold In; auto.
    intros.
    unfold Complement. autounfold with sets. unfold not.
    split; intros.
    assert (S x \/ ~ S x). apply H.
    inversion H1. right... intros. apply H0. constructor...
    left...
    inversion H1; subst. clear H1.
    inversion H0 as [d K | d K]; subst. unfold In in K. unfold In in H2...
    unfold In in K. unfold In in H3...
  Qed.

  Lemma Complement_Complement_compat {U : Type} : forall (S: Ensemble U), decidable S -> (√(√S)) == S.
  Proof with unfold In; auto.
    intros.
    unfold Complement. unfold not. autounfold with sets.
    split; intros.
    assert (S x \/ ~ S x). apply H.
    inversion H1... unfold not in H2. contradiction. auto...
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
    intros...
    unfold moves_def in H. inversion H. clear H...
    assert (exists N, Z moves N to P). 
    apply Prop_2_1_dual...
      apply (In_Same_set' _ _ H2) in H5... subst. 
      assert ((√Minus (T ∪ Z)) == (√Minus T ∩ √Minus Z)).  
      rewrite Minus_Union_compat.
      rewrite Union_Complement_compat. reflexivity.
      apply (In_Same_set' _ _ H5) in H7...
    inversion H as [N']; clear H.
    assert (exists N', T moves M to N').        
    apply Prop_2_1. split.
      assert (K1: Plus T == (Plus S) ∩ √(Plus Z)). rewrite HeqS. 
      rewrite Plus_Union_compat. rewrite I_U_dist_r.
      rewrite Empty_set_property. rewrite Empty_set_ident.
      unfold Same_set; unfold Included... 
      apply In_Complement... unfold not in H3. apply (H3 x)...
      assert (K2: Minus T == (Minus S) ∩ √(Minus Z)). rewrite HeqS. 
      rewrite Minus_Union_compat. rewrite I_U_dist_r.
      rewrite Empty_set_property. rewrite Empty_set_ident.
      unfold Same_set; unfold Included... 
      apply In_Complement... unfold not in H1. apply (H1 x)...
      assert ((MinusPlus T) == (MinusPlus S ∩ √(Minus Z)) ∪ (Minus S ∩ (PlusMinus Z)) ). 
      unfold MinusPlus. unfold PlusMinus. rewrite K1. rewrite K2.
      rewrite (Intersection_Complement_compat).
      rewrite (Complement_Complement_compat).
      unfold Same_set; unfold Included...
        inversion H7... left... right... 
        inversion H. apply In_Intersection in H6... apply In_Intersection in H6... 
        inversion H. apply In_Intersection in H6... apply In_Intersection in H6... 
        inversion H; apply In_Intersection in H6...  
        apply all_decidable. apply all_decidable.
      assert (M == (Union M (Intersection (Minus S) P))).
      unfold Same_set; unfold Included...
        inversion H6... symmetry in H4. apply (In_Same_set' _ _ H4)...
        apply (In_Same_set' _ _ H2) in H9...
      unfold Included...
      apply (In_Same_set' _ _ H) in H7... symmetry in H6.
      apply (In_Same_set' _ _ H6)...
      inversion H7. left... symmetry in H4.
      apply (In_Same_set' _ _ H4)... unfold MinusPlus in H9. right...
      unfold MinusPlus in H9... right...
 
      constructor... apply (In_Same_set' _ _ H4) in H6...
      rewrite HeqS in H8. assert ((√Plus (T ∪ Z)) == ((√ Plus T ∩ √ Plus Z))).
      rewrite Plus_Union_compat. rewrite Union_Complement_compat...
      apply (In_Same_set' _ _ H6) in H8...

    inversion H as [N]; clear H. 
    exists N. exists N'...
    
    unfold moves_def in H5. inversion H5. clear H5.
    unfold moves_def in H6. inversion H6. clear H6.
    rewrite H7. rewrite H5. 
    assert ((Plus T) == (Intersection (Plus S) (Complement (Plus Z)))).
    rewrite HeqS. rewrite Plus_Union_compat. rewrite I_U_dist_r.
    rewrite Empty_set_property. rewrite Empty_set_ident.
    unfold Same_set; unfold Included... apply In_Complement... unfold not in H3. apply (H3 x)...
    assert ((Minus T) == (Intersection (Minus S) (Complement (Minus Z)))).
    rewrite HeqS. rewrite Minus_Union_compat. rewrite I_U_dist_r.
    rewrite Empty_set_property. rewrite Empty_set_ident.
    unfold Same_set; unfold Included... apply In_Complement... unfold not in H1. apply (H1 x)...
    rewrite H6. rewrite H9. rewrite Intersection_Complement_compat. rewrite Complement_Complement_compat.
    rewrite U_I_dist_l. rewrite Intersection_trans. rewrite (Intersection_sym (M ∪ √Plus Z) _).
    rewrite <- Intersection_trans. rewrite (I_U_dist_l (M ∪ Plus S)). rewrite <- H2.
    assert ((Minus Z) ⊆ Union (MinusPlus S) (Plus S)).
    assert ((Union (MinusPlus S) (Plus S)) == (Union (Minus S) (Plus S))).
    unfold MinusPlus. rewrite U_I_dist_r. rewrite Full_set_property. rewrite Full_set_ident_right...
    apply all_decidable.
    unfold Included... symmetry in H10. apply (In_Same_set' _ _ H10). left... rewrite HeqS.
    assert ((Minus (T ∪ Z)) == ((Minus T ∪ Minus Z))). apply Minus_Union_compat. symmetry in H12.
    apply (In_Same_set' _ _ H12). right...
    assert ((MinusPlus S ∪ Plus S) ⊆ (Union M (Plus S))). unfold MinusPlus. unfold Included...
    inversion H11... left... symmetry in H4. apply (In_Same_set' _ _ H4)...
    assert (Minus Z ⊆ M ∪ Plus S). eapply Included_trans. apply H10... assumption.
    assert (((M ∪ Plus S) ∩ Minus Z) == (Minus Z)).
    unfold Same_set; unfold Included... rewrite H13.
    assert ((M ∪ √Plus Z) == (√Plus Z)).
    unfold Same_set; unfold Included...
    inversion H14... apply In_Complement... assert (x ∈ Plus S). rewrite HeqS.
    assert (Plus (T ∪ Z) == (Plus T ∪ Plus Z)). apply Plus_Union_compat. symmetry in H17.
    apply (In_Same_set' _ _ H17). right...
    apply (In_Same_set' _ _ H4) in H15... rewrite H14...
    apply all_decidable.
    apply all_decidable.
  Qed.

End PreParityTheory.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Parity Complexes                                     *)
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
      triangle (Full_set _) x y -> triangle (Full_set _) y x -> x = y.

  Axiom axiom3b:
    forall x y z : carrier, 
    triangle (Full_set _) x y ->
    (~ (In (plus z) x /\ In (minus z) y) /\ ~ (In (plus z) y /\ In (minus z) x)).
  (* This last condition somewhat awkwardly phrased, this might become tricky later *)

End ParityComplex.

Module ParityComplexTheory (M : ParityComplex).

  Import M.
  Import C.
  Import PPT. 

  (* Section 1 *)

Ltac unfold_In := repeat 
    match goal with 
      | H: In ?P ?x |- _ => unfold In in H 
      | H: Plus ?P ?x |- _ => unfold Plus in H  
      | H: Minus ?P ?x |- _ => unfold Minus in H  
    end.

  Lemma Prop_1_1 : 
    forall x, 
    (Plus (plus x)) ∩ (Minus (minus x)) == (Empty_set _) == (Plus (minus x)) ∩ (Minus (plus x))
    /\
    (MinusPlus (minus x)) == Intersection (Minus (minus x)) (Minus (plus x)) == (MinusPlus (plus x))
    /\
    (PlusMinus (minus x)) == Intersection (Plus (minus x)) (Plus (plus x))   == (PlusMinus (plus x)).
  Proof with repeat basic; auto.
    assert (H: forall x y, (In (Plus (plus x)) y /\ In (Minus (minus x)) y) -> False). admit.
    assert (K: forall x y, (In (Minus (plus x)) y /\ In (Plus (minus x)) y) -> False). admit.

    intros; split; split.
    unfold Same_set; unfold Included... 
      exfalso. apply (H x x0)...
      inversion H0. inversion H0.
    unfold Same_set; unfold Included... 
      inversion H0. inversion H0. exfalso. apply (K x x0)...
 
    split; unfold MinusPlus. unfold Same_set; unfold Included...
    
  Admitted.


  Lemma Prop_1_2 :
    forall u v x,
    triangle (Full_set carrier) u v ->
    In (plus x) v ->
    (minus u) ∩ (Plus (minus x)) == Empty_set _.
  Proof with repeat basic; auto.
    intros.
    unfold Same_set; unfold Included... 
    unfold Plus in H3. unfold In in H3... rename x1 into w. 
    assert (less w u). unfold less. apply (Inhabited_intro _ _ x0)... 
    assert (triangle (Full_set carrier) w v). unfold triangle. 
    eapply rt_trans. apply rt_step.  apply H1. apply H. eapply axiom3b in H5... 
    unfold not in H7. exfalso. apply H7... apply H0. apply H3. inversion H1. inversion H1.
  Qed.

  Lemma Prop_1_3 : 
    forall R S, 
      tight R -> well_formed S -> R ⊆ S -> is_a_segment R S. 
  Admitted.

  (* Section 2 *)
  
  Lemma Observation_p322 :
    forall (T Z : Ensemble carrier),
    well_formed (Union T Z) ->
    Disjoint T Z ->
    Perp T Z. 
  Proof with repeat basic; auto.
    intros. remember (Union T Z) as S. 
    unfold well_formed in H...
    unfold Perp... 
    unfold Plus in H3. unfold In in H3.
    unfold Plus in H4. unfold In in H4...
    assert (dim x0 = 1+ (dim x)). symmetry. apply plus_dim. unfold In...
    assert (dim x1 = 1+ (dim x)). symmetry. apply plus_dim. unfold In...
    assert (x0 = x1). eapply H2. apply H0. apply H7. unfold not. unfold perp. intros... 
    unfold Same_set in H9... unfold Included in H8... assert (x ∈ Empty_set carrier).
    apply H8... inversion H9. subst.
    unfold not in H. eapply H... apply H3... apply H4...
    unfold Minus in H3. unfold In in H3.
    unfold Minus in H4. unfold In in H4...
    assert (dim x0 = 1+ (dim x)). symmetry. apply minus_dim. unfold In...
    assert (dim x1 = 1+ (dim x)). symmetry. apply minus_dim. unfold In...
    assert (x0 = x1). eapply H2. apply H0. apply H7. unfold not. unfold perp. intros... 
    unfold Same_set in H10... unfold Included in H8... assert (x ∈ Empty_set carrier).
    apply H8... inversion H10. subst.
    unfold not in H. eapply H... apply H3... apply H4...
  Qed.

  (* Section 3 *)

  Record cell : Type :=
  {
    M : Ensemble _;
    P : Ensemble _;
    cell_non_empty : ~ (M == Empty_set _) /\ ~(P == Empty_set _);
    cell_wf : well_formed M /\ well_formed P;
    cell_finite: Finite M /\ Finite P;
    M_moves : M moves M to P;
    P_moves : P moves M to P
  }.

  Definition Big_0 := Ensemble cell.

  Definition is_a_cell (M P : Ensemble _) : Prop :=
    exists a b c d e R, R = Build_cell M P a b c d e.

  Definition source (n : nat) (A : cell) : cell.
    inversion A. Admitted.

  Definition target (n : nat) (A : cell) : cell.
    inversion A. Admitted.

  Definition composable (n : nat) (A B : cell) : Prop := target n A = source n B. 

  Definition composite (n : nat) (A B : cell) : cell.
     Admitted.

  Definition cell_dim (n : nat) (A : cell) : Prop := A = source n A.

  Definition receptive (S : Ensemble carrier) : Prop :=
    (forall x, (Plus (minus x)) ∩ (Plus (plus x)) ⊆ S ->
       S ∩ (Minus (minus x)) == Empty_set _ ->
       S ∩ (Minus (plus x)) == Empty_set _ ) /\ 
    (forall x, (Minus (plus x)) ∩ (Minus (minus x)) ⊆ S ->
       S ∩ (Plus (plus x)) == Empty_set _ ->
       S ∩ (Plus (minus x)) == Empty_set _ ).

  Definition cell_receptive (A : cell) : Prop.
    inversion A as [M P a s d].
    apply ((receptive M) /\ (receptive P)). 
    Defined.

  Lemma Prop_3_1 :
    forall x M P, 
      (plus x) moves M to P ->
      receptive M ->
      (minus x) moves M to P.
  Admitted.

  Lemma Lemma_3_2a : 4 = 4. Admitted.
  (* need to read the corrigenda to fix this *)


  Lemma Lemma_3_2b : 
    (forall Q : cell, cell_receptive Q) ->
    forall (n : nat), forall M P a b c d e, cell_dim n (Build_cell M P a b c d e) ->
    forall X, (X ⊆ elem_at_dim (S n)) /\ Finite X /\ well_formed X /\ ((PlusMinus X) ⊆ M) ->
    exists Y, (Y = (M ∪ Minus X) ∩ √(Plus X)) /\ is_a_cell (M ∪ Y) (P ∪ Y) /\ (Minus X ∩ M == Empty_set _).
  Admitted.

  Lemma Lemma_3_2c : 
    (forall Q : cell, cell_receptive Q) ->
    forall (n : nat), forall M P a b c d e, cell_dim n (Build_cell M P a b c d e) ->
    forall X, (X ⊆ elem_at_dim (S n)) /\ Finite X /\ well_formed X /\ ((PlusMinus X) ⊆ M) ->
    exists Y, (Y = (M ∪ Minus X) ∩ √(Plus X)) /\ is_a_cell (M ∪ Y ∪ X) (P ∪ X).
  Admitted.

  Lemma Prop_3_3 :
    (forall Q : cell, cell_receptive Q).
  Admitted.

  Lemma Prop_3_4 :
    forall M P, is_a_cell M P ->
    forall z n, dim z = S n ->
    minus z ⊆ P ->
    Minus M ∩ plus z == Empty_set _.
  Admitted.

  Lemma Prop_3_5 :
    forall M P N Q, is_a_cell M P /\ is_a_cell N Q ->
    (forall n m, m < n-1 -> (M == N /\ P == Q /\ P = N)) -> 
    (Minus M ∩ Plus N == Empty_set _) /\ is_a_cell (M) (N).
  Admitted.

  Lemma Theorem_3_6a :
    4 = 4. (* Big_O is an w-category. *)
  Admitted. 

  Lemma Theorem_3_6b :
    forall M P N Q (n: nat), 
      is_a_cell M P -> is_a_cell N Q -> 4 = 4 ->
      Minus (M ∪ P) ∩ Plus (N ∪ Q) == Empty_set _.
  Admitted. 

  (* Section 4 *)
 
  Inductive pi (x : carrier) : Ensemble carrier :=
    | pi_singleton : pi x x. (*
    | pi_plusminus : forall y, y ∈ PlusMinus (pi x) -> pi x y. *)

  Inductive mu (x : carrier) : Ensemble carrier :=
    | mu_singleton : mu x x. (*
    | mu_minusplus : forall y, y ∈ MinusPlus (pi x) -> pi x y. *)

  Notation "'<<' x '>>'" := ((mu 4 x) (pi 4 x)) (at level 85).

  Lemma Theorem_4_1 :
    forall M P n, is_a_cell M P ->
    forall u, u ∈ M -> ~((M, P) = (mu u, pi u)) ->
    exists (NQ LR : cell), cell_dim n NQ /\ (cell_dim n LR) /\
    (exists (m : nat), (m < n) /\ ~(cell_dim m NQ) /\ ~(cell_dim m LR)) /\
    4 = 4.
  Admitted.

  Definition relevant x : Prop := is_a_cell (mu x) (pi x).
 
  Definition is_an_atom (A : cell) : Prop := exists x, relevant x. 

  Lemma Observation_p331 :
    (forall x, dim x = 0 -> relevant x) /\
    (forall x, dim x = 1 -> relevant x) /\
    (forall x, dim x = 2 -> (relevant x <-> 
      ( is_singleton (Minus (minus x) ∩ Minus (plus x)) /\ 
        is_singleton (Plus  (minus x) ∩ Plus  (plus x)) ))).
  Admitted.

  Lemma Theorem_4_2 :
    4=4 (* Big_O is freely generated by the atoms *).
  Admitted.    

End ParityComplexTheory.                                    

Inductive dUnion {A : Type} (B C : Ensemble A) : Ensemble A :=
  |  dUnion_introl : forall x:A, In B x -> ~ (In C x) -> In (dUnion B C) x
  |  dUnion_intror : forall x:A, In C x -> ~ (In B x) -> In (dUnion B C) x.
Arguments dUnion : default implicits.


Ltac big_guy := 
  match goal with
    | H: ?P /\ ?Q |- _ => inversion H; clear H
    | H: _ |- ?P /\ ?Q => split
    | H1: In ?P ?X |- _ => unfold In in H1
    | H1: (Intersection (?P) (?Q)) ?X |- _ => inversion H1 as [y A B C]; clear H1 C y; unfold In in A; unfold In in B
    | H1: (Intersection ?P (Complement ?Q)) ?X |- _ => inversion H1 as [y A B C]; clear H1 C y; unfold In in A; unfold In in B
    | H: _ |- (Intersection ?P ?Q) ?X => constructor; unfold In  
    | H1: ?P, H2: ?P -> False |- _ => contradiction
    | H: _ |- Disjoint ?P ?Q => constructor
    | H: Disjoint ?P ?Q |- _ => inversion H as [K]; clear H; autounfold with sets in K
    | H: _ |- In ?P ?X => unfold In
    | H: _ |- not ?P => unfold not
    | H: not ?P |- _ => unfold not in H
    | H: exists x, ?P |- _ => inversion H; clear H
    | H: forall x, ?P |- _ => intros
    | H: _ |- (Complement ?P) ?X => unfold Complement; unfold In; unfold not
    | H: (Complement ?P) ?X |- _ => unfold Complement in H; unfold In in H; unfold not in H
  end.