
(* Written by Mitchell Buckley 12/11/2013 *)

Require Import Ensembles Constructive_sets.
Require Import myFiniteDefs.
Require Import Relations.
Require Import mySetoids.
Require Import Utf8_core.
Require Import Max Le.
Require Import Arith.

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

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Basic definitions                                    *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Definition restrict {A : Type} (X : Ensemble A) (R : relation A) : relation A :=
   (fun x => (fun y => In X x /\ In X y /\ R x y)).

Definition is_singleton {A : Type} (X : Ensemble A) : Prop :=
  exists x, X == Singleton x.

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
  Axiom plus_minus_disjoint : forall (y : carrier), dim y > 0 ->  Intersection (plus y) (minus y) == Empty_set _.
  Axiom zero_faces: forall (x : carrier),   (dim x) = 0 -> (plus x == minus x == Empty_set _).
  Axiom all_decidable : forall (S : Ensemble carrier), decidable S. 

End PreParity.

Module PreParityTheory (M : PreParity).

  Import M.

  Definition sub (S : Ensemble carrier) (n : nat) := 
    fun (x : carrier) => (In S x /\ dim x  = n).
  Definition sup (S : Ensemble carrier) (n : nat) := 
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
    (Intersection (Plus X) (Plus Y) == Empty_set _) /\ (Intersection (Minus X) (Minus Y) == Empty_set _).
  Definition perp (x y : carrier) : Prop :=
    (Intersection (plus x) (plus y) == Empty_set _) /\ (Intersection (minus x) (minus y) == Empty_set _).

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

  Hint Unfold PlusMinus MinusPlus Perp perp less curly_less triangle solid_triangle
     triangle_rest solid_triangle_rest : sets v62.

  Definition moves_def (S M P : Ensemble carrier) : Prop :=
    P == (Intersection (Union (M) (Plus S)) (Complement (Minus S))) /\
    M == (Intersection (Union (P) (Minus S)) (Complement (Plus S))).

  Notation "S 'moves' M 'to' P" := (moves_def S M P) (at level 89).

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
      triangle u v ->  In R v -> Intersection (minus u) (PlusMinus R) == (Empty_set _).

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
    | H: _ |- decidable _ => apply all_decidable
  end.

  Ltac subsuptac := 
  match goal with
    | H: In (sub ?P ?n) ?x |- _ => unfold In in H; unfold sub in H
    | H: In (sup ?P ?n) ?x |- _ => unfold In in H; unfold sup in H
    | H: _ |- In (sub ?P ?n) ?x => unfold In; unfold sub
    | H: _ |- In (sup ?P ?n) ?x => unfold In; unfold sup
  end.

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

  Lemma Empty_set_zero {U : Type} : forall T : (Ensemble U), Intersection T (Empty_set _) == (Empty_set _).
  Proof with repeat basic; auto.
    intros. unfold Same_set, Included... inversion H. 
  Qed.
 
  Lemma Prop_2_1_dual : forall (S P : Ensemble carrier), 
     (exists (M : Ensemble carrier), S moves M to P) 
     <->
     (PlusMinus S) ⊆ P /\ Intersection P (Minus S) == Empty_set _.
  Proof with repeat basic; auto.
    unfold moves_def; unfold PlusMinus; unfold MinusPlus...
    intros. split...

    eapply Included_Same_set_compat. reflexivity. symmetry. apply H.
    unfold Included... rewrite H. rewrite Intersection_trans. 
    rewrite (Intersection_sym _ (Minus S)). rewrite Empty_set_property. 
    rewrite Empty_set_zero...

    exists ((P ∪ Minus S) ∩ √Plus S)...
    rewrite U_I_dist_r.
    rewrite Full_set_property.
    rewrite Full_set_ident_right.
    rewrite I_U_dist_r.
    unfold Same_set; unfold Included...
    left... apply In_Complement... admit.
    inversion H...
      inversion H3... apply H0...
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

  Lemma Prop_2_3 : 
    forall (S M P T Q : Ensemble carrier),
    S moves M to P -> T moves P to Q -> (Intersection (Minus S) (Plus T) == Empty_set _) 
    ->
    (S ∪ T) moves M to Q.
  Proof with repeat basic; auto.
    intros...
    unfold moves_def in H...
    unfold moves_def in H0...
    unfold moves_def...
    
    rewrite H. 
    assert (Plus T == Intersection (Plus T) (Complement (Minus S))).
      unfold Same_set; unfold Included... apply In_Complement... unfold not in H2. 
      assert (In (Minus S ∩ Plus T) x). apply In_Intersection. split; assumption. 
      apply (In_Same_set' _ _ H1) in H6. inversion H6. 
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
      unfold Same_set; unfold Included... apply In_Complement... unfold not in H2. 
      assert (In (Minus S ∩ Plus T) x). apply In_Intersection. split; assumption. 
      apply (In_Same_set' _ _ H1) in H6. inversion H6. 
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

  Lemma Included_Empty_set {U : Type} : 
    forall (S T : Ensemble U), Included S T -> T  == (Empty_set _) -> S  == (Empty_set _).
  Proof with repeat basic; auto.
    unfold Same_set, Included...
    inversion H0. 
  Qed.

  Lemma Disjoint_result {U : Type} : 
    forall (S T : Ensemble U), Intersection S T == Empty_set _ -> S == Intersection S (Complement T).
  Proof with repeat basic; auto.
    unfold Same_set, Included... apply In_Complement. unfold not. intros.
    assert (x ∈ Empty_set U -> False)... inversion H3. apply H3... apply H0...
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
    unfold moves_def in H...
    
    assert (exists N, Z moves N to P). 
    apply Prop_2_1_dual. 
      split; try assumption.
      assert (Included (Minus Z) (Minus S)).
        unfold Minus, Included, In... exists x0... rewrite HeqS... right...
      eapply (Included_Empty_set). eapply Intersection_Included_compat.
      reflexivity. apply H. unfold Same_set, Included... 
      apply (In_Same_set' _ _ H1) in H6... inversion H5. inversion H5. 
    inversion H as [N']; clear H.

    assert (exists N', T moves M to N').        
    apply Prop_2_1. split.
      assert (K1: Plus T == (Plus S) ∩ √(Plus Z)). 
        rewrite HeqS. rewrite Plus_Union_compat. rewrite I_U_dist_r.
        rewrite Empty_set_property. rewrite Empty_set_ident_right.
        unfold Same_set; unfold Included... 
        apply In_Complement... admit. 
      assert (K2: Minus T == (Minus S) ∩ √(Minus Z)). rewrite HeqS. 
        rewrite Minus_Union_compat. rewrite I_U_dist_r.
        rewrite Empty_set_property. rewrite Empty_set_ident_right.
        unfold Same_set; unfold Included... 
        apply In_Complement...  admit. 
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
        apply (In_Same_set' _ _ H1) in H9...
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
      rewrite Empty_set_property. rewrite Empty_set_ident_right.
      apply Disjoint_result... 
    assert ((Minus T) == (Intersection (Minus S) (Complement (Minus Z)))).
      rewrite HeqS. rewrite Minus_Union_compat. rewrite I_U_dist_r.
      rewrite Empty_set_property. rewrite Empty_set_ident_right.
      unfold Same_set; unfold Included... apply In_Complement... unfold not in H1. admit.
    rewrite H6. 
    rewrite H9. 
    rewrite Intersection_Complement_compat. 
    rewrite Complement_Complement_compat.
    rewrite U_I_dist_l. 
    rewrite Intersection_trans. 
    rewrite (Intersection_sym (M ∪ √Plus Z) _).
    rewrite <- Intersection_trans. 
    rewrite (I_U_dist_l (M ∪ Plus S)). 
    rewrite <- H1.
    assert ((Minus Z) ⊆ Union (MinusPlus S) (Plus S)).
      assert ((Union (MinusPlus S) (Plus S)) == (Union (Minus S) (Plus S))).
        unfold MinusPlus. rewrite U_I_dist_r. rewrite Full_set_property. rewrite Full_set_ident_right...
        apply all_decidable.
      unfold Included... symmetry in H10. apply (In_Same_set' _ _ H10). left... rewrite HeqS.
      assert ((Minus (T ∪ Z)) == ((Minus T ∪ Minus Z))). 
        apply Minus_Union_compat. 
      symmetry in H12. apply (In_Same_set' _ _ H12). right...
    assert ((MinusPlus S ∪ Plus S) ⊆ (Union M (Plus S))). 
      unfold MinusPlus. unfold Included...
      inversion H11... left... symmetry in H4. apply (In_Same_set' _ _ H4)...
    assert (Minus Z ⊆ M ∪ Plus S). 
      eapply Included_trans. apply H10... assumption.
    assert (((M ∪ Plus S) ∩ Minus Z) == (Minus Z)).
      unfold Same_set; unfold Included... rewrite H13.
    assert ((M ∪ √Plus Z) == (√Plus Z)).
      unfold Same_set; unfold Included...
      inversion H14... apply In_Complement... assert (x ∈ Plus S). rewrite HeqS.
      assert (Plus (T ∪ Z) == (Plus T ∪ Plus Z)). 
        apply Plus_Union_compat. 
      symmetry in H17. apply (In_Same_set' _ _ H17). right...
      apply (In_Same_set' _ _ H4) in H15... 
    rewrite H14...
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
    remember axiom3b as axiom3b. clear Heqaxiom3b.
    assert (H: forall x y, (In (Plus (plus x)) y /\ In (Minus (minus x)) y) -> False).
    intros... rename y into u.
    unfold Plus in H0. unfold In in H0. 
    unfold Minus in H1. unfold In in H1...
    rename x0 into v. rename x1 into w. assert (less w v).
    unfold less. eapply Inhabited_intro... apply H3... apply H2... 
    assert (triangle w v). eapply (Relation_Operators.rt1n_trans).
    apply H. left... eapply axiom3b in H4... unfold not in H5. apply H5... apply H0.
    apply H1. 

    assert (K: forall x y, (In (Minus (plus x)) y /\ In (Plus (minus x)) y) -> False).
    intros... rename y into u.
    unfold Plus in H2. unfold In in H2. 
    unfold Minus in H1. unfold In in H1...
    rename x0 into v. rename x1 into w. assert (less v w).
    unfold less. eapply Inhabited_intro... apply H3... apply H4... 
    assert (triangle v w). eapply (Relation_Operators.rt1n_trans).
    apply H0. left... eapply axiom3b in H5... unfold not in H7. apply H7... apply H1.
    apply H2. 

    intros; split; split.
    unfold Same_set; unfold Included... rename x0 into y. 
      exfalso. apply (H x y)...
      inversion H0. inversion H0.
    unfold Same_set; unfold Included... 
      inversion H0. inversion H0. exfalso. apply (K x x0)...
 
    split; unfold MinusPlus. unfold Same_set; unfold Included... rename x0 into y.
    assert (In (Union (Plus (minus x)) (Minus (plus x))) y).
    apply (In_Same_set' _ _ (axiom1 x))... apply In_Union in H0... inversion H0... 
    apply In_Complement... apply (K x x0)...

    unfold Same_set; unfold Included...
    apply In_Complement... apply (H x x0)...
    pose (axiom1 x).
    assert (In (Plus (plus x) ∪ Minus (minus x)) x0).
    symmetry in s.
    apply (In_Same_set' _ _ s)... apply In_Union in H0... inversion H0... 

    split; unfold PlusMinus. 

    unfold Same_set; unfold Included...
    pose (axiom1 x).
    assert (In (Plus (plus x) ∪ Minus (minus x)) x0).
    symmetry in s.
    apply (In_Same_set' _ _ s)... apply In_Union in H0... inversion H0...
    apply In_Complement... apply (H x x0)...
    
    unfold Same_set; unfold Included...
    apply In_Complement... apply (K x x0)...
    assert (In (Union (Plus (minus x)) (Minus (plus x))) x0).
    apply (In_Same_set' _ _ (axiom1 x))... apply In_Union in H0... inversion H0... 
  Qed.

  Lemma Prop_1_2 :
    forall u v x,
    triangle u v ->
    In (plus x) v ->
    (minus u) ∩ (Plus (minus x)) == Empty_set _.
  Proof with repeat basic; auto.
    intros.
    unfold Same_set; unfold Included... 
    unfold Plus in H3. unfold In in H3... rename x1 into w. 
    assert (less w u). unfold less. apply (Inhabited_intro _ _ x0)... 
    assert (triangle w v). unfold triangle. 
    eapply Relation_Operators.rt1n_trans. apply H1. apply H. eapply axiom3b in H5... 
    unfold not in H7. exfalso. apply H7... apply H0. apply H3. inversion H1. inversion H1.
  Qed.

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

  Lemma Prop_1_3 : 
    forall R S, 
      tight R -> well_formed S -> R ⊆ S -> is_a_segment R S.
  Proof with repeat basic; auto.
    unfold is_a_segment.
    unfold tight.
    unfold well_formed.
    unfold triangle. intros...
    assert (exists m, (dim x = Datatypes.S m)).
      inversion H4... apply plus_dim in H8. exists (dim x0). auto.  
    rename x into w. rename y into u. rename z into v.
    assert (dim w = dim u). apply equal_dim. unfold triangle. eapply Relation_Operators.rt1n_trans. 
      apply H4. left. 
    inversion H4 as [y]...
    assert (minus u ∩ PlusMinus R == Empty_set carrier).
      apply (H u v). eapply rest_implies_full. apply H7.
      assumption.  
    assert (~(In (PlusMinus R) y)).
      unfold not; intros... assert (In (Empty_set carrier) y). 
      apply (In_Same_set' _ _ H9)... inversion H13. unfold not in H12.
    assert (In (Plus R) y).
      unfold Plus. unfold In. exists w...
    assert (In (Minus R) y). 
      assert (y ∈ Minus R \/ ~(y ∈ Minus R)). apply all_decidable...
      inversion H14. assumption. exfalso. apply H12.
      unfold PlusMinus...
    inversion H14 as [z]...
    assert (u = z).
      eapply H3.  
      rewrite <- H8. apply H10. 
      apply minus_dim in H17. rewrite <- H17. rewrite <- H10.
      apply plus_dim in H0...
      unfold not. unfold perp...
      assert (In (Empty_set carrier) y). apply (In_Same_set' _ _ H19)...
      inversion H15.
      rewrite H15...
  Qed. 

  Lemma xplus_is_tight :
    forall x, tight (plus x).
  Proof with repeat basic; auto.
    unfold tight; intros.
    assert (Intersection (minus u) (Plus (minus x)) == Empty_set _). 
      apply (Prop_1_2 u v)...
    assert (Plus (minus x) ∩ Plus (plus x) == PlusMinus (plus x)). 
      eapply Prop_1_1. 
    rewrite <- H2. 
    rewrite <- Intersection_trans. 
    rewrite H1.
    unfold Same_set, Included; split; intros... inversion H3. 
  Qed.

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
    apply Disjoint_intersection_condition. constructor. unfold not in *. 
    intros...
    unfold Plus in H3. unfold In in H3.
    unfold Plus in H4. unfold In in H4...
    assert (dim x0 = 1+ (dim x)). symmetry. apply plus_dim. unfold In...
    assert (dim x1 = 1+ (dim x)). symmetry. apply plus_dim. unfold In...
    assert (x0 = x1). eapply H2. apply H0. apply H7. unfold not. unfold perp. intros... 
    unfold Same_set in H9... unfold Included in H8... assert (x ∈ Empty_set carrier).
    apply H8... inversion H9. subst.
    unfold not in H. eapply H... apply H3... apply H4...
    apply Disjoint_intersection_condition. constructor. unfold not in *. 
    intros...
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

  Definition is_a_cell (cell_M cell_P : Ensemble _) : Prop :=
    Inhabited cell_M /\ Inhabited cell_P /\
    well_formed cell_M /\ well_formed cell_P /\
    Finite cell_M /\ Finite cell_P /\
    (cell_M moves cell_M to cell_P) /\ (cell_P moves cell_M to cell_P).
  
  Record cell : Type :=
  {
    cell_M : Ensemble _;
    cell_P : Ensemble _;
    cell_axioms : is_a_cell cell_M cell_P
  }.

  Definition celldim (M P : Ensemble carrier) (n : nat) :=
    setdim (Union M P) n.

  Notation "R === S" := (cell_M R == cell_M S /\ cell_P R == cell_P S) (at level 89). 

  Ltac basic2 :=
    match goal with
      | H: well_formed ?P |- _ => unfold well_formed in H
      | H: Inhabited ?P |- _ => inversion H; clear H
    end.

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

  Hint Unfold Same_set Included In sup.
  (*Hint Extern 4 (In _ _) => (match goal with | H: Same_set ?S ?T, K: In ?S ?X |- In ?T ?X => apply (In_Same_set' ?S ?T ?X); assumption 
    end). *)

  Lemma sup_Same_set : forall n, forall S T, S == T -> (sup S n) == (sup T n).
  Proof.
    unfold Same_set, Included, sup, In. 
    try solve [intuition eauto].   
  Qed.

  Lemma sup_Intersection : forall T R n, sup (Intersection T R) n == Intersection (sup T n) (sup R n).
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Same_set; unfold Included...
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

  Lemma le_total : forall n m, (n <= m) \/ (m <= n).
  Proof with auto.
    intros n.
    induction n; intros.
      left. apply le_0_n.
      induction m. 
        right. apply le_0_n. 
        inversion IHm. 
          left... 
          inversion H; subst.
            left. right. left.
            right. apply le_n_S...
  Qed.

  Lemma Finite_have_maximal_element : 
    forall (T : Ensemble carrier), Finite T -> Inhabited T -> exists u, ((In T u) /\ 
      (forall v, (In T v) -> dim v <= dim u)).
  Proof with repeat basic; auto.
    intros.
    induction H.
      inversion H0. inversion H. 
      
      assert ((A == Empty_set _) \/ (Inhabited A)). apply Finite_Empty_or_Inhabited. assumption.
           inversion H2. 
           exists x... apply Add_intro2. unfold Add in H4... inversion H4.
           apply (In_Same_set' _ _ H3) in H5. inversion H5. apply Singleton_inv in H5.        
           subst. apply le_refl. 
           apply IHFinite in H3. inversion H3 as [z]. 
           assert (((dim x) <= (dim z)) \/ ((dim z) <= (dim x))). apply le_total.
           inversion H5; [exists z | exists x]... left... unfold Add in H4...
           inversion H4... apply Singleton_inv in H10; subst...
           right... apply Singleton_intro... unfold Add in H4...
           inversion H4... apply (le_trans _ (dim z) _)... 
           apply Singleton_inv in H10; subst...

      assert (Inhabited T). inversion H0. eapply (Inhabited_intro _ _ x). 
      apply (In_Same_set' _ _ H1)... 
      apply IHFinite in H2. inversion H2. exists x...
      symmetry in H1. apply (In_Same_set' _ _ H1)... 
      apply H5. apply (In_Same_set' _ _ H1)...  
  Qed. 

  Lemma cell_has_dim : forall M P, is_a_cell M P -> exists m, celldim M P m.
  Proof with repeat basic; auto.
    intros.
    unfold is_a_cell in H...
    assert (Finite (Union M P)). 
    apply Finite_Union.
    apply all_decidable. 
    assumption.
    assumption. 
    apply Finite_have_maximal_element in H6.
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

  Lemma Inhabited_Included {U} : 
    forall (S : Ensemble U), Inhabited S -> forall T, Included S T -> Inhabited T.
  Proof.
    unfold Included. intros.
    inversion H. eapply (Inhabited_intro). apply H0. apply H1. 
  Qed.

  Definition source (n : nat) (A : cell) : cell.
    inversion A. rename cell_M0 into M. rename cell_P0 into P. 
    apply (Build_cell (sup M n) ((sub M n) ∪ (sup P n))). 
  Proof with repeat (basic || subsuptac); repeat basic2; auto.
    unfold is_a_cell in cell_axioms0...
    (* I THINK WE NEED THIS BASIC CONDITION, CHECK WITH DOM *)
    assert (forall x, In M x -> dim x <= n) as ASS1. admit.
    assert (forall x, In P x -> dim x <= n) as ASS2. admit.
    unfold is_a_cell... 
    (**) apply (Inhabited_intro _ _ x0)...
    (**) apply (Inhabited_intro _ _ x)... right...
    (**) unfold well_formed... apply (H9 n0)...
    (**) unfold well_formed... apply (H9 n0)...
    (**) eapply Finite_Included. apply all_decidable. apply H3. 
      apply sup_Included.
    (**) apply Finite_Union...  
      eapply Finite_Included. apply all_decidable. apply H4. apply sup_Included.
      eapply Finite_Included. apply all_decidable. apply H3. apply sub_Included.  
    (**) unfold moves_def...
    assert ((sup P n) == sup ((M ∪ Plus M) ∩ √Minus M) n). apply sup_Same_set. 
    unfold moves_def in H5...
    rewrite H0... clear H0.
    unfold Same_set; unfold Included... 
    inversion H0.
     left... apply (In_Same_set' _ _ (sup_Intersection (M ∪ Plus M) (√Minus M) n)) in H10... 
     inversion H12. left... right...
    unfold In, Plus.
    unfold In, Plus in H11.
    inversion H11. exists x2...
    inversion H0. apply In_Complement. unfold not; intros. unfold In, Minus in H10; inversion H10...
    unfold In, Minus in H11; inversion H11... apply minus_dim in H16. rewrite <- H16 in H19.
    rewrite <- H13 in H19. eapply le_Sn_n. apply H19.
    apply (In_Same_set' _ _ (sup_Intersection (M ∪ Plus M) (√Minus M) n)) in H10... 
    apply In_Complement. unfold not. intros. assert (x1 ∈ Minus M -> False). intros... apply H15. 
    unfold In, Minus in H11. inversion H11...
    unfold In, Minus. exists x3...
    inversion H10. right... 
    apply In_Complement. unfold not. intros. assert (x1 ∈ Minus M -> False). intros... apply H11. 
    inversion H0... unfold In, Minus. exists x2... apply H14...
    right... 
    inversion H0... right... unfold In, Plus. exists x2...
    apply In_Complement. unfold not. intros. apply H11. 
    unfold In, Minus. inversion H12... exists x2... unfold In, Plus in H0.
    inversion H0... apply plus_dim in H15. apply (le_trans _ (dim x2) _). apply plus_dim in H14. 
    rewrite <- H14... assumption.
admit.
admit.
Qed.

  Definition target (n : nat) (A : cell) : cell.
    inversion A. apply (Build_cell ((sup cell_M0 n) ∪ (sub cell_P0 n)) (sup cell_P0 n)). Admitted.

  Definition composable (n : nat) (A B : cell) : Prop := (target n A === source n B). 

  Definition composite (n : nat) (A B : cell) : cell.
   inversion A.
   inversion B.
   rename cell_M0 into M.
   rename cell_P0 into P.
   rename cell_M1 into N.
   rename cell_P1 into Q.
   apply (Build_cell (M ∪ (N ∩ √(sub N n))) ((P ∩ √(sub P n)) ∪ Q)).
   Proof with repeat basic; repeat basic2; auto.
     unfold is_a_cell in cell_axioms0. 
     unfold is_a_cell in cell_axioms1. 
     unfold is_a_cell... 
     (**)apply (Inhabited_intro _ _ x0). left...
     (**)apply (Inhabited_intro _ _ x1). right... 
     (**)eapply Finite_Union. apply all_decidable.
     eapply Finite_Included. apply all_decidable. apply H3.
     unfold Included... apply H11.
     (**)eapply Finite_Union. apply all_decidable. apply H4.
     eapply Finite_Included. apply all_decidable. apply H12.
     unfold Included...
     clear H14 H9 H6 H1 x x0 x1 x2. 
     (**) admit. 
     (**) admit. 
   Qed.

  Definition receptive (S : Ensemble carrier) : Prop :=
    (forall x, (Plus (minus x)) ∩ (Plus (plus x)) ⊆ S ->
       (Inhabited (S ∩ (Minus (minus x))) -> False) ->
       (Inhabited (S ∩ (Minus (plus x))) -> False))  /\ 
    (forall x, (Minus (plus x)) ∩ (Minus (minus x)) ⊆ S ->
       (Inhabited (S ∩ (Plus (plus x))) -> False) ->
       (Inhabited (S ∩ (Plus (minus x))) -> False)).

  Definition cell_receptive (M P : Ensemble carrier) : Prop :=
    receptive M /\ receptive P.

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
      unfold Included in H2. apply H2. apply (In_Same_set' _ _ H3)... clear H3.
    assert (Disjoint M (Plus(minus x))).
      unfold receptive in H0... apply (H5 x). 
      Focus 3. eapply (Inhabited_intro)... apply H6. assumption.
      Focus 2. intros... inversion H0; clear H0... 
       unfold moves_def in H... apply (In_Same_set' _ _ H10) in H0...
      unfold moves_def in H... unfold Included...
        assert ((In (Plus (plus x)) x1) \/ ~(In (Plus (plus x)) x1)). apply all_decidable.
        inversion H. pose (Prop_1_1 x)... assert (In (Empty_set _) x1). apply (In_Same_set' _ _ H14)...
        inversion H12. symmetry in H8. apply (In_Same_set' _ _ H8)...
    assert (exists Y, minus x moves M to Y). apply Prop_2_1. 
    constructor; assumption. inversion H5 as [P']. clear H5.
    assert (P == P'). unfold moves_def in H6. inversion H6. clear H6. rewrite H5. 
      symmetry. rewrite I_U_dist_r. remember (Prop_1_1 x). clear Heqa... 
      unfold PlusMinus in H8. rewrite H8. inversion H; clear H. rewrite H3.
      rewrite I_U_dist_r.
      assert ((Plus (plus x) ∩ √Minus (plus x)) == (Plus (minus x) ∩ Plus (plus x))).        
        unfold Same_set; unfold Included...
        assert (x0 ∈ (Plus (plus x) ∪ Minus (minus x))). left. assumption. 
        apply (In_Same_set' _ _ (axiom1 x)) in H... inversion H...
        apply In_Complement... assert (In (Plus (minus x) ∩ Plus (plus x)) x0).
        do 2 basic. assumption. assumption. apply (In_Same_set' _ _ H11) in H17.
        unfold PlusMinus in H17...
      assert ((M ∩ √Minus (plus x)) == (M ∩ √Minus (plus x) ∩ √Plus (minus x))). 
        unfold Same_set; unfold Included... apply In_Complement... unfold not in H6. 
        apply (H6 x0)...
      assert ((M ∩ √Minus (minus x)) == (M ∩ √Minus (minus x) ∩ √Plus (plus x))). 
        unfold Same_set; unfold Included... apply In_Complement... 
        apply (In_Same_set' _ _ H14) in H17...
      rewrite H15. rewrite H16. 
      rewrite H.
      repeat rewrite (Intersection_trans M _ _). repeat rewrite Union_Complement_compat.
      rewrite (Union_sym (Minus (minus x)) _). rewrite (axiom1 x).
      rewrite (Union_sym _ (Minus (plus x))).
      reflexivity.        
      
    unfold moves_def. unfold moves_def in H6. rewrite <- H5 in H6. 
    assumption. 
  Qed.

  Lemma nat_ind_012 :
    forall P : nat -> Prop, 
     P 0 -> P 1 -> P 2 -> 
    (∀ n : nat, P (S (S n)) → P (S (S (S n)))) -> 
     ∀ n : nat, P n.
  Proof with try assumption.
    intros.
    destruct n...
    destruct n...
    induction n...
    apply H2...
  Qed.

  Lemma Lemma_3_2_b : 
    (forall M P : Ensemble carrier, is_a_cell M P -> cell_receptive M P) ->
    forall (n : nat) M P, (is_a_cell M P /\ celldim M P n) ->
    forall X, (X ⊆ (sub (Full_set _) (S n))) /\ Finite X /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n)) ->
    exists Y, (Y = ((sub M n) ∪ Minus X) ∩ √(Plus X)) /\ is_a_cell ((sup M (n-1)) ∪ Y) ((sup P (n-1)) ∪ Y) /\ (Minus X ∩ (sub M n) == Empty_set _).
  Proof with repeat basic; auto.
    intros...
    remember ((sub M n ∪ Minus X) ∩ √Plus X) as Y. rewrite HeqY. 
    assert (exists m, cardinal X m). apply cardinality_exists...
    inversion H0 as [m card_X]; clear H0.
    induction m.
      admit. clear IHm.
    induction m.
      apply cardinality_one_Singleton in card_X.
      inversion card_X; clear card_X.
      assert (Plus X == plus x). unfold Same_set, Included... inversion H7...
        apply (In_Same_set' X _ H0) in H9. inversion H9. subst... unfold Plus. unfold In at 1. 
        exists x... eapply (In_Same_set'). symmetry in H0. apply H0. constructor.
      assert (Minus X == minus x). unfold Same_set, Included... inversion H8...
        apply (In_Same_set' X _ H0) in H10. inversion H10. subst... unfold Minus. unfold In at 1. 
        exists x... eapply (In_Same_set'). symmetry in H0. apply H0. constructor.
      assert (plus x ⊆ sub M n). unfold Included. intros. assert (x0 ∈ minus x ∨ ¬x0 ∈ minus x)...
        apply all_decidable. inversion H10. exfalso. remember (plus_minus_disjoint x) as K. admit. 
        unfold Included in H5. apply H5. unfold PlusMinus. admit. 
      induction n. 
        (* n = 0 *)
        assert (plus x == sub M 0). admit.
        assert (minus x == Y). admit.
        assert (dim x = 1). admit.
        exists Y...
        admit. 
        rewrite H8. rewrite <- H10. rewrite (Intersection_sym). apply plus_minus_disjoint.
        rewrite H12...

        (* n > 0 *)        
        assert (is_a_segment (plus x) (sub M (S n))). apply Prop_1_3.
        admit. admit. admit.
        assert (exists S T, (sub M n) == Union (Union S (plus x)) T) as decompMn. admit.
        inversion decompMn as [S decomp]. clear decompMn. inversion decomp as [T decompMn].
        clear decomp.
        Admitted.

  Lemma Lemma_3_2_c : 
  (forall M P : Ensemble carrier, is_a_cell M P -> cell_receptive M P) ->
    forall (n : nat) M P, (is_a_cell M P /\ celldim M P n) ->
      forall X, (X ⊆ (sub (Full_set _) (S n))) /\ Finite X /\ well_formed X /\ ((PlusMinus X) ⊆ (sub M n)) ->
    exists Y, (Y = ((sub M n) ∪ Minus X) ∩ √(Plus X)) /\ is_a_cell ((sup M (n-1)) ∪ Y ∪ X) (P ∪ X).
  Proof with repeat basic; auto.
    intros...
    exists (((sub M n) ∪ Minus X) ∩ √Plus X)...
    unfold is_a_cell...
    admit.
    admit.
      unfold is_a_cell in H4...
      apply Finite_Union...
      apply Finite_Union... 
      assert (Finite (√Plus X ∩ (sub M n ∪ Minus X))).
      eapply Finite_Intersection. apply Finite_Union... 
      assert (forall Y, Finite Y -> Finite (Minus Y)) as L. 
        intros. induction H12. 
        apply (Same_set_is_finite (Empty_set _)). constructor.
        unfold Same_set, Included, In... unfold Minus in H12. inversion H12... inversion H12.
        inversion H12.
        apply (Same_set_is_finite (Union (Minus A) (minus x))). apply Finite_Union...
        apply minus_fin. unfold Same_set, Included... unfold Minus in H15. unfold In at 1 in H15...
        inversion H15... left... unfold Minus, In. exists x1... right. inversion H16. assumption.  
        inversion H15. inversion H16... exists x1... left... exists x... right... constructor. 
        eapply Same_set_is_finite.  apply IHFinite. unfold Same_set, Included, Minus, In...
        exists x0... eapply In_Same_set'. apply H14... assumption. symmetry in H14.
        exists x0... eapply In_Same_set'. apply H14... assumption.
        apply L...
      eapply Finite_Included. apply all_decidable. apply H9.
      apply sub_Included... basic. 
      eapply Same_set_is_finite. apply H12. apply Intersection_sym.
      eapply Finite_Included. apply all_decidable. apply H9. apply sup_Included.

      unfold is_a_cell in H4... apply Finite_Union... 

    assert (exists Y, (Y = ((sub M n) ∪ Minus X) ∩ √(Plus X)) /\ is_a_cell ((sup M (n-1)) ∪ Y) ((sup P (n-1)) ∪ Y) /\ (Minus X ∩ (sub M n) == Empty_set _)).
    apply Lemma_3_2_b...
    inversion H0... rewrite H0 in H9; clear H0. rename x into Y. 
    rewrite <- H8 in H9. rewrite <- H8.
    unfold is_a_cell in H9...
    unfold moves_def in *...
    assert (((Y ∪ (Plus X)) ∩ (√(Minus X))) == (sub M n)). 
    rewrite H8. rewrite (U_I_dist_r). rewrite Full_set_property.
    rewrite Full_set_ident_right. rewrite (I_U_dist_r). rewrite (I_U_dist_r). 
    rewrite Empty_set_property. rewrite Empty_set_ident_right.
    apply (Same_set_trans _ ((sub M n) ∪ (Plus X ∩ √Minus X)) _). apply Union_mor...
    unfold Same_set, Included... unfold Complement, not. unfold In at 1. intros. 
    assert (In (Minus X ∩ sub M n) x). apply In_Intersection. split; assumption. apply (In_Same_set' _ _ H10) in H22. 
    inversion H22. assert ((Plus X ∩ √Minus X) == (PlusMinus X)). unfold Same_set, Included, PlusMinus...
    rewrite H16. unfold Included in H5. unfold Same_set, Included... inversion H21... basic.

Admitted.

  Lemma Prop_3_3 :
    (forall M P : Ensemble carrier, is_a_cell M P -> cell_receptive M P).
  Proof with repeat basic; auto.
    intros. 
    assert (∃ m : nat, celldim M P m). apply cell_has_dim...
    inversion H0 as [m]; clear H0.  
    inversion H; clear H...
    unfold celldim in H1. unfold setdim in H1.
    destruct m. 
      unfold cell_receptive; split; unfold receptive; split. 
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

  Lemma Theorem_3_6b :
    forall M P N Q (n: nat), 
      is_a_cell M P -> is_a_cell N Q -> 4 = 4 ->
      Minus (M ∪ P) ∩ Plus (N ∪ Q) == Empty_set _.
  Admitted. 

  (* Section 4 *)

  Definition mu_proper (x : carrier) : Ensemble carrier :=
    fun y => exists T n, In T y /\ mu x n T.

  Notation "'<<' x '>>'" := ((mu_proper x) (mu_proper x)) (at level 85).

  Lemma Theorem_4_1 :
    forall M P n, is_a_cell M P ->
    forall u, u ∈ M -> ~((M, P) = (mu_proper u, mu_proper u)) ->
    exists N Q L R, is_a_cell N Q /\ is_a_cell L R /\ celldim N Q n /\ (celldim L R n) /\
    (exists (m : nat), (m < n) /\ ~(celldim N Q m) /\ ~(celldim L R m)) /\
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






