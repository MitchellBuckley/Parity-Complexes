
(** Written by Mitchell Buckley. Started on 25/11/2013 while a PhD student at Macquarie University **)

(**
  This collection began as a set results needed for dealing with Parity complexes.
  That is still its primary function, but it now covers a wide range of rewrite rules
  for Ensembles and a large library of basic results concerning Ensembles, Intersection,
  Union etc.
**)

(** Import libraries **)

Require Import Ensembles.
Require Import Setoid.
Require Import Utf8_core.

(** Set Implicit variables **)

Arguments In : default implicits.
Arguments Setminus : default implicits.
Arguments Disjoint : default implicits.
Arguments Inhabited : default implicits.
Arguments Intersection : default implicits.
Arguments Union : default implicits.
Arguments Same_set : default implicits.
Arguments Included : default implicits.
Arguments Complement : default implicits.
Arguments Empty_set {U} _.
Arguments Full_set {U} _.

Hint Unfold Complement.

(** Notation **)

Notation "A == B"      := (Same_set A B) (at level 79).
Notation "A ∪ B"       := (Union A B) (at level 61).
Notation "A ∩ B"       := (Intersection A B) (at level 61).
Notation "A ⊆ B"       := (Included A B) (at level 79).
Notation "x ∈ A"       := (In A x) (at level 71).
Notation "√ A"         := (Complement A) (at level 51).
Notation "A == B == C" := ((A == B) /\ (B == C)) (at level 79, B at next level).
Notation "A ⊆ B ⊆ C"   := ((A ⊆ B) /\ (B ⊆ C)) (at level 79, B at next level).

(** Definition of decidability **)

Definition decidable {A : Type} (X : Ensemble A) : Prop :=
  forall (x : A), (x ∈ X) \/ ~(x ∈ X).

Hint Unfold decidable.

(** Tactics **)

Ltac disj := 
  match goal with
    | H: ?P \/ ?Q |- _ => inversion H; clear H
    | H: (?P ∪ ?Q) ?x |- _ => inversion H as [a K aeq | b K beq]; [clear H aeq a | clear H beq b]; unfold In in K
    | H: ?P ?x |- (?P ∪ ?Q) ?x => left
    | H: ?Q ?x |- (?P ∪ ?Q) ?x => right
 end.

Ltac conj := 
  match goal with
    | H: (?P ∩ ?Q) ?x |- _ => inversion H as [a H1 H2 aeq]; clear H a aeq
    | H: ?P /\ ?Q |- _ => inversion H; clear H
    | H: _ |- (?P ∩ ?Q) ?x => split
    | H: _ |- (?P /\ ?Q) => split
  end; unfold In in *.

Ltac neg :=
  match goal with
    | H: (√(?P)) ?x |- _ => unfold Complement in H; unfold In, not in H
    | H: _ |- (√(?P)) ?x => unfold Complement; unfold In, not
  end.

Ltac misc :=
  match goal with
    | H: ?P, K: ?P -> False |- _ => contradiction
    | H: Empty_set ?x |- _ => contradiction
    | H: Full_set ?x |- _ => clear H
    | H: _ |- Full_set ?x => constructor
    | H: ?a = ?b |- _ => subst
    | H: Singleton ?a ?a |- _ => clear a
    | H: Singleton ?a ?b |- _ =>   inversion H as [K]; clear H; try rewrite K in *; clear K
    | H: Disjoint ?a ?b |- _ => inversion H as [L]; clear H; unfold not, In in L 
    | H: _ |- Disjoint ?a ?b => constructor; unfold In, not; intros
    | H: Inhabited ?S |- _ => inversion H; clear H
end.

Ltac crush := 
   autounfold with *;
   intuition; 
   repeat (conj || disj || neg || misc); 
   auto.

  (** Setoid relations and morphisms **)

  (** Same_set: **)

  Lemma Same_set_sym {U : Type} :
    forall (S T : Ensemble U), S == T -> T == S.
  Proof with crush.
    crush.
  Qed.

  Lemma Same_set_refl {U : Type} :
    forall (S : Ensemble U), S == S.
  Proof with crush.
    crush.
  Qed.

  Lemma Same_set_trans {U : Type} :
    forall (S T R : Ensemble U), S == T -> T == R -> S == R.
  Proof with crush.
    crush.
  Qed.

  Add Parametric Relation (U: Type) : (Ensemble U) (@Same_set U)
    reflexivity proved by (Same_set_refl (U:=U))
    symmetry proved by (Same_set_sym (U:=U))
    transitivity proved by (Same_set_trans (U:=U))
  as set_eq.

  Lemma Intersection_Same_set_compat {U : Type} :
    forall (S S': Ensemble U), S == S'
    ->
    forall (T T': Ensemble U), T == T'
    ->
    (S ∩ T) == (S' ∩ T').
  Proof with crush.
    crush; inversion H; eauto.
  Qed.

  Add Parametric Morphism U : (@Intersection U) with 
    signature (@Same_set U) ==> (@Same_set U) ==> (@Same_set U) as Intersection_mor.
  Proof.
    apply Intersection_Same_set_compat.
  Qed.

  Lemma Union_Same_set_compat {U : Type} :
    forall (S S': Ensemble U), S == S'
    ->
    forall (T T': Ensemble U), T == T'
    ->
    (Union S T) == (Union S' T').
  Proof with crush.
    crush. 
    left... right... left... right...
  Qed.

  Add Parametric Morphism U : (@Union U) with 
    signature (@Same_set U) ==> (@Same_set U) ==> (@Same_set U) as Union_mor.
  Proof.
    apply Union_Same_set_compat.
  Qed.

  Lemma Complement_Same_set_compat {U : Type} :
    forall (S T: Ensemble U), S == T
    ->
    (√ S) == (√ T).
  Proof with crush.
    crush.
  Qed.

  Add Parametric Morphism U : (@Complement U) with 
    signature (@Same_set U) ==> (@Same_set U) as Complement_mor.
  Proof.
    apply Complement_Same_set_compat.
  Qed.

  Add Parametric Morphism U : (@Included U) with 
    signature (@Same_set U) ==> (@Same_set U) ==> (@iff) as Included_Same_set_mor.
  Proof with crush.
    crush. 
  Qed.

  Add Parametric Morphism U : (@Inhabited U) with 
    signature (@Same_set U) ==> (@iff) as Inhabited_Same_set.
  Proof with crush.
    crush; exists x0...
  Qed.

  Add Parametric Morphism U : (@Disjoint U) with 
    signature (@Same_set U) ==> (@Same_set U) ==> (@iff) as Disjoint_Same_set.
  Proof with crush.
    crush.    (* why doesn't conj. find a match here? **)
    inversion H2; clear H2; subst; unfold In in *. 
    apply (L x1)...
    inversion H2; clear H2; subst; unfold In in *.
    apply (L x1)...
  Qed.

  Add Parametric Morphism U: (@Add U) with 
    signature (@Same_set U) ==> (@eq U) ==> (@Same_set U) as Add_mor.
  Proof with crush.
    crush. left... left... 
  Qed.

  Add Parametric Morphism U : (@In U) with 
    signature (@Same_set U) ==> (@eq U) ==> (@iff) as In_Same_set_mor.
  Proof with crush.
    crush.
  Qed.

  Add Parametric Morphism U : (@Setminus U) with 
    signature (@Same_set U) ==> (@Same_set U) ==> (@Same_set U) as Setminus_Same_set_mor.
  Proof with crush.
    crush.
  Qed.

  (** Inclusion: *)

  Lemma Included_trans {U : Type} :
    forall (S T R : Ensemble U), Included S T -> Included T R -> Included S R.
  Proof with crush.
    crush.
  Qed.

  Lemma Included_refl {U : Type} :
    forall (S : Ensemble U), Included S S.
  Proof with crush.
    crush.
  Qed.

  Add Parametric Relation (U: Type) : (Ensemble U) (@Included U)
    reflexivity proved by (Included_refl (U:=U))
    transitivity proved by (Included_trans (U:=U))
  as set_incl.

  Lemma Union_Included_compat {U : Type} :
    forall (S T : Ensemble U), S ⊆ T 
    → 
    forall (S' T' : Ensemble U), S' ⊆ T' 
    → 
    (S ∪ S') ⊆ (T ∪ T').
  Proof with crush.
    crush.
    left... right...
  Qed.

  Add Parametric Morphism U : (@Union U) with 
    signature (@Included U) ==> (@Included U) ==> (@Included U) as Union_incl_mor.
  Proof.
    apply Union_Included_compat.
  Qed.

  Lemma Intersection_Included_compat {U : Type} :
    forall (S T : Ensemble U), S ⊆ T 
    → 
    forall (S' T' : Ensemble U), S' ⊆ T' 
    → 
    (S ∩ S') ⊆ (T ∩ T').
  Proof with crush.
    crush; inversion H1...
  Qed.

  Add Parametric Morphism U : (@Intersection U) with 
    signature (@Included U) ==> (@Included U) ==> (@Included U) as Intersection_incl_mor.
  Proof.
    apply Intersection_Included_compat.
  Qed.

  Lemma Complement_Included_compat {U : Type} :
    forall (T S : Ensemble U), S ⊆ T 
    → 
    Included (√ T) (√ S).
  Proof with crush.
    crush.
  Qed.

  Add Parametric Morphism U : (@Complement U) with 
    signature (@Included U) --> (@Included U) as Complement_incl_mor.
  Proof.
    apply (Complement_Included_compat).
  Qed.

  (** Iff: *)

  Add Parametric Relation : (Prop) (@iff)
    reflexivity proved by (iff_refl)
    symmetry proved by (iff_sym)
    transitivity proved by (iff_trans)
  as prop_iff.

  Lemma or_iff_compat :
    forall (S T : Prop), iff S T 
    → 
    forall (S' T' : Prop), iff S' T' 
    → 
    iff (S \/ S') (T \/ T').
  Proof with intuition. 
    autounfold with *... 
  Qed.

  Add Parametric Morphism : (@or) with 
    signature (@iff) ==> (@iff) ==> (@iff) as or_iff_mor.
  Proof.
    apply or_iff_compat.
  Qed.

  Lemma and_iff_compat :
    forall (S T : Prop), iff S T 
    → 
    forall (S' T' : Prop), iff S' T' 
    → 
    iff (S /\ S') (T /\ T').
  Proof with intuition. 
    autounfold with *... 
  Qed.

  Add Parametric Morphism : (@and) with 
    signature (@iff) ==> (@iff) ==> (@iff) as and_iff_mor.
  Proof.
    apply and_iff_compat.
  Qed.

  Lemma not_iff_compat :
    forall (S T : Prop), iff S T 
    → 
    iff (not S) (not T).
  Proof with intuition. 
    autounfold with *... 
  Qed.

  Add Parametric Morphism : (@not) with 
    signature (@iff) ==> (@iff) as not_iff_mor.
  Proof.
    apply not_iff_compat.
  Qed.

  (* IMPLICATION *)
  
  (*
    
  Definition impl (S T : Prop) : Prop := S -> T.

  Lemma impl_iff_compat :
    forall (S T : Prop), iff S T 
    → 
    forall (S' T' : Prop), iff S' T' 
    → 
    iff (S -> S') (T -> T').
  Proof with intuition. 
    autounfold with *... 
  Qed.

  Add Parametric Morphism : (@impl) with 
    signature (@iff) ==> (@iff) ==> (@iff) as impl_iff_mor.
  Proof.
    apply impl_iff_compat.
  Qed.
  
  *)

  (** Distribition laws **)

  Lemma I_U_dist_l {U : Type} :
    forall (S T R: Ensemble U), (S ∩ (Union T R)) == (Union (S ∩ T) (S ∩ R)).
  Proof with crush.
    crush.
    left... 
    right...
  Qed.

  Lemma I_U_dist_r {U : Type} :
    forall (S T R: Ensemble U), (Intersection (Union T R) S) == (Union (T ∩ S) (R ∩ S)) .
  Proof with crush.
    crush.
    left... 
    right...
  Qed.

  Lemma U_I_dist_r {U : Type} :
    forall (S T R: Ensemble U), (Union (T ∩ R) S) == ((Union T S) ∩ (Union R S)).
  Proof with crush.
    autounfold with *.
    intuition.
    disj. conj. conj; left... conj; right... 
    conj. disj. inversion H1. left; intuition. right... 
    inversion H1. right; auto. right; auto.
  Qed.

  Lemma U_I_dist_l {U : Type} :
    forall (S T R: Ensemble U), (Union S (T ∩ R)) == ((Union S T) ∩ (Union S R)).
  Proof with crush. 
    autounfold with *.
    intuition.
    disj. conj. left... left... conj. conj. right... right...
    conj. disj. left... inversion H1. left... right...
  Qed.

  (** Properties of Full_set and Empty_set **)

  Lemma Full_set_property {U : Type} :
    forall (S : Ensemble U), decidable S -> (Union (√ S) S) == (Full_set).
  Proof with crush. 
    crush.
    specialize H with (x:=x). 
    disj; [right | left]...
  Qed.

  Lemma Empty_set_property {U : Type} :
    forall (S : Ensemble U), (S ∩ (√ S)) == (Empty_set).
  Proof with crush. 
    crush.
  Qed.

  Lemma empty_def {U : Type} : forall (P : Ensemble U),  (forall x, (~(x ∈ P))) <-> (P == Empty_set).
  Proof with crush. 
    crush.
    apply H in H0...
    apply H0 in H... 
  Qed.

  Lemma full_def {U : Type} : forall (P : Ensemble U),  (forall x, ((x ∈ P))) <-> (P == Full_set).
  Proof with crush. 
    crush.
    apply H1...
  Qed.

  Lemma Empty_set_zero_right {U : Type} : forall T : (Ensemble U), T ∩ (Empty_set) == (Empty_set).
  Proof with crush.
    crush.
  Qed.

  Lemma Empty_set_zero_left  {U : Type} : forall T : (Ensemble U), (Empty_set) ∩ T == (Empty_set).
  Proof with crush.
    crush.
  Qed.

  Lemma Full_set_zero_right {U : Type} : forall T : (Ensemble U), Union T (Full_set) == (Full_set).
  Proof with crush.
    crush. crush.
  Qed.

  Lemma Full_set_zero_left  {U : Type} : forall T : (Ensemble U), Union (Full_set) T == (Full_set).
  Proof with crush.
    crush. crush.
  Qed.

  Lemma Complement_Empty_set {U : Type} : √ (Empty_set) == @Full_set U.
  Proof with crush.
    crush.
  Qed.

  Lemma Complement_Full_set {U : Type} : √ (Full_set) == @Empty_set U.
  Proof with crush.
    autounfold with *. split; intros. unfold not in H. exfalso. apply H. constructor. 
    inversion H. 
  Qed.

  Lemma Add_Empty_is_Singleton {U : Type} :
    forall (x : U), Add U (Empty_set) x == Singleton U x.
  Proof with crush.
    crush.
  Qed. 

  (** MONOID PROPERTIES OF UNION AND INTERSECTION **)

  Lemma Union_trans {U : Type} : forall (S T R : Ensemble U),
    (S ∪ T) ∪ R == S ∪ (T ∪ R).
  Proof with crush. 
    crush.
    inversion K. 
    left... right...
    right... left...
    inversion K. 
    left... right...
  Qed.

  Lemma Union_sym {U : Type} : forall (S T : Ensemble U),
    (S ∪ T) == (T ∪ S).
  Proof with crush. 
    crush.
  Qed.

  Lemma Union_idemp {U : Type} : forall (S : Ensemble U), (Union S S) == S.
  Proof with crush. 
    crush.
  Qed.

  Lemma Intersection_trans {U : Type} : forall (S T R : Ensemble U),
    (S ∩ T) ∩ R == S ∩ (T ∩ R).
  Proof with crush. 
    crush. crush.
    inversion H1...
    inversion H1...
    inversion H2...
    inversion H2...
  Qed.

  Lemma Intersection_sym {U : Type} : forall (S T: Ensemble U), (S ∩ T) == (T ∩ S).
  Proof with crush. 
    crush.
  Qed.

  Lemma Intersection_idemp {U : Type} : forall (S : Ensemble U), (S ∩ S) == S.
  Proof with crush. 
    crush.
  Qed.

  Lemma Full_set_ident_right {U : Type} :
    forall (S : Ensemble U), Same_set (S ∩ (Full_set)) S.
  Proof with crush. 
    crush.
  Qed.

  Lemma Empty_set_ident_right {U : Type} : forall (S : Ensemble U), (Union S (Empty_set)) == S.
  Proof with crush. 
    crush.
  Qed.

  Lemma Empty_set_ident_left {U : Type} :
    forall (S : Ensemble U), Union Empty_set S == S.
  Proof with crush.
    crush.
  Qed.

  Lemma Full_set_ident_left {U : Type} :
    forall (S : Ensemble U), Same_set (Intersection (Full_set) S) S.
  Proof with crush. 
    crush.
  Qed.

  (** COMPLEMENT PROPERTIES **)

  Lemma Union_Complement_compat {U : Type} : forall (S T : Ensemble U),
    (√S ∩ √T) == (√(Union S T)).
  Proof with crush. 
    crush.
    intros H1; apply H. left... 
    intros H1; apply H. right... 
  Qed.

  Lemma Intersection_Complement_compat {U : Type} : forall (S T: Ensemble U), decidable S -> √(S ∩ T) == (Union (√S) (√T)).
  Proof with crush. 
    crush.
    specialize H with (x:=x)...
    right... apply H0... left... 
    inversion H1... inversion H1... 
  Qed.

  Lemma Complement_Complement_compat {U : Type} : forall (S: Ensemble U), decidable S -> (√(√S)) == S.
  Proof with crush. 
    crush.
    specialize H with (x:=x)...
  Qed.

  Lemma Complement_Included_flip {U : Type} : forall S T : Ensemble U, 
    Included T (√ S) -> Included S (√ T).
  Proof with crush.
    autounfold with *...
    apply (H x)...
  Qed.

  Lemma Complement_closure {U : Type}: 
    forall S : Ensemble U, Included S (√ (√ S)). 
  Proof with intuition.
    autounfold with *...
  Qed.

  (** INCLUSION PROPERTIES **)

  Lemma Union_Included_left {U : Type} : 
    forall (S T: Ensemble U), S ⊆ T -> Union S T == T.
  Proof with crush. 
    crush.
  Qed.

  Lemma Union_Included_right {U : Type} : 
    forall (S T: Ensemble U), S ⊆ T -> Union T S == T.
  Proof with crush. 
    crush.
  Qed.

  Lemma Intersection_Included_left {U : Type} : 
    forall (S T: Ensemble U), S ⊆ T -> S ∩ T == S.
  Proof with crush. 
    crush. 
  Qed.

  Lemma Inhabited_Included {U : Type} : 
    forall (S : Ensemble U), Inhabited S -> forall T, Included S T -> Inhabited T.
  Proof with crush.
    crush. apply (Inhabited_intro _ _ x)...
  Qed.

  Lemma Included_Empty_set {U : Type} : 
    forall (S T : Ensemble U), Included S T -> T  == (Empty_set) -> S  == (Empty_set).
  Proof with crush.
    crush.
  Qed.

  Lemma Included_Full_set {U : Type} : 
    forall (S T : Ensemble U), Included S T -> S  == (Full_set) -> T == (Full_set).
  Proof with crush.
    crush.
  Qed.

  Lemma Union_Included_cancel_right {U : Type} : forall S T R: (Ensemble U), 
    Included S R -> Included S (Union R T).
  Proof with crush.
    crush. left...
  Qed.

  Lemma Union_Included_cancel_left {U : Type} : forall S T R: (Ensemble U), 
    Included S R -> Included S (Union T R).
  Proof with crush.
    crush... right...
  Qed.

  Lemma Intersection_Included_cancel_right {U : Type} : forall S T R: (Ensemble U), 
    Included S R -> Included (S ∩ T) R.
  Proof with crush.
    crush...
  Qed.

  Lemma Intersection_Included_cancel_left {U : Type} : forall S T R: (Ensemble U), 
    Included S R -> Included (T ∩ S) R.
  Proof with crush.
    crush...
  Qed.

  (** PROPERTIES OF DISJOINT **)

  Lemma Disjoint_Intersection_condition {U : Type} : 
    forall (S T : Ensemble U), (Disjoint S T) <-> (S ∩ T == Empty_set).
  Proof with crush. 
    crush.
    exfalso. apply (L x)... assert (Empty_set x)... 
  Qed.

  Lemma Disjoint_result {U : Type} : 
    forall (S T : Ensemble U), S ∩ T == Empty_set -> S == S ∩ (√ T).
  Proof with crush.
    crush. intros. assert (Empty_set x)... apply H0... 
    inversion H...
  Qed.

  Lemma Disjoint_property_left {U : Type} : forall S T: (Ensemble U), 
    Disjoint S T -> Included S (√ T).
  Proof with crush.
    crush... apply (L x)...
  Qed.

  Lemma Disjoint_property_right {U : Type} : forall S T: (Ensemble U), 
    Disjoint S T -> Included T (√ S).
  Proof with crush.
    crush... apply (L x)...
  Qed.

  Lemma Disjoint_sym {U : Type} : forall S T: (Ensemble U), Disjoint S T <-> Disjoint T S.
  Proof with crush.
    intros S T; split; intros H; inversion H as [K]; constructor...
    apply (K x)...
    apply (K x)...
  Qed.

  (** EXTRA MEMBERSHIP PROPERTIES **)

  Lemma In_Union {U : Type} :
    forall (x : U) (S T: Ensemble U),  x ∈ (S ∪ T) <-> (x ∈ S) \/ (x ∈ T).
  Proof with crush.
    crush.
  Qed.

  Lemma In_Intersection {U : Type} :
    forall (x : U) (S T: Ensemble U), x ∈ (S ∩ T) <-> (x ∈ S) /\ (x ∈ T).
  Proof with crush.
    crush. 
  Qed. 

  Lemma In_Complement {U : Type} :
    forall (S : Ensemble U) (x : U), (x ∈ (√ S)) <-> (~ (x ∈ S)).
  Proof with crush.
    crush.
  Qed.

  (** OTHER MISCELLANEOUS RESULTS **)

  Lemma Setminus_is_Intersection_Complement {U : Type} :
    forall (S T: Ensemble U), (Setminus S T) == (S ∩ (√ T)).
  Proof with crush. 
    crush.
  Qed.

  Lemma add_subtract {U : Type} : 
    forall (A : Ensemble U) x, decidable (Singleton U x) -> (x ∈ A) -> (A == Add U (Setminus A (Singleton U x)) x).
  Proof with crush. 
    crush.
    specialize H with (x0:=x0)...
    left...
    inversion K...
  Qed.

  Lemma Included_Singleton {U : Type} : forall S, @Inhabited U S ->
     forall a, Included S (Singleton U a) -> S == (Singleton U a).
  Proof with intuition.
    intros.
    unfold Same_set...
    unfold Included...
    inversion H1; clear H1; subst.
    inversion H; clear H.
    assert (x0 ∈ Singleton U x). 
    apply H0...
    inversion H...
  Qed.

  Lemma Add_Setminus_Singleton {U : Type} : 
    (forall (a b : U), ((a=b) \/ ~(a=b))) -> 
    forall x X, @In U X x -> 
      (X == Add U (Setminus X (Singleton U x)) x).
  Proof with intuition.
    intros. 
    unfold Same_set, Included, Add, Setminus...
      - assert ((x0 = x) \/ ~(x0 = x))...
        + right... rewrite H3... 
        + left... unfold In at 1... inversion H2...
      - apply In_Union in H1... 
        + unfold In at 1 in H2...
        + inversion H2... rewrite <- H1... 
  Qed.  

  Lemma Disjoint_three {U : Type} : 
    forall S T R, @Disjoint U S R /\ Disjoint T R -> 
      Disjoint (Union S T) R.
  Proof with intuition.
    intros...
    constructor...
    apply In_Intersection in H... 
    apply In_Union in H2... 
    inversion H0; clear H0... 
      apply (H2 x)... 
    inversion H1; clear H1... 
      apply (H2 x)...
  Qed.

  Lemma Setminus_cancel {U : Type} : forall S, Setminus S S == @Empty_set U.
  Proof with intuition.
    intros...
    crush.
  Qed. 

  Lemma Setminus_Empty_set {U : Type}: forall T, Setminus T (@Empty_set U) == T.
  Proof with intuition. 
    unfold Setminus, Same_set, Included...
      unfold In at 1 in H...
      unfold In at 1...
      inversion H0... 
  Qed.

  Lemma add_subtract' :
  ∀ (U : Type) (A B: Ensemble U),
  decidable (A) → Included A B → Union (Setminus B A) A == B. 
Proof with intuition. 
  intros.
  unfold Same_set, Included...
  apply In_Union in H1...
  unfold Setminus, In at 1 in H2...
  assert ((In A x) \/ ~(In A x))...
  apply H.
Qed.


  Hint Resolve Same_set_sym Same_set_refl Same_set_trans.
  Hint Resolve Included_refl Included_trans.
  Hint Resolve Union_trans Union_sym Union_idemp. 
  Hint Resolve Intersection_trans Intersection_sym Intersection_idemp. 
  Hint Resolve Empty_set_ident_left Empty_set_ident_right Full_set_ident_left Full_set_ident_right. 
  Hint Resolve Empty_set_zero_left Empty_set_zero_right Full_set_zero_left Full_set_zero_right. 
