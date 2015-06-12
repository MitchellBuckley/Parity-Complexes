
(** Written by Mitchell Buckley. Started on 25/11/2013 while a PhD student at Macquarie University **)

(**
  This collection began as a set of results needed for dealing with Parity Complexes.
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
Arguments Singleton : default implicits.
Arguments Empty_set {U} _.
Arguments Full_set {U} _.

Hint Constructors Singleton Full_set Empty_set Inhabited.
Hint Unfold Complement.

(** Notation **)

Notation "A == B"      := (Same_set A B) (at level 71).
Notation "A ⊆ B"       := (Included A B) (at level 71).
Notation "x ∈ A"       := (In A x) (at level 71).
Notation "A == B == C" := ((A == B) /\ (B == C)) (at level 71, B at next level).
Notation "A ⊆ B ⊆ C"   := ((A ⊆ B) /\ (B ⊆ C)) (at level 71, B at next level).
Notation "A ∪ B"       := (Union A B) (at level 61).
Notation "A ∩ B"       := (Intersection A B) (at level 61).
Notation "A '\' B"     := (Setminus A B) (at level 61).
Notation "√ A"        := (Complement A) (at level 59).

(** Definition of decidability **)

Definition decidable {A : Type} (X : Ensemble A) : Prop :=
  forall (x : A), (x ∈ X) \/ ~(x ∈ X).

Hint Unfold decidable.

(** Tactics **)

Ltac disj :=
  match goal with
    | H: In (?P ∪ ?Q) ?x |- _ => inversion H; clear H
    | H: In ?P ?x |- In (?P ∪ ?Q) ?x => left
    | H: In ?Q ?x |- In (?P ∪ ?Q) ?x => right
 end.

Ltac conj :=
  match goal with
    | H: In (Intersection _ _) _ |- _ => inversion H; clear H
    | H: _ |- In (?P ∩ ?Q) ?x => constructor
  end.

Ltac neg :=
  match goal with
    | H: In (√(?P)) ?x |- _ => unfold Complement, not, In at 1 in H
    | H: _ |- In (√(?P)) ?x => unfold Complement, not, In at 1
  end.

Ltac misc_2 :=
  match goal with
    | H: _ |- _ == _ => unfold Same_set
    | H: ?S == ?T |- _ => unfold Same_set in H
    | H: _ |- Included ?S ?T => unfold Included
    | H: Included ?S ?T |- _ => unfold Included in H
    | H: Disjoint ?a ?b |- _ => inversion H; clear H
    | H: _ |- Disjoint ?a ?b => constructor; unfold not; intros
    | H: Inhabited ?S |- _ => inversion H; clear H
 end.

Ltac misc :=
  match goal with
    | H: _ |- In (Setminus ?S ?T) _ => unfold Setminus, In at 1
    | H: In (Setminus ?S ?T) _ |- _ => unfold Setminus, In at 1 in H
    | H: ?x ∈ Add ?U ?A ?y |- _ => unfold Add in H
    | H: _ |- ?x ∈ Add ?U ?A ?y => unfold Add
    | H: In Empty_set ?x |- _ => inversion H
    | H: In Full_set ?x |- _ => clear H
    | H: _ |- In Full_set ?x => constructor
    | H: ?a = ?b |- _ => subst
    | H: In (Singleton ?a) ?a |- _ => clear a
    | H: In (Singleton ?a) ?b |- _ => inversion H as [K]; clear H; try rewrite K in *; clear K
end.


Ltac crush := 
   repeat (repeat (conj || disj || neg || misc || misc_2); intuition); intuition.


  (** EXTRA MEMBERSHIP PROPERTIES **)

  (* Fundamental relationship between union/or, intersection/and, complement/not *)

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

  Hint Resolve In_Union In_Intersection In_Complement. 

  (** Setoid relations and morphisms **)

  (** Same_set: **)

  (* Same_set is symmetric, reflexive and transitive *)

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

  (* Same_set is stable under Intersection, Union, Complement *)

  Lemma Intersection_Same_set_compat {U : Type} :
    forall (S S': Ensemble U), S == S'
    ->
    forall (T T': Ensemble U), T == T'
    ->
    (S ∩ T) == (S' ∩ T').
  Proof with crush.
    crush.
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
    (S ∪ T) == (S' ∪ T').
  Proof with crush.
    crush.
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

  (* Inclusion, Inhabited, Disjunction, Add, In, and Setminus are all compatible with Same_set  *)

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
    crush; apply H2 with x1...
  Qed.

  Add Parametric Morphism U: (@Add U) with
    signature (@Same_set U) ==> (@eq U) ==> (@Same_set U) as Add_mor.
  Proof with crush.
    crush.
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

  (* Inclusion is transitive and reflexive *)

  Lemma Included_trans {U : Type} :
    forall (S T R : Ensemble U), S ⊆ T -> T ⊆ R -> S ⊆ R.
  Proof with crush.
    crush.
  Qed.

  Lemma Included_refl {U : Type} :
    forall (S : Ensemble U), S ⊆ S.
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
    crush. 
  Qed.

  Add Parametric Morphism U : (@Intersection U) with
    signature (@Included U) ==> (@Included U) ==> (@Included U) as Intersection_incl_mor.
  Proof.
    apply Intersection_Included_compat.
  Qed.

  Lemma Complement_Included_compat {U : Type} :
    forall (T S : Ensemble U), S ⊆ T
    →
    (√ T) ⊆ (√ S).
  Proof with crush.
    crush.
  Qed.

  Add Parametric Morphism U : (@Complement U) with
    signature (@Included U) --> (@Included U) as Complement_incl_mor.
  Proof.
    apply Complement_Included_compat.
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
    intuition.
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
    intuition. 
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
    intuition. 
  Qed.

  Add Parametric Morphism : (@not) with
    signature (@iff) ==> (@iff) as not_iff_mor.
  Proof.
    apply not_iff_compat.
  Qed.

  (* IMPLICATION *)

  Definition impl (S T : Prop) : Prop := S -> T.

  Lemma impl_iff_compat :
    forall (S T : Prop), iff S T
    →
    forall (S' T' : Prop), iff S' T'
    →
    iff (S -> S') (T -> T').
  Proof with intuition.
    intuition. 
  Qed.

  Add Parametric Morphism : (@impl) with
    signature (@iff) ==> (@iff) ==> (@iff) as impl_iff_mor.
  Proof.
    apply impl_iff_compat.
  Qed.

  Add Parametric Morphism {U : Type} : (@Disjoint U) with
    signature (@Included U) --> (@Included U) --> (@impl) as Disjoint_impl_mor.
  Proof with crush.
    unfold impl...
    apply H2 with x1...
  Qed.

  (** Distribition laws **)

  (* Intersection distributes over Union on the left *)

  Lemma I_U_dist_l {U : Type} :
    forall (S T R: Ensemble U), (S ∩ (T ∪ R)) == ((S ∩ T) ∪ (S ∩ R)).
  Proof with crush.
    crush.
  Qed.

  (* Intersection distributes over Union on the right *)

  Lemma I_U_dist_r {U : Type} :
    forall (S T R: Ensemble U), ((T ∪ R) ∩ S) == ((T ∩ S) ∪ (R ∩ S)) .
  Proof with crush.
    crush.
  Qed.

  (* Union distributes over Intersection on the right *)

  Lemma U_I_dist_r {U : Type} :
    forall (S T R: Ensemble U), ((T ∩ R) ∪ S) == ((T ∪ S) ∩ (R ∪ S)).
  Proof with crush.
    crush.
  Qed.

  (* Union distributes over Intersection on the left *)

  Lemma U_I_dist_l {U : Type} :
    forall (S T R: Ensemble U), (S ∪ (T ∩ R)) == ((S ∪ T) ∩ (S ∪ R)).
  Proof with crush.
    crush.
  Qed.

  (** Properties of Full_set and Empty_set **)

  (*  *)

  Lemma Full_set_property {U : Type} :
    forall (S : Ensemble U), decidable S -> ((√ S) ∪ S) == (Full_set).
  Proof with crush.
    crush.
    unfold decidable in H.
    specialize H with (x:=x)...
  Qed.

  Lemma Empty_set_property {U : Type} :
    forall (S : Ensemble U), (S ∩ (√ S)) == (Empty_set).
  Proof with crush.
    crush.
  Qed.

  (* Definitive property of the empty set *)

  Lemma Empty_set_def {U : Type} : forall (P : Ensemble U),  (forall x, (~(x ∈ P))) <-> (P == Empty_set).
  Proof with crush.
    crush. 
    apply H in H0...
    apply H1 in H0...
  Qed.

  (* Definitive property of the full set *)

  Lemma Full_set_def {U : Type} : forall (P : Ensemble U),  (forall x, ((x ∈ P))) <-> (P == Full_set).
  Proof with crush.
    crush.
  Qed.

  (* The empty set is zero under Intersection *)

  Lemma Empty_set_zero_right {U : Type} : forall T : (Ensemble U), T ∩ (Empty_set) == (Empty_set).
  Proof with crush.
    crush.
  Qed.

  Lemma Empty_set_zero_left  {U : Type} : forall T : (Ensemble U), (Empty_set) ∩ T == (Empty_set).
  Proof with crush.
    crush.
  Qed.

  (* The full set is zero under Union *)
 
  Lemma Full_set_zero_right {U : Type} : forall T : (Ensemble U), T ∪ (Full_set) == (Full_set).
  Proof with crush.
    crush.
  Qed.

  Lemma Full_set_zero_left  {U : Type} : forall T : (Ensemble U), (Full_set) ∪ T == (Full_set).
  Proof with crush.
    crush.
  Qed.

  (* The empty set and the full set are dual under complement *)
 
  Lemma Complement_Empty_set {U : Type} : √ (Empty_set) == @Full_set U.
  Proof with crush.
    crush.
  Qed.

  Lemma Complement_Full_set {U : Type} : √ (Full_set) == @Empty_set U.
  Proof with crush.
    crush.
    exfalso; apply H... 
  Qed.

  (* Adding one to the empty set creates a singleton *)

  Lemma Add_Empty_is_Singleton {U : Type} :
    forall (x : U), Add U (Empty_set) x == Singleton x.
  Proof with crush.
    crush.
  Qed.

  (** MONOID PROPERTIES OF UNION AND INTERSECTION **)

  (* Union is associative, commutative and idempotent *)

  Lemma Union_trans {U : Type} : forall (S T R : Ensemble U),
    (S ∪ T) ∪ R == S ∪ (T ∪ R).
  Proof with crush.
    crush.
  Qed.

  Lemma Union_comm {U : Type} : forall (S T : Ensemble U),
    (S ∪ T) == (T ∪ S).
  Proof with crush.
    crush.
  Qed.

  Lemma Union_idemp {U : Type} : forall (S : Ensemble U), (S ∪ S) == S.
  Proof with crush.
    crush.
  Qed.

  (* Intersection is associative, commutative and idempotent *)

  Lemma Intersection_trans {U : Type} : forall (S T R : Ensemble U),
    (S ∩ T) ∩ R == S ∩ (T ∩ R).
  Proof with crush.
    crush.
  Qed.

  Lemma Intersection_comm {U : Type} : forall (S T: Ensemble U), (S ∩ T) == (T ∩ S).
  Proof with crush.
    crush.
  Qed.

  Lemma Intersection_idemp {U : Type} : forall (S : Ensemble U), (S ∩ S) == S.
  Proof with crush.
    crush.
  Qed.

  (* The full set is identity for Intersection *)

  Lemma Full_set_ident_left {U : Type} :
    forall (S : Ensemble U), Same_set ((Full_set) ∩ S) S.
  Proof with crush.
    crush.
  Qed.

  Lemma Full_set_ident_right {U : Type} :
    forall (S : Ensemble U), Same_set (S ∩ (Full_set)) S.
  Proof with crush.
    crush.
  Qed.

  (* The full set is identity for Union *)

  Lemma Empty_set_ident_left {U : Type} :
    forall (S : Ensemble U), Empty_set ∪ S == S.
  Proof with crush.
    crush.
  Qed.

  Lemma Empty_set_ident_right {U : Type} : forall (S : Ensemble U), (S ∪ (Empty_set)) == S.
  Proof with crush.
    crush.
  Qed.

  (** COMPLEMENT PROPERTIES **)

  (* Complement preserves Intersection/Union *)
  
  Lemma Union_Complement_compat {U : Type} : forall (S T : Ensemble U),
    (√S ∩ √T) == (√(S ∪ T)).
  Proof with crush.
    crush.
  Qed.

  Lemma Intersection_Complement_compat {U : Type} : forall (S T: Ensemble U), decidable S -> √(S ∩ T) == ((√S) ∪ (√T)).
  Proof with crush.
    crush.
    unfold decidable in H...
    specialize H with (x:=x)...
    right...
  Qed.

  (* Complement is involutive *)
  
  Lemma Complement_Complement_compat {U : Type} : forall (S: Ensemble U), decidable S -> (√(√S)) == S.
  Proof with crush.
    crush.
    unfold decidable in H. 
    specialize H with (x:=x)...
  Qed.

  Lemma Complement_Included_flip {U : Type} : forall S T : Ensemble U,
    T ⊆ (√ S) -> S ⊆ (√ T).
  Proof with crush.
    crush.
    apply H in H1... 
  Qed.

  Lemma Complement_closure {U : Type}:
    forall S : Ensemble U, S ⊆ (√ (√ S)).
  Proof with intuition.
    crush. 
  Qed.

  (** INCLUSION PROPERTIES **)

  Lemma Union_Included_left {U : Type} :
    forall (S T: Ensemble U), S ⊆ T -> S ∪ T == T.
  Proof with crush.
    crush.
  Qed.

  Lemma Union_Included_right {U : Type} :
    forall (S T: Ensemble U), S ⊆ T -> T ∪ S == T.
  Proof with crush.
    crush.
  Qed.

  Lemma Intersection_Included_left {U : Type} :
    forall (S T: Ensemble U), S ⊆ T -> S ∩ T == S.
  Proof with crush.
    crush.
  Qed.

  Lemma Inhabited_Included {U : Type} :
    forall (S : Ensemble U), Inhabited S -> forall T, S ⊆ T -> Inhabited T.
  Proof with crush.
    crush. 
    exists x... 
  Qed.

  Lemma Included_Empty_set {U : Type} :
    forall (S T : Ensemble U), S ⊆ T -> T  == (Empty_set) -> S  == (Empty_set).
  Proof with crush.
    crush.
  Qed.

  Lemma Included_Full_set {U : Type} :
    forall (S T : Ensemble U), S ⊆ T -> S  == (Full_set) -> T == (Full_set).
  Proof with crush.
    crush.
  Qed.

  Lemma Union_Included_cancel_right {U : Type} : forall S T R: (Ensemble U),
    S ⊆ R -> S ⊆ (R ∪ T).
  Proof with crush.
    crush. 
  Qed.

  Lemma Union_Included_cancel_left {U : Type} : forall S T R: (Ensemble U),
    S ⊆ R -> S ⊆ (T ∪ R).
  Proof with crush.
    crush. 
  Qed.

  Lemma Intersection_Included_cancel_right {U : Type} : forall S T R: (Ensemble U),
    S ⊆ R -> (S ∩ T) ⊆ R.
  Proof with crush.
    crush. 
  Qed.

  Lemma Intersection_Included_cancel_left {U : Type} : forall S T R: (Ensemble U),
    S ⊆ R -> (T ∩ S) ⊆ R.
  Proof with crush.
    crush. 
  Qed.

  (** PROPERTIES OF DISJOINT **)

  (* Definitive property of disjoint sets *)

  Lemma Disjoint_Intersection_condition {U : Type} :
    forall (S T : Ensemble U), (Disjoint S T) <-> (S ∩ T == Empty_set).
  Proof with crush.
    crush.
    exfalso. apply (H0 x)... 
    assert (In Empty_set x)...
  Qed.

  Lemma Disjoint_result {U : Type} :
    forall (S T : Ensemble U), S ∩ T == Empty_set -> S == S ∩ (√ T).
  Proof with crush.
    crush. 
    assert (In Empty_set x)...
  Qed.

  Lemma Disjoint_property_left {U : Type} : forall S T: (Ensemble U),
    Disjoint S T -> S ⊆ (√ T).
  Proof with crush.
    crush... 
    apply (H0 x)...
  Qed.

  Lemma Disjoint_property_right {U : Type} : forall S T: (Ensemble U),
    Disjoint S T -> T ⊆ (√ S).
  Proof with crush.
    crush... 
    apply (H0 x)...
  Qed.

  (* Disjunction is symmetric *)

  Lemma Disjoint_sym {U : Type} : forall S T: (Ensemble U), Disjoint S T <-> Disjoint T S.
  Proof with crush.
    crush;
    apply H0 with x... 
  Qed.

  (** OTHER MISCELLANEOUS RESULTS **)

  Lemma Setminus_is_Intersection_Complement {U : Type} :
    forall (S T: Ensemble U), (S \ T) == (S ∩ (√ T)).
  Proof with crush.
    crush.
  Qed.

  Lemma Add_Setminus_cancel {U : Type} :
    forall (A : Ensemble U) x, decidable (Singleton x) -> (x ∈ A) -> (A == Add U (A \ (Singleton x)) x).
  Proof with crush.
    unfold decidable...
    specialize H with (x0:=x0)...
  Qed.

  Lemma Included_Singleton {U : Type} : forall (S : Ensemble U), Inhabited S ->
     forall a, S ⊆ (Singleton a) -> S == (Singleton a).
  Proof with crush.
    crush.
    assert (x ∈ Singleton x0)...
  Qed.

  Lemma Singleton_Included {U : Type} :
    forall T u, (@Singleton U u) ⊆ T <-> u ∈ T.
  Proof with crush.
    crush.
  Qed.

  Lemma Add_Setminus_Singleton {U : Type} :
    (forall (a b : U), ((a=b) \/ ~(a=b))) ->
    forall (x : U) X, x ∈ X ->
      (X == Add U (X \ (@Singleton U x)) x).
  Proof with crush.
    crush.
    assert ((x0 = x) \/ ~(x0 = x))...
    left...
  Qed.

  Lemma Disjoint_three {U : Type} :
    forall (S T R : Ensemble U), Disjoint S R /\ Disjoint T R ->
      Disjoint (S ∪ T) R.
  Proof with crush.
    crush.
    - apply (H1 x)...
    - apply (H x)...
  Qed.

  Lemma Setminus_cancel {U : Type} : forall (S : Ensemble U), S \ S == Empty_set.
  Proof with crush.
    crush. 
  Qed.

  Lemma Setminus_Empty_set {U : Type}: forall (T : Ensemble U), T \ Empty_set == T.
  Proof with crush.
    crush. 
  Qed.

  Lemma Union_Setminus_cancel {U : Type} :
   forall (A B: Ensemble U),
    decidable A → A ⊆ B → (B \ A) ∪ A == B.
  Proof with crush.
    crush.
    assert ((x ∈ A) \/ ~(x ∈ A))...
    apply H.
  Qed.

  Lemma Disjoint_Union_Setminus {U : Type} :
    forall (S T R : Ensemble U), Disjoint S T -> R == S ∪ T -> S == R \ T.
  Proof with crush.
    crush.
      apply (H1 x)...
      apply H in H3... 
  Qed.

  Lemma Setminus_Included {U : Type}: forall (S T : Ensemble U), (S \ T) ⊆ S.
  Proof with intuition.
    crush.
  Qed.

  Hint Resolve Same_set_sym Same_set_refl Same_set_trans.
  Hint Resolve Included_refl Included_trans.
  Hint Resolve Union_trans Union_comm Union_idemp.
  Hint Resolve Intersection_trans Intersection_comm Intersection_idemp.
  Hint Resolve Empty_set_ident_left Empty_set_ident_right Full_set_ident_left Full_set_ident_right.
  Hint Resolve Empty_set_zero_left Empty_set_zero_right Full_set_zero_left Full_set_zero_right.
