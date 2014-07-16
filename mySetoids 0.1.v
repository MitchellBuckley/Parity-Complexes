
(* Written by Mitchell Buckley 25/11/2013 *)
(* 
  A collection of results needed for dealing with Parity complexes.
   -- A few core definitions
   -- Setting up setoid rewrites for Same_set
   -- Some basic results for sets
*)

Require Import Ensembles.
Require Import Setoid.
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

(* Notation for sets *)

Notation "A == B"      := (Same_set A B) (at level 79).
Notation "A ∪ B"       := (Union A B) (at level 61).
Notation "A ∩ B"       := (Intersection A B) (at level 61).
Notation "A ⊆ B"       := (Included A B) (at level 79).
Notation "x ∈ A"       := (In A x) (at level 71).
Notation "√ A"         := (Complement A) (at level 51).
Notation "A == B == C" := ((A == B) /\ (B == C)) (at level 79, B at next level).
Notation "A ⊆ B ⊆ C"   := ((A ⊆ B) /\ (B ⊆ C)) (at level 79, B at next level).

(* basic definitions *)

Definition decidable {A : Type} (X : Ensemble A) : Prop :=
  forall (x : A), (In X x) \/ ~(In X x).

(* 'In' is compatible with Union, Intersection e.t.c. *)

Lemma In_Union {U : Type} :
   forall (x : U) (S T: Ensemble U),  x ∈ (S ∪ T) <-> (x ∈ S) \/ (x ∈ T).
Proof.
  intros. split; intros.
  unfold In in H. inversion H; [left | right]; assumption.
  unfold In in H. unfold In. inversion H; [apply Union_introl | apply Union_intror]; assumption.
Qed.

Lemma In_Intersection {U : Type} :
   forall (x : U) (S T: Ensemble U), x ∈ (S ∩ T) <-> (x ∈ S) /\ (x ∈ T).
Proof.
  intros. split; intros.
  unfold In in H. inversion H. split; assumption. 
  unfold In in H. unfold In. inversion H. constructor; assumption. 
Qed. 

Lemma In_Same_set {U : Type} :
   forall (S T : Ensemble U), S == T <-> (forall x, x ∈ S <-> x ∈ T).
Proof.
  intros; constructor; intros. unfold Same_set in H. unfold Included in H. inversion H.
  split; intros; [apply H0 |apply H1]; assumption.
  unfold Same_set; unfold Included. constructor; intros; apply H in H0; assumption. 
Qed.

Lemma In_Same_set' {U : Type} :
   forall (S T : Ensemble U), S == T -> (forall x, x ∈ S -> x ∈ T).
Proof.
  intros. unfold Same_set in H. unfold Included in H. inversion H. auto.
Qed.

Lemma In_Complement {U : Type} :
   forall (S : Ensemble U) (x : U), (In (Complement S) x) <-> (~ (In S x)).
Proof.
  intros. unfold Complement. unfold In. try split; auto. 
Qed.

(* Same_set is an equivalence relation *)

Lemma Same_set_sym {U : Type} :
   forall (S T : Ensemble U), S == T -> T == S.
Proof.
 intros. unfold Same_set. intros; apply and_comm; assumption.
Qed.

Lemma Same_set_refl {U : Type} :
   forall (S : Ensemble U), S == S.
Proof.
  unfold Same_set. intros.
  constructor; unfold Included; auto.
Qed.

Lemma Same_set_trans {U : Type} :
   forall (S T R : Ensemble U), S == T -> T == R -> S == R.
Proof.
  unfold Same_set. unfold Included.
  intros. inversion H. inversion H0. auto.
Qed.

Add Parametric Relation (U: Type) : (Ensemble U) (@Same_set U)
  reflexivity proved by (Same_set_refl (U:=U))
  symmetry proved by (Same_set_sym (U:=U))
  transitivity proved by (Same_set_trans (U:=U))
as set_eq.

(* Intersection, Union e.t.c. are compatible with Same_set. *)

Lemma Intersection_Same_set_compat {U : Type} :
   forall (S S': Ensemble U), S == S'
   ->
   forall (T T': Ensemble U), T == T'
   ->
   (S ∩ T) == (S' ∩ T').
Proof.
  unfold Same_set. unfold Included. intros.
  inversion H; clear H.
  inversion H0; clear H0.
  split; intros; apply In_Intersection;
  apply In_Intersection in H0; inversion H0; clear H0; auto. 
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
Proof.
  unfold Same_set. unfold Included. intros.
  inversion H; clear H.
  inversion H0; clear H0.
  split; intros; apply In_Union;
  apply In_Union in H0; inversion H0; clear H0; auto. 
Qed.

Add Parametric Morphism U : (@Union U) with 
signature (@Same_set U) ==> (@Same_set U) ==> (@Same_set U) as Union_mor.
Proof.
 apply Union_Same_set_compat.
Qed.

Lemma Complement_Same_set_compat {U : Type} :
   forall (S T: Ensemble U), S == T
   ->
   (Complement S) == (Complement T).
Proof.
  unfold Same_set. unfold Included. unfold Complement. unfold In. intros.
  inversion H; clear H. auto.
Qed.

Add Parametric Morphism U : (@Complement U) with 
signature (@Same_set U) ==> (@Same_set U) as Complement_mor.
Proof.
 apply Complement_Same_set_compat.
Qed.

(* Included is a refl. trans. relation *)

Lemma Included_trans {U : Type} :
   forall (S T R : Ensemble U), Included S T -> Included T R -> Included S R.
Proof.
  unfold Included. auto.
Qed.

Lemma Included_refl {U : Type} :
   forall (S : Ensemble U), Included S S.
Proof.
  intros. unfold Included. auto.
Qed.

Add Parametric Relation (U: Type) : (Ensemble U) (@Included U)
  reflexivity proved by (Included_refl (U:=U))
  transitivity proved by (Included_trans (U:=U))
as set_incl.

(* Union, Intersection e.t.c are compatible with Inclusion *)

Lemma Union_Included_compat {U : Type} :
   forall (S T : Ensemble U), S ⊆ T 
   → 
   forall (S' T' : Ensemble U), S' ⊆ T' 
   → 
   (S ∪ S') ⊆ (T ∪ T').
Proof.
 unfold Included. intros.
 apply In_Union.
 apply In_Union in H1.
 inversion H1; auto.
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
Proof.
 unfold Included. intros.
 apply In_Intersection.
 apply In_Intersection in H1.
 inversion H1; auto.
Qed.

Add Parametric Morphism U : (@Intersection U) with 
signature (@Included U) ==> (@Included U) ==> (@Included U) as Intersection_incl_mor.
Proof.
apply Intersection_Included_compat.
Qed.

(* In this case, we make clear that complement is contravariant *)

Add Parametric Morphism U : (@Complement U) with 
signature (@Included U) --> (@Included U) as Complement_incl_mor.
Proof.
 unfold Included. unfold Complement. unfold In. unfold not.
 auto.
Qed.

(* On Prop, iff is an equivalence relation *)

Add Parametric Relation : (Prop) (@iff)
  reflexivity proved by (iff_refl)
  symmetry proved by (iff_sym)
  transitivity proved by (iff_trans)
as prop_iff.

(* or, and e.t.c are compatible with iff *)

Lemma or_iff_compat :
   forall (S T : Prop), iff S T 
   → 
   forall (S' T' : Prop), iff S' T' 
   → 
   iff (S \/ S') (T \/ T').
Proof.
  unfold iff.
  intros. inversion H. inversion H0.
  constructor; intros A; inversion A; auto.
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
Proof.
  unfold iff.
  intros. inversion H. inversion H0.
  constructor; intros A; inversion A; auto.
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
Proof.
  unfold iff. unfold not.
  intros. inversion H. 
  constructor; auto.
Qed. 

Add Parametric Morphism : (@not) with 
signature (@iff) ==> (@iff) as not_iff_mor.
Proof.
apply not_iff_compat.
Qed.

(* Implication is compatible with if *)

Definition impl (S T : Prop) : Prop := S -> T.

Lemma impl_iff_compat :
   forall (S T : Prop), iff S T 
   → 
   forall (S' T' : Prop), iff S' T' 
   → 
   iff (S -> S') (T -> T').
Proof.
  unfold iff.
  intros. inversion H. inversion H0.
  constructor; intros; auto.
Qed. 

Add Parametric Morphism : (@impl) with 
signature (@iff) ==> (@iff) ==> (@iff) as impl_iff_mor.
Proof.
apply impl_iff_compat.
Qed.

(* Other basic results for sets *)

Lemma I_U_dist_l {U : Type} :
   forall (S T R: Ensemble U), (Intersection S (Union T R)) == (Union (Intersection S T) (Intersection S R)).
Proof.
  intros. symmetry. unfold Same_set. split; unfold Included; intros.
  apply In_Union in H.  
  apply In_Intersection. inversion H. apply In_Intersection in H0. 
  inversion H0. constructor. assumption. apply In_Union. left. assumption. 
  inversion H0. constructor. assumption. apply In_Union. right. assumption. 

  apply In_Intersection in H.  
  apply In_Union. inversion H. apply In_Union in H1.
  inversion H1. left. apply In_Intersection. split; assumption.
  right. apply In_Intersection. split; assumption.
Qed.

Lemma I_U_dist_r {U : Type} :
   forall (S T R: Ensemble U), Same_set (Intersection (Union T R) S) (Union (Intersection T S) (Intersection R S)) .
Proof.
  intros. symmetry. unfold Same_set. split; unfold Included; intros.
  apply In_Union in H.  
  apply In_Intersection. inversion H. apply In_Intersection in H0. 
  inversion H0. constructor. apply In_Union. left. assumption. assumption. 
  inversion H0. constructor. apply In_Union. right. assumption. assumption. 

  apply In_Intersection in H.  
  apply In_Union. inversion H. apply In_Union in H0.
  inversion H0. left. apply In_Intersection. split; assumption.
  right. apply In_Intersection. split; assumption.
Qed.

Lemma U_I_dist_r {U : Type} :
   forall (S T R: Ensemble U), Same_set (Union (Intersection T R) S) (Intersection (Union T S) (Union R S)).
Proof.
  intros. symmetry. unfold Same_set. split; unfold Included; intros.
  apply In_Intersection in H.  
  apply In_Union. inversion H. apply In_Union in H0. apply In_Union in H1. 
  inversion H0. inversion H1. left. apply In_Intersection. constructor; assumption. 
  right; assumption. right; assumption. 

  apply In_Intersection. apply In_Union in H. constructor; apply In_Union; inversion H.
  apply In_Intersection in H0. inversion H0. left; assumption.
  right; assumption.
  apply In_Intersection in H0. inversion H0. left; assumption.
  right; assumption.
Qed.

Lemma U_I_dist_l {U : Type} :
   forall (S T R: Ensemble U), Same_set (Union S (Intersection T R)) (Intersection (Union S T) (Union S R)).
Proof.
  intros. symmetry. unfold Same_set. split; unfold Included; intros.
  apply In_Intersection in H.  
  apply In_Union. inversion H. apply In_Union in H0. apply In_Union in H1. 
  inversion H0. left; assumption. inversion H1. left; assumption. 
  right. apply In_Intersection. constructor; assumption. 

  apply In_Intersection. apply In_Union in H. constructor; apply In_Union; inversion H.
  left; assumption. apply In_Intersection in H0. inversion H0. right; assumption.
  left; assumption.
  apply In_Intersection in H0. inversion H0. right; assumption.
Qed.

Lemma Full_set_property {U : Type} :
  forall (S : Ensemble U), decidable S -> Same_set (Union (Complement S) S) (Full_set U).
Proof.
  intros. unfold Same_set. constructor; unfold Included; intros.
  unfold decidable in H. constructor. apply In_Union. assert (K: In S x \/ ~ In S x). apply H. 
  inversion K. right; assumption. left. apply In_Complement. apply H1.
Qed.

Lemma Empty_set_property {U : Type} :
   forall (S : Ensemble U), Same_set (Intersection S (Complement S)) (Empty_set U).
Proof.
  intros. unfold Same_set. constructor; unfold Included; intros.
  apply In_Intersection in H. inversion H. unfold In in H1. unfold Complement in H1. 
  unfold not in H1. apply H1 in H0. inversion H0. 
  unfold In in H. inversion H. 
Qed.

Lemma Included_Same_set_compat {U : Type} :
   forall (P Q R S : Ensemble U), P == Q -> R == S -> Included P R -> Included Q S.
Proof.
  autounfold with sets.
  intros. inversion H; clear H. inversion H0; clear H0. auto.
Qed.


Lemma empty_def {U : Type} : forall (P : Ensemble U),  (forall x, (~(In P x))) <-> (P == Empty_set _).
Proof.
  unfold Same_set; unfold Included; unfold not.
  intros. split; intros. split; intros. apply H in H0; contradiction.
  inversion H0.
  inversion H. apply H1 in H0. inversion H0. 
Qed.

Lemma full_def {U : Type} : forall (P : Ensemble U),  (forall x, ((In P x))) <-> (P == Full_set _).
Proof.
  unfold Same_set; unfold Included; unfold not.
  intros. split; intros. split; intros.
  constructor. apply H.
  inversion H.
  apply H1.
  constructor.
Qed.

Lemma Full_set_ident_right {U : Type} :
   forall (S : Ensemble U), Same_set (Intersection S (Full_set U)) S.
Proof.
  intros. unfold Same_set. unfold Included.
  split.
  intros. apply In_Intersection in H. inversion H. assumption.
  intros. apply In_Intersection. constructor. assumption. constructor.
Qed. 

Lemma Empty_set_ident_right {U : Type} : forall (S : Ensemble U), (Union S (Empty_set _)) == S.
Proof with auto.
  intros.
  unfold Same_set; unfold Included...
  split; intros...
    inversion H...
      inversion H0.
    left...
Qed. 

Lemma Union_trans {U : Type} : forall (S T R : Ensemble U),
 (S ∪ T) ∪ R == S ∪ (T ∪ R).
Proof with (repeat (intros; try split); auto).
  intros. unfold Same_set; unfold Included...
  inversion H...
  inversion H0...
  left...
  right; left...
  right; right...
  inversion H...
  left; left...
  inversion H0...
  left; right...
  right...
Qed.

Lemma Union_sym {U : Type} : forall (S T : Ensemble U),
 (S ∪ T) == (T ∪ S).
Proof with (repeat (intros; try split); auto).
  intros. unfold Same_set; unfold Included...
  inversion H...
    right... left...
  inversion H...
    right... left...
Qed.
   
Lemma Intersection_trans {U : Type} : forall (S T R : Ensemble U),
 (S ∩ T) ∩ R == S ∩ (T ∩ R).
Proof with (repeat (intros; try split); auto).
  intros.
  unfold Same_set; unfold Included...
  inversion H; subst...
  inversion H0; subst...
  inversion H; subst...
  inversion H0; subst...
  inversion H; subst...
  inversion H; subst...
  inversion H; subst...
  inversion H1; subst...
  inversion H; subst...
  inversion H1; subst...
Qed.

  Lemma Intersection_sym {U : Type} : forall (S T: Ensemble U), (Intersection S T) == (Intersection T S).
  Proof with auto.
    intros.
    unfold Same_set; unfold Included.
    split; intros x H; inversion H; subst;
      constructor...
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

  Lemma Intersection_idemp {U : Type} : forall (S : Ensemble U), (Intersection S S) == S.
  Proof with auto.
    intros.
    unfold Same_set; unfold Included...
    split; intros...
      inversion H...
      constructor...
  Qed. 

Lemma Setminus_is_Intersection_Complement {U : Type} :
  forall (S T: Ensemble U), (Setminus S T) == (Intersection S (Complement T)).
Proof.
  intros. unfold Same_set. unfold Included.
  split; intros.
  unfold In in H. unfold Setminus in H. inversion H. 
  apply In_Intersection. constructor. assumption. apply In_Complement. assumption.
  apply In_Intersection in H. inversion H.
  unfold Setminus. unfold In. constructor. assumption.
  (*apply In_Complement in H1.  bug here somehow *)
  unfold In in H1. unfold Complement in H1. assumption. 
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

  Lemma add_subtract {U : Type} : 
    forall (A : Ensemble U) x, decidable (Singleton U x) -> (In A x) -> (A == Add U (Setminus A (Singleton U x)) x).
  Proof with auto.
    intros S x xDec SFin. 
    unfold Same_set; unfold Included; split; intros...
        unfold Add.
        assert (((In (Singleton U x) x0)) \/ ~((In (Singleton U x) x0))). apply xDec.
        inversion H0. right... left. unfold In; unfold Setminus. split; assumption. 
        unfold Add in H. apply In_Union in H. inversion H.  
        unfold In in H0. unfold Setminus in H0... inversion H0; clear H0.
        assumption. inversion H0. subst. assumption.
  Qed.

  Lemma Disjoint_intersection_condition {U : Type} : 
    forall (S T : Ensemble U), (Disjoint S T) <-> (Intersection S T == Empty_set _).
  Proof with auto.
    intros; split; intros.

    inversion H. unfold not in *.
    unfold Same_set, Included.
    split; intros. 
    apply H0 in H1. contradiction. 
    contradiction. 

    constructor. unfold not.
    intros.
    unfold Same_set, Included in *.
    inversion H. clear H.
    apply H1 in H0. 
    contradiction.
  Qed.

