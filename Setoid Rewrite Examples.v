
(* Written by Mitchell Buckley 11/11/2013 *)
(* A few examples of setoid rewrite *)

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

Notation "A == B" := (Same_set A B) (at level 61).
Notation "A ∪ B" := (Union A B) (at level 61).
Notation "A ∩ B" := (Intersection A B) (at level 61).
Notation "A ⊆ B" := (Included A B) (at level 61).
Notation "x ∈ A" := (In A x) (at level 61).
Notation "√ A"   := (Complement A) (at level 61).

(* Some basic lemmas for 'In'. They're not very interesting, just useful *)

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

Lemma In_Complement {U : Type} :
   forall (S : Ensemble U) (x : U), (In (Complement S) x) <-> (~ (In S x)).
Proof.
  intros. unfold Complement. unfold In. split; auto. 
Qed.


(* Setoid rewrite for Same_set *)

(* first, we need to show that the Same_set relation is
   transitive, symmetric and reflexive. *)

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

(* Now, we can record this relation and its properties explicitly. *)

Add Parametric Relation (U: Type) : (Ensemble U) (@Same_set U)
  reflexivity proved by (Same_set_refl (U:=U))
  symmetry proved by (Same_set_sym (U:=U))
  transitivity proved by (Same_set_trans (U:=U))
as set_eq.

(*
   Have a look at the parameters given above. The (U : Type) are arguments
   you might need to include in general. Then (Ensemble U) is the Type upon 
   which the relation is defined. Then (@Same_set U) is the relation in 
   question. 
   
   The body records the basic properties we ask for.

   The final line gives a name to this recorded information.
*)

(* 
   Now that the relation is defined, we want to prove that certain 
   constructions are compatible with the relation 
*)

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

(* 
   Having proved this basic fact, we can record Intersection
   as a morphism over this relation. See below.
*)

Add Parametric Morphism U : (@Intersection U) with 
  signature (@Same_set U) ==> (@Same_set U) ==> (@Same_set U) as Intersection_mor.
Proof.
  apply Intersection_Same_set_compat.
Qed.

(*
   The function in question is Intersection, as indicated on the first line.

   The function preserves Same-set relation completely. This is indicated by 
   the signature line.

   This morphism is recorded under the name Intersection_mor.

   The proof is supplied.
*)

(*
   The signature here can be modified. It's not clear to me exactly how.
   I think we can define morphisms that preserve different relations
   in different ways. In particular, ==> can be replaced with
   ++> or --> to explicitly indicate a covariant or contravariant
   behaviour.

   And I suppose you could have signatures that represent conditions
   like
     x R y ->
     w S z ->
     (F x w) T (F y z)
   where R, S, T are different relations and F is our morphism. In that
   case, I don't know how (co|contra)variance would be handled.
*)

(* Union is a morphism of Same_set *)

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

(* Complement is a morphism of Same_set *)

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

(* 
   Now that these relations and morphisms are defined, we can take
   advantage of the standard rewrite library.
*)

Lemma Same_set_Example_1 {A : Type} : 
  forall (S T U V : Ensemble A),
    (S == T) ->
    (U == V) ->
    (((S ∪ U ) ∩ √V) ∪ T) == (((T ∪ U ) ∩ √U) ∪ T).
Proof.
  intros.
  rewrite H.
  rewrite H0.
  rewrite <- H. (* this line not necessary, just here for demonstration *)
  reflexivity.
Qed.

(* 
   Notice that we can use 'reflexivity' and 'symmetry' in place of
   calling the explicit Lemma above.
*)

Lemma Same_set_Example_2 {A : Type} : 
  forall (S T U V : Ensemble A),
    (S == T) ->
    (V == T) ->
    (S == V).
Proof.
  intros.
  symmetry in H0.
  eapply Same_set_trans.
  apply H. assumption.
Qed.

(* 
   Can you suggest some more interesting examples? Or even
   examples that demonstrate the limitations of this?
*)


(* Setoid rewrite for Included *)

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

(* 
   This relation is not symmetric, but the relation feature doesn't
   care. It can record any relation at all. 
*)

(* 
   I wonder if you can define other properties such as anti-symmetry.
   I don't know. 
*)

Add Parametric Relation (U: Type) : (Ensemble U) (@Included U)
  reflexivity proved by (Included_refl (U:=U))
  transitivity proved by (Included_trans (U:=U))
as set_incl.

(* Union is a morphism for Included. *)

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

(* Inersection is a morphism for Included. *)

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

(* Complement is a morphism *)
(* In this case, we make clear that complement is contravariant *)

Add Parametric Morphism U : (@Complement U) with 
signature (@Included U) --> (@Included U) as Complement_incl_mor.
Proof.
 unfold Included. unfold Complement. unfold In. unfold not.
 auto.
Qed.

(* An example, can you think of more? *)

Lemma Included_Example_1 {A : Type} : 
  forall (S T U V : Ensemble A),
    (S ⊆ T) ->
    (U ⊆ V) ->
    ((S ∪ U) ∩ (√V)) ⊆ ((T ∪ V) ∩ (√U)).
Proof.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

(* This is an interesting relation: iff P Q := P <-> Q *)

Add Parametric Relation : (Prop) (@iff)
  reflexivity proved by (iff_refl)
  symmetry proved by (iff_sym)
  transitivity proved by (iff_trans)
as prop_iff.

(* or is a morphism for iff. *)

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

(* and is a morphism for iff. *)

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

(* not is a morphism for iff. *)

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

(* What about implication? *)

Definition impl (S T : Prop) : Prop := S -> T.

(* impl is a morphism for iff. *)

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

(* An example, can you come up with more? *)

Lemma iff_Example_1 :
 forall P Q R S,
 (P <-> Q) ->
 (R <-> S) ->
 (P -> (Q -> S) -> R).
Proof.
 intros. rewrite H0. symmetry in H. rewrite H in H2. auto.
Qed.
