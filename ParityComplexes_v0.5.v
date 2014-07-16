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


(* Notation *)

Notation "A == B" := (Same_set A B) (at level 61).
Notation "A ∪ B" := (Union A B) (at level 61).
Notation "A ∩ B" := (Intersection A B) (at level 61).
Notation "A ⊆ B" := (Included A B) (at level 61).
Notation "x ∈ A" := (In A x) (at level 61).
Notation "√ A"   := (Complement A) (at level 61).


(* Some early, fundamental definitions *)

Definition decidable {A : Type} (X : Ensemble A) : Prop :=
  forall (x : A), (In X x) \/ ~(In X x).


(* Basic lemmas for 'In' *)

Lemma In_Union {U : Type} :
   forall (x : U) (S T: Ensemble U), In (Union S T) x <-> In S x \/ In T x.
Proof.
  intros. split; intros.
  unfold In in H. inversion H; [left | right]; assumption.
  unfold In in H. unfold In. inversion H; [apply Union_introl | apply Union_intror]; assumption.
Qed.

Lemma In_Intersection {U : Type} :
   forall (x : U) (S T: Ensemble U), In (Intersection S T) x <-> In S x /\ In T x.
Proof.
  intros. split; intros.
  unfold In in H. inversion H. split; assumption. 
  unfold In in H. unfold In. inversion H. constructor; assumption. 
Qed. 

Lemma In_Same_set {U : Type} :
   forall (x : U) (S T : Ensemble U), S == T -> (In S x <-> In T x).
Proof.
  intros. unfold Same_set in H. unfold Included in H. inversion H.
  split; intros; [apply H0 |apply H1]; assumption.
Qed.

Lemma In_Complement {U : Type} :
   forall (S : Ensemble U) (x : U), (In (Complement S) x) <-> (~ (In S x)).
Proof.
  intros. unfold Complement. unfold In. split; auto. 
Qed.


(* Setoid rewrite for Same_set *)

Lemma Same_set_symm {U : Type} :
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
  symmetry proved by (Same_set_symm (U:=U))
  transitivity proved by (Same_set_trans (U:=U))
as set_eq.

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

Add Parametric Morphism U : (@Complement U) with 
signature (@Included U) --> (@Included U) as Complement_incl_mor.
Proof.
 unfold Included. unfold Complement. unfold In. unfold not.
 auto.
Qed.

(* Setoid rewrite for iff *)

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

Lemma setoid_iff_example :
 forall P Q R S,
 (P <-> Q) ->
 (R <-> S) ->
 (P -> (Q -> S) -> R).
Proof.
 intros. rewrite H0. symmetry in H. rewrite H in H2. auto.
Qed.

(* Properties of Union *)

Lemma Union_comm {U : Type} :
   forall (S T : Ensemble U), (Union S T) == (Union T S).
Proof.
  intros. unfold Same_set. split; unfold Included; intros.
  apply In_Union in H. apply In_Union. apply or_comm. assumption.
  apply In_Union in H. apply In_Union. apply or_comm. assumption.
Qed.

Lemma Union_assoc {U : Type} :
   forall (S T R: Ensemble U), (Union (Union S T) R) == (Union S (Union T R)).
Proof.
 intros.
 unfold Same_set. unfold Included. split; intros. 
 apply In_Union in H. inversion H. apply In_Union in H0. inversion H0.
 apply In_Union. left; assumption.
 apply In_Union. right; apply In_Union; left; assumption.
 apply In_Union. right; apply In_Union; right; assumption.
 apply In_Union in H. inversion H.
 apply In_Union. left. apply In_Union. left. assumption.
 apply In_Union in H0. inversion H0.
 apply In_Union. left; apply In_Union; right; assumption.
 apply In_Union. right; assumption. 
Qed.

Lemma Empty_set_ident_right {U : Type} :
   forall (S : Ensemble U), Same_set (Union S (Empty_set U)) S.
Proof.
  intros. unfold Same_set. unfold Included.
  split; intros.
  apply In_Union in H. inversion H. assumption. inversion H0.
  apply In_Union. left; assumption. 
Qed.

Lemma Empty_set_ident_left {U : Type} :
   forall (S : Ensemble U), Same_set (Union (Empty_set U) S) S.
Proof.
  intros. unfold Same_set. unfold Included.
  split; intros.
  apply In_Union in H. inversion H. inversion H0.
  assumption. apply In_Union. right; assumption. 
Qed.


(* Properties of Intersection *)

Lemma Intersection_comm {U : Type} :
   forall (S T : Ensemble U), (Intersection S T) == (Intersection T S).
Proof.
  intros. unfold Same_set. split; unfold Included; intros.
  apply In_Intersection in H. apply In_Intersection. apply and_comm; assumption.
  apply In_Intersection in H. apply In_Intersection. apply and_comm; assumption.
Qed.

Lemma Intersection_assoc {U : Type} :
   forall (S T R: Ensemble U), (Intersection (Intersection S T) R) == (Intersection S (Intersection T R)).
Proof.
 intros.
 unfold Same_set. unfold Included. split; intros. 
 apply In_Intersection in H. inversion H. apply In_Intersection in H0. inversion H0.
 apply In_Intersection; constructor; try assumption; try constructor; try assumption. 
 apply In_Intersection in H. inversion H. apply In_Intersection in H1. inversion H1.
 apply In_Intersection; constructor; try assumption; try constructor; try assumption. 
Qed.

Lemma Full_set_ident_right {U : Type} :
   forall (S : Ensemble U), Same_set (Intersection S (Full_set U)) S.
Proof.
  intros. unfold Same_set. unfold Included.
  split.
  intros. apply In_Intersection in H. inversion H. assumption.
  intros. apply In_Intersection. constructor. assumption. constructor.
Qed.

Lemma Full_set_ident_left {U : Type} :
   forall (S : Ensemble U), Same_set (Intersection (Full_set U) S) S.
Proof.
  intros. unfold Same_set. unfold Included.
  split.
  intros. apply In_Intersection in H. inversion H. assumption.
  intros. apply In_Intersection. constructor. constructor. assumption.
Qed.


(* Distributive properties *)

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

(* Properties of Inclusion *)

Lemma Included_Union_left {U : Type} :
   forall (S T R: Ensemble U), Included S T -> Included S (Union T R).
Proof.
  unfold Included.
  intros. apply In_Union. left. apply H. assumption.
Qed.

Lemma Included_Union_right {U : Type} :
   forall (S T R: Ensemble U), Included S R -> Included S (Union T R).
Proof.
  unfold Included.
  intros. apply In_Union. right. apply H. assumption.
Qed.

Lemma Included_Intersection_left {U : Type} :
   forall (S R: Ensemble U), Included (Intersection R S) S.
Proof.
  unfold Included.
  intros. apply In_Intersection in H. inversion H. assumption. 
Qed.

Lemma Included_Intersection_right {U : Type} :
   forall (S R: Ensemble U), Included (Intersection S R) S.
Proof.
  unfold Included.
  intros. apply In_Intersection in H. inversion H. assumption. 
Qed.

(* A few useful identities *)

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

Lemma Union_Complement_is_Full_set {U : Type} :
  forall (S : Ensemble U), decidable S -> Same_set (Full_set U) (Union (Complement S) S).
Proof.
  intros. unfold Same_set. constructor; unfold Included; intros.
  unfold decidable in H. apply In_Union. assert (K: In S x \/ ~ In S x). apply H. 
  inversion K. right; assumption. left. apply In_Complement. apply H1.
  unfold In. constructor.
Qed.

Lemma Intersection_Complement_is_Empty_set {U : Type} :
   forall (S : Ensemble U), Same_set (Intersection S (Complement S)) (Empty_set U).
Proof.
  intros. unfold Same_set. constructor; unfold Included; intros.
  apply In_Intersection in H. inversion H. unfold In in H1. unfold Complement in H1. 
  unfold not in H1. apply H1 in H0. inversion H0. 
  unfold In in H. inversion H. 
Qed.

Lemma On_Complements_and_Intersection {U :Type} :
  forall (S T : Ensemble U), 
    ((S ∪ T) ∩ (√ T)) == (S ∩ (√ T)).
Proof.
  intros.
  rewrite I_U_dist_r.
  rewrite Intersection_Complement_is_Empty_set.
  rewrite Empty_set_ident_right. 
  reflexivity.
Qed.

(* UNKNOWN MATERIAL *)

Definition rel (A : Type) : Type := A -> A -> Prop.

Definition decidable_rel {A : Type} (R : rel A) : Prop :=
  forall (x y : A), (R x y) \/ ~(R x y).

Inductive Fin : nat -> Type :=
| fO : forall (n : nat), Fin (S n)
| fS : forall (n : nat), Fin n -> Fin (S n).

Record bijection (A B : Type) : Type :=
  {
    f : A -> B;
    f' : B -> A;
    left_inverse_ax : forall (x : A), f' (f x) = x;
    right_inverse_ax : forall (y : B), f (f' y) = y
  }.

Record finite_cardinality (A : Type) : Type :=
  {
    card : nat;
    card_bij : bijection A (Fin card)
  }.

(** We use subset types { x | In X x } to turn Ensembles into types.         **
 ** That the following is the correct definition ultimately relies on        **
 ** proof irrelevance                                                        **)

Definition finite_set {A : Type} (X : Ensemble A) : Type := 
  finite_cardinality { x | In X x }.

Inductive finite_set' {A : Type} : Ensemble A -> Prop :=
  | fin_empty: finite_set' (Empty_set A)
  | fin_plus: forall x S, finite_set' S -> finite_set' (Add A S x).

(** Inductive definition of the reflexive transitive closure of a relation  **)

Inductive rt_closure {A : Type} (R : rel A) : rel A :=
  | rt_refl : forall (x : A), rt_closure R x x
  | rt_cons : forall (x y z : A), 
                 R x y -> rt_closure R y z -> rt_closure R x z.

Lemma rt_trans : 
  forall {A : Type} (R : rel A) (x y z : A),
    rt_closure R x y -> rt_closure R y z -> rt_closure R x z.
Proof.
  intros A R x y z H.
  revert z.
  induction H as [ | x w y H K IH ].
  trivial.
  intros z L.
  apply (rt_cons _ x w z).
  trivial.
  apply IH.
  trivial.
Qed.
  
(** But Ross' definitions need us to consider reflexive transitive closures  **
 ** of relations restricted to some subset. We use subset types to turn      **
 ** Ensembles into types.                                                    **)

Definition rest_rel 
           {A : Type} (X : Ensemble A) (R : rel A) : rel { x | In X x }. 
  compute.
  intros H K.
  destruct H as [x p].
  destruct K as [y q].
  apply (R x y).
Defined.

Definition unrest_rel 
           {A : Type} {X : Ensemble A} (R : rel { x | In X x }) : rel A :=
  fun (x y : A) => 
    exists (p : In X x) (q : In X y), R (existT _ x p) (existT _ y q).

Definition rt_closure_ens {A : Type} (X : Ensemble A) (R : rel A) :=
  unrest_rel (rt_closure (rest_rel X R)).

(* PreParity Complexes *)

Module Type PreParity.

  Parameter carrier : Type.
  Parameter dim : carrier -> nat.
  Parameter plus minus : carrier -> Ensemble carrier.

  Axiom plus_minus_disjoint : forall (y : carrier), Disjoint (plus y) (minus y).
  Axiom plus_dim : forall (x y : carrier), In (plus y) x -> S(dim x) = dim y. 
  Axiom minus_dim : forall (x y : carrier), In (minus y) x -> S(dim x) = dim y. 
  Axiom plus_dec : forall (x : carrier), finite_set (plus x).
  Axiom minus_dec : forall (x : carrier), finite_set (minus x).

End PreParity.

Lemma nat_eq_decidable : forall (n m : nat), (n = m) \/ ~(n = m).
Proof.
  intros n; induction n; intro m; case m; auto.
  intro n'; destruct (IHn n'); auto.
Qed.

Lemma finite_is_decidable {U : Type} : 
  forall (S : Ensemble U), finite_set S -> decidable S.
Proof.
  admit. (* This should be done at some point? *)
Qed.

(** The following "functor" defines some functions and proves some theorems **
 ** which apply to any PreParity module.                                    **)

Module PreParityDefns (M : PreParity).

  Import M.

  Definition Plus (X : Ensemble carrier) : Ensemble carrier :=
    fun (y : carrier) => (exists (x : carrier), (In X x) /\ (In (plus x) y)).
  Definition Minus (X : Ensemble carrier) : Ensemble carrier :=
    fun (y : carrier) => (exists (x : carrier), (In X x) /\ (In (minus x) y)). 

  Definition PlusMinus (X : Ensemble carrier) : Ensemble carrier :=
    Setminus (Plus X) (Minus X).
  Definition MinusPlus (X : Ensemble carrier) : Ensemble carrier :=
    Setminus (Minus X) (Plus X).

  Definition Perp (X Y : Ensemble carrier) : Prop :=
    (Disjoint (Plus X) (Plus Y)) /\ (Disjoint (Minus X) (Minus Y)).
  Definition perp (x y : carrier) : Prop :=
    (Disjoint (plus x) (plus y)) /\ (Disjoint (minus y) (minus y)).

  Definition less (x y : carrier) : Prop :=
    (Inhabited (Intersection (plus x) (minus y))).
  Definition curly_less (x y : carrier) : Prop :=
    (In (minus y) x) \/ (In (plus x) y). 
  
  Definition triangle (S : Ensemble carrier) : rel carrier := 
    rt_closure_ens S less.
  Definition solid_triangle (S : Ensemble carrier) : rel carrier := 
    rt_closure_ens S curly_less.

  Definition cells (n : nat) : Ensemble carrier :=
    fun (x : carrier) => (dim x = n).

  Definition moves (S M P : Ensemble carrier) : Prop :=
    P == (Intersection (Union (M) (Plus S)) (Complement (Minus S))) /\
    M == (Intersection (Union (P) (Minus S)) (Complement (Plus S))).

 (* my temporary tactics for this stuff *) 

Ltac invertexists := 
  match goal with
    H1: exists x, ?P |- _ => inversion H1; clear H1
  end.

Ltac invertconj :=
  match goal with
    H1: ?P /\  ?Q |- _ => inversion H1; clear H1
  end.

Ltac invertInters H :=
  inversion H as [?a L K ?b]; subst; unfold In in K; unfold In in L; clear H.


Hint Constructors Union Intersection.
Hint Unfold In.

Ltac brute_logic := unfold MinusPlus; unfold PlusMinus; unfold Setminus; unfold moves; 
                        unfold Same_set; unfold Included; unfold In; unfold not.
 
Ltac other_logic := repeat (try intros; try invertexists; try invertconj; try apply conj; try apply ex_intro). 

(* Basic results for Preparity Complexes *)

  Lemma Obs_p321 : 
    forall (S : Ensemble carrier), moves S (MinusPlus S) (PlusMinus S).
  Proof.
  brute_logic.
  other_logic.

  constructor; unfold In.
    right; unfold In. assumption. 
    unfold Complement; unfold In; unfold not. assumption.
  inversion H as [a L M b]; subst; unfold In in M; unfold In in L; clear H.
  unfold Complement in M. unfold not in M. unfold In in M. 
  inversion L as [a B C | a B C]; subst; unfold In in B.
     invertconj. apply M in H; contradiction. 
     assumption.
  inversion H as [a L M b]; subst; unfold In in M; unfold In in L; clear H.
  unfold Complement in M. unfold not in M. unfold In in M.
  contradiction. 
  constructor; unfold In.
    right; unfold In. assumption. 
    unfold Complement; unfold In; unfold not. assumption.
  inversion H as [a L M b]; subst; unfold In in M; unfold In in L; clear H.
  unfold Complement in M. unfold not in M. unfold In in M. 
  inversion L as [a B C | a B C]; subst; unfold In in B.
     invertconj. apply M in H; contradiction. 
     assumption.
  inversion H as [a L M b]; subst; unfold In in M; unfold In in L; clear H.
  unfold Complement in M. unfold not in M. unfold In in M.
  contradiction.
  Qed.

  Lemma Prop_2_1 : forall (S M : Ensemble carrier), 
     (exists (P : Ensemble carrier), moves S M P) 
     ->
     (MinusPlus S) ⊆ M /\ Disjoint M (Plus S).
  Proof.


    intros S M. split. 
    inversion H as [wP hP].
    unfold moves in hP. inversion hP as [hPA hPB]. clear hP.
   
    admit. 

    inversion H as [wP hP].
    unfold moves in hP. inversion hP as [hPA hPB]. clear hP.
      
      constructor. unfold not. intros.
      apply In_Intersection in H0. inversion H0. eapply In_Same_set in hPB. apply hPB in H1.
      apply In_Intersection in H1. inversion H1.
      (* apply In_Complement in H4. bug here somewhere. *)
      unfold In in H4. unfold Complement in H4. apply H4. assumption.
  Qed. 

  Lemma Prop_2_1' : forall (S M : Ensemble carrier), 
     (exists (P : Ensemble carrier), moves S M P) 
     ->
     (MinusPlus S) ⊆ M /\ Disjoint M (Plus S).
  Proof.

    brute_logic.
    other_logic. apply H4.
    constructor; unfold In.
      right; unfold In. assumption.
      unfold Complement. unfold In. unfold not. assumption.
    constructor. intros. unfold In. unfold not. intros.
    inversion H as [a L K b]; subst; unfold In in K; unfold In in L; clear H.
    apply H0 in L.
    inversion L as [a J G b]; subst; unfold In in J; unfold In in G; clear L.
      unfold Complement in G. unfold In in G. unfold not in G. 
      contradiction. 
  Qed.

  Lemma Prop_2_1_rev : forall (S M : Ensemble carrier), 
     decidable (Minus S)
     ->
     Included (MinusPlus S) M /\ Disjoint M (Plus S)
     ->
     (exists (P : Ensemble carrier), moves S M P).
  Proof.
      intros S M K. intros. apply ex_intro with (x:= Intersection (Union M (Plus S)) (Complement (Minus S))).
      inversion H. clear H. unfold moves. constructor.
      
      reflexivity.

      symmetry.
      replace (((M ∪ Plus S) ∩ (√Minus S)) ∪ Minus S) with ((((M ∪ Plus S) ∪ Minus S) ∩ ((√Minus S) ∪ Minus S))).
      replace ((√Minus S) ∪ Minus S) with (Full_set carrier).
      rewrite Full_set_ident_right.
      rewrite I_U_dist_r.
      replace (Minus S ∩ (√Plus S)) with (MinusPlus S).
      rewrite I_U_dist_r.
      rewrite Intersection_Complement_is_Empty_set.
      rewrite Empty_set_ident_right.
      replace (M ∩ (√Plus S)) with M.
      
      admit.
      admit.
      unfold MinusPlus. admit. (* rewrite Setminus_is_Intersection_Complement. *)
      admit. (* rewrite Union_Complement_is_Full_set. *)
      admit. (* rewrite U_I_dist_r. *)
  Qed.

  Lemma Prop_2_2 : 
    forall (S A B X: Ensemble carrier),
    moves S A B -> X ⊆ A -> Disjoint (MinusPlus S) X 
    -> 
    forall (Y : Ensemble carrier),  
    Disjoint Y (Plus S) -> Disjoint Y (Minus S) 
    ->
    moves S ((A ∪ Y) ∩ (√X)) ((B ∪ Y) ∩ (√X)).
  Proof. admit. Qed.

  Lemma Prop_2_3 : 
    forall (S M P T Q : Ensemble carrier),
    moves S M P -> moves T P Q -> Disjoint (Minus S) (Plus T) 
    ->
    moves (S ∪ T) M Q.
  Proof. admit. Qed.

  Lemma Prop_2_4 :
    forall (T Z M P : Ensemble carrier),
    moves (Union T Z) M P -> 
    Included (PlusMinus Z) P ->
    Perp T Z ->
    exists N, moves T M N /\ moves Z N P.
  Proof. admit. Qed.

(* Material from Chapter 1 *)

  Definition well_formed (X : Ensemble carrier) : Prop :=
    (forall (x y : carrier), dim x = O -> dim y = 0 -> x = y )
    /\
    (forall (n : nat) (x y : carrier), dim x = S n -> dim y = S n -> not (perp x y) -> x = y).

  Axiom axiom1 :
    forall x, Union (Plus (plus x)) (Minus (minus x)) == Union (Plus (minus x)) (Minus (plus x)).

  Axiom axiom2 :
    forall x, well_formed (plus x) /\ well_formed (minus x).

  Axiom axiom3a:
    forall x y   : carrier, triangle (Full_set carrier) x y -> triangle (Full_set carrier) y x -> x = y.

  Axiom axiom3b:
    forall x y z : carrier, 
    triangle (Full_set carrier) x y ->
    (not (In (plus z) x /\ In (minus z) y) /\ not (In (plus z) y /\ In (minus z) y)).

  Lemma Prop_1_1 : 
    forall x, 
    Disjoint (Plus (plus x)) (Minus (minus x)) 
    /\
    Disjoint (Plus (minus x)) (Minus (plus x))
    /\
    (MinusPlus (minus x)) == Intersection (Minus (minus x)) (Minus (plus x))
    /\
    Intersection (Minus (minus x)) (Minus (plus x)) == (MinusPlus (plus x))
    /\
    (PlusMinus (minus x)) == Intersection (Plus (minus x)) (Plus (plus x))
    /\
    Intersection (Plus (minus x)) (Plus (plus x)) == (PlusMinus (plus x)).
  Admitted.

  Lemma Prop_1_2 :
    forall u v x,
    triangle (Full_set carrier) u v ->
    In (plus x) v ->
    Disjoint (minus u) (Plus (minus x)).
  Admitted.


End PreParityDefns.








(** The one point type **)

Inductive One :=
| star : One.

Lemma decidable_eq_One : decidable_rel (eq (A := One)).
Proof.
  compute.
  intro x; case x; intro y; case y.
  left; trivial.
Qed.

(** Empty sets are always decidable and have cardinatily 0 **)

Lemma decidable_empty : forall (A : Type), decidable (Empty_set A).
Proof.
  compute; intros.
  right; intro H; inversion H.
Qed.

Lemma cardinality_empty : forall (A : Type), finite_set (Empty_set A).
Proof.
  compute. intro A.
  apply (Build_finite_cardinality _ 0).
  assert (f : { x | Empty_set A x } -> Fin 0).
  intro H; destruct H as [x p]; inversion p.
  assert (f' : Fin 0 -> { x | Empty_set A x}).  
  intro H; inversion H.
  apply (Build_bijection _ _ f f').
  intro x. destruct x as [x' p]. inversion p.
  intro y. inversion y.
Qed.

(** Now let's define a module which implements the PreParity interface     **
 ** which we do by providing definitions for all the functions and proofs  **
 ** for all the axioms defined there                                       **)

Module ZeroCell <: PreParity.

  Definition carrier := One.

  Definition decidable_eq_carrier := decidable_eq_One.

  Definition dim (x : One) : nat := 0.

  Definition plus (x : One) : Ensemble carrier := Empty_set _.
  Definition minus (x : One) : Ensemble carrier := Empty_set _.

  Lemma plus_dec : forall (x : One), decidable (plus x).
  Proof.
    intro x.
    unfold plus.
    apply decidable_empty.
  Qed.
  
  Lemma minus_dec : forall (x : One), decidable (minus x).
  Proof.
    intro x.
    unfold minus.
    apply decidable_empty.
  Qed.

  Lemma plus_fin : forall (x : carrier), finite_set (plus x).
  Proof.
    intro x. case x. compute.
    apply cardinality_empty.
  Qed.

  Lemma minus_fin : forall (x : carrier), finite_set (minus x).
  Proof.
    intro x. case x. compute.
    apply cardinality_empty.
  Qed.
  
  Lemma plus_dim : forall (x y : One), In (plus y) x -> S(dim x) = dim y.
  Proof.
    intros x y H.
    unfold plus in H.
    inversion H.
  Qed.
  
  Lemma minus_dim : forall (x y : One), In (minus y) x -> S(dim x) = dim y.
  Proof.
    intros x y H.
    unfold plus in H.
    inversion H.
  Qed.

End ZeroCell.

(** And we can construct an associated module of definitions and lemmas **
 ** using the PreParityDefns functor                                    **)

Module ZeroCellDefns := PreParityDefns ZeroCell.

(** We can use the definitions in ZeroCell and ZeroCellDefns by Importing    **
 ** those modules into a scope. Here we do this within a section, so that    **
 ** these definition don't "escape" to pollute all of the rest of our theory **)

Section Test.

  Import ZeroCell.
  Import ZeroCellDefns.

  (** So all of the definitions in ZeroCell and ZeroCellDefns are 
      available here **)

  Print minus_dim.

End Test.

(** But they are no longer available here **)