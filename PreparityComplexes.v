
(* Written by Mitchell Buckley 12/11/2013 *)

Require Import Ensembles Constructive_sets.
Require Import myFiniteDefs.
Require Import Relations.
Require Import mySetoids.
Require Import Utf8_core.
Require Import Max Le.
Require Import Arith.
Require Import Setoid.
Require Import Recdef.

Hint Constructors Finite Cardinal Singleton Full_set.

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
(* Independent Lemmas                                   *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma strong_induction : 
    forall P : nat -> Prop,
    P O -> 
    (forall n : nat, (forall m, m <= n -> P m) -> P (S n)) -> 
    forall n : nat, P n.
  Proof with intuition.

    intros P.
    set (Q := fun n => (forall m, m <= n -> P m)).

    intros.
    assert (Q 0). unfold Q... inversion H1...
    assert (forall l, Q l -> Q (S l)). unfold Q...
    inversion H3...
    assert (Q n) as D.
      apply (nat_ind Q)...
    apply (D n). left.
  Qed.

  Lemma lt_eq_eq_lt_dec: forall k m, {k < m} + {k = m} + {k = S m} + {S m < k}. 
  Proof with intuition.
   intros. 
   pose (lt_eq_lt_dec k m)... 
   unfold lt in b. 
   apply le_lt_eq_dec in b...
  Qed.

  Lemma lt_Sn_n : forall n, ~(S n < n).
  Proof with intuition.
    intros n.
    induction n... 
    apply (lt_n_0) in H...
  Qed.

  Lemma lt_SSn : ∀ n : nat, ¬S (S n) < n. 
  Proof with intuition.
    intros n.
    induction n...
      inversion H...
  Qed.

  Lemma le_SSn : ∀ n : nat, ¬S (S n) <= n. 
  Proof with intuition.
    intros n.
    induction n...
      inversion H...
  Qed.

  Lemma lt_SSSn : ∀ n : nat, ¬S (S (S n)) < n. 
  Proof with intuition.
    intros n.
    induction n...
      inversion H...
  Qed.

  Lemma le_SSSn : ∀ n : nat, ¬S (S (S n)) <= n. 
  Proof with intuition.
     intros n.
    induction n...
      inversion H...
  Qed.

  Lemma SSn_n : forall n, S (S n) = n -> False. 
  Proof with intuition. 
    intros... 
    induction n...
    inversion H...
  Qed.

  Lemma le_SSn_n : forall n, S (S n) <= n -> False. 
  Proof with intuition. 
    intros... 
    induction n...
    inversion H... 
  Qed.

  Hint Resolve SSn_n le_SSn_n.

  (* at some stage these should go, we never need to use n-1 *)
  Lemma qwer   : forall n, (n-1 <= n). Admitted.
  Lemma qwer'  : forall n, (n-1 <  n). Admitted.
  Lemma qwer'' : forall n, (n <= n-1) -> False. Admitted.

  Lemma Sn_minus_1 : forall n, (S n - 1 = n).
  Proof. 
    intros. 
    simpl. 
    symmetry. 
    apply minus_n_O. 
  Qed.

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
  Axiom plus_Finite :         forall (x : carrier),   Finite (plus x).
  Axiom minus_Finite :        forall (x : carrier),   Finite (minus x).
  Axiom plus_Inhabited :      forall (x : carrier),   dim x > 0 -> (Inhabited (plus x)).
  Axiom minus_Inhabited :     forall (x : carrier),   dim x > 0 -> (Inhabited (minus x)).
  Axiom plus_zero:            forall (x : carrier),   (dim x) = 0 ->  plus x == Empty_set.
  Axiom minus_zero:           forall (x : carrier),   (dim x) = 0 -> minus x == Empty_set.
  Axiom plus_minus_Disjoint : forall (y : carrier),   Disjoint (plus y) (minus y).
  
  Hint Resolve plus_dim minus_dim plus_Finite minus_Finite plus_minus_Disjoint.

  End PreParity.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Pre-Parity Complex Results                           *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

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
  Inductive triangle_rest (S : Ensemble carrier) : relation carrier :=
    | tr_refl  : forall x, In (S) x -> triangle_rest S x x
    | tr_trans : forall x y z, In (S) x -> less x y -> triangle_rest S y z -> triangle_rest S x z.

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
    Plus Minus sup sub: sets v62.

  Definition moves_def (S M P : Ensemble carrier) : Prop :=
    P == (Intersection (Union (M) ( Plus S)) (Complement (Minus S))) 
    /\
    M == (Intersection (Union (P) (Minus S)) (Complement ( Plus S))).

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
(* decidability and Finite                           *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma all_decidable : forall (S : Ensemble carrier), Finite S -> decidable S. 
  Proof.
    intros.
    apply Finite_are_decidable.
    apply carrier_decidable_eq.
    assumption.
  Qed.

  Hint Resolve all_decidable.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Tactics                                              *)
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
    | H: In (Union _ _) _ |- _ => apply In_Union in H
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

  Ltac splits := 
    match goal with
    | H: _ |- _ /\ _ => split; [idtac | try splits]
    end.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* triangle_rest                           *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Inductive triangle_rest' (S : Ensemble carrier) : relation carrier :=
    | tr_refl'  : forall x, In (S) x -> triangle_rest' S x x
    | tr_trans' : forall x y z, In (S) z -> less y z -> triangle_rest' S x y -> triangle_rest' S x z.

  Lemma triangle_rest_in_set : forall S, forall x y, triangle_rest S x y -> In S x /\ In S y.
  Proof with intuition.
    intros...
    induction H... induction H...
  Qed.

  Lemma triangle_rest_equiv : forall S, forall x y, triangle_rest S x y <-> triangle_rest' S x y.
  Proof with intuition.
  Admitted.

  Hint Resolve triangle_rest_in_set.

  Lemma triangle_rest_trans : forall X, forall y z, triangle_rest X y z -> forall x, triangle_rest X z x -> triangle_rest X y x.
  Proof with intuition.
	    intros...
    generalize dependent x.
    induction H...
      rename x0 into w.
      apply (tr_trans _ _ y)...
  Qed.

  Lemma triangle_rest_ind' :
    forall (S : Ensemble carrier) (P : carrier → carrier → Prop),
      (∀ x : carrier, x ∈ S → P x x) ->
        (∀ x y z : carrier,  
          triangle_rest S x y → triangle_rest S y z → P y z → P x z) ->
            ∀ u v : carrier, triangle_rest S u v → P u v.
  Proof with intuition.
    intros...
    induction H1... 
      apply (H0 x y z)...
      apply (tr_trans _ x y y)... left...
      inversion H3...  
  Qed.

  Lemma rest_implies_full : forall S x y, triangle_rest S x y -> triangle x y.
  Proof with intuition.
    intros.
    induction H...
      left.
      apply (Relation_Operators.rt1n_trans _ _ _ y)...
  Qed.

  Lemma equal_dim : forall x y, triangle x y -> (dim x = dim y). 
  Proof with repeat basic; auto.
    unfold triangle.
    apply (clos_refl_trans_1n_ind carrier).
      intros... 
      intros... 
      inversion H; clear H. rename x0 into w...
      apply plus_dim in H. apply minus_dim in H3. rewrite <- H1. rewrite <- H3.
      rewrite <- H...
  Qed.

  Lemma less_decidable : forall x y, ((less x y) \/ ~(less x y)).
  Proof with intuition.
    intros.
    assert (Finite (Intersection (plus x) (minus y))).
      apply Finite_Intersection. 
      apply minus_Finite.
      apply all_decidable...
    apply Finite_Empty_or_Inhabited in H.
    inversion H; clear H; [right | left]...
      unfold less in H.
      rewrite H0 in H.
      inversion H. 
      inversion H1.
  Qed.

  Lemma triangle_rest_Included : forall S x y, triangle_rest S x y -> 
    forall T, Included S T -> triangle_rest T x y.
  Proof with intuition.
    intros...
    induction H...
      left...
      right with y...
  Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma plus_minus_Disjoint_Lemma : forall x y, In (plus y) x -> In (minus y) x -> False.
  Proof with intuition.
    intros.
    pose (plus_minus_Disjoint y). 
    apply Disjoint_Intersection_condition in d. 
    assert (In (Empty_set) x)... rewrite <- d... inversion H1.
  Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Hint Extern 2 (False) =>
    match goal with
    | H : S ?n <= ?n |- False => apply le_Sn_n in H; assumption
    | H : ?n   =  S ?n  |- False => apply n_Sn in H; assumption
    | H : S ?n =  ?n |- False => symmetry in H; apply n_Sn in H; assumption
    | H : In Empty_set _ |- False => inversion H
    | H : In (plus ?y) ?x, K : In (minus ?y) ?x |- False => apply (plus_minus_Disjoint_Lemma _ _ H K); assumption
    | H : S _ = 0 |- False => inversion H
    | H : ?n = 0, K : ?n = S _ |- False => rewrite K in H; inversion H
    end.

  Hint Extern 2 (False) =>
    match goal with
    | H : S ?n = S ?m |- False => inversion H; clear H
    | H : ?n = S (S ?n)  |- False => apply n_SSn in H
    | H : S (S ?n) =  ?n |- False => symmetry in H; apply n_SSn in H
    | H : S (S ?n) <  ?n |- False => apply lt_SSn in H
    | H : S (S ?n) <= ?n |- False => apply le_SSn in H
    | H : ?n = S (S (S ?n))  |- False => apply n_SSSn in H
    | H : S (S (S ?n)) =  ?n |- False => symmetry in H; apply n_SSSn in H
    | H : S (S (S ?n)) <  ?n |- False => apply lt_SSSn in H
    | H : S (S (S ?n)) <= ?n |- False => apply le_SSSn in H
    | H : ?m = ?n, H' : S ?n = ?m |- False => rewrite H in H'
    end.

  Hint Extern 2 (False) => 
    match goal with
    | H : S ?n < ?n |- False => apply lt_Sn_n in H; assumption
    | H :   ?n < ?n |- False => apply lt_irrefl in H; assumption
    | H :   ?m < ?n , H' : ?n = ?m |- False => rewrite H' in H; apply lt_irrefl in H; assumption
    | H :   ?m < ?n , H' : ?m = ?n |- False => rewrite H' in H; apply lt_irrefl in H; assumption
    | H : S ?m < ?n , H' : ?n = ?m |- False => rewrite H' in H; apply lt_Sn_n in H; assumption
    | H : S ?m < ?n , H' : ?m = ?n |- False => rewrite H' in H; apply lt_Sn_n in H; assumption
    end.

  Hint Extern 2 (In _ _) => 
    match goal with 
      | H : ?S == ?T, _: In ?T ?x |- In ?S ?x => rewrite H; assumption 
      | H : ?S == ?T, _: In ?S ?x |- In ?T ?x => rewrite <- H; assumption 
    end.

  Hint Resolve lt_irrefl le_lt_dec lt_Sn_n.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Setoid rewrite stuff                                 *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

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

  Add Parametric Morphism : (@PlusMinus) with 
    signature (@Same_set carrier) ==> (@Same_set carrier) as PlusMinus_Same_set.
  Proof with crush.
    intros. unfold PlusMinus. rewrite H...
  Qed.

  Add Parametric Morphism : (@MinusPlus) with 
    signature (@Same_set carrier) ==> (@Same_set carrier) as MinusPlus_Same_set.
  Proof with crush.
    intros. unfold MinusPlus. rewrite H...
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

  Add Parametric Morphism : (setdim) with 
    signature (@Same_set carrier) ==> (@eq nat) ==> (@iff) as setminus_Same_set.
  Proof with intuition.
    unfold setdim... 
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
    intros S T... 
    induction H0.
      left. rewrite <- H...
      apply (tr_trans _ _ y); try rewrite <- H...
    induction H0.
      left. rewrite H...
      apply (tr_trans _ _ y); try rewrite H...
  Qed.

  Add Parametric Morphism : (well_formed) with
    signature (@Same_set carrier) ==> (iff) as well_formed_Same_set.
  Proof with intuition.
    autounfold with *...
      refine (H3 _ _ _ n _ _ _)...
      refine (H3 _ _ _ n _ _ _)...
  Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* sub and sup                                          *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma sub_Included_Lemma : forall S T m, Included (S) (sub T m) -> forall x, (In S x -> dim x = m). 
  Proof with crush. 
    unfold setdim...
    apply H...
  Qed.

  Lemma sub_def_Lemma : forall m x S, In (sub S m) x -> (dim x = m). 
  Proof with crush. 
    crush. 
  Qed.

  Lemma sup_def_Lemma : forall S m x, In (sup S m) x -> (dim x <= m). 
  Proof with crush. 
    crush. 
  Qed.

  Hint Extern 1 (dim _ = _) => 
    match goal with 
      | H: ?X ⊆ (sub _ (?n)), _: In ?X ?x |- (dim ?x = ?n) => apply (sub_Included_Lemma _ _ _ H)
      | H: In (sub _ ?n) ?x |- (dim ?x = ?n) => apply (sub_def_Lemma _ _ _ H) 
      | H: dim ?x = S ?n, K: In (minus ?x) ?y |- (dim ?y = ?n) =>
          apply minus_dim in K; rewrite H in K; inversion K; trivial
    end.

  Hint Extern 1 (dim _ <= _) => 
    match goal with 
    | H: In (sup _ ?n) ?x |- (dim ?x <= ?n) => apply (sup_def_Lemma _ _ _ H) 
    end.

  Hint Resolve qwer qwer' qwer'' sub_Included_Lemma sub_def_Lemma sup_def_Lemma le_Sn_n n_Sn.

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

  Lemma sub_Union : forall T R n, sub (Union T R) n == Union (sub T n) (sub R n).
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Same_set; unfold Included...
    inversion H0; [left | right]...
    inversion H; [left | right]...
    inversion H; inversion H0...
  Qed.

  Lemma sup_Union : forall T R n, sup (Union T R) n == Union (sup T n) (sup R n).
  Proof with repeat (basic || subsuptac); auto.
    intros.
    unfold Same_set; unfold Included...
    inversion H0; [left | right]...
    inversion H; [left | right]...
    inversion H; inversion H0...
  Qed.

  Lemma sub_Included_compat : forall S T, S ⊆ T -> forall m, (sub S m) ⊆ (sub T m).
  Proof.
    autounfold with *. intuition.
  Qed.

  Lemma sup_Included_compat : forall S T, S ⊆ T -> forall m, (sup S m) ⊆ (sup T m).
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

  Lemma sub_Plus : forall n T, sub (Plus T) n == Plus (sub T (S n)).
  Proof with intuition.
    autounfold with *. 
    intros. split.
    intros... 
    inversion H0. exists x0... subst. symmetry. apply plus_dim...
    intros.
    inversion H; clear H...
    exists x0...
    apply plus_dim in H1... rewrite H2 in H1... 
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

  Lemma sup_Minus : forall T n, sup (Minus T) n == Minus (sup T (S n)).
  Proof with repeat (basic || subsuptac); auto.
    unfold Same_set.
    intros.
    unfold Included...
    unfold Plus in H0. unfold In in H0. inversion H0. clear H0...
    unfold Plus. unfold In. exists x0... unfold sup... apply minus_dim in H2.
    rewrite <- H2. apply le_n_S...
    generalize dependent n.
    unfold Minus. unfold Included...
    unfold In. exists x0... unfold sup in H...
    unfold In in H. inversion H. clear H...
    apply le_S_n. apply minus_dim in H1. rewrite H1...
  Qed.

  Lemma sub_Setminus : 
    forall A B k, sub (Setminus A B) k == Setminus (sub A k) (sub B k).
  Proof with intuition.
    crush.
  Qed.

  Lemma sub_PlusMinus : forall n T, sub (PlusMinus T) n == PlusMinus (sub T (S n)).
  Proof with intuition.
    intros.
    unfold PlusMinus.
    repeat (rewrite <- Setminus_is_Intersection_Complement).
    rewrite sub_Setminus.
    rewrite sub_Plus.
    rewrite sub_Minus...
  Qed.

  Lemma sub_MinusPlus : forall n T, sub (MinusPlus T) n == MinusPlus (sub T (S n)).
  Proof with intuition.
    intros.
    unfold MinusPlus.
    repeat (rewrite <- Setminus_is_Intersection_Complement).
    rewrite sub_Setminus.
    rewrite sub_Plus.
    rewrite sub_Minus...
  Qed.

  Lemma sub_sup_Empty_set : forall n k, n < k -> forall S, sub (sup S n) k == Empty_set.
  Proof with intuition.
    autounfold with *... 
    subst. exfalso. 
    apply (le_Sn_n n).
    apply (le_trans _ (dim x))...
  Qed. 

  Lemma sub_sup_cancel : forall k n, k <= n -> forall P, sub (sup P n) k == sub P k.
  Proof with intuition. 
    crush...
  Qed.

  Lemma sup_sub_comm : forall S n k, sup (sub S n) k == sub (sup S k) n. 
  Proof with intuition. 
    crush.
  Qed.

  Lemma sup_sup_comm : forall S n k, sup (sup S n) k == sup (sup S k) n. 
  Proof with intuition. 
    crush.
  Qed.

  Lemma sup_sup_min : forall S n k, k <= n -> sup (sup S n) k == sup S k. 
  Proof with intuition. 
    crush. apply (le_trans _ k)...
  Qed.

  Lemma sub_Singleton_Empty_set : forall y k, ~(dim y = k) -> sub (Singleton y) k == Empty_set.
  Proof with intuition.
    intros...
    crush. 
    inversion H1; subst...
  Qed. 

  Lemma sub_plus_Empty_set : forall y k, ~(dim y = S k) -> sub (plus y) k == Empty_set.
  Proof with intuition.
    intros...
    crush.
    assert (S (dim x) = dim y)...
    apply H. rewrite <- H0...
  Qed. 

  Lemma sub_minus_Empty_set : forall y k, ~(dim y = S k) -> sub (minus y) k == Empty_set.
  Proof with intuition.
    intros...
    crush.
    assert (S (dim x) = dim y)...
    apply H. rewrite <- H0...
  Qed. 

  Lemma sub_Singleton : forall y k, (dim y = k) -> sub (Singleton y) k == Singleton y.
  Proof with intuition.
    intros...
    crush.
    inversion H0; subst... 
  Qed. 

  Lemma sub_plus : forall y k, (dim y = S k) -> sub (plus y) k == plus y.
  Proof with intuition.
    intros...
    crush.
    assert (S (dim x) = dim y)...
    rewrite H in H1... 
  Qed. 

  Lemma sub_minus : forall y k, (dim y = S k) -> sub (minus y) k == minus y.
  Proof with intuition.
    intros...
    crush.
    assert (S (dim x) = dim y)...
    rewrite H in H1... 
  Qed. 

  Lemma sub_sup_0 : forall X, sub X 0 == sup X 0.
  Proof with intuition.
    crush. rewrite H1... 
  Qed.

  Lemma sub_Sn_sup_n : forall M n, (Union (sub M (S n)) (sup M n)) == sup M (S n).
  Proof with intuition.
   crush. 
   rewrite H0; crush.
   inversion H1; clear H1; [left | right]; crush.
  Qed.

  Lemma sub_sub_Empty_set : forall n k, ~(n=k) -> forall T, sub (sub T n) k == Empty_set.
  Proof with intuition. 
    intros...
    crush... apply H. rewrite H3 in H2...
  Qed. 

  Lemma sub_Included' : forall S T, Included S T -> forall n, Included (sub S n) (sub T n).
  Proof with intuition. 
    crush. 
  Qed. 

  Lemma Same_set_by_dimension : forall R T, 
    (R == T) <-> forall k, sub R k == sub T k.
  Proof with intuition.
    intros...
    rewrite H...
    unfold Same_set, Included...
    assert (In (sub R (dim x)) x)... 
    rewrite H in H1. subsuptac... 
    assert (In (sub T (dim x)) x)... 
    rewrite <- H in H1. subsuptac... 
  Qed.

  Lemma Finite_sub : forall T, Finite T -> forall n, Finite (sub T n). 
  Proof with intuition.
    intros.
    apply (Finite_Included'' T)...
    assert ({dim x = n} + {~ (dim x) = n})...
      apply eq_nat_dec.
  Qed.

  Lemma Finite_sup : forall T, Finite T -> forall n, Finite (sup T n). 
  Proof with intuition.
    intros.
    apply (Finite_Included'' T)...
    assert ({dim x <= n} + {~ (dim x) <= n})...
      apply le_dec.
  Qed.

  Hint Resolve Finite_sub Finite_sup.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Plus and Minus results *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma Plus_Union : forall S T,
     Plus (Union S T) == Union (Plus S) (Plus T).
  Proof with intuition. 
    autounfold with *...
    inversion H... inversion H1; [left |right]; unfold In; exists x0...
    inversion H; subst;
    unfold In in H0; inversion H0; exists x0... 
    left... right...
  Qed.

  Lemma Minus_Union : forall S T,
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

  Lemma Plus_Singleton : forall x, Plus (Singleton x) == plus x.
  Proof with intuition.
    autounfold with *... inversion H... inversion H1... exists x...
  Qed.

  Lemma Minus_Singleton : forall x, Minus (Singleton x) == minus x.
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
      apply plus_minus_Disjoint...
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
      apply plus_minus_Disjoint...
    inversion H1. apply (H4 x0)...
    apply plus_zero in H2... 
    assert (In Empty_set x0).
    rewrite <- H2... 
    unfold In in *...
  Qed.

  Lemma Plus_Finite : 
    forall A, Finite A ->
      Finite (Plus A).
  Proof with intuition.
    intros.
    induction H...
      apply (Finite_Same_set Empty_set)...
      crush. 
      inversion H... 

      unfold Add.
      rewrite Plus_Union.
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
      apply (Finite_Same_set Empty_set)...
      crush. inversion H... 

      unfold Add. 
      rewrite Minus_Union. 
      rewrite Minus_Singleton. 
      apply Finite_Union...
   
      rewrite H0...
  Qed.

  Lemma PlusMinus_Finite : 
    forall A, Finite A ->
      Finite (PlusMinus A).
  Proof with intuition.
    intros.
    unfold PlusMinus.
    apply (Finite_Included'' (Plus A))...
    apply Plus_Finite...
    crush.
    assert ((In (Minus A) x) \/ ~(In (Minus A) x))...
      apply all_decidable...
      apply Minus_Finite...
    right... apply In_Intersection in H1...
  Qed.

  Lemma MinusPlus_Finite : 
    forall A, Finite A ->
      Finite (MinusPlus A).
  Proof with intuition.
    intros.
    unfold MinusPlus.
    apply (Finite_Included'' (Minus A))...
    apply Minus_Finite...
    crush.
    assert ((In (Plus A) x) \/ ~(In (Plus A) x))...
      apply all_decidable...
      apply Plus_Finite...
    right... apply In_Intersection in H1...
  Qed.

  Lemma Minus_Included : forall X Y, Included X Y -> Included (Minus X) (Minus Y). 
  Proof with intuition. 
    crush... 
    inversion H0; clear H0. 
    exists x0...
  Qed.

  Lemma Plus_Included : forall X Y, Included X Y -> Included (Plus X) (Plus Y). 
  Proof with intuition. 
    crush... 
    inversion H0; clear H0. 
    exists x0...
  Qed.

  Lemma Plus_Empty_set : Plus (Empty_set) == Empty_set.
  Proof with intuition. 
    unfold Same_set, Included... 
    exfalso; inversion H... 
    exfalso... 
  Qed.

  Lemma Minus_Empty_set : Minus (Empty_set) == Empty_set.
  Proof with intuition. 
    unfold Same_set, Included... 
    exfalso; inversion H... 
    exfalso... 
  Qed.  

  Hint Resolve all_decidable Plus_Finite Minus_Finite PlusMinus_Finite MinusPlus_Finite.

  Lemma dim_1_properties : forall x, dim x = 1 -> 
    ( 
    Plus  (minus x) == Empty_set /\
    Plus  (plus  x) == Empty_set /\
    Minus (minus x) == Empty_set /\
    Minus (plus  x) == Empty_set 
    ). 
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

  (** WELL_FORMED PROPERTIES **)
  
  Lemma well_formed_Included : 
    forall T, well_formed T -> forall R, Included R T -> well_formed R.
  Proof with intuition.
    autounfold with *...
    refine (H1 _ _ _ n _ _ _)... 
  Qed.

  Lemma well_formed_Singleton : 
    forall x, well_formed (Singleton x).
  Proof with intuition.
    intros x.
    unfold well_formed...
    inversion H2; inversion H3; subst...
    inversion H0; inversion H1; subst...
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

  Lemma well_formed_by_dimension : 
    forall X, 
      well_formed X <-> forall n, well_formed (sub X n).
  Proof with intuition.
    intros...
    - unfold well_formed in *...
      + apply H0... apply  H4. apply H5.
      + apply H1 with (n := n0)... apply H2. apply H3.
    - unfold well_formed in *...
      + apply (H 0)... 
      + specialize H with (n := (S n))...
        apply (H6) with (n := n)...
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
          refine (H1 _ _ _ n _ _ _)... 
          exfalso; apply (H2 x y)... rewrite H, H7...
        inversion H6; clear H6; subst...
          exfalso; apply (H2 y x)... rewrite H, H7...
          refine (H4 _ _ _ n _ _ _)... 
    Qed.

  Hint Resolve well_formed_Singleton well_formed_Included.

  (** MAXIMAL and MINIMAL ELEMENTS **)

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
           right... unfold Add in H4...
           inversion H4... apply (le_trans _ (dim z) _)... 
           apply Singleton_inv in H10; subst...

      assert (Inhabited T). inversion H0. apply (Inhabited_intro _ _ x). 
      rewrite <- H1... 
      apply IHFinite in H2. inversion H2. exists x...
  Qed. 

  Hint Resolve Finite_are_decidable carrier_decidable_eq.

  Lemma Setminus_Finite : 
    forall A, @Finite carrier A ->
    forall B, Finite B ->
      Finite (Intersection A (Complement B)).
  Proof with intuition.
    intros.
    induction H.
    - apply (Finite_Same_set Empty_set)...

    - unfold Add.
      rewrite I_U_dist_r. 
      apply Finite_Union...
      assert (In B x \/ ~(In B x)). 
        apply all_decidable... 
      inversion H2; clear H2.
      + apply (Finite_Same_set Empty_set).
        constructor.
        unfold Same_set, Included...  
        * repeat basic. 
          inversion H4; clear H4; subst... unfold Complement, In at 1 in H5...
        * inversion H2...
      + apply (Finite_Same_set (Singleton x)).
        apply Finite_Singleton.
        unfold Same_set, Included...
        * repeat basic. 
          inversion H4...
        * inversion H2; clear H2; subst...

    - rewrite H1...
  Qed.

  Lemma triangle_rest_dec : 
    forall T, 
      Finite T -> 
      forall x z, (triangle_rest T z x \/ ~(triangle_rest T z x)).
  Proof with intuition.
   (* could use strong induction on cardinality of T? *)
   intros T TFin. 
   assert (exists n, Cardinal T n) as K.
   apply Cardinality_exists... 
   inversion K as [n TCard]; clear K. 
   revert n T TFin TCard. 
   refine (strong_induction _ _ _)...
     - right... 
       apply Cardinality_zero_Empty_set in TCard. 
       rewrite TCard in H...
       apply triangle_rest_in_set in H...
     - set (R := fun r => less z r /\ In T r).
       assert (Finite R) as RFin. 
         apply (Finite_Included'' T)... 
         unfold R, Included... unfold In at 1 in H0...
         assert ((less z x0) \/ ~(less z x0))...
         apply less_decidable. 
         left... unfold R, In at 1... 
         right... unfold R, In at 1 in H1...
       assert (exists n, Cardinal R n) as J.
       apply Cardinality_exists... 
       inversion J as [k RCard]; clear J...
       assert (decidable T) as Tdec.
         apply Finite_are_decidable...       
       assert ((In T x) \/ ~(In T x))... 
         apply Tdec.
       assert ((In T z) \/ ~(In T z))... 
         apply Tdec.
       assert ((z = x) \/ ~(z = x))... 
         apply carrier_decidable_eq.       
       left. 
       rewrite H3; left...
                     
       destruct k. 
       + right...
         inversion H0...
         assert (In R y).
           unfold R, In at 1...
           apply triangle_rest_in_set in H6... 
         apply Cardinality_zero_Empty_set in RCard. 
         rewrite RCard in H9... 
       + set (T' := Setminus T (Singleton z)). 
         assert (Finite T') as T'Fin. 
           unfold T'... 
           rewrite Setminus_is_Intersection_Complement. 
           apply Setminus_Finite...  
           apply Finite_Singleton...
         set (Q := fun w => triangle_rest T' w x).
         assert (Finite Q) as QFin. 
           apply (Finite_Included'' T)... 
           unfold Q, Included, In at 1...
           apply triangle_rest_in_set in H0...
           unfold T', In at 1 in H4... inversion H4... 
           assert ((x0 = z) \/ ~(x0 = z)). 
             apply carrier_decidable_eq... 
           idtac... 
           right... 
           rewrite H5 in H4.
           assert (In T' z). 
             unfold Q, In at 1 in H4... 
             apply triangle_rest_in_set in H4... 
           unfold T', In at 1 in H6...
           inversion H6...
           assert (triangle_rest T' x0 x ∨ (triangle_rest T' x0 x → False)). 
             apply (H n)...
             unfold T'. apply Cardinal_Setminus... 
           idtac...  
         assert (Finite (Intersection R Q)).
           apply Finite_Intersection...
         apply (Finite_Empty_or_Inhabited) in H0...
         * right...
           inversion H0...
           assert (In (Intersection R Q) y). 
             apply In_Intersection...
             unfold R, In at 1...
             apply triangle_rest_in_set in H7... 
             unfold Q, In at 1...         
             subst.
             admit. (* ?? *) 
           rewrite H4 in H10... 
         * left... 
           inversion H4; clear H4.
           apply In_Intersection in H0... 
           unfold R, In at 1 in H4.
           unfold Q, In at 1 in H5.
           right with x0... 
           apply (triangle_rest_Included T')...
           unfold T'... 
           apply Setminus_Included. 

       + right... apply H2... apply triangle_rest_in_set in H0... 
       + right... apply H1... apply triangle_rest_in_set in H0... 
  Qed.

  Hint Resolve Finite_Singleton sub_sup_0.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* dimension stuff                                      *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma Minus_dim : 
      forall X Y n, Included X (sub Y (S n)) -> 
      forall y, In (Minus X) y ->
      dim y = n.
  Proof with intuition.
    idtac... unfold Minus, In at 1 in H0...
    inversion H0; clear H0...
    assert (dim x = (S n))...
  Qed.

  Lemma Plus_dim : 
      forall X n, Included X (sub Full_set (S n)) -> 
      forall y, In (Plus X) y ->
      dim y = n.
  Proof with intuition.
    idtac... unfold Plus, In at 1 in H0...
    inversion H0; clear H0...
    assert (dim x = (S n))... assert (S (dim y) = (dim x))...
    rewrite H1 in H3...
  Qed.

  Lemma Plus_dim' : 
      forall X n, Included X (sup Full_set (n)) -> 
      forall y, In (Plus X) y ->
      S (dim y) <= n.
  Proof with intuition.
    idtac... unfold Plus, In at 1 in H0...
    inversion H0; clear H0...
    assert (dim x <= (n))... apply H...  assert (S (dim y) = (dim x))...
    rewrite H3...
  Qed.

  Lemma Minus_dim' : 
      forall X n, Included X (sup Full_set (n)) -> 
      forall y, In (Minus X) y ->
      S (dim y) <= n.
  Proof with intuition.
    idtac... unfold Minus, In at 1 in H0...
    inversion H0; clear H0...
    assert (dim x <= (n))... apply H...  assert (S (dim y) = (dim x))...
    rewrite H3...
  Qed.
  
  Hint Resolve Finite_sub Finite_sup PlusMinus_Finite MinusPlus_Finite Plus_Finite Minus_Finite.

  Lemma setdim_Union : forall S T n, (setdim S n /\ setdim T n) <-> setdim (Union S T) n.
  Proof with intuition.
    unfold setdim... basic... 
  Qed.

  Lemma setdim_sup : forall S n k, k <= n -> setdim (sup S k) n.
  Proof with intuition.
    unfold setdim, sup... unfold In at 1 in H0... apply (le_trans _ k)... 
  Qed.

  Lemma setdim_sub : forall S n k, k <= n -> setdim (sub S k) n.
  Proof with intuition.
    unfold setdim, sub... unfold In at 1 in H0... rewrite H2... 
  Qed.

  Lemma setdim_Setminus : forall R T n, setdim R n -> setdim (Setminus R T) n.
  Proof with intuition.
    unfold setdim, Setminus... unfold In at 1 in H0...
  Qed.

  Lemma setdim_Minus : forall T n, setdim T (S n) -> setdim (Minus T) n.
  Proof with intuition.
    unfold setdim... 
    inversion H0...  assert (S (dim x) = dim x0)... apply H in H2... 
    rewrite <- H1 in H2...
  Qed.

  Lemma setdim_Included : forall R T, Included R T -> forall n, setdim T n -> setdim R n.
  Proof with intuition.
    unfold setdim... 
  Qed.

  Lemma setdim_Singleton : forall x n, setdim (Singleton x) n <-> dim x <= n. 
  Proof with intuition.
    unfold setdim...
    inversion H0...
    rewrite <- H1...
  Qed.

  Ltac setdimtac :=
    match goal with
     | H : _ |- setdim (Union _ _) _ => apply setdim_Union
     | H : _ |- setdim (Setminus _ _) _ => apply setdim_Setminus
     | H : _ |- setdim (Intersection _ (Complement _)) _ => rewrite <- Setminus_is_Intersection_Complement
     | H : _ |- setdim (sub _ _) _ => apply setdim_sub
     | H : _ |- setdim (sup _ _) _ => apply setdim_sup
     | H : _ |- setdim (Minus _) _ => apply setdim_Minus
     | H : _ |- setdim (Singleton _) _ => apply setdim_Singleton
    end; 
    intuition; 
    try setdimtac.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* movement results                                     *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma moves_by_dim : forall T M P, ((T moves M to P) <-> (forall n, (sub T (S n) moves (sub M n) to (sub P n)))).
  Proof with intuition. 
    intros... 
     - unfold moves_def in *... 
       + rewrite H0... 
         rewrite <- Setminus_is_Intersection_Complement.
         rewrite sub_Setminus. 
         rewrite Setminus_is_Intersection_Complement.
         rewrite sub_Union.
         rewrite sub_Minus.
         rewrite sub_Plus...
       + rewrite H1... 
         rewrite <- Setminus_is_Intersection_Complement.
         rewrite sub_Setminus. 
         rewrite Setminus_is_Intersection_Complement.
         rewrite sub_Union.
         rewrite sub_Minus.
         rewrite sub_Plus...
     - unfold moves_def in *... 
       + unfold Same_set, Included... 
         assert (In (sub P (dim x)) x)... 
         specialize H with (n := (dim x))...
         rewrite <- sub_Plus in H2.
         rewrite <- sub_Minus in H2.
         rewrite <- sub_Union in H2.
         rewrite <- Setminus_is_Intersection_Complement in H2.
         rewrite <- sub_Setminus in H2. 
         rewrite Setminus_is_Intersection_Complement in H2.
         rewrite H2 in H1... 
         subsuptac... 
         assert (In (sub ((M ∪ Plus T) ∩ √Minus T) (dim x)) x)... 
         specialize H with (n := (dim x))...
         rewrite <- sub_Plus in H2.
         rewrite <- sub_Minus in H2.
         rewrite <- sub_Union in H2.
         rewrite <- Setminus_is_Intersection_Complement in H2.
         rewrite <- sub_Setminus in H2. 
         rewrite Setminus_is_Intersection_Complement in H2.
         rewrite <- H2 in H1... 
         subsuptac... 
       + unfold Same_set, Included... 
         assert (In (sub M (dim x)) x)... 
         specialize H with (n := (dim x))...
         rewrite <- sub_Plus in H3.
         rewrite <- sub_Minus in H3.
         rewrite <- sub_Union in H3.
         rewrite <- Setminus_is_Intersection_Complement in H3.
         rewrite <- sub_Setminus in H3. 
         rewrite Setminus_is_Intersection_Complement in H3.
         rewrite H3 in H1... 
         subsuptac... 
         assert (In (sub ((P ∪ Minus T) ∩ √Plus T) (dim x)) x)... 
         specialize H with (n := (dim x))...
         rewrite <- sub_Plus in H3.
         rewrite <- sub_Minus in H3.
         rewrite <- sub_Union in H3.
         rewrite <- Setminus_is_Intersection_Complement in H3.
         rewrite <- sub_Setminus in H3. 
         rewrite Setminus_is_Intersection_Complement in H3.
         rewrite <- H3 in H1... 
         subsuptac... 
  Qed.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* weird lemmas                                         *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma weird_lemma_3 :  
    forall S T : Ensemble carrier,
    (S ⊆ T /\ 
    (forall x z : carrier, x ∈ S ∧ z ∈ S -> 
        forall y, triangle_rest T x y ∧ triangle_rest T y z -> 
           y ∈ S)) ->
    (is_a_segment S T).
  Proof with intuition.
   intros...
   unfold is_a_segment...
   apply (H1 x z)...
   assert (In T y)...
     inversion H4... 
   apply (tr_trans _ _ y)...
   left...
  Qed.

  Lemma weird_lemma_4 :  
    forall S T : Ensemble carrier,
    (is_a_segment S T)
    ->
    (S ⊆ T /\ 
    (forall x z : carrier, x ∈ S ∧ z ∈ S -> 
        forall y, triangle_rest T x y ∧ triangle_rest T y z -> 
           y ∈ S)).
  Proof with intuition.
    intros. 
    unfold is_a_segment in H...
    (* need other induction principle for triangle_rest *)
  Admitted.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* initial and final segments                           *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  Lemma initial_property : forall S T M, 
    is_initial_segment S M -> 
    Included T M ->
    Disjoint S T -> 
      forall a b, 
        In S a -> 
        In T b ->
        less b a -> False.
  Proof with intuition.
    intros...
    unfold is_initial_segment in H... 
    inversion H1; clear H1... 
    apply (H b)... apply In_Intersection... 
    apply (H6 _ a)... apply (tr_trans _ _ a)... left... 
  Qed.

  Lemma final_property : forall T S M, 
    is_final_segment T M -> 
    Included S M ->
    Disjoint S T -> 
      forall a b, 
        In S a -> 
        In T b ->
        less b a -> False.
  Proof with intuition.
    intros...
    unfold is_final_segment in H... 
    inversion H1; clear H1... 
    apply (H a)... apply In_Intersection... 
    apply (H6 b)... apply (tr_trans _ _ a)... left... 
  Qed.

  Lemma Perp_thing :
    forall U V, Disjoint U V -> well_formed (Union U V) -> Finite U -> Finite V -> 
       (forall a b, In U a /\ In V b -> dim a = dim b) ->
       (Plus U ∩ Plus V == Empty_set ∧ Minus U ∩ Minus V == Empty_set). 
  Proof with intuition.
    intros... 
    - rename H3 into G.
      unfold well_formed in H0...
      apply Disjoint_Intersection_condition. 
      constructor... 
      apply In_Intersection in H0... 
      inversion H5; clear H5.
      inversion H6; clear H6...
      assert (x0 = x1).
        remember (dim x0) as w.
        destruct (w).
        + exfalso. rewrite plus_zero in H7...
        + refine (H4 _ _ _ w _ _ _)...
          rewrite Heqw. symmetry. apply G...
          unfold perp in H5... 
          assert (In Empty_set x)... 
          rewrite <- H9... +
      rewrite H5 in *.
      inversion H... 
      apply (H9 x1)... 
    - rename H3 into G.
      unfold well_formed in H0...
      apply Disjoint_Intersection_condition. 
      constructor... 
      apply In_Intersection in H0... 
      inversion H5; clear H5.
      inversion H6; clear H6...
      assert (x0 = x1).
        remember (dim x0) as w.
        destruct (w).
        + exfalso. rewrite minus_zero in H7...
        + refine (H4 _ _ _ w _ _ _)...
          rewrite Heqw. symmetry. apply G...
          unfold perp in H5... 
          assert (In Empty_set x)... 
          rewrite <- H10... +
      rewrite H5 in *.
      inversion H... 
      apply (H9 x1)... 
  Qed.

  Lemma TT : forall k S T, setdim T k /\ setdim S k -> 
                (forall m, m <= k -> sub T m == sub S m) -> S == T.
  Proof with intuition.
   intros...
     unfold Same_set, Included... 
       assert (dim x <= k)...
       apply (sub_Included T (dim x))...
       rewrite H0...
       assert (dim x <= k)...
       apply (sub_Included S (dim x))...
       rewrite <- H0...
  Qed.

  Lemma weird_lemma_2 : forall S T, 
    well_formed S -> 
    well_formed T -> 
    Perp S T -> 
    sub (Union S T) 0 == Empty_set -> 
    well_formed (Union S T).
  Proof with intuition.
  intros...
  unfold well_formed in *...
    exfalso; assert (In Empty_set x)... rewrite <- H2... 
    repeat (basic; intuition)... 
      refine (H4 _ _ _ n _ _ _)...
      exfalso; apply H9; unfold perp... 
      assert (Finite (plus x ∩ plus y)). apply Finite_Intersection... apply Finite_Empty_or_Inhabited in H1... 
      assert (Inhabited (Plus S ∩ Plus T)). inversion H12; clear H12... exists x0...
      apply In_Intersection in H1... apply In_Intersection... exists y... exists x... 
      exfalso... inversion H1... rewrite H6 in H13... 
      assert (Finite (minus x ∩ minus y)). apply Finite_Intersection... apply Finite_Empty_or_Inhabited in H1... 
      assert (Inhabited (Minus S ∩ Minus T)). inversion H12; clear H12... exists x0...
      apply In_Intersection in H1... apply In_Intersection... exists y... exists x... 
      exfalso... inversion H1... rewrite H11 in H13...
      exfalso; apply H9; unfold perp... 
      assert (Finite (plus x ∩ plus y)). apply Finite_Intersection... apply Finite_Empty_or_Inhabited in H1... 
      assert (Inhabited (Plus S ∩ Plus T)). inversion H12; clear H12... exists x0...
      apply In_Intersection in H1... apply In_Intersection... exists x... exists y... 
      exfalso... inversion H1... rewrite H6 in H13... 
      assert (Finite (minus x ∩ minus y)). apply Finite_Intersection... apply Finite_Empty_or_Inhabited in H1... 
      assert (Inhabited (Minus S ∩ Minus T)). inversion H12; clear H12... exists x0...
      apply In_Intersection in H1... apply In_Intersection... exists x... exists y... 
      exfalso... inversion H1... rewrite H11 in H13...
      refine (H5 _ _ _ n _ _ _)...
  Qed.

  Lemma Cardinal_eq_Included_Same_set : 
    forall n Z, Cardinal Z n -> 
        forall X, Cardinal X n -> 
            @Included carrier Z X -> X == Z.
  Proof with intuition.
    intros n Z Zcard.
    induction Zcard...
      - apply Cardinality_zero_Empty_set... 
      - unfold Same_set...
        unfold Add, Included...
        assert (X == Add (Setminus X (Singleton x)) x). 
          apply Add_Setminus_Singleton. apply carrier_decidable_eq...
          apply H1... 
        assert (Setminus X (Singleton x) == A). 
          apply IHZcard...
          apply Cardinal_Setminus... unfold Included... 
          assert ((x1 = x) \/ ~(x1 = x))... apply carrier_decidable_eq...
            + exfalso. apply H... rewrite <- H6...
            + unfold Setminus, In at 1... inversion H5... + 
        rewrite H3 in H2. 
        unfold Add in H2. apply In_Union in H2... 
      - rewrite <- H. apply IHZcard...
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
    apply all_decidable... 

    rewrite U_I_dist_r.
    rewrite Full_set_property.
    rewrite Full_set_ident_right.
    rewrite I_U_dist_r.
    rewrite Empty_set_property.
    rewrite Empty_set_ident_left.
    reflexivity. 
    apply all_decidable... 
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
    assert ((M ∩ √Plus S) == M). apply Intersection_Included_left.
    apply Disjoint_property_right. apply Disjoint_sym. assumption. 
    rewrite H; clear H.
    symmetry. rewrite Union_sym.
    apply Union_Included_left. apply H0.
    apply all_decidable... 
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
    assert ((P ∩ √Minus S) == P). apply Intersection_Included_left.
    apply Disjoint_property_right. apply Disjoint_sym. assumption. 
    rewrite H; clear H.
    symmetry. rewrite Union_sym.
    apply Union_Included_left. apply H0. 
    auto.
  Qed.

  Lemma Prop_2_1_dual' : ∀ S P : Ensemble carrier,
       Finite S
    → (S moves ((P ∪ Minus S) ∩ √Plus S) to P)
         ↔ PlusMinus S ⊆ P ∧ Disjoint P (Minus S).
  Proof with intuition. 
    intros S P SFin. split; intros.
    apply Prop_2_1_dual...
    exists ((P ∪ Minus S) ∩ √Plus S). assumption.
    apply Prop_2_1_dual in H...
    inversion H as [M K]. 
    unfold moves_def in *...
    rewrite <- H1...
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
          
        apply Disjoint_Intersection_condition.
        rewrite Intersection_trans. rewrite (Intersection_sym _ (Plus S)).
        rewrite <- Intersection_trans.
        rewrite I_U_dist_r. assert (Disjoint Y (Plus S)). apply H2. 
        apply Disjoint_Intersection_condition in H. rewrite H.
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
    rewrite Minus_Union. rewrite Union_Complement_compat...
    rewrite <- H5.
    rewrite <- Intersection_trans.
    assert ((Plus S ∪ Plus T) == (Plus (S ∪ T))). 
    rewrite Plus_Union...
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
    rewrite Plus_Union. rewrite Union_Complement_compat... rewrite Union_sym...
    rewrite <- H5.
    rewrite <- Intersection_trans.
    assert ((Minus T ∪ Minus S) == (Minus (S ∪ T))). 
    rewrite Minus_Union... rewrite Union_sym...
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
        rewrite HeqS. rewrite Minus_Union. apply Union_Included_cancel_left. reflexivity.
      apply Disjoint_Intersection_condition. apply (Included_Empty_set _ (P ∩ Minus S)). apply Intersection_Included_compat...
      rewrite H2. rewrite Intersection_trans. rewrite (Intersection_sym _ (Minus S)). 
      rewrite Empty_set_property...
    inversion H1 as [N']; clear H1.

    assert (exists N', T moves M to N').        
    apply Prop_2_1. assumption. split.
      assert (K1: Plus T == (Plus S) ∩ √(Plus Z)). 
        rewrite HeqS. rewrite Plus_Union. rewrite I_U_dist_r.
        rewrite Empty_set_property. rewrite Empty_set_ident_right.
        apply Disjoint_result... 
      assert (K2: Minus T == (Minus S) ∩ √(Minus Z)). rewrite HeqS. 
        rewrite Minus_Union. rewrite I_U_dist_r.
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

      (* apply Disjoint_Intersection_condition.  *)
      constructor... rewrite H3 in H6...
      rewrite HeqS in H8. assert ((√Plus (T ∪ Z)) == ((√ Plus T ∩ √ Plus Z))).
      rewrite Plus_Union. rewrite Union_Complement_compat...
      rewrite H6 in H8...

    inversion H1 as [N]; clear H1. 
    exists N. exists N'...
    
    unfold moves_def in H5. inversion H5. clear H5.
    unfold moves_def in H6. inversion H6. clear H6.
    rewrite H7, H5. 
    assert ((Plus T) == (Intersection (Plus S) (Complement (Plus Z)))).
      rewrite HeqS. rewrite Plus_Union. rewrite I_U_dist_r.
      rewrite Empty_set_property. rewrite Empty_set_ident_right.
      apply Disjoint_result. assumption.
    assert ((Minus T) == (Intersection (Minus S) (Complement (Minus Z)))).
      rewrite HeqS. rewrite Minus_Union. rewrite I_U_dist_r.
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
      rewrite H10. rewrite HeqS. rewrite Minus_Union. left; right...
    assert ((MinusPlus S ∪ Plus S) ⊆ (Union M (Plus S))). 
      unfold MinusPlus. rewrite H3. apply Union_Included_compat. 
      apply Intersection_Included_compat. apply Union_Included_cancel_left. 
      reflexivity. reflexivity. reflexivity.
    assert (Minus Z ⊆ M ∪ Plus S). 
      apply (Included_trans _ (MinusPlus S ∪ Plus S)). apply H10... assumption.
    assert (((M ∪ Plus S) ∩ Minus Z) == (Minus Z)).
      unfold Same_set; unfold Included... rewrite H13.
    assert ((M ∪ √Plus Z) == (√Plus Z)).
      apply Union_Included_left.
      rewrite H3. apply Intersection_Included_cancel_left.
      apply Complement_Included_flip. rewrite HeqS. 
      rewrite Plus_Union. apply (Included_trans _ (Plus T ∪ Plus Z) _).
      unfold Included; intros; right... apply Complement_closure.
    rewrite H14... auto. auto.
  Qed.

  Lemma Prop_2_4' : (* ignore this lemma for the moment, sort it out near the end *)
    forall (T Z M P : Ensemble carrier),
    Finite Z -> Finite T -> (Union T Z) moves M to P -> 
    Included (PlusMinus Z) P ->
    Perp T Z ->
    (T moves M to (M ∪ Plus T) ∩ √Minus T) /\ 
    (Z moves (P ∪ Minus Z) ∩ √Plus Z to P) /\ 
    ((P ∪ Minus Z) ∩ √Plus Z == (M ∪ Plus T) ∩ √Minus T).
  Proof with repeat basic; auto.
    intros T Z M P ZFin TFin. 
    remember (Union T Z) as S.
    intros.
    assert (Finite S) as SFin. 
      rewrite HeqS. apply Finite_Union...
    
    assert ((T moves M to (M ∪ Plus T) ∩ √Minus T)) as A.
    apply Prop_2_1'. 
    assumption. 
    admit. (* ?? *)

    assert ((Z moves (P ∪ Minus Z) ∩ √Plus Z to P)) as B.
    apply Prop_2_1_dual'. 
    assumption.
      split; try assumption.
      assert (Included (Minus Z) (Minus S)). 
        rewrite HeqS. rewrite Minus_Union. apply Union_Included_cancel_left. reflexivity.
      apply Disjoint_Intersection_condition. 
      apply (Included_Empty_set _ (P ∩ Minus S))... 
      apply Intersection_Included_compat...
      admit. (* ?? *)
    
    intuition. 

    unfold moves_def in A...
    unfold moves_def in B...
    unfold moves_def in H...

    assert ((Plus T) == (Intersection (Plus S) (Complement (Plus Z)))) as C.
      rewrite HeqS. rewrite Plus_Union. rewrite I_U_dist_r.
      rewrite Empty_set_property. rewrite Empty_set_ident_right.
      apply Disjoint_result. assumption.
    assert ((Minus T) == (Intersection (Minus S) (Complement (Minus Z)))) as D.
      rewrite HeqS. rewrite Minus_Union. rewrite I_U_dist_r.
      rewrite Empty_set_property. rewrite Empty_set_ident_right.
      apply Disjoint_result. assumption. 
    rewrite C, D. 
    rewrite Intersection_Complement_compat. 
    rewrite Complement_Complement_compat.
    rewrite U_I_dist_l. 
    rewrite Intersection_trans. 
    rewrite (Intersection_sym (M ∪ √Plus Z) _).
    rewrite <- Intersection_trans. 
    rewrite (I_U_dist_l (M ∪ Plus S)). 
    rewrite <- H7.
    assert ((Minus Z) ⊆ Union (MinusPlus S) (Plus S)). admit. (* ?? *)
    assert ((MinusPlus S ∪ Plus S) ⊆ (Union M (Plus S))). admit. (* ?? *)
    assert (Minus Z ⊆ M ∪ Plus S). admit. (* ?? *) 
    assert (((M ∪ Plus S) ∩ Minus Z) == (Minus Z)). admit. (* ?? *)
    assert ((M ∪ √Plus Z) == (√Plus Z)). admit. (* ?? *)
    rewrite H11...
    rewrite H12...  
    auto. 
    auto.
  Qed.

End PreParityTheory.


