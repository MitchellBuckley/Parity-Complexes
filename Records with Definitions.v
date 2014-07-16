
(* Written by Mitchell Buckley 19/11/2013 *)

Require Import Ensembles.
Require Import Finite_sets.
Require Import Relations.
Require Import Utf8_core.

Unset Strict Implicit.
Set Implicit Arguments.

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

(* Notation *)

Notation "A == B" := (Same_set A B) (at level 79).
Notation "A ∪ B" := (Union A B) (at level 61).
Notation "A ∩ B" := (Intersection A B) (at level 61).
Notation "A ⊆ B" := (Included A B) (at level 79).
Notation "x ∈ A" := (In A x) (at level 71).
Notation "√ A"   := (Complement A) (at level 51).
Notation "A == B == C" := ((A == B) /\ (B == C)) (at level 79, B at next level).
Notation "A ⊆ B ⊆ C" := ((A ⊆ B) /\ (B ⊆ C)) (at level 79, B at next level).

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

(*
Record test : Type :=
{
  set : Type;
  rel : set -> set -> Type
}.


Coercion set : test >-> Sortclass.

Notation "A === B" := (rel _ A B) (at level 79).


Definition reflexive (A : test) := 
  forall (a : A), a === a.
*)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Pre-Parity Complexes and associated results          *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Record PreParity : Type :=
{
  carrier :> Type;
  dim : carrier -> nat;
  plus : carrier -> Ensemble carrier;
  minus : carrier -> Ensemble carrier;

  plus_dim :  forall (x y : carrier), In (plus y) x -> S(dim x) = dim y;
  minus_dim : forall (x y : carrier), In (minus y) x -> S(dim x) = dim y; 
  plus_fin :  forall (x : carrier),   Finite (plus x);
  minus_fin : forall (x : carrier),   Finite (minus x);
  plus_non_empty : forall (x : carrier),  dim x > 0 -> (Inhabited (plus x));
  minus_non_empty : forall (x : carrier),  dim x > 0 -> (Inhabited (minus x));
  plus_minus_disjoint : forall (y : carrier), dim y > 0 ->  Disjoint (plus y) (minus y);
  zero_faces: forall (x : carrier),   (dim x) = 0 -> (plus x == minus x == Empty_set _)
}.

Arguments dim : default implicits.
Arguments plus : default implicits.
Arguments minus : default implicits.

Section PreParityTheory.

  Variable carrier : PreParity.

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
    (Intersection (Plus X) (Plus Y) == Empty_set _) /\ (Intersection (Minus X) (Minus Y) == Empty_set _).
  Definition perp (x y : carrier) : Prop :=
    (Intersection (plus x) (plus y) == Empty_set _) /\ (Intersection (minus x) (minus y) == Empty_set _).

  Definition less (x y : carrier) : Prop :=
    (Inhabited (Intersection (plus x) (minus y))).
  Definition curly_less (x y : carrier) : Prop :=
    (In (minus y) x) \/ (In (plus x) y). 
  
  Definition triangle (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans_1n _ (less).
  Definition solid_triangle (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans_1n _ (curly_less).
  Definition triangle_rest (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans_1n _ (restrict S less).
  Definition solid_triangle_rest (S : Ensemble carrier) : relation carrier := 
    clos_refl_trans_1n _ (restrict S curly_less).
    

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

  (* Section 2 *)

  Lemma Observation_p321 : 
    forall (S : Ensemble carrier), S moves (MinusPlus S) to (PlusMinus S).
  Admitted.

  Lemma Prop_2_1 : forall (S M : Ensemble carrier), 
     (exists (P : Ensemble carrier), S moves M to P) 
     <->
     (MinusPlus S) ⊆ M /\ Disjoint M (Plus S).
  Proof. admit.
  Qed.

  Lemma Prop_2_2 : 
    forall (S A B X: Ensemble carrier),
    S moves A to B -> X ⊆ A -> Disjoint (MinusPlus S) X 
    -> 
    forall (Y : Ensemble carrier),  
    Disjoint Y (Plus S) -> Disjoint Y (Minus S) 
    ->
    S moves ((A ∪ Y) ∩ (√X)) to ((B ∪ Y) ∩ (√X)).
  Proof. admit. Qed.

  Lemma Prop_2_3 : 
    forall (S M P T Q : Ensemble carrier),
    S moves M to P -> T moves P to Q -> Disjoint (Minus S) (Plus T) 
    ->
    (S ∪ T) moves M to Q.
  Proof. admit. Qed.

  Lemma Prop_2_4 :
    forall (T Z M P : Ensemble carrier),
    (Union T Z) moves M to P -> 
    Included (PlusMinus Z) P ->
    Perp T Z ->
    exists N, (T moves M to N) /\ (Z moves N to P).
  Proof. admit. Qed.

End PreParityTheory.

Record ParityComplex : Type :=
{
  underlying_preparity :> PreParity;
  axiom1 :
    forall (x : underlying_preparity), 
      Union (Plus (plus x)) (Minus (minus x)) == Union (Plus (minus x)) (Minus (plus x));

  axiom2 :
    forall (x : underlying_preparity), 
      well_formed (plus x) /\ well_formed (minus x);

  axiom3a:
    forall (x y : underlying_preparity), 
      triangle (Full_set _) x y -> triangle (Full_set _) y x -> x = y;

  axiom3b:
    forall (x y z : underlying_preparity), 
    triangle (Full_set _) x y ->
    (~ (In (plus z) x /\ In (minus z) y) /\ ~ (In (plus z) y /\ In (minus z) y))
  (* This last condition somewhat awkwardly phrased, this might become tricky later *)

}.

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Parity Complexes                                     *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

Section ParityComplexTheory.

  Variable carrier : ParityComplex.

  Notation "S 'moves' M 'to' P" := (moves_def S M P) (at level 89).
  (* this notation could maybe be improved, see p321 *)

  (* Section 1 *)

  Lemma Prop_1_1 : 
    forall x : carrier, 
    (Plus (plus x)) ∩ (Minus (minus x)) == (Empty_set _) == (Plus (minus x)) ∩ (Minus (plus x))
    /\
    (MinusPlus (minus x)) == Intersection (Minus (minus x)) (Minus (plus x)) == (MinusPlus (plus x))
    /\
    (PlusMinus (minus x)) == Intersection (Plus (minus x)) (Plus (plus x))   == (PlusMinus (plus x)).
  Admitted.

  Lemma Prop_1_2 :
    forall (u v x : carrier),
    triangle (Full_set carrier) u v ->
    In (plus x) v ->
    (minus u) ∩ (Plus (minus x)) == Empty_set _.
  Admitted.

  Lemma Prop_1_3 : 
    forall R S : Ensemble carrier, 
      tight R -> well_formed S -> R ⊆ S -> is_a_segment R S. 
  Admitted.

  (* Section 2 *)
  
  Lemma Observation_p322 :
    forall (S T Z : Ensemble carrier),
    well_formed S ->
    S == Union T Z ->
    Disjoint T Z ->
    Perp T Z. 
    Admitted.
  (* Not sure that I got this right *)
    
  (* Section 3 *)

  Record cell : Type :=
  {
    M : Ensemble carrier;
    P : Ensemble carrier;
    cell_non_empty : ~ (M == Empty_set _) /\ ~(P == Empty_set _);
    cell_wf : well_formed M /\ well_formed P;
    cell_finite: Finite M /\ Finite P;
    M_moves : moves_def M M P;
    P_moves : moves_def P M P
  }.

  Definition Big_0 := Ensemble cell.

  Definition is_a_cell (S T : Ensemble _) : Prop :=
    exists R : cell, M R = S /\ P R = T. 

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

(*
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
*)
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

Definition one_preparity : PreParity.
  refine 
  {|
    carrier := True;
    dim True := 0;
    plus True := Empty_set _;
    minus True := Empty_set _
  |}.
  intros. inversion H.
  intros. inversion H.
  intros. constructor.
  intros. constructor.
  intros. inversion H.
  intros. inversion H.
  intros. inversion H.
  intros. constructor; unfold Same_set; constructor; unfold Included; intros; assumption.
Defined.

Definition one : ParityComplex.
  refine 
  {|
    underlying_preparity := one_preparity
  |}.
  admit. admit. admit. admit.
Defined.

