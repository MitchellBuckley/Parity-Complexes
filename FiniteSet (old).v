Inductive finSet : nat -> Type :=
  fZero : forall {n : nat}, finSet (S n)
| fSucc : forall {n : nat}, finSet (S n) -> finSet (S (S n)).


Check (@fZero 0).
Check fSucc (fSucc (@fZero 0)).

Inductive finList {A : Type} : nat -> Type :=
  fNil : forall {n : nat}, @finList A 0
| fCons : forall {n : nat}, A -> @finList A n -> @finList A (S n).

Check (fCons 1 fNil).

Definition power (A : Type) : Type := A -> Prop.

Class preParity 
      (C : nat -> Type) 
      (plus minus : forall {n : nat}, C (S n) -> power (C n)) : Prop := {}.

Inductive rtClose {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  reflAx : forall {a : A}, rtClose R a a
| transAx : forall {a b c : A}, R a b -> rtClose R b c -> rtClose R a c. 

Lemma test : forall (A : Type) (R : A -> A -> Prop) (a b : A), R a b -> rtClose R a b.
intros A R a b H.
exact (transAx R H (reflAx R)).
Qed.

 


