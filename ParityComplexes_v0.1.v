
(** 
    Just including some logic, to get things started.
    In particular, we need exists. Maybe this can be included 
    in a logic module?
**)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(**
    Next, we want to introduce the type of 'Sets' that we're 
    going to use. I've chosen ... to be quite conservative.
**)


(** 
    Below, we define the class of preParity Complexes as a family of Types,
    together with plus and minus relations. 
**)

Class preParity 
      (C : nat -> Type) 
      (pos neg : forall {n : nat}, C (S n) -> C n -> Prop) : Prop := { }.

Generalizable Variables C pos neg.

(** 
    We make the following definitions as given in Ross's paper. In particular,
    subsets are the main structure upon which the theory is framed 

    So far, much of this is Admitted, in place of getting actual details in there.
    We really need to sort out what kind of decidable sets we want.
*)

Class subset `{X : preParity C pos neg} (T : Type): Prop. 

Definition is_empty : Type -> Prop. Admitted.

Definition complement : Type -> Type. Admitted.

Definition setpos `{X : preParity C pos neg} (Y : Type) : Type.  Admitted.
Definition setneg `{X : preParity C pos neg} (Y : Type) : Type.  Admitted.
          
Definition setposneg `{X : preParity C pos neg} (Y : Type) : Type.  Admitted.
Definition setnegpos `{X : preParity C pos neg} (Y : Type) : Type.  Admitted.

Definition el_pos `{X : preParity C pos neg} {n : nat} (x : C (S n)) : Type.  Admitted.
Definition el_neg `{X : preParity C pos neg} {n : nat} (x : C (S n)) : Type.  Admitted.

Definition intersect (A B : Type) : Type. Admitted.
Definition union (A B : Type) : Type. Admitted.

(**
Notation "x ;; y" := (intersect (x) (y)) (at level 50, left associativity) 
                       : sets_scope.

Notation "x ,, y" := (union (x) (y)) (at level 50, left associativity) 
                       : sets_scope.
*)

Definition orth `{X : preParity C pos neg} (S T : Type) : Prop :=
  subset S /\
  subset T /\
  is_empty (union (intersect (setneg S) (setneg T)) (intersect (setpos S) (setpos T))).

Definition orth' `{X : preParity C pos neg} {S : Type} : S -> S -> Prop. Admitted.

Definition well_formed `{X : preParity C pos neg} (S : Type) : Prop :=
  subset S /\
  (* about S_0  /\ *)
  forall x y : S, ~ ( orth' x y ) -> x = y.

(** 
    Let's prove the results contained in Section 2: Movement. These do not
    rely on any of the axioms introduced later. 
*)

Definition el_lt `{X : preParity C pos neg} {n : nat} : C (S n) -> C (S n) -> Prop :=
 (fun (x y : C (S n)) => ~ is_empty (intersect (el_pos x) (el_neg y))).

Inductive rtClose {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  reflAx : forall {a : A}, rtClose R a a
| transAx : forall {a b c : A}, R a b -> rtClose R b c -> rtClose R a c. 


Notation "x << y" := ( rtClose el_lt x y)
(at level 50, left associativity) 
                       : nat_scope .

Notation "x == y" := ( x = y )
(at level 50, left associativity) 
                       : nat_scope .


Class ParityComplex `{X : preParity C pos neg} : Prop := 
{ 
  axiom1  : forall (n : nat) (x : C (S (S n))),
    union (setneg (el_neg x)) (setpos (el_pos x)) == union (setpos (el_neg x)) (setneg (el_pos x)) ;
  axiom2  : forall (n : nat) (x : C (S n)), 
    well_formed (el_neg x) /\ well_formed (el_pos x);
  axiom3a : forall (n : nat) (x y: C (S n)), 
    (x << y) /\ (y << x) -> x = y ;
  axiom3b : forall (n : nat) (x y: C (S n)), 
    (x << y) /\ False 
}.

Proposition Prop_1_1 `{X : preParity C pos neg} : forall (n : nat) (x : C (S (S n))),
  is_empty (intersect (setpos (el_pos x)) (setneg (el_neg x))) /\
  is_empty (intersect (setpos (el_neg x)) (setpos (el_neg x))) /\
  intersect (setneg (el_neg x)) (setneg (el_pos x)) == setnegpos (el_neg x) /\
  intersect (setneg (el_neg x)) (setneg (el_pos x)) == setnegpos (el_pos x) /\
  intersect (setneg (el_neg x)) (setneg (el_pos x)) == setposneg (el_neg x) /\
  intersect (setpos (el_neg x)) (setpos (el_pos x)) == setposneg (el_pos x) .
Admitted.

Proposition Prop_1_2 `{X : preParity C pos neg} : 
   forall (n : nat) (x : C (S (S n))) (u v : C (S n)),
   (u << v) /\ (pos (S n) x v) -> is_empty (intersect (el_neg u) (setpos (el_neg x))).
Admitted.

(** Proposition Prop_1_3 `{X : preParity C pos neg} : ?? . 
Admitted.
**)

Definition moves `{X : preParity C pos neg} (T M P: Type) : Prop := 
 ( P == intersect (union M (setpos T)) (complement (setneg T)) ) /\  
 ( M == intersect (union P (setneg T)) (complement (setpos T)) ) .

Proposition Prop_2_1 `{X : preParity C pos neg} :
   forall (T M : Type), exists (P : Type), 
   moves T M P   <->   (setnegpos T = M) /\ is_empty (intersect M (setpos T)).
Admitted.

Proposition Prop_2_2 `{X : preParity C pos neg} :
   forall (T A B X: Type),
   (moves T A B) /\ (X = A) /\ is_empty (intersect (setnegpos T) X) ->
   forall (Y : Type),
   is_empty (intersect Y (setneg T)) /\ is_empty (intersect Y (setpos T)) -> 
   (moves T (intersect (union A Y) (complement X)) (intersect (union B Y) (complement X))).
Admitted.

 


