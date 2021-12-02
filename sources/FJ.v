Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.


From RecordUpdate Require Export RecordSet.
Export RecordSetNotations.

Definition FJ : string := "Featherweight Java".
Definition GJ : string := "Generic Java".
Definition FGJ : string := "Featherweight GJ".

(**
  Driver for Modeling Object Oriented and Featherweight Java concepts
*)

(** The Records structure is particularly useful in modeling Object-Oriented Concepts*)

Set Printing Projections.


Record Pair {A : Type} {B : Type} : Type := mkPair {
  fst : A;
  snd : B
}.

Record Ctr := mkCtr {
  key : string;
  count : nat
}.

(* We can model sub-classing by creating Record Instance (We also handle Generics for GJ in a similar fashion). *)
Check (mkPair nat nat).
Check (mkPair nat nat 3 2).

Example PairInstance := mkPair nat nat 3 2.


Compute PairInstance.(fst).


Definition PairCtr (a : string) (b : nat) := 
{|  fst := a;
    snd := b |}.

(** 
    Coq does not provide built-in update functionality for Record fields. 
    We explore a third-party library which achieves the same.
*)

Instance ModifiableCtrInstance : Settable _ := settable! mkCtr <key; count>.
Definition updateKey record k : Ctr := record <| key := k |>.
Definition updateCount record v : Ctr := record <| count := v |>.
Definition updateKeyCount record k v: Ctr := record <| key := k |> <| count := v |>.


Definition PairOfA {A} (a : A) (b : A) := 
mkPair A A a b.

Check @PairOfA.	 
Compute PairOfA 3 2.
Compute snd(PairCtr "key" 1) <> 1.  

(** Modeling FJ concepts in Coq **)
(*
   Below snippets implement the main goals provided by FJ's core calculus.
*)

Module FJ_Module.
(** Modeling Syntax *)

(*
    Deriving from the whitepaper ==>
    A, B, C, D, E => Class Names
    f, g => Field Names
    m => Method Names
    x => Variables
    d, e => Expressions
    L => Class Declarations
    K => Constructor Declarations
    M => Method Declarations
    
    'this' is implicitly Bound to every Method Declaration
    f' => Possibly empty sequence f1, ... , fn
    Similarly for C', x', e' etc.
    M' => M1...Mn
    Empty Sequence => '()'
    
*)

Definition C : string := "C".
Definition C' : string := "C'".
Definition f : string := "f".
Definition f' : string := "f'".
Definition K : string := "K".
Definition M : string := "M".
Definition M' : string := "M'".
Definition x : string := "x".


Hint Unfold C : core.
Hint Unfold C' : core.
Hint Unfold f : core.
Hint Unfold f' : core.
Hint Unfold K : core.
Hint Unfold M : core.
Hint Unfold M' : core.
Hint Unfold x : core. 

(** ** Types *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Concat : ty -> ty -> ty.


(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_type : ty -> tm
  | tm_var   : string -> tm
  | tm_method : tm -> tm
  | tm_concat : tm -> tm -> tm
  | tm_concat1 : ty -> tm -> tm
  | tm_concat2 : tm -> ty -> tm
  | tm_cast : ty -> tm -> tm
  | tm_multi : tm -> tm -> tm
  | tm_new : ty -> tm -> tm
  | tm_mtype : tm -> ty -> tm
  | tm_mbody : string -> string -> tm
  | tm_fields : ty -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm.

Coercion tm_type : ty >-> tm.
Coercion tm_var : string >-> tm.


Declare Custom Entry fj.



Reserved Notation "A '<:' B" (at level 40).
Notation "'mtype' '(' A ',' B ')'" := (tm_mtype A B).
Notation "A '==>' B" := (tm_mtype A B).
Notation "'mbody '(' m ',' A ')'" := (tm_mbody m A).
Notation "'fields{' C '}'" := (tm_fields C).
Notation "'m{' x '}'" := (tm_method x) (at level 40).
Notation "C '\./' D" := (tm_concat C D) (at level 40).
Notation "C ';' D" := (tm_multi C D) (at level 40).
Notation "C '\.' D" := (tm_concat1 C D) (at level 40).
Notation "C './' D" := (tm_concat2 C D) (at level 40).
Notation "{ C }? e" := (tm_cast C e) (at level 40).
Notation "( x )" := x (x at level 99).


(* Sub-Typing Rules *)
Inductive subclass : tm -> tm -> Prop :=
  | ST_Generic : forall (C : ty) (D : ty), C <: D
  | ST_Transitive : forall (C : ty) (D : ty) (E : ty), 
                C <: D ->
                D <: E ->
                C <: E
where "C '<:' D" := (subclass C D).


Reserved Notation "'class' C 'extends' D ';;' comm" (at level 40, C at next level, D at next level, comm at next level). 

Inductive tm_class : tm -> tm -> tm -> Prop :=
  | TM_Derived : forall C D comm, 
                  C <: D ->
                  class C extends D ;; comm
where "'class' C 'extends' D ';;' comm" := (tm_class C D comm).


Reserved Notation "C '\in/' D" (at level 40).
Inductive tm_inclusion : tm -> tm -> Prop :=
  | Generic_Inc: forall C D, C \in/ D
where "C '\in/' D" := (tm_inclusion C D).



Definition context := partial_map ty.

Reserved Notation "Gamma '|-' x ':' X"  (at level 40, x at next level, X at level 0).


(** Expression Typing in FJ*)
Inductive exp_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x X,
      Gamma x = Some X ->
      Gamma |- x : X
  | T_Field : forall Gamma (e0 : tm) (C0 : ty) (C' : ty) f',
      Gamma |- e0 : C0 ->
      fields{C0} =  (C'\.f') ->
      Gamma |- (e0 \./ f) : C'
  | T_Invk : forall Gamma m C C0 C' e' D' e0,
             e0 \in/ e' ->
             Gamma |- e0 : C0 ->
             mtype(m,C0) = (D' ==> C) ->
             Gamma |- e' : C' ->
             C' <: D' ->
             Gamma |- (e0 \./ m{e'}) : C
  | T_New : forall Gamma (C : ty) (C' : ty) (D' : ty) (e : tm) (f' : tm),
            fields{C} = ( D'\.f') ->
            Gamma |- e : C' ->
            C' <: D' ->
            Gamma |- tm_new C e : C
  | T_UCast : forall Gamma (C : ty) D e0,
                Gamma |- e0 : D ->
                D <: C ->
                Gamma |- ({ C }? e0) : C
  | T_DCast : forall Gamma (C : ty) ( D : ty) e0,
                Gamma |- e0 : D ->
                C <: D ->
                C <> D ->
                Gamma |- ({ C }? e0) : C
  | T_SCast : forall Gamma (C : ty) ( D : ty) e0,
                Gamma |- e0 : D ->
                ~(C <: D) ->
                ~(D <: C) ->
                Gamma |- ({ C }? e0) : C
where "Gamma '|-' x ':' X" := (exp_type Gamma x X).

Reserved Notation "t '-->' t'" (at level 40).

(** Reduction Rules*)
Inductive reduction : tm -> tm -> Prop :=
(* Computation *)
  | R_Field : forall  (C : ty) (C' : ty) (f' : tm) (fi : tm) (ei : tm) (e' : tm),
              fields{C} = (C'\.f') ->
              ei \in/ e' ->
              fi \in/ f' ->
              (tm_new C e') \./ fi --> ei
  | R_Cast : forall (C : ty) (D : ty) (e' : tm),
             C <: D ->
             ({D}? (tm_new C e')) --> (tm_new C e')
(* Congruence *)
  | RC_Field : forall e0 e0' f,
               e0 --> e0' ->
               (e0 \./ f) --> (e0' \./ f)
  | RC_Invk_Recv : forall e0 e0' e',
                   e0 --> e0' ->
                  (e0 \./ m{e'}) --> (e0' \./ m{e'})
  | RC_Invk_Arg : forall e0 ei ei',
                   ei --> ei' ->
                  (e0 \./ m{ei}) --> (e0 \./ m{ei'})
  | RC_New_Arg  : forall C ei ei',
                   ei --> ei' ->
                  tm_new C ei --> tm_new C ei'
  | RC_Cast : forall C e0 e0',
              e0 --> e0' ->
              ({ C }? e0) --> ({ C }? e0')
where "t '-->' t'" := (reduction t t').

Check @multi.

Notation multireduction := (multi reduction).
Notation "t1 '-->*' t2" := (multireduction t1 t2) (at level 40).

Theorem subject_reduction : forall Gamma e e' C (C' : ty),
  Gamma |- e : C ->
  e --> e' ->
  C' <: C ->
  Gamma |- e' : C'.
Proof.
Admitted.


Theorem progress : forall Gamma e C C0 e' C' f f',
  Gamma |- e : C ->
  e \in/ e' ->
  ({ C0 }? e' \./ f ) \in/ e ->
  (fields{C0} =  (C'\.f')) /\ (f \in/ f').
Proof.
Admitted. 


Theorem type_soundness : forall e e' e'' C D v,
    empty |- e : C ->
    e -->* e' ->
    empty |- v : D ->
    ((e' = v) /\ (D <: C)) \/ ( (D <: C) /\ (e' = { D }? (tm_new C e''))).
Proof.
Admitted.

Definition cast_safe (Gamma : context) (e : tm) (C : ty) (e_cast : tm):= forall Gamma e C e_cast, 
                          Gamma |- e : C ->
                          (e_cast = ({ C }? e)).

Theorem cast_safety_preservation_on_reduction : forall Gamma e e' C e_cast e_cast',
    cast_safe Gamma e C e_cast ->
    e --> e'->
    cast_safe Gamma e' C e_cast'.
Proof.
Admitted.

Theorem cast_safe_progress : forall Gamma e e' C e_cast,
    cast_safe Gamma e C e_cast ->
    e \in/ e' ->
    {C}? (tm_new C e') \in/ e.
Proof.
Admitted.

End FJ_Module.