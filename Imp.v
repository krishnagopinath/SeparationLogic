(** * Imp: Simple Imperative Programs *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(* Renamed state to valuation for notational convenience *)
Definition valuation := total_map nat.
Definition heap := total_map nat.

Definition empty_valuation : valuation :=
  t_empty 0.

Definition empty_heap : heap :=
  t_empty 0.

Check t_empty.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | AVar :  id -> aexp 
  | ARead : id -> aexp.

Definition A : id := Id 0.
Definition B : id := Id 1.
Definition C : id := Id 2.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** ** Evaluation  *)

(* Renamed st to v for notational convenience *)
Fixpoint aeval (h : heap) (v : valuation) (a : aexp) : nat :=
  match a with
  | ANum x => x                               
  | APlus a1 a2 => (aeval h v a1) + (aeval h v a2)
  | AMinus a1 a2  => (aeval h v a1) - (aeval h v a2)
  | AMult a1 a2 => (aeval h v a1) * (aeval h v a2)
  (** 
   As of now, the below constructors 
   just perform lookup on different structures 
  *)                               
  | AVar x => v x
  | ARead x => h x 
  end.

Fixpoint beval (h : heap) (v : valuation) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval h v a1) (aeval h v a2)
  | BLe a1 a2   => leb (aeval h v a1) (aeval h v a2)
  | BNot b1     => negb (beval h v b1)
  | BAnd b1 b2  => andb (beval h v b1) (beval h v b2)
  end.

Compute  aeval empty_heap (t_update empty_valuation A 5)
        (APlus (ANum 3) (AMult (AVar A) (ANum 2))).


(* ################################################################# *)
(** * Commands *)


Inductive com : Type :=
  | CSkip : com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CVar : id -> aexp -> com
  | CWrite : id -> aexp -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'[*' x ']'  '::=' a" :=
  (CWrite x a) (at level 60).
Notation "x '::=' a" :=
  (CVar x a) (at level 60).

(* ################################################################# *)
(** * Evaluation *)

Inductive ceval : heap -> valuation -> com -> heap -> valuation -> Prop :=
  | E_Skip : forall (h : heap) (v : valuation),
      ceval h v SKIP h v
  | E_Seq : forall (c1 c2 : com) (h1 h2 h3 : heap) (v1 v2 v3 : valuation),
      ceval h1 v1 c1 h2 v2 ->
      ceval h2 v2 c2 h3 v3 ->
      ceval h1 v1 (c1 ;; c2) h3 v3
  | E_IfTrue : forall (h1 h2 : heap) (v1 v2 : valuation) (b : bexp) (c1 c2 : com),
      beval h1 v1 b = true ->
      ceval h1 v1 c1 h2 v2 ->
      ceval h1 v1 (IFB b THEN c1 ELSE c2 FI) h2 v2
  | E_IfFalse : forall (h1 h2 : heap) (v1 v2 : valuation) (b : bexp) (c1 c2 : com),
      beval h1 v1 b = false ->
      ceval h1 v1 c2 h2 v2 ->
      ceval h1 v1 (IFB b THEN c1 ELSE c2 FI) h2 v2
  | E_WhileEnd : forall (h : heap) (v : valuation) (b : bexp) (c : com),
      beval h v b = false ->
      ceval h v (WHILE b DO c END) h v
  | E_WhileLoop : forall (h1 h2 h3 : heap) (v1 v2 v3 : valuation) (b : bexp) (c : com),
      beval h1 v1 b = true ->
      ceval h1 v1 c h2 v2 ->
      ceval h2 v2 (WHILE b DO c END) h3 v3 ->
      ceval h1 v1 (WHILE b DO c END) h3 v3 
  | E_Var  : forall (h : heap) (v : valuation) (a1 : aexp) (n : nat) (x : id),
      aeval h v a1 = n ->
      ceval h v (x ::= a1) h (t_update v x n)
  | E_Write : forall (h : heap) (v : valuation) (x : id) ( a1 : aexp) (n : nat),
      aeval h v a1 = n ->
      ceval h v ( [*x] ::= a1) (t_update h x n) v.




Example ex_cwrite :  ceval empty_heap empty_valuation
                           ( [*A] ::= (APlus (ANum 3) (ANum 12)))
                           (t_update empty_heap A 15) empty_valuation.
Proof.
  simpl. apply E_Write; auto. Qed.

Example ex_complex :
  ceval
    empty_heap empty_valuation
    ([*A] ::= ANum 2;;
     IFB BEq (ARead A) (ANum 2)
       THEN [*B] ::= ANum 3
       ELSE [*C] ::= ANum 4
     FI)     
     (t_update (t_update empty_heap A 2) B 3) empty_valuation.
Proof.
  apply E_Seq with (t_update empty_heap A 2) empty_valuation.
  - constructor; auto.
  - repeat constructor; auto.
Qed.

(** pup_to_n  *)
(** An Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y]. *)
   
Definition pup_to_n : com :=
  [*B] ::= ANum 0;;  
  WHILE (BNot (BEq (ANum 0) (ARead A))) DO
  (
    [*B] ::= APlus (ARead B) (ARead A);;
    [*A] ::= AMinus (ARead A) (ANum 1)
  )
  END.

(* Proof that this program executes as intended for [X] = [2] *)
Theorem pup_to_2_ceval :
  ceval (t_update empty_heap A 2) empty_valuation
  pup_to_n  
  (t_update (t_update (t_update (t_update (t_update (t_update empty_heap A 2) B 0) B 2) A 1) B 3) A 0) empty_valuation.
Proof.
  apply E_Seq with (h2 := (t_update (t_update empty_heap A 2) B 0) ) (v2 := empty_valuation).
  - constructor; auto. 
  - apply E_WhileLoop  with (h2 := (t_update (t_update (t_update (t_update empty_heap A 2) B 0) B 2) A 1))
                           (v2 := empty_valuation).
    + auto.
    + apply E_Seq with (h2 := (t_update (t_update (t_update empty_heap A 2) B 0) B 2))
                         (v2 := empty_valuation); apply E_Write; auto; constructor.
    + apply E_WhileLoop with (h2 :=  (t_update (t_update (t_update (t_update (t_update (t_update empty_heap A 2) B 0) B 2) A 1) B 3) A 0)) (v2 := empty_valuation).
      * auto.
      * apply E_Seq with (h2 := (t_update (t_update (t_update (t_update (t_update empty_heap A 2) B 0) B 2) A 1) B 3)) (v2 := empty_valuation);
        apply E_Write; auto; constructor.
      * apply E_WhileEnd. auto.
Qed.       

    
(** [] *)


(* $Date: 2016-07-18 $ *)

(* TODO Some notational sugar for the map types (I mean, just look at the last proof) *)
(* TODO Find a way to represent heap and valuation as one st object - Its getting tedious*)




