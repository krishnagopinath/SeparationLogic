Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.
Require Import Hoare.
Require Import Coq.Logic.FunctionalExtensionality.


(* The formula emp accepts only the empty heap *)
Definition emp : Assertion :=
  fun (h : heap) (_: valuation) => h = empty_heap. 

(* formula p -> a accepts only the heap whose only address is p, mapped to (nat a) *)
Definition ptoa (p : hid) (a : nat) : Assertion :=
  fun (h : heap) (v : valuation) =>
    h = (update empty_heap p a).

(* formula p -> a accepts only the heap whose only address is p, mapped to (id a) *)
Definition ptoav (p : hid) (a : id) : Assertion :=
  fun (h : heap) (v : valuation) =>
    h = (update empty_heap p (v a)).

(* Creating an existential quantifier that works for Assertions instead of Props.
 * Ripping off a lot of stuff from First-order quantifiers section of : 
 * https://coq.inria.fr/library/Coq.Init.Logic.html *)
Definition ex_assert {A:Type} (P : A -> Assertion) : Assertion :=
  fun h v => exists x, (P x) h v. 

(* definition of star *)
Definition star (P Q : Assertion) : Assertion :=
  fun (h : heap) (v : valuation) =>
    exists h1, exists h2,
        (* heap can be split into pieces /\ the split pieces are disjoint *) 
        (h = merge h1 h2) /\  (disjoint h1 h2) /\
        (P h1 v) /\ (Q h2 v).

(* Some notations that will keep us in line with the frap book *)
Notation "'exists' x .. y , p" := (ex_assert (fun x => .. (ex_assert (fun y => p)) ..)) : separation_scope.

Delimit Scope separation_scope with sep.
Local Open Scope separation_scope.

(*Check (exists v, ( * (Id 10) |-> v))%sep.*)

(** ** Redoing Memory write *)

(**

      ------------------------------ (hoare_heap_write)
      {{[*p] |-> v }} [*p] ::= v' {{ [*p] |-> v' }}
 *)

Lemma hoare_heap_write_num : forall (p : hid) (a' : nat),
  {{ (exists a,  ptoa p a)%sep }}
    [*p] ::= ANum a'
  {{ ( ptoa p a') }}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst. simpl.
  destruct H0. unfold ptoa. unfold ptoa in H0. rewrite H0. apply update_shadow.
Qed.
  
Lemma hoare_heap_write_var : forall (p : hid) (i:id) ,
  {{ (exists v, ptoa p v)%sep }}
    [*p] ::= AVar i
  {{ (ptoav p i) }}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst. simpl.
  destruct H0. unfold ptoav. unfold ptoa in H0. rewrite H0. apply update_shadow.
Qed.


(** ** Heap Memory Allocation *)

(**

      ------------------------------ (hoare_heap_alloc)
      {{emp}} (a ::= Alloc n) {{ 0^n  }}
 *)

Check ptoa (Id 1) 0.

Fixpoint mptoa (a : hid) (n : nat) : Assertion :=
  match n with
  | 0 => emp
  | S n' => star (ptoa (id_add a n')  0) (mptoa a n') 
  end. 


(* 
 E_Allocate : forall (h : heap) (v : valuation) (a : hid)  (n : nat),
      (forall (i : nat),  i < n -> h (id_add a i) = None) ->
      ceval h v ( a ::= Alloc n) (allocate h a n)  v

 *)

Lemma merge_allocate : forall m1 m2 a n,
  merge m1 (allocate m2 a n) = allocate (merge m1 m2) a n.
Proof.
  intros.
  induction n.
  - simpl. reflexivity.
  - Admitted.


Lemma hoare_heap_alloc : forall (p : hid) (n :nat),
  {{emp}}
   p ::= Alloc n 
  {{mptoa p n}}.
Proof.
  unfold hoare_triple.
  intros p n h h' v v' H HEmp.
  inversion H. subst. rewrite HEmp.
  induction n as [ | n' IHn' ]. 
  { simpl. reflexivity. }
  { simpl. unfold star.
    exists (update (empty_heap) p 0), (allocate empty_heap (id_add p 1) n'). 
    split. 
     { simpl. rewrite merge_allocate. reflexivity. }
   split.
     { unfold disjoint. intros a [Hh1 Hh2].
       destruct Hh1. 
       rewrite update_neq.
       - reflexivity.
       - Admitted.
         
       
    
    
    

      
    
      
      
    (* find out what h1 and h2 are *)
    (* apply IHn' *)

(* Heap memory free *)

(* Check if all the pointers in memory region point to SOME value  *)
(*
Fixpoint allocated (p : hid) (n : nat)  : Assertion :=
  match n with
  | 0 => emp
  | S n' => star (exists (v : nat), ptoa (id_add p  v)%sep  (allocated (id_add p 1) n')
  end.
  
Lemma hoare_heap_free : forall (p : hid) (n : nat),
  {{ allocated p n }}
    Free (p, n)
  {{ emp }}.
Proof.
  unfold hoare_triple.
  intros p n h h' v v' HEval HAlloc.
  inversion HEval. subst.
  unfold emp.
  induction n as [ | n' IHn'].
  - simpl. simpl in HAlloc. unfold emp in HAlloc. assumption.
  - simpl. simpl in HAlloc. unfold star in HAlloc.
    destruct HAlloc as [ h1 [h2 [HMerge [HDisjoint [HPtoa HAllocated]]]] ].
    
*)  
    
     
  (* 27th November 2016 *)
