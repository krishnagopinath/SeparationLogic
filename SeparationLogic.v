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
Print valuation.
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
        (h = h1 +++ h2) /\  h1 # h2 /\
        (P h1 v) /\ (Q h2 v).

(* Some notations that will keep us in line with the frap book *)
Notation "'exists' x .. y , p" := (ex_assert (fun x => .. (ex_assert (fun y => p)) ..)) : separation_scope.
Notation " P * Q " := (star P Q) : sep_scope.

Delimit Scope separation_scope with sep.
Local Open Scope separation_scope.

(*Check (exists v, ( * (Id 10) |-> v))%sep.*)

(** ** Redoing Memory write *)

(**

      ------------------------------ (hoare_heap_write)
      {{[*p] |-> v }} [*p] ::= v' {{ [*p] |-> v' }}
 *)

(*
 E_Write : forall (h : heap) (v : valuation) (x : hid) ( a : aexp) (n v' : nat),
      aeval h v a = n ->
      h x = Some v' ->
      ceval h v ( [*x] ::= a) (update h x n) v.

*)

Lemma hoare_heap_write_num : forall (P : hid) (a' : nat),
  {{ (exists a,  ptoa P a)%sep }}
    [*P] ::= ANum a'
  {{ ( ptoa P a') }}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst. simpl.
  destruct H0. unfold ptoa. unfold ptoa in H0. rewrite H0. apply update_shadow.
Qed.
  
Lemma hoare_heap_write_var : forall (P : hid) (i:id) ,
  {{ (exists v, ptoa P v)%sep }}
    [*P] ::= AVar i
  {{ (ptoav P i) }}.
Proof.
  unfold hoare_triple. intros.
  inversion H. subst. simpl.
  destruct H0. unfold ptoav. unfold ptoa in H0. rewrite H0. apply update_shadow.
Qed.
  
  (* 27th November 2016 *)
