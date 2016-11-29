Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.

(* Some house-keeping *)

(* Redoing the definition for heap because we need some error checking on it *)
Definition heap := partial_map nat.
Definition empty_heap : heap := empty.

Check valuation.

(* The mixed embedding object language *)

(* 
   [res] gives the type of the value computed by [cmd] i.e, 
   
   cmd nat := heap -> (heap, (result of [cmd] of type [nat])).

*)

(* Needed for [Loop] *)
Inductive looper a :=
| Done (i : a)
| Again (i : a).


Inductive cmd : Set -> Type :=
| Return {res : Set}  : res -> cmd res
(* Bind passes in the result of the command, [res'] as an argument to the the second [cmd], (the thing that comes up after [;])  *)                                   
| Bind { res res' : Set} : cmd res' -> (res' -> cmd res) -> cmd res
| Read : id -> cmd nat
(* I guess, [cmd unit] would indicate that the type that [cmd] computes is nothing, as this is a [Write] op *)
| Write : id -> nat -> cmd unit
(* Takes in the number of indices to allocate in the heap as a [nat] *)
| Alloc : (* number of contiguous memory spaces, 'n'*) nat -> cmd nat
| Free : (* start, 'a' *) nat -> (* end, 'n' *) nat -> cmd unit
(* [looper] checks if this the current condition of the loop is [Done] or [Again] *)
| Loop {a : Set} : a -> (a -> cmd (looper a)) -> cmd a.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).

(* Small step semantics *)

Fixpoint allocate (h : heap) (a n : nat) : heap  :=
  match n with
  | 0 => h
  | S n' => allocate (update h (Id (a + n')) 0) a n'
  end.

Notation "h '[' a '|->' 'O(' n ')'  ']'" := (allocate h a n) (right associativity, at level 80).

Fixpoint deallocate (h: heap) (a n : nat) : heap :=
  match n with
  | 0 => h
  | S n' => deallocate (remove h (Id a)) (a+1) n'
  end.

Notation "h -- '[' a ',' 'a' '+' n ')' " := (deallocate h a n) (right associativity, at level 80). 

Inductive interp : forall {X : Set}, heap * cmd X -> heap * cmd X -> Prop  :=
| BindStep : forall (res res' : Set) (c1 c1' : cmd res') (c2 : res' -> cmd res) (h h' : heap),
    interp (h, c1) (h', c1') -> interp (h,  x <- c1; (c2 x)) (h', x <-c1'; (c2 x))
| BindDone : forall (res res' : Set) (v : res') (c : res' -> cmd res)  (h : heap),
    interp (h, (x <- Return v; c x)) (h, c v)
| ReadStep : forall (a : id) (h : heap) (v : nat),
    h a = Some v -> interp (h, Read a) (h, Return v)
| WriteStep : forall (a : id) (h h' : heap) (v : nat) (u : unit),
    (* https://coq.inria.fr/library/Coq.Init.Datatypes.html  *)
    interp (h, Write a v) (h', Return u)
| LoopStep : forall (acc : Set) (h : heap) (i : acc) (c : acc -> cmd (looper acc)),
    interp (h, Loop i c) (h, x <- (c i); match x with
                                         | Done _ a => Return a
                                         | Again _ a => Loop a c
                                         end)
| AllocStep : forall (n a : nat) (h : heap),
    (* make sure the range of allocated pieces stays between [a, a + n) *)
    (forall i, i < n ->
               (* if it does, make sure that those (a+n) adresses are unmapped *)
               h (Id (a + i)) = None) ->
    interp (h, Alloc n) (h[a |-> O(n)], Return a)
| FreeStep : forall (n a : nat) (h : heap) (u : unit),
    interp (h, Free a n) (h -- [a , a + n), Return u).


(* 27th November 2016 *)