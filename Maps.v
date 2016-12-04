(** * Maps: Total and Partial Maps *)

(* TODO : Reprove some partial_map Lemmas *) 

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive id : Type :=
| Id : nat -> id.

Definition id_add (a : id) (b : nat) : id :=
  match a, b with
  | Id n, n' => Id (n + n')
  end.

Definition beq_id id1 id2 :=
  match id1,id2 with
    | Id n1, Id n2 => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall id, true = beq_id id id.
Proof.
  intros [n]. simpl. rewrite <- beq_nat_refl.
  reflexivity. Qed.

Theorem beq_id_true_iff : forall id1 id2 : id,
  beq_id id1 id2 = true <-> id1 = id2.
Proof.
   intros [n1] [n2].
   unfold beq_id.
   rewrite beq_nat_true_iff.
   split.
   - (* -> *) intros H. rewrite H. reflexivity.
   - (* <- *) intros H. inversion H. reflexivity.
Qed.


Theorem beq_id_false_iff : forall x y : id,
  beq_id x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_id_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.


Theorem false_beq_id : forall x y : id,
   x <> y
   -> beq_id x y = false.
Proof.
  intros x y. rewrite beq_id_false_iff.
  intros H. apply H. Qed.

(* ################################################################# *)
(** * Total Maps *)

Definition total_map (A:Type) := id -> A.


Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : id) (v : A) :=
  fun x' => if beq_id x x' then v else m x'.

Definition t_remove {A:Type} (m : total_map A) (def : A) (key : id) : total_map A :=
  fun key' => if beq_id key key' then def else m key'.

Lemma t_update_eq : forall A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  intros. unfold t_update. rewrite <-beq_id_refl. reflexivity. Qed.

Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (t_update m x1 v) x2 = m x2.
Proof. Admitted.

Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof. Admitted.

Lemma beq_idP : forall x y, reflect (x = y) (beq_id x y).
Proof. Admitted.


Theorem t_update_same : forall X x (m : total_map X),
  t_update m x (m x) = m.
Proof. Admitted.

Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof. Admitted.

Lemma t_apply_empty:  forall A x v, @t_empty A v x = v.
Proof. Admitted.

(* ################################################################# *)
(** * Partial maps *)

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  fun _ => None. 

Definition update {A:Type} (m : partial_map A)
                  (key : id) (v : A) :=
  fun key' => if beq_id key key' then Some v else m key'.

Definition lookup {A:Type} (m : partial_map A)
           (key : id) := m key.

Definition remove {A:Type} (m : partial_map A) (key : id) : partial_map A :=
  fun key' => if beq_id key key' then None else m key'.

Definition merge {A:Type} (m1 m2 : partial_map A) : partial_map A :=
  fun key => match (m1 key) with
             | None => m2 key
             | v => v
             end.

Definition disjoint {A: Type} (m1 m2 : partial_map A) : Prop :=
  (* dom(m1) and dom(m2) = null. *) 
  (* If m1 and m2 give out values for the same Id, then the heaps are NOT disjoint *)
  forall (a : id),  (m1 a <> None) /\ (m2 a <> None) -> False.

Notation "m1 '+++' m2" := (merge m1 m2) (at level 69).
Notation "m1 '#' m2" := (disjoint m1 m2) (at level 79).

                            
Lemma apply_empty : forall A x, @empty A x = None.
Proof. Admitted.

Lemma update_eq : forall A (m: partial_map A) x v,
  (update m x v) x = Some v.
Proof. Admitted.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
Proof. Admitted.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.
Proof. Admitted.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  update m x v = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.


