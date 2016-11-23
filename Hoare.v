(** * Hoare: Hoare Logic, Part I *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.


(* ################################################################# *)
(** * Assertions *)


Definition Assertion := heap -> valuation -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall (h : heap) (v : valuation), P h v -> Q h v.

Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ################################################################# *)
(** * Hoare Triples *)

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall (h h' : heap) (v v' : valuation),
     ceval h v c h' v'  ->
     P h v  ->
     Q h' v'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall h v, Q h v) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros.
  apply H.  Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall h v, ~(P h v)) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q c H. unfold hoare_triple.
  intros.
  unfold not in H. apply H in H1.
  inversion H1.  Qed.

(* ################################################################# *)
(** * Proof Rules *)

(* ================================================================= *)
(** ** Assignment *)

(**

      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X ::= a {{Q}}
*)

Definition assn_sub X a P : Assertion :=
  fun (h : heap) (v : valuation) =>
    P h (t_update v X (aeval h v a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H. subst.
  unfold assn_sub in H0. apply H0.  Qed.

(* ================================================================= *)
(** ** Consequence *)

(** 
                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp. unfold hoare_triple.
  intros. apply (Hhoare h h' v v').
  assumption. unfold assert_implies in Himp. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp. unfold hoare_triple.
  intros.
  unfold assert_implies in Himp.
  apply Himp.
  apply (Hhoare h h' v v').
  assumption. assumption. Qed.

(** 
                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  Check hoare_consequence_pre.
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* ================================================================= *)
(** ** Skip *)

(** Since [SKIP] doesn't change the state, it preserves any
    property [P]:

      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  unfold hoare_triple. intros. inversion H. subst.
  assumption.  Qed.

(* ================================================================= *)
(** ** Sequencing *)

(** 
        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;;c2 {{R}}.
Proof.
  unfold hoare_triple. intros.
  inversion H1. subst.
  apply H with h2 v2. try assumption.
  apply H0 with h v. assumption. assumption.
Qed.

(* ================================================================= *)
(** ** Conditionals *)

(** 

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}
 *)

Definition bassn b : Assertion :=
  fun h v => (beval h v b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b h v,
  beval h v b = true -> (bassn b) h v.
Proof.
  intros.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b h v,
  beval h v b = false -> ~ ((bassn b) h v).
Proof.
  intros b h v Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{fun h v => P h v /\ bassn b h v}} c1 {{Q}} ->
  {{fun h v => P h v /\ ~(bassn b h v)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse h h' v v' HE HP.
  inversion HE; subst.
  - (* b is true *)
    unfold hoare_triple in HTrue.
    apply (HTrue h h' v v').
      assumption.
      split. assumption.
             apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse h h' v v').
      assumption.
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(* ----------------------------------------------------------------- *)
(** ** Loops *)

(**

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

    The proposition [P] is called an _invariant_ of the loop.
*)

Lemma hoare_while : forall P b c,
  {{fun h v => P h v /\ bassn b h v}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun h v => P h v /\ ~ (bassn b h v)}}.
Proof.
  intros P b c Hhoare h h' v v' He HP.
  (* Like we've seen before, we need to reason by induction
     on [He], because, in the "keep looping" case, its hypotheses
     talk about the whole loop instead of just [c]. *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileEnd *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileLoop *)
    apply IHHe2. reflexivity.
    unfold hoare_triple in Hhoare.
    apply (Hhoare h1 h2 v1 v2). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(* ================================================================= *)
(** ** Memory write *)

(**

      ------------------------------ (hoare_heap_write)
      {{Q [* x |-> a2]}} [*x] ::= a2 {{Q}}
 *)

Definition heap_sub x a P : Assertion :=
  fun (h : heap) (v : valuation) =>
    P (t_update h x (aeval h v a)) v.

Notation "P '[*' x |-> a ]" := (heap_sub x a P) (at level 10).

Theorem hoare_heap_write : forall Q x a,
  {{Q [* x |-> a]}} ([*x] ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H. subst.
  unfold heap_sub in H0. apply H0.  Qed.


(* ################################################################# *)
(** ** Example Programs *)

(**
      {{P}}
       swap
      {{P'}}
 *)

Module swap_proof.


  Definition J : aexp := ANum 0.
  Definition K : aexp := ANum 1.
  Definition temp : aexp := ANum 2.

  Definition Jid : id := Id 0.
  Definition Kid : id := Id 1.
  Definition tempid : id := Id 2.
  
  Definition swap : com :=
    temp **= ARead J;;
    J **= ARead K;; 
    K **= ARead temp.
         
  Theorem swap_ok : 
    {{ fun h v => (h Jid = 5) /\ (h Kid = 7)  }}
      swap
    {{ fun h v => (h Jid = 7) /\ (h Kid = 5) }}.
  Proof.
    unfold swap.
    eapply hoare_seq.
    - eapply hoare_seq. apply hoare_heap_write. apply hoare_heap_write.
    - apply hoare_heap_write.

  

End swap_proof.
  
(** [] *)

(** $Date: 2016-07-13 12:41:41 -0400 (Wed, 13 Jul 2016) $ *)

