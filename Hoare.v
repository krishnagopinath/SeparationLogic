(** * Hoare: Hoare Logic, Part I *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Imp.
Require Import Maps.


(* ################################################################# *)
(** * Assertions *)


Definition Assertion := heap -> valuation -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall (h h' : heap) (v v' : valuation), P h v -> Q h' v'.

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
     ceval c h v h' v'  ->
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
    P h (t_update v X (aeval v h a)).

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  inversion H. subst.
  unfold assn_sub in H0. apply H0.  Qed.

(** Here's a first formal proof using this rule. *)

Example assn_sub_example :
  {{(fun h v => v X = 3) [X |-> ANum 3]}}
  (X ::= (ANum 3))
  {{fun h v => v X = 3}}.
Proof.
  apply hoare_asgn.  Qed.

Example assn_sub_ex1 :
  {{(fun h v =>  v X <= 5) [X |-> APlus (AId X) (ANum 1)] }}
     (X ::= APlus (AId X) (ANum 1))
     {{(fun h v =>  v X <= 5 )}}.
Proof.
  apply hoare_asgn. Qed.

Example assn_sub_ex2 :
  {{(fun h v =>  (0 <= v X /\ v X <= 5)) [X |-> ANum 3]}}
  X ::= ANum 3
  {{ (fun h v => (0 <= v X /\ v X <= 5)) }}.
Proof.
  apply hoare_asgn. Qed.
  

(* ================================================================= *)
(** ** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need.
    For instance, while

      {{(X = 3) [X |-> 3]}} X ::= 3 {{X = 3}},

    follows directly from the assignment rule,

      {{True}} X ::= 3 {{X = 3}}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    equivalent, so if one triple is valid, then the other must
    certainly be as well.  We can capture this observation with the
    following rule:

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}

    Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.

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
  intros P P' Q c Hhoare Himp.
  intros st st' Hc HP. apply (Hhoare st st').
  assumption. apply Himp. assumption. Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  intros st st' Hc HP.
  apply Himp.
  apply (Hhoare st st').
  assumption. assumption. Qed.

(** For example, we can use the first consequence rule like this:

                {{ True }} ->>
                {{ 1 = 1 }}
    X ::= 1
                {{ X = 1 }}

    Or, formally... *)

Example hoare_asgn_example1 :
  {{fun st => True}} (X ::= (ANum 1)) {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre
    with (P' := (fun st => st X = 1) [X |-> ANum 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. reflexivity.
Qed.

(** Finally, for convenience in some proofs, we can state a combined
    rule of consequence that allows us to vary both the precondition
    and the postcondition at the same time.

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
  apply hoare_consequence_pre with (P' := P').
  apply hoare_consequence_post with (Q' := Q').
  assumption. assumption. assumption.  Qed.

(* ================================================================= *)
(** ** Digression: The [eapply] Tactic *)

(** This is a good moment to introduce another convenient feature of
    Coq.  We had to write "[with (P' := ...)]" explicitly in the proof
    of [hoare_asgn_example1] and [hoare_consequence] above, to make
    sure that all of the metavariables in the premises to the
    [hoare_consequence_pre] rule would be set to specific
    values.  (Since [P'] doesn't appear in the conclusion of
    [hoare_consequence_pre], the process of unifying the conclusion
    with the current goal doesn't constrain [P'] to a specific
    assertion.)

    This is annoying, both because the assertion is a bit long and
    also because, in [hoare_asgn_example1], the very next thing we are
    going to do -- applying the [hoare_asgn] rule -- will tell us
    exactly what it should be!  We can use [eapply] instead of [apply]
    to tell Coq, essentially, "Be patient: The missing part is going
    to be filled in later in the proof." *)

Example hoare_asgn_example1' :
  {{fun st => True}}
  (X ::= (ANum 1))
  {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.  reflexivity.  Qed.

(** In general, [eapply H] tactic works just like [apply H] except
    that, instead of failing if unifying the goal with the conclusion
    of [H] does not determine how to instantiate all of the variables
    appearing in the premises of [H], [eapply H] will replace these
    variables with _existential variables_ (written [?nnn]), which
    function as placeholders for expressions that will be
    determined (by further unification) later in the proof. *)

(** In order for [Qed] to succeed, all existential variables need to
    be determined by the end of the proof. Otherwise Coq
    will (rightly) refuse to accept the proof. Remember that the Coq
    tactics build proof objects, and proof objects containing
    existential variables are not complete. *)

Lemma silly1 : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. apply HP.

(** Coq gives a warning after [apply HP].  (The warnings look
    different between Coq 8.4 and Coq 8.5.  In 8.4, the warning says
    "No more subgoals but non-instantiated existential variables."  In
    8.5, it says "All the remaining goals are on the shelf," meaning
    that we've finished all our top-level proof obligations but along
    the way we've put some aside to be done later, and we have not
    finished those.)  Trying to close the proof with [Qed] gives an
    error. *)

Abort.

(** An additional constraint is that existential variables cannot be
    instantiated with terms containing ordinary variables that did not
    exist at the time the existential variable was created.  (The
    reason for this technical restriction is that allowing such
    instantiation would lead to inconsistency of Coq's logic.) *)

Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. eapply HQ. destruct HP as [y HP'].

(** Doing [apply HP'] above fails with the following error:

     Error: Impossible to unify "?175" with "y".

    In this case there is an easy fix: doing [destruct HP] _before_
    doing [eapply HQ]. *)

Abort.

Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP'].
  eapply HQ. apply HP'.
Qed.

(** The [apply HP'] in the last step unifies the existential variable
    in the goal with the variable [y].

    Note that the [assumption] tactic doesn't work in this case, since
    it cannot handle existential variables.  However, Coq also
    provides an [eassumption] tactic that solves the goal if one of
    the premises matches the goal up to instantiations of existential
    variables. We can use it instead of [apply HP'] if we like. *)

Lemma silly2_eassumption : forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP']. eapply HQ. eassumption.
Qed.

(** **** Exercise: 2 stars (hoare_asgn_examples_2)  *)
(** Translate these informal Hoare triples...

       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}

   ...into formal statements (name them [assn_sub_ex1'] and 
   [assn_sub_ex2']) and use [hoare_asgn] and [hoare_consequence_pre] 
   to prove them. *)

(* FILL IN HERE *)
(** [] *)

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
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ================================================================= *)
(** ** Sequencing *)

(** More interestingly, if the command [c1] takes any state where
    [P] holds to a state where [Q] holds, and if [c2] takes any
    state where [Q] holds to one where [R] holds, then doing [c1]
    followed by [c2] will take any state where [P] holds to one
    where [R] holds:

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
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

      {{ a = n }}
    X ::= a;;
      {{ X = n }}    <---- decoration for Q
    SKIP
      {{ X = n }}
*)

(** Here's an example of a program involving both assignment and
    sequencing. *)

Example hoare_asgn_example3 : forall a n,
  {{fun st => aeval st a = n}}
  (X ::= a;; SKIP)
  {{fun st => st X = n}}.
Proof.
  intros a n. eapply hoare_seq.
  - (* right part of seq *)
    apply hoare_skip.
  - (* left part of seq *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. subst. reflexivity. 
Qed.

(** We typically use [hoare_seq] in conjunction with
    [hoare_consequence_pre] and the [eapply] tactic, as in this
    example. *)

(** **** Exercise: 2 stars (hoare_asgn_example4)  *)
(** Translate this "decorated program" into a formal proof:

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2))
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (swap_exercise)  *)
(** Write an Imp program [c] that swaps the values of [X] and [Y] and
    show that it satisfies the following specification:

      {{X <= Y}} c {{Y <= X}}
*)

Definition swap_program : com 
  (* REPLACE THIS LINE WITH   := _your_definition_ . *) . Admitted.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
  swap_program
  {{fun st => st Y <= st X}}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (hoarestate1)  *)
(** Explain why the following proposition can't be proven:

      forall (a : aexp) (n : nat),
         {{fun st => aeval st a = n}}
         (X ::= (ANum 3);; Y ::= a)
         {{fun st => st Y = n}}.
*)

(* FILL IN HERE *)
(** [] *)

(* ================================================================= *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?  

    Certainly, if the same assertion [Q] holds after executing 
    either of the branches, then it holds after the whole conditional.  
    So we might be tempted to write:

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      --------------------------------
      {{P}} IFB b THEN c1 ELSE c2 {{Q}}

   However, this is rather weak. For example, using this rule,
   we cannot show 

     {{ True }}
     IFB X == 0
     THEN Y ::= 2
     ELSE Y ::= X + 1
     FI
     {{ X <= Y }}

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]). *)
(**

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}
*)

(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** A couple of useful facts about [bassn]: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  - (* b is true *)
    apply (HTrue st st').
      assumption.
      split. assumption.
             apply bexp_eval_true. assumption.
  - (* b is false *)
    apply (HFalse st st').
      assumption.
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(* ----------------------------------------------------------------- *)
(** *** Example *)

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example :
    {{fun st => True}}
  IFB (BEq (AId X) (ANum 0))
    THEN (Y ::= (ANum 2))
    ELSE (Y ::= APlus (AId X) (ANum 1))
  FI
    {{fun st => st X <= st Y}}.
Proof.
  (* WORKED IN CLASS *)
  apply hoare_if.
  - (* Then *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros st [_ H].
    apply beq_nat_true in H.
    rewrite H. omega.
  - (* Else *)
    eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub, t_update, assert_implies.
    simpl; intros st _. omega.
Qed.

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  (* FILL IN HERE *) Admitted.

(* ----------------------------------------------------------------- *)
(** *** Exercise: One-sided conditionals *)

(** **** Exercise: 4 stars (if1_hoare)  *)

(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [IF1 b THEN c FI]. Here [b] is a
    boolean expression, and [c] is a command. If [b] evaluates to
    [true], then command [c] is evaluated. If [b] evaluates to
    [false], then [IF1 b THEN c FI] does nothing.

    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)

(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity).

(** Next we need to extend the evaluation relation to accommodate
    [IF1] branches.  This is for you to do... What rule(s) need to be
    added to [ceval] to evaluate one-sided conditionals? *)

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st \\ st' ->
                  (WHILE b1 DO c1 END) / st' \\ st'' ->
                  (WHILE b1 DO c1 END) / st \\ st''
(* FILL IN HERE *)

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** Now we repeat (verbatim) the definition and notation of Hoare triples. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st \\ st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

(** Finally, we (i.e., you) need to state and prove a theorem,
    [hoare_if1], that expresses an appropriate Hoare logic proof rule
    for one-sided conditionals. Try to come up with a rule that is
    both sound and as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, prove formally [hoare_if1_good] that your rule is
    precise enough to show the following valid Hoare triple:

  {{ X + Y = Z }}
  IF1 Y <> 0 THEN
    X ::= X + Y
  FI
  {{ X = Z }}
*)

(** Hint: Your proof of this triple may need to use the other proof
    rules also. Because we're working in a separate module, you'll
    need to copy here the rules you find necessary. *)

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st => st X = st Z }}.
Proof. (* FILL IN HERE *) Admitted.

End If1.
(** [] *)

(* ================================================================= *)
(** ** Loops *)

(** Finally, we need a rule for reasoning about while loops. *)

(** Suppose we have a loop

      WHILE b DO c END

    and we want to find a pre-condition [P] and a post-condition
    [Q] such that

      {{P}} WHILE b DO c END {{Q}}

    is a valid triple. *)

(** First of all, let's think about the case where [b] is false at the
    beginning -- i.e., let's assume that the loop body never executes
    at all.  In this case, the loop behaves like [SKIP], so we might
    be tempted to write: *)

(**

      {{P}} WHILE b DO c END {{P}}.
*)

(** But, as we remarked above for the conditional, we know a
    little more at the end -- not just [P], but also the fact
    that [b] is false in the current state.  So we can enrich the
    postcondition a little: *)
(**

      {{P}} WHILE b DO c END {{P /\ ~b}}
*)

(** What about the case where the loop body _does_ get executed?
    In order to ensure that [P] holds when the loop finally
    exits, we certainly need to make sure that the command [c]
    guarantees that [P] holds whenever [c] is finished.
    Moreover, since [P] holds at the beginning of the first
    execution of [c], and since each execution of [c]
    re-establishes [P] when it finishes, we can always assume
    that [P] holds at the beginning of [c].  This leads us to the
    following rule: *)
(**

                   {{P}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~b}}
*)
(** This is almost the rule we want, but again it can be improved a
    little: at the beginning of the loop body, we know not only that
    [P] holds, but also that the guard [b] is true in the current
    state.  This gives us a little more information to use in
    reasoning about [c] (showing that it establishes the invariant by
    the time it finishes).  This gives us the final version of the
    rule:
*)
(**

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

    The proposition [P] is called an _invariant_ of the loop.
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
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
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.

(** One subtlety in the terminology is that calling some assertion [P]
    a "loop invariant" doesn't just mean that it is preserved by the
    body of the loop in question (i.e., [{{P}} c {{P}}], where [c] is
    the loop body), but rather that [P] _together with the fact that
    the loop's guard is true_ is a sufficient precondition for [c] to
    ensure [P] as a postcondition.

    This is a slightly (but significantly) weaker requirement.  For
    example, if [P] is the assertion [X = 0], then [P] _is_ an
    invariant of the loop

    WHILE X = 2 DO X := 1 END

    although it is clearly _not_ preserved by the body of the
    loop. *)

Example while_example :
    {{fun st => st X <= 3}}
  WHILE (BLe (AId X) (ANum 2))
  DO X ::= APlus (AId X) (ANum 1) END
    {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold bassn, assn_sub, assert_implies, t_update. simpl.
    intros st [H1 H2]. apply leb_complete in H2. omega.
  unfold bassn, assert_implies. intros st [Hle Hb].
    simpl in Hb. destruct (leb (st X) 2) eqn : Heqle.
    exfalso. apply Hb; reflexivity.
    apply leb_iff_conv in Heqle. omega.
Qed.

(** We can use the while rule to prove the following Hoare triple,
    which may seem surprising at first... *)

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  (* WORKED IN CLASS *)
  intros P Q.
  apply hoare_consequence_pre with (P' := fun st : state => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - (* Loop body preserves invariant *)
    apply hoare_post_true. intros st. apply I.
  - (* Loop invariant and negated guard imply postcondition *)
    simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - (* Precondition implies invariant *)
    intros st H. constructor.  Qed.

(** Of course, this result is not surprising if we remember that
    the definition of [hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    post-condition. *)

(** Hoare rules that only talk about terminating commands are
    often said to describe a logic of "partial" correctness.  It is
    also possible to give Hoare rules for "total" correctness, which
    build in the fact that the commands terminate. However, in this
    course we will only talk about partial correctness. *)

(* ----------------------------------------------------------------- *)
(** *** Exercise: [REPEAT] *)

(** **** Exercise: 4 stars, advanced (hoare_repeat)  *)
(** In this exercise, we'll add a new command to our language of
    commands: [REPEAT] c [UNTIL] a [END]. You will write the
    evaluation rule for [repeat] and add a new Hoare rule to
    the language for programs involving it. *)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ;; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
(* FILL IN HERE *)
.

(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Notation "c1 '/' st '\\' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion)
                        : Prop :=
  forall st st', (c / st \\ st') -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** To make sure you've got the evaluation rules for [REPEAT] right,
    prove that [ex1_repeat evaluates correctly. *)

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state \\
               t_update (t_update empty_state X 1) Y 1.
Proof.
  (* FILL IN HERE *) Admitted.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

(* FILL IN HERE *)

(** For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:

  {{ X > 0 }}
  REPEAT
    Y ::= X;;
    X ::= X - 1
  UNTIL X = 0 END
  {{ X = 0 /\ Y > 0 }}
*)

End RepeatExercise.
(** [] *)

(* ################################################################# *)
(** * Summary *)

(** So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs.  In the reminder of this chapter we'll explore a
    systematic way to use Hoare Logic to prove properties about
    programs. The rules of Hoare Logic are:

             ------------------------------ (hoare_asgn)
             {{Q [X |-> a]}} X::=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} SKIP {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ---------------------  (hoare_seq)
              {{ P }} c1;;c2 {{ R }}

              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} WHILE b DO c END {{P /\ ~b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}

    In the next chapter, we'll see how these rules are used to prove
    that programs satisfy specifications of their behavior. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (himp_hoare)  *)
(** In this exercise, we will derive proof rules for the [HAVOC]
    command, which we studied in the last chapter.

    First, we enclose this work in a separate module, and recall the
    syntax and big-step semantics of Himp commands. *)

Module Himp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : id -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'HAVOC' X" := (CHavoc X) (at level 60).

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st \\ st' ->
                  (WHILE b1 DO c1 END) / st' \\ st'' ->
                  (WHILE b1 DO c1 END) / st \\ st''
  | E_Havoc : forall (st : state) (X : id) (n : nat),
              (HAVOC X) / st \\ t_update st X n

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** The definition of Hoare triples is exactly as before. Unlike our
    notion of program equivalence, which had subtle consequences with
    occassionally nonterminating commands (exercise [havoc_diverge]),
    this definition is still fully satisfactory. Convince yourself of
    this before proceeding. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', c / st \\ st' -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

(** Complete the Hoare rule for [HAVOC] commands below by defining
    [havoc_pre] and prove that the resulting rule is correct. *)

Definition havoc_pre (X : id) (Q : Assertion) : Assertion 
  (* REPLACE THIS LINE WITH   := _your_definition_ . *) . Admitted.

Theorem hoare_havoc : forall (Q : Assertion) (X : id),
  {{ havoc_pre X Q }} HAVOC X {{ Q }}.
Proof.
  (* FILL IN HERE *) Admitted.

End Himp.
(** [] *)

(** $Date: 2016-07-13 12:41:41 -0400 (Wed, 13 Jul 2016) $ *)

