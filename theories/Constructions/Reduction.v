(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Normalization.

Import ListNotations.

(* For typeable terms, the normal form is computable. *)
Lemma normal_form_is_decidable:
  forall g e t,
  typing g e t typed_conv ->
  exists2 f,
  rt(step g) e f & normal (step g) f.
Proof.
  intros.
  apply strong_normalization in H.
  induction H using SN_ind.
  destruct step_is_decidable with x g as [ (y, ?) | ? ].
  - destruct H2 with y as (z, ?, ?).
    + now apply t_step.
    + exists z; eauto with cps.
  - exists x.
    + apply rt_refl.
    + intros y ?.
      apply n.
      now exists y.
Qed.

(*
  It should be enough to use an evaluation context rather than an arbitrary one.

(* Call-by-value evaluation contexts. *)
Inductive evaluation_context: context -> Prop :=
  | evaluation_context_hole:
    evaluation_context context_hole
  | evaluation_context_app_left:
    forall e f,
    evaluation_context e ->
    evaluation_context (context_app_left e f)
  | evaluation_context_app_right:
    forall v e,
    value v ->
    evaluation_context e ->
    evaluation_context (context_app_right v e)
  | evaluation_context_def_val:
    forall e t f,
    evaluation_context e ->
    evaluation_context (context_def_val e t f)
  | evaluation_context_def_body:
    forall v t f,
    value v ->
    evaluation_context f ->
    evaluation_context (context_def_body v t f).
*)

Axiom boolean: term.
Axiom bool_tt: term.
Axiom bool_ff: term.

Axiom cbn: relation term.

Definition eval: relation term :=
  fun e v =>
    rst(cbn) e v /\ value v.

(* We can't properly define this relation the standard way as it would violate
   the strict positivity rule. Instead, we use a trick similar to Sangiorgi's
   definition of stratified strong bisimilarity (definition 2.2.10 on the "The
   pi-calculus: A Theory of Mobile Processes"). By induction on some natural
   number, we count how many times the (CONV) rule will be necessary; then we
   define that two terms are observationally equivalent if they are equivalent
   no matter for every possible number of steps we need. *)

Fixpoint observational_approx (n: nat): env -> term -> relation term :=
  fun g t e1 e2 =>
    match n with
    | 0 => True
    | S m =>
        forall (h: context) v,
        typing [] (h e1) boolean (observational_approx m)->
        typing [] (h e2) boolean (observational_approx m) ->
        eval (h e1) v <-> eval (h e2) v
   end.

Definition observational: env -> term -> relation term :=
  fun g t e1 e2 =>
    (* We take the intersection of all approximations. *)
    forall n, observational_approx n g t e1 e2.

Lemma observational_is_consistent:
  forall g t,
  ~(forall e1 e2, observational g t e1 e2).
Proof.
  repeat intro.
  specialize (H bool_tt bool_ff 1).
  unfold observational_approx in H; simpl in H.
  specialize (H context_hole bool_tt).
  destruct H as (?, _); simpl.
  - admit.
  - admit.
  - simpl in H.
    destruct H.
    + split.
      * apply rst_refl.
      * admit.
    + (* H is an absurd! *)
      admit.
Admitted.

Lemma observational_is_conservative:
  forall g e t,
  typing g e t typed_conv ->
  typing g e t observational.
Proof.
  (* Mutual induction with valid environment...? *)
  admit.
Admitted.
