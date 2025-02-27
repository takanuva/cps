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
  typing g e t conv ->
  exists2 f,
  rt(step g) e f & normal (step g) f.
Proof.
  intros.
  apply strong_normalization in H.
  induction H using SN_ind.
  destruct step_is_decidable with g x as [ (y, ?H) | ?H ].
  - destruct H2 with y as (z, ?, ?).
    + now apply t_step.
    + exists z; eauto with cps.
  - exists x.
    + apply rt_refl.
    + intros y ?.
      now apply H0 with y.
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

Fixpoint observational_approx (n: nat): env -> relation term :=
  fun g e1 e2 =>
    match n with
    | 0 => True
    | S m =>
        forall (h: context) v,
        typing [] (h e1) boolean (observational_approx m) ->
        typing [] (h e2) boolean (observational_approx m) ->
        eval (h e1) v <-> eval (h e2) v
   end.

Local Notation approx := observational_approx.

Definition observational: env -> relation term :=
  fun g e1 e2 =>
    (* We take the intersection of all approximations. *)
    forall n, approx n g e1 e2.

Lemma observational_is_consistent:
  forall g,
  ~(forall e1 e2, observational g e1 e2).
Proof.
  repeat intro.
  (* Assume the relation is degenerate; so [true ~ false]. *)
  specialize (H bool_tt bool_ff 1).
  unfold observational_approx in H; simpl in H.
  (* On every context, they return the same value; we pick the empty context and
     the truth value. *)
  specialize (H context_hole bool_tt).
  (* Now we observe... *)
  destruct H as (?, _); simpl.
  - (* True is typable, obviously. *)
    repeat constructor.
  - (* False is also typable, obviously. *)
    repeat constructor.
  - (* If [true] reduces to [true] (trivial), then [false] reduces to [true]:
       that's an absurd! *)
    simpl in H.
    destruct H.
    + split; auto with cps.
    + (* ... *)
      admit.
Admitted.

Lemma observational_conv:
  forall g e f,
  conv g e f ->
  observational g e f.
Proof.
  (* Since this is the intersection of all approximations, we need to show that
     this is valid for every level. We can do this by case analysis. *)
  unfold observational.
  destruct n; simpl; intros.
  (* Case: zero. *)
  - trivial.
  (* Case: succ. *)
  - split; intros (?, ?).
    + admit.
    + admit.
Admitted.

Lemma observational_is_conservative:
  forall j,
  infer conv j ->
  infer observational j.
Proof.
  (* We simply reconstruct the proof tree, judgement by judgement. *)
  induction 1.
  - now apply typing_iset.
  - now apply typing_bound with d t.
  - now apply typing_pi with s1 s2.
  - now apply typing_abs.
  - now apply typing_app with t.
  - now apply typing_def.
  - now apply typing_sigma with s1 s2.
  - now apply typing_pair.
  - now apply typing_proj1 with u.
  - now apply typing_proj2 with t.
  - now apply typing_bool.
  - now apply typing_true.
  - now apply typing_false.
  - now apply typing_if with s.
  - (* The only difference in the structure is on the (CONV) rule, which will
       require us to show that [t] and [u] are observationally equivalent; this
       follows directly since, by our hypothesis, they are convertible. *)
    apply typing_conv with t s.
    + assumption.
    + assumption.
    + now apply observational_conv.
  - apply valid_env_nil.
  - now apply valid_env_var with s.
  - now apply valid_env_def with s.
Qed.

Theorem extensionality:
  forall g f1 f2 a b,
  typing g f1 (pi a b) conv ->
  typing g f2 (pi a b) conv ->
  (forall x, typing g x a conv ->
    observational g (application f1 x) (application f2 x)) ->
  observational g f1 f2.
Proof.
  unfold observational; intros.
  admit.
Admitted.
