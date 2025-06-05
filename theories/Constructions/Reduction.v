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
    rt(cbn) e v /\ value v.

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
    (* We take the intersection of all approximations! *)
    forall n, approx n g e1 e2.

Lemma observational_approx_unfold:
  forall n g e1 e2,
  approx (S n) g e1 e2 =
    (forall (h: context) v,
     typing [] (h e1) boolean (approx n) ->
     typing [] (h e2) boolean (approx n) ->
     eval (h e1) v <-> eval (h e2) v).
Proof.
  auto.
Qed.

Lemma observational_tt_ff:
  forall g,
  ~observational g bool_tt bool_ff.
Proof.
  (* Assume the relation is degenerate; so [true ~ false]. *)
  repeat intro.
  (* For every approximation level, on every context, true and false return the
     same value after computation; we pick the empty context and the truth value
     for checking. *)
  specialize (H 1).
  unfold approx in H; simpl in H.
  specialize (H context_hole bool_tt).
  (* Now we observe... *)
  destruct H as (?, _); simpl.
  - (* True is typable, obviously. *)
    repeat constructor.
  - (* So is false. *)
    repeat constructor.
  - (* If [true] reduces to [true] (which is trivial), then [false] should also
       reduce to [true]: that's an absurd! *)
    simpl in H; destruct H.
    + (* Clearly... *)
      split; auto with cps.
    + (* TODO: properly define CBN and CBV. *)
      admit.
Admitted.

Lemma observational_is_consistent:
  forall g,
  ~(forall e1 e2, observational g e1 e2).
Proof.
  repeat intro.
  (* Follows directly from the above: on any context, [true] and [false] are
     different values. *)
  now apply observational_tt_ff with g.
Qed.

Lemma observational_approx_reduces:
  forall n g e t,
  typing g e t (approx n) ->
  exists f,
  rt(cbn) e f.
Proof.
  induction n; intros.
  - (* Huh... is this even true as is? I don't think so! *)
    admit.
  - apply IHn with g t.
    apply infer_subset with (approx (S n)).
    + clear IHn g e t H; intros.
      admit.
    + assumption.
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
    + (* Just as above... *)
      admit.
Admitted.

Lemma observational_is_conservative:
  forall j,
  infer conv j ->
  infer observational j.
Proof.
  intros.
  apply infer_subset with conv.
  - exact observational_conv.
  - assumption.
Qed.

Lemma extensionality_if:
  forall g f1 f2 a b,
  typing g f1 (pi a b) conv ->
  typing g f2 (pi a b) conv ->
  (forall x, typing g x a conv ->
    observational g (application f1 x) (application f2 x)) ->
  observational g f1 f2.
Proof.
  repeat intro.
  induction n; simpl; intros.
  - easy.
  - split; intros.
    + (* Ignore, for now, definitions inside the context [g], as the relation
         will need to be reworked to take care of that. In order to prove that
         pi types admit functional extensionality in the observational relation,
         we first check if the context [h] goes inside a binder. If it does, it
         means that [f1] plays no role in the computation itself, so neither
         will [f2] and thus we finish. If [f1] doesn't go into a binder, though,
         it will be used in the computation. We have now to find an equivalent
         applicative context for [h], i.e., a context [(([] e1) ...) en]. If the
         number of arguments is zero, this has to be the empty context, which is
         an absurd given that [f1] would be a boolean due to [H4] and it can
         never be a function as it is in [H]. If there are some arguments, we
         take the first one, [e1], and give it to [H1] to show that [f1 e1] and
         [f2 e2] are equivalent. If they are, so will be [f1 e1 ... en] and
         [f2 e1 ... en], which is our context. As it's equivalent to [h], this
         means [f1 ...] will return [v], and so will [f2 ...] as expected. *)
      admit.
    + (* Same as above. *)
      admit.
Admitted.

Lemma extensionality_only_if:
  forall g f1 f2 a b,
  typing g f1 (pi a b) conv ->
  typing g f2 (pi a b) conv ->
  observational g f1 f2 ->
  forall x,
  typing g x a conv ->
  observational g (application f1 x) (application f2 x).
Proof.
  repeat intro.
  destruct n; simpl; intros.
  - easy.
  - specialize (H1 (S n)); simpl in H1.
    (* We need composition of contexts to finish this, but this is clearly true
       as we can supply [h (application [-] x)] to [H2] and get our goal. *)
    admit.
Admitted.
