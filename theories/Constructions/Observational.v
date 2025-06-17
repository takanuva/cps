(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
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
Require Import Local.Constructions.Reduction.

Import ListNotations.

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
    | 0 =>
      True
    | S m =>
      forall (h: context) v,
      (* TODO: close over g! *)
      typing [] (h e1) boolean (observational_approx m) ->
      typing [] (h e2) boolean (observational_approx m) ->
      eval (h e1) v <-> eval (h e2) v
   end.

Local Notation approx := observational_approx.

Definition observational: env -> relation term :=
  fun g e1 e2 =>
    (* We take the intersection of all approximations! *)
    forall n, approx n g e1 e2.

Lemma approx_unfold:
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

Theorem observational_is_consistent:
  forall g,
  ~(forall e1 e2, observational g e1 e2).
Proof.
  repeat intro.
  (* Follows directly from the above: on any context, [true] and [false] are
     different values. *)
  now apply observational_tt_ff with g.
Qed.

(* Goal
  forall j n,
  infer observational j -> infer (approx n) j.
Proof.
  intros.
  apply infer_subset with observational; intros.
  - repeat intro.
    apply H0.
  - assumption.
Qed. *)

Lemma observational_conv:
  forall g,
  inclusion (conv g) (observational g).
Proof.
  repeat intro.
  generalize dependent y.
  generalize dependent x.
  generalize dependent g.
  induction n; intros.
  - easy.
  - rewrite approx_unfold; split; intros.
    + (* Respecting variables, conv is a congruence. So if we close over g,
         we have that conv [] (h (g x)) (h (g y))... so if one evaluates to a
         boolean, by Church-Rosser, so does the other. Typing doesn't seem to
         be relevant here... *)
      admit.
    + (* Same as above. *)
      admit.
Admitted.

Lemma observational_if:
  forall n g e1 e2,
  (forall (h: context) v,
   typing [] (h e1) boolean observational ->
   typing [] (h e2) boolean observational ->
   eval (h e1) v <-> eval (h e2) v) ->
  approx n g e1 e2.
Proof.
  admit.
Admitted.

Theorem observational_characterization:
  forall g e1 e2,
  observational g e1 e2 <->
    (forall (h: context) v,
     typing [] (h e1) boolean observational ->
     typing [] (h e2) boolean observational ->
     eval (h e1) v <-> eval (h e2) v).
Proof.
  (* This gives a characterization of the observational relation. This is indeed
     the definition we would have liked to give it, but defining it in this way
     would violate strict positivity rules. *)
  split; intros.
  - (* This is trivially so. From H, e1 and e2 are equivalent at level 1. *)
    specialize (H 1).
    rewrite approx_unfold in H.
    apply H.
    + (* Terms are always convertible if equivalent at level 0, so any typing
         derivation is enough. *)
      apply infer_subset with observational.
      * easy.
      * assumption.
    + (* Ditto. *)
      apply infer_subset with observational.
      * easy.
      * assumption.
  - (* This case is a bit trickier... see the documentation for it above. *)
    intro.
    now apply observational_if.
Qed.

Theorem observational_is_conservative:
  forall j,
  infer conv j ->
  infer observational j.
Proof.
  intros.
  apply infer_subset with conv; intros.
  - apply observational_conv.
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

Theorem extensionality:
  forall g f1 f2 a b,
  typing g f1 (pi a b) conv ->
  typing g f2 (pi a b) conv ->
  observational g f1 f2 <->
  (forall x,
   typing g x a conv ->
   observational g (application f1 x) (application f2 x)).
Proof.
  split; intros.
  - now apply extensionality_only_if with a b.
  - now apply extensionality_if with a b.
Qed.

Theorem observational_consistency:
  ~exists e, typing [] e bottom observational.
Proof.
  intros (e, ?).
  admit.
Admitted.
