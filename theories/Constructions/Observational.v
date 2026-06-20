(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
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

(* TODO: check also https://www.cs.ox.ac.uk/files/293/lazy.pdf. *)

Local Notation eval := cbv_eval.

Local Definition complete_relation: typing_equivalence :=
  fun g e1 e2 =>
    True.

Local Definition phi (R: typing_equivalence): typing_equivalence :=
  fun g e1 e2 =>
    forall (h: context) v,
    typing [] (h e1) boolean R ->
    typing [] (h e2) boolean R ->
    eval (h e1) v <-> eval (h e2) v.

Fixpoint approx_naive (n: nat): typing_equivalence :=
  match n with
  | 0 =>
    complete_relation
  | S m =>
    phi (approx_naive m)
  end.

Definition approx (n: nat): typing_equivalence :=
  fun g e1 e2 =>
    forall m,
    m <= n -> approx_naive m g e1 e2.

Definition observational: typing_equivalence :=
  fun g e1 e2 =>
    forall n, approx_naive n g e1 e2.

Lemma approx_is_monotone:
  forall n g e1 e2,
  approx (S n) g e1 e2 ->
  approx n g e1 e2.
Proof.
  repeat intro.
  apply H.
  lia.
Qed.

Lemma observational_refl:
  forall g e,
  observational g e e.
Proof.
  repeat intro.
  destruct n; simpl.
  - unfold complete_relation.
    trivial.
  - repeat intro.
    firstorder.
Qed.

Lemma observational_sym:
  forall g e1 e2,
  observational g e1 e2 ->
  observational g e2 e1.
Proof.
  repeat intro.
  destruct n; simpl.
  - unfold complete_relation.
    trivial.
  - specialize (H (S n)); simpl in H.
    firstorder.
Qed.

Lemma observational_tt_ff:
  forall g,
  ~observational g bool_tt bool_ff.
Proof.
  (* Assume the relation is degenerate; so [true ~ false]. *)
  repeat intro.
  (* For every approximation level, on every context, true and false return the
     same value after computation; we pick the empty context and the true value
     for checking. *)
  specialize (H 1); simpl in H.
  unfold phi in H.
  specialize (H context_hole bool_tt).
  simpl in H.
  (* Now we observe... *)
  destruct H as (?, _); simpl.
  - repeat constructor.
  - repeat constructor.
  - (* As true trivially evaluates to true, so should false: which of course is
       an absurd. *)
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

Theorem observational_equality:
  forall g e1 e2,
  observational g e1 e2 ->
  forall (h: context) v R,
  typing [] (h e1) boolean R ->
  typing [] (h e2) boolean R ->
  eval (h e1) v <-> eval (h e2) v.
Proof.
  intros.
  specialize (H 1).
  apply H.
  - apply infer_subset with (R := R); repeat intro.
    + unfold complete_relation.
      trivial.
    + assumption.
  - apply infer_subset with (R := R); repeat intro.
    + unfold complete_relation.
      trivial.
    + assumption.
Qed.

Theorem observational_is_conservative:
  forall j,
  infer conv j ->
  infer observational j.
Proof.
  intros.
  (* TODO: infer_subset should probably give us a witness of typing and that the
     element is a subterm... *)
  admit.
Admitted.

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
  - repeat intro.
    split; intros.
    + (* TODO: I no longer believe the following is correct...

         Ignore, for now, definitions inside the context [g], as the relation
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
    unfold phi in H1 |- *; repeat intro.
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

Lemma boolean_ex_falso:
  forall R e,
  typing [] e bottom R ->
  typing [] (application e boolean) boolean R.
Proof.
  intros.
  eapply typing_app.
  - eassumption.
  - apply typing_bool.
    constructor.
  - (* TODO: sigma is missing some laws... *)
    vm_compute.
    reflexivity.
Qed.

Theorem observational_consistency:
  ~exists e, typing [] e bottom observational.
Proof.
  (* Assume that false is derivable in the observational type system. *)
  intros (e, ?).
  (* So, easily, we can eliminate it to generate a boolean. *)
  apply boolean_ex_falso in H.
  (* ... *)
  admit.
Admitted.
