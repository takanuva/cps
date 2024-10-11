(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.AbstractRewriting.
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Residuals.
Require Import Local.Confluence.

(* The following method is present on the "Factorization and Normalization,
   Essentially" paper, and was hinted to me by dr. Accattoli through private
   communication. This seems way simpler than what I was trying to do. *)

(* TODO: we have some unusual rules here... perhaps we should name them. *)

Inductive inner: relation pseudoterm :=
  | inner_nonstatic_ctxjmp:
    forall h xs ts c,
    nonstatic h ->
    length xs = length ts ->
    inner (bind (h (jump #h xs)) ts c)
      (bind
         (h (apply_parameters xs 0 (lift (S #h) (length ts) c)))
         ts c)
  | inner_bind_left:
    LEFT inner
  | inner_bind_right:
    forall b ts c1 c2,
    beta c1 c2 ->
    inner (bind b ts c1) (bind b ts c2).

Lemma beta_inner:
  inclusion inner beta.
Proof.
  induction 1; auto with cps.
Qed.

Global Hint Resolve beta_inner: cps.

Lemma step_inner:
  inclusion inner step.
Proof.
  auto with cps.
Qed.

Global Hint Resolve step_inner: cps.

Inductive leftmost_marked: bool -> redexes -> Prop :=
  | leftmost_marked_type:
    leftmost_marked false redexes_type
  | leftmost_marked_prop:
    leftmost_marked false redexes_prop
  | leftmost_marked_base:
    leftmost_marked false redexes_base
  | leftmost_marked_void:
    leftmost_marked false redexes_void
  | leftmost_marked_bound:
    forall n,
    leftmost_marked false (redexes_bound n)
  | leftmost_marked_negation:
    forall ts,
    leftmost_marked false (redexes_negation ts)
  | leftmost_marked_jump:
    forall r k xs,
    leftmost_marked r (redexes_jump r k xs)
  | leftmost_marked_bind:
    forall r b ts c,
    leftmost_marked r b ->
    leftmost_marked r (redexes_bind b ts c).

Lemma leftmost_marked_mark:
  forall b,
  leftmost_marked false (mark b).
Proof.
  induction b; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - now constructor.
Qed.

(* Notice that we are not assuming that parallel inner reduction has at least
   one mark as we do in the standard parallel reduction, mostly because there's
   no need to. We could, of course, do it anyways. *)

Definition parallel_inner: relation pseudoterm :=
  fun b c =>
    exists2 r,
    residuals [] (mark b) r (mark c) & leftmost_marked false r.

Lemma inner_parallel_inner:
  inclusion inner parallel_inner.
Proof.
  induction 1.
  - (* Very similar to the [parallel_beta] lemma! *)
    exists (redexes_bind (mark_context h (redexes_jump true #h xs)) ts
      (mark c)); simpl.
    + constructor.
      * do 2 rewrite <- mark_context_is_sound; simpl.
        apply residuals_mark_context.
        rewrite mark_apply_parameters_is_sound.
        rewrite mark_lift_is_sound.
        rewrite <- H0.
        constructor.
        rewrite <- residuals_context_to_env_length.
        apply item_insert_head with (k := 0).
        constructor.
      * apply residuals_term.
    + (* Clearly true, as h is nonstatic! *)
      constructor; clear c.
      generalize (redexes_jump true #h xs) as c; intros.
      clear H0 xs ts.
      induction H using nonstatic_ind; simpl; intros.
      * constructor.
        apply leftmost_marked_mark.
      * now constructor.
  - destruct IHinner as (r, ?, ?).
    exists (redexes_bind r ts (mark c)); simpl.
    + constructor.
      * now apply residuals_tail with (g := []).
      * rewrite app_nil_r.
        apply residuals_term.
    + now constructor.
  - apply parallel_beta in H as (r, ?, ?).
    exists (redexes_bind (mark b) ts r); simpl.
    + constructor.
      * apply residuals_term.
      * now apply residuals_tail with (g := []).
    + constructor.
      apply leftmost_marked_mark.
Qed.

Local Hint Resolve inner_parallel_inner: cps.

Lemma parallel_inner_rt_inner:
  inclusion parallel_inner rt(inner).
Proof.
  admit.
Admitted.

Local Hint Resolve parallel_inner_rt_inner: cps.

Lemma rt_inner_and_rt_parallel_inner_are_equivalent:
  same_relation rt(inner) rt(parallel_inner).
Proof.
  split; induction 1; eauto with cps.
Qed.

Lemma macro_merge:
  inclusion (comp parallel_inner head) parallel.
Proof.
  admit.
Admitted.

Lemma macro_split:
  inclusion parallel (comp rt(head) parallel_inner).
Proof.
  admit.
Admitted.

(* TODO: move and generalize this (Accattoli's method) to the abstract rewriting
   file, and then just use it here. *)

Theorem factorization:
  inclusion rt(beta) (comp rt(head) rt(inner)).
Proof.
  assert (inclusion rt(union head parallel_inner)
    (comp rt(head) rt(parallel_inner))).
  - apply local_postponement.
    unfold postpones, inclusion; intros.
    destruct macro_split with x y as (z, ?, ?).
    + apply macro_merge; auto.
    + exists z; auto with cps.
  - unfold inclusion; intros.
    destruct H with x y as (z, ?, ?).
    + clear H.
      induction H0; eauto with cps.
      apply parallel_beta in H.
      apply macro_split in H.
      destruct H as (z, ?, ?).
      apply rt_trans with z.
      * clear H0 y.
        induction H; eauto with cps.
      * auto with cps.
    + apply rt_inner_and_rt_parallel_inner_are_equivalent in H2.
      eauto with cps.
Qed.

Corollary rt_beta_characterization:
  same_relation rt(beta) (comp rt(head) rt(inner)).
Proof.
  split.
  - apply factorization.
  - intros x z ?.
    (* Clearly true. *)
    destruct H as (y, ?, ?).
    apply rt_trans with y.
    + clear H0 z.
      induction H; eauto with cps.
    + clear H x.
      induction H0; eauto with cps.
Qed.
