(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Reduction.
Require Import Local.Residuals.

(** ** Parallel reduction *)

(* The parallel reduction relation can perform one or more jumps at once in a
   single step. Note that this is a bit different from the usual formulation in
   the lambda calculus because we require at least one jump, so this relation is
   not reflexive. We do so because this is useful for some of the preservation
   proofs, as we want the transitive closure of this relation to coincide with
   the transitive closure of the jump reduction. Then, of course, we can go back
   to the usual definition by taking its reflexive closure, which we will do for
   the confluence proof. *)

Definition parallel: relation pseudoterm :=
  fun b c =>
    exists2 r,
    residuals [] (mark b) r (mark c) & redexes_count r > 0.

Global Hint Unfold parallel: cps.

Lemma parallel_bind_left:
  LEFT parallel.
Proof.
  unfold LEFT; intros.
  destruct H as (r, ?, ?).
  exists (redexes_bind r ts (mark c)); simpl.
  - constructor.
    + apply residuals_tail with (g := []).
      assumption.
    + apply residuals_term.
  - lia.
Qed.

Global Hint Resolve parallel_bind_left: cps.

Lemma parallel_bind_right:
  RIGHT parallel.
Proof.
  unfold RIGHT; intros.
  destruct H as (r, ?, ?).
  exists (redexes_bind (mark b) ts r); simpl.
  - constructor.
    + apply residuals_term.
    + apply residuals_tail with (g := []).
      assumption.
  - lia.
Qed.

Global Hint Resolve parallel_bind_right: cps.

(* Jump reduction is a subset of parallel reduction. *)

Lemma t_beta_bind_left:
  LEFT t(beta).
Proof.
  induction 1; eauto with cps.
Qed.

Lemma t_beta_bind_right:
  RIGHT t(beta).
Proof.
  induction 1; eauto with cps.
Qed.

(* TODO: move these few lemmas to [Residuals.v]! *)

Lemma redexes_count_mark_context:
  forall r h,
  redexes_count (mark_context h r) = redexes_count r.
Proof.
  induction h; simpl.
  - reflexivity.
  - rewrite redexes_count_mark; lia.
  - rewrite redexes_count_mark; lia.
Qed.

Fixpoint residuals_context_to_env h :=
  match h with
  | context_hole =>
    []
  | context_left r ts c =>
    residuals_context_to_env r ++ [Some (length ts, mark c)]
  | context_right b ts r =>
    residuals_context_to_env r ++ repeat None (length ts)
  end.

Lemma residuals_context_to_env_length:
  forall h,
  length (residuals_context_to_env h) = #h.
Proof.
  induction h; simpl.
  - reflexivity.
  - rewrite app_length.
    rewrite IHh; simpl.
    lia.
  - rewrite app_length.
    rewrite repeat_length.
    rewrite IHh; simpl.
    reflexivity.
Qed.

Lemma residuals_mark_context:
  forall h g a r b,
  residuals (residuals_context_to_env h ++ g) a r b ->
  residuals g (mark_context h a) (mark_context h r) (mark_context h b).
Proof.
  induction h; simpl; intros.
  - assumption.
  - constructor.
    + apply IHh.
      rewrite <- app_assoc in H.
      assumption.
    + apply residuals_term.
  - constructor.
    + apply residuals_term.
    + apply IHh.
      rewrite <- app_assoc in H.
      assumption.
Qed.

Lemma parallel_beta:
  forall a b,
  beta a b -> parallel a b.
Proof.
  (* By induction on the step, as it's compatible. *)
  induction 1.
  (* Case: step_ctxjmp. *)
  - (* As the hole has a single jump, choose to mark only it. *)
    exists (redexes_bind (mark_context h (redexes_jump true #h xs)) ts
      (mark c)); simpl.
    + (* This single jump will be bound to the correct continuation. *)
      constructor.
      * do 2 rewrite <- mark_context_is_sound; simpl.
        apply residuals_mark_context.
        rewrite mark_apply_parameters_is_sound.
        rewrite mark_lift_is_sound.
        rewrite <- H.
        constructor.
        rewrite <- residuals_context_to_env_length.
        apply item_insert_head with (k := 0).
        constructor.
      * apply residuals_term.
    + (* We explictly stated there is going to be one mark. *)
      rewrite redexes_count_mark.
      rewrite redexes_count_mark_context.
      simpl; lia.
  (* Case: step_bind_left. *)
  - apply parallel_bind_left.
    assumption.
  (* Case: step_bind_right. *)
  - apply parallel_bind_right.
    assumption.
Qed.

Global Hint Resolve parallel_beta: cps.

Lemma t_beta_parallel:
  forall a b,
  parallel a b -> t(beta) a b.
Proof.
  intros.
  destruct H as (r, ?, ?).
  admit.
Admitted.

Global Hint Resolve t_beta_parallel: cps.

Lemma t_beta_and_t_parallel_coincide:
  same_relation t(beta) t(parallel).
Proof.
  split; induction 1; eauto with cps.
Qed.

Lemma rt_beta_and_rt_parallel_coincide:
  same_relation rt(beta) rt(parallel).
Proof.
  split.
  - induction 1; eauto with cps.
  - induction 1; eauto with cps.
    (* TODO: there should be a hint for this! *)
    apply clos_t_clos_rt; auto with cps.
Qed.

(* ** Confluence *)

Lemma parallel_is_joinable:
  forall x y,
  parallel x y ->
  forall z,
  parallel x z ->
  exists2 w,
  r(parallel) y w & r(parallel) z w.
Proof.
  destruct 1 as (r, ?, ?).
  destruct 1 as (s, ?, ?).
  edestruct paving.
  - exact H.
  - exact H1.
  - exists (unmark d).
    + admit.
    + admit.
Admitted.

Lemma r_parallel_has_diamond:
  diamond r(parallel).
Proof.
  destruct 1; destruct 1.
  - rename y0 into z.
    apply parallel_is_joinable with x.
    + assumption.
    + assumption.
  - exists y; auto with cps.
  - exists y; auto with cps.
  - exists x; auto with cps.
Qed.

Lemma parallel_is_confluent:
  confluent parallel.
Proof.
  assert (diamond t(r(parallel))).
  - apply transitive_closure_preserves_diagram; auto with cps.
    exact r_parallel_has_diamond.
  - intros x y ? z ?.
    (* I really should add some automation for this... TODO: review me. *)
    destruct H with x y z as (w, ?, ?).
    + apply r_and_t_closures_commute.
      apply rt_characterization.
      assumption.
    + apply r_and_t_closures_commute.
      apply rt_characterization.
      assumption.
    + exists w.
      * apply rt_characterization.
        apply r_and_t_closures_commute.
        assumption.
      * apply rt_characterization.
        apply r_and_t_closures_commute.
        assumption.
Qed.

Lemma beta_is_confluent:
  confluent beta.
Proof.
  compute; intros.
  apply rt_beta_and_rt_parallel_coincide in H.
  apply rt_beta_and_rt_parallel_coincide in H0.
  (* TODO: might wanna review this after adding some automation. *)
  destruct parallel_is_confluent with x y z as (w, ?, ?).
  - assumption.
  - assumption.
  - exists w.
    + apply rt_beta_and_rt_parallel_coincide.
      assumption.
    + apply rt_beta_and_rt_parallel_coincide.
      assumption.
Qed.

Theorem step_is_confluent:
  confluent step.
Proof.
  (*
  assert (confluent (union beta tidy)).
  (* By the Hindley-Rosen lemma, the union of beta and tidy is confluent. *)
  - apply hindley_rosen.
    + apply beta_is_confluent.
    + apply tidy_is_confluent.
    + apply rt_beta_and_rt_tidy_commute.
  (* And this union is the same as the one-step reduction, so it's confluent. *)
  - intros x y ? z ?.
    assert (same_relation star rt(union beta tidy)).
    + clear H H0 H1 x y z.
      split; induction 1.
      * apply step_characterization in H; auto with cps.
      * auto with cps.
      * eauto with cps.
      * apply step_characterization in H; auto with cps.
      * auto with cps.
      * eauto with cps.
    + apply H2 in H0.
      apply H2 in H1.
      destruct H with x y z as (w, ?, ?); auto.
      exists w.
      * apply H2.
        assumption.
      * apply H2.
        assumption.
  *)
  admit.
Admitted.

Corollary step_is_church_rosser:
  church_rosser step.
Proof.
  compute; intros.
  apply confluence_implies_church_rosser; auto.
  exact step_is_confluent.
Qed.

Corollary uniqueness_of_normal_form:
  forall a b,
  [a <=> b] ->
  normal step a ->
  normal step b ->
  a = b.
Proof.
  intros.
  (* TODO: generalize this proof into [AbstractRewriting.v]. *)
  destruct step_is_church_rosser with a b as (c, ?, ?); auto.
  assert (a = c /\ b = c) as (?, ?).
  - split.
    + clear b H H1 H3.
      induction H2.
      * exfalso.
        apply H0 with y.
        assumption.
      * reflexivity.
      * destruct IHclos_refl_trans1; auto.
    + clear a H H0 H2.
      induction H3.
      * exfalso.
        apply H1 with y.
        assumption.
      * reflexivity.
      * destruct IHclos_refl_trans1; auto.
  - congruence.
Qed.
