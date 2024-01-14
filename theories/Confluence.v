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
Require Import Local.Shrinking.
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

(* TODO: should we move this to the residuals file...? *)

Lemma subset_mark_unmark:
  forall r,
  subset (mark (unmark r)) r.
Proof.
  induction r; simpl; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct r.
    + constructor.
    + constructor.
  - constructor; auto.
Qed.

(* TODO: this one too... *)

Lemma redexes_pick:
  forall r,
  redexes_count r > 0 ->
  { s | subset s r & redexes_count s = 1 }.
Proof.
  induction r; intros.
  - exfalso; inversion H.
  - exfalso; inversion H.
  - exfalso; inversion H.
  - exfalso; inversion H.
  - exfalso; inversion H.
  - exfalso; inversion H.
  - destruct r.
    + eexists (redexes_jump true f xs); eauto with cps.
    + exfalso; inversion H.
  - simpl in H.
    (* Computationally, we'd rather pick the rightmost redex, because this is
       the shortest path to develop a set of redexes. Still, this function is
       quadratic on the size of the term while it could probably be done in a
       linear way. Oh well... *)
    destruct (le_gt_dec (redexes_count r2) 0).
    + destruct IHr1; try lia.
      exists (redexes_bind x ts (mark (unmark r2))).
      * constructor; auto.
        apply subset_mark_unmark.
      * simpl.
        rewrite redexes_count_mark.
        lia.
    + destruct IHr2; try lia.
      exists (redexes_bind (mark (unmark r1)) ts x).
      * constructor; auto.
        apply subset_mark_unmark.
      * simpl.
        now rewrite redexes_count_mark.
Qed.

Lemma beta_residuals:
  forall r,
  redexes_count r = 1 ->
  forall a b,
  residuals [] (mark a) r (mark b) ->
  beta a b.
Proof.
  admit.
Admitted.

Global Hint Resolve beta_residuals: cps.

Lemma t_beta_parallel:
  forall a b,
  parallel a b -> t(beta) a b.
Proof.
  intros.
  destruct H as (r, ?, ?).
  generalize dependent a.
  generalize dependent b.
  (* Proceed by induction on the maximum development length. *)
  induction (finite_development r) using SN_ind; intros.
  rename s into H1, x into r.
  (* We can pick any redex now. *)
  destruct redexes_pick with r as (s, ?H, ?H); auto.
  (* Since s is a subset of r, we can reduce it on r. *)
  assert (exists rs, residuals [] r s rs) as (rs, ?) by eauto 7 with cps.
  (* Similarly, it's compatible with a, thus we may reduce it on a. *)
  assert (exists c, residuals [] (mark a) s c) as (c, ?) by eauto 9 with cps.
  (* Since a has no marks, c can't possibly have marks as well. *)
  rewrite mark_unmark_is_sound with c in H6 by eauto with cps.
  (* Now, since we've reduced just s from a to c, we can reduce the remainder
     and go to b by the partial development lemma. *)
  assert (residuals [] (mark (unmark c)) rs (mark b)).
  - eapply partial_development; eauto with cps.
  - (* As s has a single mark, we can go from a to c by performing a jump. *)
    assert (beta a (unmark c)) by eauto with cps.
    (* Is this everything, or are there any more steps in rs? *)
    destruct (le_gt_dec (redexes_count rs) 0).
    + (* We need a single step to finish. *)
      assert (unmark c = b) by eauto with arith cps; subst.
      now constructor.
    + (* There's at least one more step, which we reduce by using the inductive
         hypothesis. *)
      apply t_trans with (unmark c).
      * now constructor.
      * assert (redexes_count s > 0) by lia.
        apply H2 with rs; eauto with cps.
        constructor; now constructor 1 with s.
Qed.

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
    + destruct (le_gt_dec (redexes_count pr) 0).
      * assert (mark y = d) by eauto with arith cps; subst.
        rewrite unmark_mark_is_sound.
        apply r_refl.
      * constructor.
        exists pr; auto.
        admit.
    + destruct (le_gt_dec (redexes_count rp) 0).
      * assert (mark z = d) by eauto with arith cps; subst.
        rewrite unmark_mark_is_sound.
        apply r_refl.
      * constructor.
        exists rp; auto.
        admit.
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
  apply diamond_for_same_relation with rt(union beta smol).
  - apply shrinking_preserves_confluence.
    + apply smol_is_shrinking.
    + apply beta_is_confluent.
  - apply same_relation_rt.
    apply same_relation_sym.
    apply step_characterization.
Qed.

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
