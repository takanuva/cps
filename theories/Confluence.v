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
  intros.
  admit.
Admitted.

Lemma r_parallel_has_diamond:
  diamond r(parallel).
Proof.
  admit.
Admitted.

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

Lemma tidy_has_weak_diamond:
  forall x y,
  tidy x y ->
  forall z,
  tidy x z ->
  exists2 w,
  r(tidy) y w & r(tidy) z w.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    + exists (remove_binding 0 b).
      * auto with cps.
      * auto with cps.
    + rename b into b1.
      exists (remove_binding 0 b2).
      * apply r_step.
        apply tidy_subst.
        assumption.
      * apply r_step.
        apply tidy_gc.
        apply not_free_tidy with b1; auto.
    + rename c into c1.
      exists (remove_binding 0 b).
      * auto with cps.
      * auto with cps.
  - dependent destruction H0.
    + clear IHtidy.
      exists (remove_binding 0 b2).
      * apply r_step.
        apply tidy_gc.
        apply not_free_tidy with b1; auto.
      * apply r_step.
        apply tidy_subst.
        assumption.
    + edestruct IHtidy as (b4, ?, ?); eauto.
      exists (bind b4 ts c).
      * destruct H1; auto with cps.
      * destruct H2; auto with cps.
    + rename c into c1.
      exists (bind b2 ts c2).
      * auto with cps.
      * auto with cps.
  - dependent destruction H0.
    + clear IHtidy.
      exists (remove_binding 0 b).
      * auto with cps.
      * auto with cps.
    + rename b into b1.
      exists (bind b2 ts c2).
      * auto with cps.
      * auto with cps.
    + edestruct IHtidy as (c4, ?, ?); eauto.
      exists (bind b ts c4).
      * destruct H1; auto with cps.
      * destruct H2; auto with cps.
Qed.

Lemma tidy_is_confluent:
  confluent tidy.
Proof.
  assert (diamond r(tidy)).
  (* The reflexive closure of tidy has the diamond property. *)
  - destruct 1; destruct 1; try rename y0 into z.
    + eapply tidy_has_weak_diamond; eauto.
    + exists y; auto with cps.
    + exists y; auto with cps.
    + exists x; auto with cps.
  (* The diamond property implies confluence. *)
  - (* Oh boy... it's the same relation, but we gotta convince Coq. TODO: add a
       proper morphism and review this one! *)
    apply transitive_closure_preserves_commutation in H.
    intros x y ? z ?.
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

Inductive tidy_context_case (h: context) k xs b: Prop :=
  | tidy_context_case_inside:
    (forall c, tidy (h c) b) ->
    tidy_context_case h k xs b
  | tidy_context_case_scope:
    forall r s us d,
    h = compose_context r (context_left s us d) ->
    b = r (remove_binding 0 (s (jump k xs))) ->
    not_free 0 (s (jump k xs)) ->
    tidy_context_case h k xs b
  | tidy_context_case_orthogonal1:
    forall r s us d e,
    h = compose_context r (context_left s us d) ->
    b = (compose_context r (context_left s us e)) (jump k xs) ->
    tidy d e ->
    tidy_context_case h k xs b
  | tidy_context_case_orthogonal2:
    forall r s us d e,
    h = compose_context r (context_right d us s) ->
    b = (compose_context r (context_right e us s)) (jump k xs) ->
    tidy d e ->
    tidy_context_case h k xs b.

Lemma tidy_context_case_analysis:
  forall (h: context) k xs b,
  tidy (h (jump k xs)) b -> tidy_context_case h k xs b.
Proof.
  induction h; simpl; intros.
  - inversion H.
  - dependent destruction H; simpl.
    + apply tidy_context_case_scope with
        (r := context_hole) (s := h) (us := ts) (d := c); auto.
    + edestruct IHh; eauto; simpl.
      * apply tidy_context_case_inside; eauto with cps.
      * apply tidy_context_case_scope with
          (r := context_left r ts c) (s := s) (us := us) (d := d); simpl;
          congruence.
      * apply tidy_context_case_orthogonal1 with
          (r := context_left r ts c) (s := s) (us := us) (d := d) (e := e);
          simpl; congruence.
      * apply tidy_context_case_orthogonal2 with
          (r := context_left r ts c) (s := s) (us := us) (d := d) (e := e);
          simpl; congruence.
    + apply tidy_context_case_orthogonal1 with
        (r := context_hole) (s := h) (us := ts) (d := c) (e := c2); auto.
  - dependent destruction H; simpl.
    + apply tidy_context_case_inside; eauto with cps.
    + apply tidy_context_case_orthogonal2 with
        (r := context_hole) (s := h) (us := ts) (d := b) (e := b2); auto.
    + edestruct IHh; eauto; simpl.
      * apply tidy_context_case_inside; eauto with cps.
      * apply tidy_context_case_scope with
          (r := context_right b ts r) (s := s) (us := us) (d := d); simpl;
          congruence.
      * apply tidy_context_case_orthogonal1 with
          (r := context_right b ts r) (s := s) (us := us) (d := d) (e := e);
          simpl; congruence.
      * apply tidy_context_case_orthogonal2 with
          (r := context_right b ts r) (s := s) (us := us) (d := d) (e := e);
          simpl; congruence.
Qed.

Lemma rt_beta_and_rt_tidy_commute:
  commutes rt(beta) rt(tidy).
Proof.
  (* We'll prove a much easier local verification instead. *)
  apply strong_commutation_implies_commutation.
  (* Now we may follow. *)
  induction 1; intros.
  - dependent destruction H0.
    + (* This can't happen! A jump can't be performed to a continuation k if
         k doesn't appear free at all. *)
      exfalso.
      (* TODO: we should make a lemma about not_free and contexts. *)
      assert (exists n, n = 0 + #h) as (n, ?); eauto.
      replace #h with n in H0; try lia.
      generalize dependent n.
      generalize O as o.
      clear H ts c.
      induction h; intros.
      * simpl in H0, H1.
        dependent destruction H0.
        dependent destruction H0.
        lia.
      * simpl in H0, H1.
        dependent destruction H0.
        eapply IHh; eauto.
        lia.
      * simpl in H0, H1.
        dependent destruction H0.
        eapply IHh; eauto.
        lia.
    + (* This might be the worst case. So, we're performing a garbage collection
         step in H[k<xs>]. There are two cases: either k<xs> is part of the
         removed continuation, or it remains in there after the garbage step; in
         the latter, either it had the removed continuation within its scope, or
         it hadn't. We proceed by case analysis.

        TODO: please, refactor the following code. I'm exhausted...
      *)
      rename b2 into b.
      edestruct tidy_context_case_analysis; eauto.
      * exists (bind b ts c); auto with cps.
      * rewrite H1.
        rewrite H2.
        rewrite compose_context_is_sound; simpl.
        eexists.
        --- apply rt_step.
            apply tidy_bind_left.
            apply tidy_context.
            apply tidy_gc.
            rewrite compose_context_bvars; simpl.
            edestruct not_free_context_split; eauto.
            simpl in H5.
            dependent destruction H5.
            apply not_free_context_merge; auto.
            rewrite Nat.add_comm.
            apply not_free_apply_parameters; auto.
            rewrite Nat.add_0_r.
            apply lifting_more_than_n_makes_not_free_n; lia.
        --- (* We gotta demonstrate that we indeed have a (CTXJMP) redex. *)
            unfold remove_binding.
            do 2 rewrite context_subst_is_sound.
            rewrite Nat.add_0_r.
            rewrite compose_context_bvars; simpl.
            assert (#h = #(compose_context r (context_left s us d)));
              try congruence.
            rewrite compose_context_bvars in H4.
            simpl in H4.
            rewrite subst_distributes_over_jump.
            rewrite subst_bound_gt; try lia.
            rewrite subst_distributes_over_apply_parameters.
            rewrite subst_lift_simplification; try lia.
            rewrite <- H4.
            do 2 rewrite <- compose_context_is_sound.
            remember (compose_context r (context_subst 0 0 s)) as t.
            assert (#t = #r + #s).
            +++ rewrite Heqt.
                rewrite compose_context_bvars.
                rewrite context_subst_bvars.
                reflexivity.
            +++ replace (pred #h) with #t; try lia.
                replace #h with (S #t); try lia.
                apply r_step.
                apply beta_ctxjmp.
                rewrite map_length.
                assumption.
      * rewrite H1.
        eexists (bind (compose_context r (context_left s us e) _) ts c).
        --- do 2 rewrite compose_context_is_sound; simpl.
            apply rt_step.
            apply tidy_bind_left.
            apply tidy_context.
            apply tidy_bind_right.
            assumption.
        --- rewrite compose_context_bvars; simpl.
            rewrite H2.
            remember (compose_context r (context_left s us e)) as t.
            assert (#h = #t).
            +++ rewrite H1.
                rewrite Heqt.
                do 2 rewrite compose_context_bvars; simpl.
                reflexivity.
            +++ rewrite H4.
                replace (#r + S #s) with #t.
                *** apply r_step.
                    apply beta_ctxjmp.
                    assumption.
                *** rewrite Heqt.
                    rewrite compose_context_bvars; simpl.
                    reflexivity.
      * rewrite H1.
        eexists (bind (compose_context r (context_right e us s) _) ts c).
        --- do 2 rewrite compose_context_is_sound; simpl.
            apply rt_step.
            apply tidy_bind_left.
            apply tidy_context.
            apply tidy_bind_left.
            assumption.
        --- rewrite compose_context_bvars; simpl.
            rewrite H2.
            remember (compose_context r (context_right e us s)) as t.
            assert (#h = #t).
            +++ rewrite H1.
                rewrite Heqt.
                do 2 rewrite compose_context_bvars; simpl.
                reflexivity.
            +++ rewrite H4.
                replace (#r + (#s + length us)) with #t.
                *** apply r_step.
                    apply beta_ctxjmp.
                    assumption.
                *** rewrite Heqt.
                    rewrite compose_context_bvars; simpl.
                    reflexivity.
    + (* The garbage collection step happens in the continuation to which a jump
         is being performed, so this means that we duplicate the garbage redex
         and must perform it twice. *)
      rename c into c1.
      exists (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c2)))
        ts c2); auto with cps.
      eapply rt_trans.
      * apply rt_step.
        apply tidy_bind_right.
        eassumption.
      * apply rt_step.
        apply tidy_bind_left.
        apply tidy_context.
        apply tidy_apply_parameters.
        apply tidy_lift.
        assumption.
  - dependent destruction H0.
    + (* The jump happens on the left, in which a continuation is removed. It is
         clearly the case that we can still remove it as a jump can't introduce
         a free variable. *)
      exists (remove_binding 0 b2).
      * apply rt_step.
        constructor.
        apply not_free_beta with b1; auto.
      * eauto with cps.
    + (* Both happen on the left, so follow by induction. *)
      edestruct IHbeta as (b4, ?, ?); eauto.
      exists (bind b4 ts c).
      * auto with cps.
      * destruct H2; auto with cps.
    + (* The jump happens on the left, and the garbage collection on the right,
         so this is easy. *)
      rename c into c1.
      exists (bind b2 ts c2).
      * auto with cps.
      * auto with cps.
  - dependent destruction H0.
    + (* The step happens in a removed continuation, so we can ignore it. *)
      exists (remove_binding 0 b).
      * auto with cps.
      * auto with cps.
    + (* The jump happens on the right, and the garbage collection on the left,
         so this is just like the one above. *)
      rename b into b1.
      exists (bind b2 ts c2).
      * auto with cps.
      * auto with cps.
    + (* Both happen on the right, so follow by induction. *)
      edestruct IHbeta as (c4, ?, ?); eauto.
      exists (bind b ts c4).
      * auto with cps.
      * destruct H2; auto with cps.
Qed.

Theorem step_is_confluent:
  confluent step.
Proof.
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
