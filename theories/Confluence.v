(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
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

Definition parallel: relation pseudoterm :=
  fun a b =>
    exists2 r,
    residuals_full (mark a) r (mark b) & regular [] r.

Lemma parallel_refl:
  forall e,
  parallel e e.
Proof.
  intros.
  exists (mark e).
  - exists (mark e).
    + apply residuals_mark_term.
    + apply redexes_full_mark_equals_mark.
  - apply regular_mark_term.
Qed.

Global Hint Resolve parallel_refl: cps.

Lemma parallel_bind:
  forall b1 b2 ts c1 c2,
  parallel b1 b2 ->
  parallel c1 c2 ->
  parallel (bind b1 ts c1) (bind b2 ts c2).
Proof.
  intros.
  destruct H as (p, (b2', ?, ?), ?).
  destruct H0 as (r, (c2', ?, ?), ?).
  exists (redexes_bind p ts r); simpl.
  - eexists (redexes_bind b2' ts c2'); simpl.
    + constructor; auto.
    + rewrite H1, H3; f_equal.
      apply redexes_flow_mark_equals_mark.
  - constructor.
    + apply regular_tail with (g1 := []).
      assumption.
    + apply regular_tail with (g1 := []).
      assumption.
Qed.

Global Hint Resolve parallel_bind: cps.

Lemma parallel_bind_left:
  LEFT parallel.
Proof.
  unfold LEFT; intros.
  apply parallel_bind; auto with cps.
Qed.

Global Hint Resolve parallel_bind_left: cps.

Lemma parallel_bind_right:
  RIGHT parallel.
Proof.
  unfold RIGHT; intros.
  apply parallel_bind; auto with cps.
Qed.

Global Hint Resolve parallel_bind_right: cps.

Lemma parallel_beta:
  forall a b,
  beta a b -> parallel a b.
Proof.
  (* By induction on the step. *)
  unfold parallel; induction 1.
  (* Case: step_ctxjmp. *)
  - simpl.
    (* The context can't have any jumps in it. *)
    do 2 rewrite <- mark_context_is_sound; simpl.
    (* As the hole has a single jump, chose to mark only it. *)
    exists (redexes_bind (mark_context h (redexes_jump true #h xs))
      ts (mark c)).
    + (* The development will have a placeholder on its place. *)
      exists (redexes_bind (mark_context h (redexes_placeholder #h xs))
        ts (mark c)).
      * (* The only mark is sound. *)
        auto with cps.
      * (* And it's development results in our reduct. *)
        simpl.
        rewrite redexes_full_mark_equals_mark.
        f_equal.
        rewrite redexes_full_mark_context_simplification; auto.
        rewrite redexes_flow_mark_context_simplification.
        f_equal; simpl.
        destruct (Nat.eq_dec #h #h); try lia.
        destruct (Nat.eq_dec (length ts) (length xs)); try lia.
        rewrite redexes_lift_is_sound.
        rewrite redexes_apply_parameters_is_sound.
        rewrite H; reflexivity.
    + (* Clearly the single jump is also regular. *)
      constructor.
      * rewrite <- H.
        apply regular_single_jump with (g := []).
      * apply regular_mark_term.
  (* Case: step_bind_left. *)
  - destruct IHbeta as (p, (b2', ?, ?), ?).
    (* As there's a single mark, on the left, use it. *)
    exists (redexes_bind p ts (mark c)); simpl.
    + (* We know which will be the development. *)
      exists (redexes_bind b2' ts (mark c)); simpl.
      * constructor; auto with cps.
      * rewrite H1.
        f_equal; auto with cps.
        rewrite redexes_flow_mark_equals_mark; auto.
    + constructor.
      * eapply regular_tail in H2; eauto.
      * apply regular_mark_term.
  (* Case: step_bind_right. *)
  - destruct IHbeta as (p, (c2', ?, ?), ?).
    (* As there's a single mark, on the right, use it. *)
    exists (redexes_bind (mark b) ts p); simpl.
    + (* Same thing as above, but on the right. *)
      exists (redexes_bind (mark b) ts c2'); simpl.
      * constructor; auto with cps.
      * rewrite H1.
        f_equal; auto with cps.
        rewrite redexes_full_mark_equals_mark; auto.
        rewrite redexes_flow_mark_equals_mark; auto.
    + constructor.
      * apply regular_mark_term.
      * eapply regular_tail in H2; eauto.
Qed.

Global Hint Resolve parallel_beta: cps.

Lemma rt_beta_parallel:
  forall a b,
  parallel a b -> rt(beta) a b.
Proof.
  intros.
  destruct H as (r, (b', ?, ?), ?).
  generalize a b b' H H0 H1; clear a b b' H H0 H1.
  induction r using redexes_structural_mark_ind; intros.
  (* Case: type. *)
  - dependent destruction H.
    destruct a;
    destruct b;
    try discriminate;
    auto with cps.
  (* Case: prop. *)
  - dependent destruction H.
    destruct a;
    destruct b;
    try discriminate;
    auto with cps.
  (* Case: base. *)
  - dependent destruction H.
    destruct a;
    destruct b;
    try discriminate;
    auto with cps.
  (* Case: void. *)
  - dependent destruction H.
    destruct a;
    destruct b;
    try discriminate;
    auto with cps.
  (* Case: bound. *)
  - dependent destruction H.
    destruct a;
    destruct b;
    try discriminate;
    dependent destruction H0;
    auto with cps.
  (* Case: negation. *)
  - dependent destruction H.
    destruct a;
    destruct b;
    try discriminate;
    dependent destruction H0;
    auto with cps.
  (* Case: jump. *)
  - dependent destruction H.
    + destruct a; try discriminate.
      destruct b; try discriminate.
      dependent destruction H0.
      auto with cps.
    + exfalso.
      inversion H1.
      inversion H4.
  (* Case: placeholder. *)
  - exfalso.
    dependent destruction H.
    destruct a; discriminate.
  (* Case: bind. *)
  - dependent destruction H0.
    destruct a; try discriminate.
    destruct b; try discriminate.
    dependent destruction x.
    dependent destruction H1.
    dependent destruction H2.
    rewrite app_nil_r in H2_0.
    apply regular_ignore_unused_tail with (g := []) in H2_0.
    apply rt_trans with (bind a1 ts1 b4).
    + apply rt_beta_bind_right.
      eapply IHr2; eauto.
    + assert (exists n, redexes_mark_count 0 r1 = n) as (n, ?); eauto.
      destruct n.
      * clear H.
        apply rt_beta_bind_left.
        (* TODO: refactor me please. *)
        apply regular_ignore_unmarked_tail with (g := []) in H2_; auto.
        eapply IHr1; eauto.
        eapply redexes_flow_ignore_unused_mark; eauto.
        eapply regular_doesnt_jump_to_free_vars.
        --- eapply redexes_full_preserves_regular.
            eapply residuals_preserve_regular; eauto.
            apply regular_mark_term.
        --- simpl; lia.
      * (* TODO: refactor this mess please! *)
        edestruct positive_mark_count_implies_context with (k := 0) (b := r1)
          as (h, (s, (xs, ?))); eauto; try lia.
        simpl in H1.
        destruct H1 as (?, (?, ?)).
        dependent destruction H2.
        dependent destruction H3.
        (* ... *)
        rewrite <- mark_context_is_sound in H0_.
        edestruct residuals_preserve_hole as (t, (e, (?, (?, ?)))); eauto.
        dependent destruction H3.
        dependent destruction H4.
        eapply rt_trans.
        --- apply rt_step.
            apply beta_ctxjmp.
            eapply regular_jump_imply_correct_arity with (g := []);
              simpl; eauto.
            f_equal; apply mark_context_bvars_and_path_are_sound; auto.
        --- eapply H with (x := redexes_bind (s (mark _)) _ (mark b4)); simpl.
            +++ rewrite redexes_mark_count_total_mark_is_zero.
                rewrite Nat.add_0_r.
                apply Nat.lt_lt_add_r.
                apply redexes_mark_count_total_lt_context.
                rewrite redexes_mark_count_total_mark_is_zero.
                simpl; auto.
            +++ constructor.
                *** rewrite <- mark_context_is_sound.
                    eapply residuals_replacing_hole; eauto.
                    apply residuals_mark_term.
                *** apply residuals_mark_term.
            +++ simpl; f_equal.
                *** symmetry in x0; destruct x0.
                    rewrite redexes_full_mark_equals_mark.
                    apply mark_context_bvars_and_path_are_sound in H1.
                    apply mark_context_bvars_and_path_are_sound in H2.
                    apply regular_jump_imply_correct_arity
                      with (g := []) in H2_; auto.
                    rewrite <- H2_ in x |- *.
                    apply redexes_flow_preserved_by_single_unmarked_jump; auto.
                *** apply redexes_full_mark_equals_mark.
            +++ constructor.
                *** eapply regular_preserved_replacing_jump_by_mark
                      with (g := []); eauto.
                    simpl; f_equal.
                    apply mark_context_bvars_and_path_are_sound; auto.
                *** apply regular_mark_term.
Qed.

Global Hint Resolve rt_beta_parallel: cps.

(* ** Confluence *)

Lemma parallel_has_diamond:
  diamond parallel.
Proof.
  unfold diamond, commutes; intros.
  destruct H as (r, (x', ?, ?), ?).
  destruct H0 as (p, (y', ?, ?), ?).
  destruct paving with (mark x) r x' p y' as (pr, rp, w, ?, ?, ?, ?); auto.
  assert (regular [] pr); eauto with cps.
  assert (regular [] rp); eauto with cps.
  assert (regular [] x'); eauto with cps.
  assert (regular [] y'); eauto with cps.
  (* We know the development of w has no marks! *)
  assert (redexes_mark_count_total (redexes_full w) = 0).
  - apply residuals_full_preserve_no_mark with (redexes_full pr) (mark y).
    + auto with cps.
    + apply redexes_mark_count_total_mark_is_zero.
    + rewrite <- H1.
      eapply residuals_partial_full_application; eauto.
      exists w; auto.
  - exists (unmark (redexes_full w)).
    + exists (redexes_full pr); auto with cps.
      rewrite <- H1.
      eapply residuals_partial_full_application; eauto.
      exists w; auto.
      rewrite <- mark_unmark_is_sound_given_no_marks; auto.
    + exists (redexes_full rp); auto with cps.
      rewrite <- H3.
      eapply residuals_partial_full_application; eauto.
      exists w; auto.
      rewrite <- mark_unmark_is_sound_given_no_marks; auto.
Qed.

Lemma transitive_parallel_has_diamond:
  diamond t(parallel).
Proof.
  apply transitive_closure_preserves_commutation.
  exact parallel_has_diamond.
Qed.

Lemma transitive_parallel_and_rt_beta_are_equivalent:
  same_relation t(parallel) rt(beta).
Proof.
  split; induction 1; eauto with cps.
Qed.

Lemma beta_is_confluent:
  confluent beta.
Proof.
  compute; intros.
  (* We apply a simple strip lemma here. *)
  destruct transitive_parallel_has_diamond with x y z as (w, ?, ?).
  - apply transitive_parallel_and_rt_beta_are_equivalent.
    assumption.
  - apply transitive_parallel_and_rt_beta_are_equivalent.
    assumption.
  - exists w.
    + apply transitive_parallel_and_rt_beta_are_equivalent.
      assumption.
    + apply transitive_parallel_and_rt_beta_are_equivalent.
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
  - (* Oh boy... it's the same relation, but we gotta convince Coq. *)
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

Lemma rt_beta_and_rt_tidy_commute:
  commutes rt(beta) rt(tidy).
Proof.
  apply strong_commutation_implies_commutation.
  induction 1; intros.
  - dependent destruction H0.
    + (* This can't happen! *)
      exfalso.
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
    + (* This might be the worst case. We are performing a jump which resides
         in a context which has a garbage collection step. It might be the case
         that the garbage includes or not the jump. *)
      admit.
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
    + admit.
    + edestruct IHbeta as (b4, ?, ?); eauto.
      exists (bind b4 ts c).
      * auto with cps.
      * destruct H2; auto with cps.
    + rename c into c1.
      exists (bind b2 ts c2).
      * auto with cps.
      * auto with cps.
  - dependent destruction H0.
    + admit.
    + rename b into b1.
      exists (bind b2 ts c2).
      * auto with cps.
      * auto with cps.
    + edestruct IHbeta as (c4, ?, ?); eauto.
      exists (bind b ts c4).
      * auto with cps.
      * destruct H2; auto with cps.
Admitted.

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
