(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.Equational.
Require Import Local.Reduction.

Import ListNotations.

Record shrinking (R: relation pseudoterm): Prop := {
  shrinking_termination:
    forall c,
    SN R c;
  shrinking_soundness:
    inclusion R sema;
  shrinking_confluence:
    confluent R;
  shrinking_commutation:
    commutes rt(beta) rt(R);
  shrinking_reordering:
    reorders beta R
}.

Lemma smol_decreases_in_size:
  forall b c,
  smol b c ->
  size b > size c.
Proof.
  intros.
  induction H; simpl.
  - rewrite remove_binding_size by auto.
    lia.
  - lia.
  - lia.
Qed.

Lemma smol_is_strongly_normalizing:
  forall b,
  SN smol b.
Proof.
  intros.
  remember (size b) as n.
  generalize dependent b.
  induction n using lt_wf_ind; intros.
  constructor; intros c ?.
  apply H with (size c).
  - rewrite Heqn.
    now apply smol_decreases_in_size.
  - reflexivity.
Qed.

Lemma smol_is_sound:
  inclusion smol sema.
Proof.
  induction 1.
  - apply sema_gc.
    assumption.
  - apply sema_bind_left.
    assumption.
  - apply sema_bind_right.
    assumption.
Qed.

Lemma smol_has_weak_diamond:
  forall x y,
  smol x y ->
  forall z,
  smol x z ->
  exists2 w,
  r(smol) y w & r(smol) z w.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    + exists (remove_binding 0 b).
      * auto with cps.
      * auto with cps.
    + rename b into b1.
      exists (remove_binding 0 b2).
      * apply r_step.
        apply smol_subst.
        assumption.
      * apply r_step.
        apply smol_gc.
        apply not_free_smol with b1; auto.
    + rename c into c1.
      exists (remove_binding 0 b).
      * auto with cps.
      * auto with cps.
  - dependent destruction H0.
    + clear IHsmol.
      exists (remove_binding 0 b2).
      * apply r_step.
        apply smol_gc.
        apply not_free_smol with b1; auto.
      * apply r_step.
        apply smol_subst.
        assumption.
    + edestruct IHsmol as (b4, ?, ?); eauto.
      exists (bind b4 ts c).
      * destruct H1; auto with cps.
      * destruct H2; auto with cps.
    + rename c into c1.
      exists (bind b2 ts c2).
      * auto with cps.
      * auto with cps.
  - dependent destruction H0.
    + clear IHsmol.
      exists (remove_binding 0 b).
      * auto with cps.
      * auto with cps.
    + rename b into b1.
      exists (bind b2 ts c2).
      * auto with cps.
      * auto with cps.
    + edestruct IHsmol as (c4, ?, ?); eauto.
      exists (bind b ts c4).
      * destruct H1; auto with cps.
      * destruct H2; auto with cps.
Qed.

Lemma smol_is_confluent:
  confluent smol.
Proof.
  apply diamond_for_same_relation with t(r(smol)).
  - apply transitive_closure_preserves_commutation.
    destruct 1; destruct 1; try rename y0 into z.
    + apply smol_has_weak_diamond with x; auto.
    + exists y; auto with cps.
    + exists y; auto with cps.
    + exists x; auto with cps.
  - split; intros x y ?.
    + apply rt_characterization.
      apply r_and_t_closures_commute.
      assumption.
    + apply r_and_t_closures_commute.
      apply rt_characterization.
      assumption.
Qed.

Inductive smol_context_case (h: context) k xs b: Prop :=
  | smol_context_case_inside:
    (forall c, smol (h c) b) ->
    smol_context_case h k xs b
  | smol_context_case_scope:
    forall r s us d,
    h = compose_context r (context_left s us d) ->
    b = r (remove_binding 0 (s (jump k xs))) ->
    not_free 0 (s (jump k xs)) ->
    smol_context_case h k xs b
  | smol_context_case_orthogonal1:
    forall r s us d e,
    h = compose_context r (context_left s us d) ->
    b = (compose_context r (context_left s us e)) (jump k xs) ->
    smol d e ->
    smol_context_case h k xs b
  | smol_context_case_orthogonal2:
    forall r s us d e,
    h = compose_context r (context_right d us s) ->
    b = (compose_context r (context_right e us s)) (jump k xs) ->
    smol d e ->
    smol_context_case h k xs b.

Local Lemma smol_context_case_analysis:
  forall (h: context) k xs b,
  smol (h (jump k xs)) b -> smol_context_case h k xs b.
Proof.
  induction h; simpl; intros.
  - inversion H.
  - dependent destruction H; simpl.
    + apply smol_context_case_scope with
        (r := context_hole) (s := h) (us := ts) (d := c); auto.
    + edestruct IHh; eauto; simpl.
      * apply smol_context_case_inside; eauto with cps.
      * apply smol_context_case_scope with
          (r := context_left r ts c) (s := s) (us := us) (d := d); simpl;
          congruence.
      * apply smol_context_case_orthogonal1 with
          (r := context_left r ts c) (s := s) (us := us) (d := d) (e := e);
          simpl; congruence.
      * apply smol_context_case_orthogonal2 with
          (r := context_left r ts c) (s := s) (us := us) (d := d) (e := e);
          simpl; congruence.
    + apply smol_context_case_orthogonal1 with
        (r := context_hole) (s := h) (us := ts) (d := c) (e := c2); auto.
  - dependent destruction H; simpl.
    + apply smol_context_case_inside; eauto with cps.
    + apply smol_context_case_orthogonal2 with
        (r := context_hole) (s := h) (us := ts) (d := b) (e := b2); auto.
    + edestruct IHh; eauto; simpl.
      * apply smol_context_case_inside; eauto with cps.
      * apply smol_context_case_scope with
          (r := context_right b ts r) (s := s) (us := us) (d := d); simpl;
          congruence.
      * apply smol_context_case_orthogonal1 with
          (r := context_right b ts r) (s := s) (us := us) (d := d) (e := e);
          simpl; congruence.
      * apply smol_context_case_orthogonal2 with
          (r := context_right b ts r) (s := s) (us := us) (d := d) (e := e);
          simpl; congruence.
Qed.

Lemma beta_and_smol_commute:
  commutes rt(beta) rt(smol).
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
      edestruct smol_context_case_analysis; eauto.
      * exists (bind b ts c); auto with cps.
      * rewrite H1.
        rewrite H2.
        rewrite compose_context_is_sound; simpl.
        eexists.
        --- apply rt_step.
            apply smol_bind_left.
            apply smol_context.
            apply smol_gc.
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
            apply smol_bind_left.
            apply smol_context.
            apply smol_bind_right.
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
            apply smol_bind_left.
            apply smol_context.
            apply smol_bind_left.
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
        apply smol_bind_right.
        eassumption.
      * apply rt_step.
        apply smol_bind_left.
        apply smol_context.
        apply smol_apply_parameters.
        apply smol_lift.
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

(*

(* TODO: some cleanup here would be nice. *)

Lemma transp_smol_bind_left:
  LEFT (transp smol).
Proof.
  intros b1 b2 ts c ?.
  apply smol_bind_left.
  assumption.
Qed.

Global Hint Resolve transp_smol_bind_left: cps.

Lemma transp_smol_bind_right:
  RIGHT (transp smol).
Proof.
  intros b1 b2 ts c ?.
  apply smol_bind_right.
  assumption.
Qed.

Global Hint Resolve transp_smol_bind_right: cps.

Lemma rt_transp_smol_bind_left:
  LEFT rt(transp smol).
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve rt_transp_smol_bind_left: cps.

Lemma rt_transp_smol_bind_right:
  RIGHT rt(transp smol).
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve rt_transp_smol_bind_right: cps.

Theorem smol_postponement:
  postpones beta smol.
Proof.
  intros y z ? x ?.
  generalize dependent z.
  induction H0; intros.
  (* Case: gc. *)
  - dependent destruction H0.
    + (* This case is simple, it's just a matter of inverting the order of the
         reductions, by using a single step on each side. Let's just tidy this
         a bit... *)
      destruct b; try destruct n; try discriminate.
      (* TODO: should we make a remove_binding_distributes_over_bind? *)
      unfold remove_binding in x.
      rewrite subst_distributes_over_bind in x.
      dependent destruction x.
      rename ts1 into ts, ts into us, b1 into b, b2 into c, c into d.
      (* Hmm... *)
      assert (b = lift 1 1 (h (jump #h xs))).
      * rewrite x.
        (* Yeah, this is the case! Should I have a lemma for this? *)
        admit.
      * rewrite H1.
        rewrite context_lift_is_sound.
        admit.
    + admit.
    + admit.
  (* Case: bind_left. *)
  - dependent destruction H.
    + admit.
    + edestruct IHsmol as (b4, ?, ?); eauto.
      exists (bind b4 ts c); auto with cps.
      admit.
    + rename c into c1.
      exists (bind b1 ts c2); auto with cps.
  (* Case: bind_right. *)
  - dependent destruction H.
    + admit.
    + rename b into b1.
      exists (bind b2 ts c1); auto with cps.
    + edestruct IHsmol as (c4, ?, ?); eauto.
      exists (bind b ts c4); auto with cps.
      admit.
Admitted.

*)

Lemma smol_may_be_reordered:
  reorders beta smol.
Proof.
  admit.
Admitted.

Theorem smol_is_shrinking:
  shrinking smol.
Proof.
  constructor.
  (* Case: termination. *)
  - apply smol_is_strongly_normalizing.
  (* Case: soundness. *)
  - apply smol_is_sound.
  (* Case: confluence. *)
  - apply smol_is_confluent.
  (* Case: commutation. *)
  - apply beta_and_smol_commute.
  (* Case: reordering. *)
  - apply smol_may_be_reordered.
Qed.

(* TODO: consider two other relations (tiny and itsy?) containing:
   - DCE and linear inlining
   - DCE, linear inlining, TCO, specialization, and some kind of floating

   It should be simple to show that the former is a shrinking reduction. The
   latter will require more work, as adding (ETA) complicates things, but I do
   believe that it should be enough to properly simulate the CBV translation
   then. Note that specialization and floating should mimick structural rules
   on linear proof nets. *)

Section Properties.

  Variable R: relation pseudoterm.

  Hypothesis shrinks: shrinking R.

  Theorem shrinking_preserves_confluence:
    confluent beta -> confluent (union beta R).
  Proof.
    intros.
    apply hindley_rosen.
    - assumption.
    - apply shrinking_confluence.
      assumption.
    - apply shrinking_commutation.
      assumption.
  Qed.

  Theorem shrinking_may_be_postponed:
    postpones beta R.
  Proof.
    apply reordering_implies_postponement.
    now apply shrinking_reordering.
  Qed.

  Theorem shrinking_preserves_strong_normalization:
    forall c,
    SN beta c <-> SN (union beta R) c.
  Proof.
    split; intros.
    - apply reordering_preserves_sn.
      + now apply shrinking_reordering.
      + now apply shrinking_termination.
      + assumption.
    - induction H using SN_ind.
      constructor; intros.
      apply H2; auto with cps.
  Qed.

End Properties.
