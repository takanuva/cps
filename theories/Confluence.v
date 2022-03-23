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

(* Keep the following as a backup; TODO: either fix it or remove it later.

(* I believe this is the smallest relation to be a valid notion of parallel
   reduction within the CPS-calculus... should check it later.

   NOTE: this relation seems broken. While residuals allow us to duplicate
   marks, we simply ignore duplicated jumps in the following instead of doing
   them as well. TODO: could we fix that by making R a multi-hole context and
   reducing copied jumps as well? *)

Inductive parallel: relation pseudoterm :=
  | parallel_refl:
    forall e,
    parallel e e
  | parallel_ctxjmp:
    forall h r xs ts c1 c2,
    same_path h r ->
    length xs = length ts ->
    (* Expect H and R to have the same hole to avoid reducing a copied jump. *)
    parallel (h (jump #h xs)) (r (jump #r xs)) ->
    parallel c1 c2 ->
    parallel (bind (h (jump #h xs)) ts c1)
      (bind (r (apply_parameters xs 0 (lift (S #r) (length ts) c2))) ts c2)
  | parallel_bind:
    forall b1 b2 ts c1 c2,
    parallel b1 b2 -> parallel c1 c2 ->
    parallel (bind b1 ts c1) (bind b2 ts c2).

Global Hint Constructors parallel: cps.

Lemma parallel_step:
  forall a b,
  [a => b] -> parallel a b.
Proof.
  induction 1.
  - eapply parallel_ctxjmp; auto.
    + apply same_path_refl.
    + apply parallel_refl.
    + apply parallel_refl.
  - apply parallel_bind; auto.
    apply parallel_refl.
  - apply parallel_bind; auto.
    apply parallel_refl.
Qed.

Global Hint Resolve parallel_step: cps.

Lemma star_parallel:
  forall a b,
  parallel a b -> [a =>* b].
Proof.
  induction 1.
  - apply star_refl.
  - eapply star_trans.
    + apply star_bind_left.
      eassumption.
    + eapply star_trans.
      * apply star_bind_right.
        eassumption.
      * apply star_ctxjmp.
        assumption.
  - eapply star_trans.
    + apply star_bind_left.
      eassumption.
    + apply star_bind_right.
      assumption.
Qed.

Global Hint Resolve star_parallel: cps.

Lemma parallel_lift:
  forall a b,
  parallel a b ->
  forall i k,
  parallel (lift i k a) (lift i k b).
Proof.
  induction 1; intros.
  - apply parallel_refl.
  - admit.
  - do 2 rewrite lift_distributes_over_bind.
    apply parallel_bind; auto.
Admitted.

Lemma parallel_subst:
  forall a b,
  parallel a b ->
  forall x k,
  parallel (subst x k a) (subst x k b).
Proof.
  induction 1; intros.
  - apply parallel_refl.
  - admit.
  - do 2 rewrite subst_distributes_over_bind.
    apply parallel_bind; auto.
Admitted.

Lemma parallel_apply_parameters:
  forall xs k a b,
  parallel a b ->
  parallel (apply_parameters xs k a) (apply_parameters xs k b).
Proof.
  induction xs; simpl; intros.
  - assumption.
  - apply IHxs.
    apply parallel_subst; auto.
Qed.

Lemma parallel_context:
  forall h: context,
  forall a b,
  parallel a b -> parallel (h a) (h b).
Proof.
  induction h; simpl; intros.
  - assumption.
  - apply parallel_bind; auto.
    apply parallel_refl.
  - apply parallel_bind; auto.
    apply parallel_refl.
Qed.

Lemma parallel_noninterference:
  forall h: context,
  forall n,
  n >= #h ->
  forall xs e,
  parallel (h (jump n xs)) e ->
  exists2 r: context,
  e = r (jump n xs) & same_path h r.
Proof.
  intros.
  apply star_parallel in H0.
  induction H0 using clos_refl_trans_ind_left.
  - exists h; auto with cps.
  - destruct IHclos_refl_trans.
    rewrite H2 in H1.
    destruct step_noninterference with x n xs z.
    + replace #x with #h; auto with cps.
    + assumption.
    + eauto with cps.
Qed.

(** ** Confluence *)

(* TODO: can't seem to finish the proof below as it is, the induction seems too
   weak... it should be possible to use the cube lemma to finish it, though. *)

Lemma parallel_has_diamond:
  diamond parallel.
Proof.
  induction 1; unfold transp; intros.
  - exists z.
    + assumption.
    + apply parallel_refl.
  - dependent destruction H3.
    + eexists (bind (r _) ts c2).
      * apply parallel_refl.
      * apply parallel_ctxjmp; auto.
    + unfold transp in * |- *.
      rename h0 into s, r0 into t, xs0 into ys.
      destruct context_eq_dec with h s.
      * destruct e.
        apply context_is_injective in x; auto.
        dependent destruction x.
        destruct IHparallel1 with (t (jump #t xs)) as (b, ?H, ?H); auto.
        destruct IHparallel2 with c3 as (c4, ?H, ?H); auto.
        destruct parallel_noninterference with r #r xs b as (u, ?H, ?H); auto.
        dependent destruction H9.
        (* Can we use multicontexts to fix H5 and H6??? *)
        replace #r with #u in H5 at 2, H6; auto with cps.
        (* I strongly assume that both r and t copy the hole the same way. *)
        admit.
      * admit.
    + unfold transp in *.
      admit.
  - dependent destruction H1.
    + exists (bind b2 ts c2).
      * apply parallel_refl.
      * apply parallel_bind; auto.
    + unfold transp in *.
      destruct IHparallel1 with (r (jump #r xs)) as (b3, ?, ?); auto.
      destruct IHparallel2 with c3 as (c4, ?, ?); auto.
      destruct parallel_noninterference with h #h xs b2 as (s, ?, ?); auto.
      dependent destruction H7.
      replace #h with #s in H3; auto with cps.
      destruct parallel_noninterference with s #s xs b3 as (t, ?, ?); auto.
      dependent destruction H7.
      admit.
    + destruct IHparallel1 with b3 as (b4, ?, ?); auto.
      destruct IHparallel2 with c3 as (c4, ?, ?); auto.
      eexists (bind b4 ts c4); auto with cps.
Admitted.
*)

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

Lemma parallel_step:
  forall a b,
  [a => b] -> parallel a b.
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
  (* Case: step_gc. *)
  - (* TODO: as of now, can't be proven. Fix this! *)
    admit.
  (* Case: step_eta. *)
  - (* TODO: as of now, can't be proven. Fix this! *)
    admit.
  (* Case: step_bind_left. *)
  - destruct IHstep as (p, (b2', ?, ?), ?).
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
  - destruct IHstep as (p, (c2', ?, ?), ?).
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
Admitted.

Global Hint Resolve parallel_step: cps.

Lemma star_parallel:
  forall a b,
  parallel a b -> [a =>* b].
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
    apply star_trans with (bind a1 ts1 b4).
    + apply star_bind_right.
      eapply IHr2; eauto.
    + assert (exists n, redexes_mark_count 0 r1 = n) as (n, ?); eauto.
      destruct n.
      * clear H.
        apply star_bind_left.
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
        eapply star_trans.
        --- apply star_ctxjmp.
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

Global Hint Resolve star_parallel: cps.

(* ** Confluence *)

Lemma parallel_has_diamond:
  diamond parallel.
Proof.
  unfold diamond, commut, transp; intros.
  destruct H as (r, (x', ?, ?), ?).
  destruct H0 as (p, (y', ?, ?), ?).
  destruct paving with (mark y) r x' p y' as (pr, rp, w, ?, ?, ?, ?); auto.
  assert (regular [] pr); eauto with cps.
  assert (regular [] rp); eauto with cps.
  assert (regular [] x'); eauto with cps.
  assert (regular [] y'); eauto with cps.
  (* We know the development of w has no marks! *)
  assert (redexes_mark_count_total (redexes_full w) = 0).
  - apply residuals_full_preserve_no_mark with (redexes_full pr) (mark x).
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
  apply transitive_closure_preserves_diamond.
  exact parallel_has_diamond.
Qed.

Lemma transitive_parallel_and_star_are_equivalent:
  same_relation t(parallel) star.
Proof.
  split; induction 1; eauto with cps.
Qed.

Theorem step_is_confluent:
  confluent step.
Proof.
  compute; intros.
  (* We apply a simple strip lemma here. *)
  destruct transitive_parallel_has_diamond with x y z as (w, ?, ?).
  - apply transitive_parallel_and_star_are_equivalent.
    assumption.
  - apply transitive_parallel_and_star_are_equivalent.
    assumption.
  - exists w.
    + apply transitive_parallel_and_star_are_equivalent.
      assumption.
    + apply transitive_parallel_and_star_are_equivalent.
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
