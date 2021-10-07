(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.
Require Import Local.Reduction.
Require Import Local.AbstractRewriting.

(** ** Parallel reduction *)

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

(** ** Residuals *)

Inductive redexes: Set :=
  | redexes_term (e: pseudoterm)
  | redexes_jump (r: bool) (f: pseudoterm) (xs: list pseudoterm)
  | redexes_placeholder (f: pseudoterm) (xs: list pseudoterm)
  | redexes_bind (b: redexes) (ts: list pseudoterm) (c: redexes).

Fixpoint mark (e: pseudoterm): redexes :=
  match e with
  | jump f xs =>
    redexes_jump false f xs
  | bind b ts c =>
    redexes_bind (mark b) ts (mark c)
  | _ =>
    redexes_term e
  end.

Fixpoint unmark (e: redexes): pseudoterm :=
  match e with
  | redexes_term e =>
    e
  | redexes_jump r f xs =>
    jump f xs
  | redexes_placeholder f xs =>
    jump f xs
  | redexes_bind b ts c =>
    bind (unmark b) ts (unmark c)
  end.

Lemma unmark_mark_is_sound:
  forall e,
  unmark (mark e) = e.
Proof.
  induction e; simpl; auto.
  rewrite IHe1, IHe2; auto.
Qed.

Fixpoint redexes_lift i k e: redexes :=
  match e with
  | redexes_term e =>
    redexes_term (lift i k e)
  | redexes_jump r f xs =>
    redexes_jump r (lift i k f) (map (lift i k) xs)
  | redexes_placeholder f xs =>
    redexes_placeholder (lift i k f) (map (lift i k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_lift i (S k) b)
      (traverse_list (lift i) k ts)
      (redexes_lift i (k + length ts) c)
  end.

Fixpoint redexes_subst y k e: redexes :=
  match e with
  | redexes_term e =>
    redexes_term (subst y k e)
  | redexes_jump r f xs =>
    redexes_jump r (subst y k f) (map (subst y k) xs)
  | redexes_placeholder f xs =>
    redexes_placeholder (subst y k f) (map (subst y k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_subst y (S k) b)
      (traverse_list (subst y) k ts)
      (redexes_subst y (k + length ts) c)
  end.

Fixpoint redexes_apply_parameters ys k e: redexes :=
  match ys with
  | [] => e
  | y :: ys => redexes_apply_parameters ys k (redexes_subst y (k + length ys) e)
  end.

Fixpoint redexes_flow y a k e: redexes :=
  match e with
  | redexes_placeholder (bound n) xs =>
    if Nat.eq_dec n k then
      if Nat.eq_dec a (length xs) then
        redexes_apply_parameters xs 0
          (redexes_lift (S n) (length xs) y)
      else
        e
    else
      e
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_flow y a (S k) b)
      ts
      (redexes_flow y a (k + length ts) c)
  | _ =>
    e
  end.

Lemma redexes_lift_lift_permutation:
  forall e i j k l,
  k <= l ->
  redexes_lift i k (redexes_lift j l e) =
    redexes_lift j (i + l) (redexes_lift i k e).
Proof.
  admit.
Admitted.

Lemma redexes_lift_distributes_over_apply_parameters:
  forall ys i k e,
  redexes_lift i k (redexes_apply_parameters ys 0 e) =
  redexes_apply_parameters (map (lift i k) ys) 0
    (redexes_lift i (length ys + k) e).
Proof.
  admit.
Admitted.

Lemma redexes_lift_addition_distributes_over_flow:
  forall b i k p a c,
  redexes_lift i (p + S k) (redexes_flow c a p b) =
    redexes_flow (redexes_lift i (k + a) c) a p (redexes_lift i (p + S k) b).
Proof.
  induction b; simpl; intros.
  - reflexivity.
  - reflexivity.
  - destruct f; try reflexivity.
    destruct (Nat.eq_dec n p).
    + rewrite lift_bound_lt; try lia.
      rewrite map_length.
      destruct (Nat.eq_dec a (length xs)).
      * destruct (Nat.eq_dec n p); try lia.
        rewrite redexes_lift_distributes_over_apply_parameters.
        f_equal; symmetry.
        rewrite redexes_lift_lift_permutation; try lia.
        f_equal; lia.
      * destruct (Nat.eq_dec n p); try lia.
        simpl.
        rewrite lift_bound_lt; try lia.
        reflexivity.
    + destruct (le_gt_dec (p + S k) n).
      * rewrite lift_bound_ge; try lia.
        destruct (Nat.eq_dec (i + n) p); try lia.
        simpl.
        rewrite lift_bound_ge; try lia.
        reflexivity.
      * rewrite lift_bound_lt; try lia.
        destruct (Nat.eq_dec n p); try lia.
        simpl.
        rewrite lift_bound_lt; try lia.
        reflexivity.
  - f_equal.
    + replace (S (p + S k)) with (S p + S k); try lia.
      apply IHb1.
    + rewrite traverse_list_length.
      replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHb2.
Qed.

Lemma redexes_lift_distributes_over_flow:
  forall b i k a c,
  redexes_lift i (S k) (redexes_flow c a 0 b) =
    redexes_flow (redexes_lift i (k + a) c) a 0 (redexes_lift i (S k) b).
Proof.
  intros.
  apply redexes_lift_addition_distributes_over_flow with (p := 0).
Qed.

Inductive residuals: redexes -> redexes -> redexes -> Prop :=
  | residuals_jump:
    forall r k xs,
    residuals
      (redexes_jump r k xs)
      (redexes_jump false k xs)
      (redexes_jump r k xs)
  | residuals_mark:
    forall r n xs,
    residuals
      (redexes_jump r (bound n) xs)
      (redexes_jump true (bound n) xs)
      (redexes_placeholder n xs)
  | residuals_placeholder:
    forall n xs,
    residuals
      (redexes_placeholder (bound n) xs)
      (redexes_placeholder (bound n) xs)
      (redexes_placeholder (bound n) xs)
  | residuals_bind:
    forall b1 b2 b3 ts c1 c2 c3,
    residuals b1 b2 b3 ->
    residuals c1 c2 c3 ->
    residuals
      (redexes_bind b1 ts c1)
      (redexes_bind b2 ts c2)
      (redexes_bind (redexes_flow c3 (length ts) 0 b3) ts c3).

Lemma residuals_is_unique:
  forall a b c1,
  residuals a b c1 ->
  forall c2,
  residuals a b c2 -> c1 = c2.
Proof.
  induction 1; intros.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H1.
    replace b5 with b3; auto.
    replace c5 with c3; auto.
Qed.

Lemma residuals_lift:
  forall a b c,
  residuals a b c ->
  forall i k,
  residuals (redexes_lift i k a) (redexes_lift i k b) (redexes_lift i k c).
Proof.
  induction 1; intros.
  - simpl.
    constructor.
  - simpl.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      constructor.
    + rewrite lift_bound_lt; auto.
      constructor.
  - simpl.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      constructor.
    + rewrite lift_bound_lt; auto.
      constructor.
  - simpl.
    rewrite redexes_lift_distributes_over_flow.
    replace (length ts) with (length (traverse_list (lift i) k ts)).
    + constructor.
      * apply IHresiduals1.
      * apply IHresiduals2.
    + apply traverse_list_length.
Qed.

Lemma residuals_flow_inversion:
  forall b1 b2 a k c1 c2 c3 e,
  residuals c1 c2 c3 ->
  residuals (redexes_flow c1 a k b1) (redexes_flow c2 a k b2) e ->
  exists b3,
  residuals b1 b2 b3.
Proof.
  admit.
Admitted.

Lemma cube:
  forall a r b,
  residuals a r b ->
  forall p c,
  residuals a p c ->
  forall rp,
  residuals r p rp ->
  forall pr,
  residuals p r pr ->
  forall d,
  residuals b pr d -> residuals c rp d.
Proof.
  induction 1; inversion_clear 1; intros.
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  - dependent destruction H1.
    dependent destruction H4.
    dependent destruction H5.
    rename b9 into x.
    (* Reconstruct our b9 term, which should exist... *)
    edestruct residuals_flow_inversion as (b9, ?); eauto.
    (* By the first inductive hypothesis... *)
    assert (residuals b5 b7 b9); eauto.
    (* By the second inductive hypothesis... *)
    assert (residuals c5 c7 c9); eauto.
    (* Proceed to build the item. *)
    constructor; auto.
    (* Invert x in H5_, then by subst lemma. *)
    admit.
Admitted.

(** ** Confluency *)

(* TODO: can't seem to finish the proof below as it is, the induction seems too
   weak... it should be possible to use the cube lemma to finish it, though. *)

Lemma parallel_is_confluent:
  confluent parallel.
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

Lemma transitive_parallel_is_confluent:
  confluent t(parallel).
Proof.
  apply transitive_closure_preserves_confluency.
  exact parallel_is_confluent.
Qed.

Lemma transitive_parallel_and_star_are_equivalent:
  forall a b,
  [a =>* b] <-> t(parallel) a b.
Proof.
  split; induction 1; eauto with cps.
Qed.

Theorem star_is_confluent:
  confluent star.
Proof.
  compute; intros.
  (* We apply a simple strip lemma here. *)
  destruct transitive_parallel_is_confluent with x y z as (w, ?, ?).
  - apply transitive_parallel_and_star_are_equivalent; auto.
  - apply transitive_parallel_and_star_are_equivalent; auto.
  - exists w.
    + apply transitive_parallel_and_star_are_equivalent; auto.
    + apply transitive_parallel_and_star_are_equivalent; auto.
Qed.

Corollary step_is_church_rosser:
  church_rosser step.
Proof.
  compute; intros.
  apply confluency_implies_church_rosser; auto.
  exact star_is_confluent.
Qed.
