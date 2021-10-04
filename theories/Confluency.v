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

(** ** Confluency *)

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
