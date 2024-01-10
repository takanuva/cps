(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Relations.
Require Import Local.Prelude.
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

(* Hindley's local postponement lemma. TODO: move me. *)

Lemma local_postponement:
  forall {T} (R S: relation T),
  inclusion (comp S R) (comp rt(R) r(S)) ->
  inclusion rt(union R S) (comp rt(R) rt(S)).
Proof.
  intros.
  (* Let us slightly change our hypothesis. *)
  assert (inclusion (comp S rt(R)) (comp rt(R) r(S))).
  - unfold inclusion; intros.
    rename y into z.
    destruct H0 as (y, ?, ?).
    generalize dependent x.
    (* For some reason I can't use clos_refl_trans_ind_right... *)
    apply clos_rt_rt1n_iff in H1.
    induction H1; intros w ?.
    + exists w; auto with cps.
    + apply clos_rt_rt1n_iff in H1.
      destruct H with w y as (v, ?, ?); eauto with cps.
      destruct H4.
      * destruct IHclos_refl_trans_1n with v as (u, ?, ?); auto.
        exists u; eauto with cps.
      * exists z; eauto with cps.
  - clear H; rename H0 into H.
    (* Now we can proceed into the proof. *)
    intros x y ?.
    (* Same thing as above! *)
    apply clos_rt_rt1n_iff in H0.
    induction H0.
    + exists x; auto with cps.
    + apply clos_rt_rt1n_iff in H1.
      destruct H0.
      * destruct IHclos_refl_trans_1n as (w, ?, ?).
        exists w; eauto with cps.
      * destruct IHclos_refl_trans_1n as (w, ?, ?).
        destruct H with x w as (v, ?, ?); eauto with cps.
        apply clos_r_clos_rt in H5.
        exists v; eauto with cps.
Qed.

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

(* Notice that we are not assuming that parallel inner reduction has at least
   one mark as we do in the standard parallel reduction, mostly because there's
   no need to. We could, of course, do it anyways. *)

Definition parallel_inner: relation pseudoterm :=
  fun b c =>
    exists2 r,
    residuals [] (mark b) r (mark c) & leftmost_marked false r.

Conjecture inner_parallel_inner:
  inclusion inner parallel_inner.

Local Hint Resolve inner_parallel_inner: cps.

Conjecture parallel_inner_rt_inner:
  inclusion parallel_inner rt(inner).

Local Hint Resolve parallel_inner_rt_inner: cps.

Lemma rt_inner_and_rt_parallel_inner_are_equivalent:
  same_relation rt(inner) rt(parallel_inner).
Proof.
  split; induction 1; eauto with cps.
Qed.

Conjecture merge:
  inclusion (comp parallel_inner head) parallel.

(* This lemma will need to perform induction on the number of consecutive head
   jumps in a redex. If the redex is regular, this may be calculated, but it'll
   be somewhat annoying to formalize. *)

Conjecture split:
  inclusion parallel (comp rt(head) parallel_inner).

Theorem factorization:
  inclusion star (comp rt(head) rt(inner)).
Proof.
  assert (inclusion rt(union head parallel_inner)
    (comp rt(head) rt(parallel_inner))).
  - apply local_postponement.
    unfold inclusion; intros.
    destruct split with x y as (z, ?, ?).
    + apply merge; auto.
    + exists z; auto with cps.
  - unfold inclusion; intros.
    destruct H with x y as (z, ?, ?).
    + clear H.
      (* Relexive and transitive cases are trivial. *)
      induction H0; eauto with cps.
      (* TODO: fix me!

      (* Though we usually would argue that a step is either essential or not,
         this is not the case here due to eta reduction: there are cases in
         which a step should be split into a head reduction followed by an inner
         reduction. So we take another route here by using [split]. *)
      apply parallel_step in H.
      apply split in H.
      destruct H as (z, ?, ?).
      (* Now, this is clearly true. *)
      apply rt_trans with z.
      * clear H0 y.
        induction H; eauto with cps.
      * auto with cps.
      *)
      admit.
    + apply rt_inner_and_rt_parallel_inner_are_equivalent in H2.
      eauto with cps.
Admitted.

Corollary star_characterization:
  same_relation star (comp rt(head) rt(inner)).
Proof.
  split.
  - apply factorization.
  - intros x z ?.
    (* Clearly true. *)
    destruct H as (y, ?, ?).
    apply star_trans with y.
    + clear H0 z.
      induction H; eauto with cps.
    + clear H x.
      induction H0; eauto with cps.
Qed.
