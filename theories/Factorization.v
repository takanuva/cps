(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.AbstractRewriting.
Require Import Local.Axiomatic.
Require Import Local.Reduction.
Require Import Local.Residuals.
Require Import Local.Confluence.

(* The following method is present on the "Factorization and Normalization,
   Essentially" paper, and was hinted to me by dr. Accattoli through private
   communication. This seems way simpler than what I was trying to do. *)

Inductive full: relation pseudoterm :=
  | full_ctxjmp:
    CTXJMP full
  (* | full_gc:
    GC full *)
  | full_bind_left:
    LEFT full
  | full_bind_right:
    RIGHT full.

Local Hint Constructors full: cps.

Lemma full_step:
  inclusion step full.
Proof.
  induction 1; eauto with cps.
Qed.

Local Hint Resolve full_step: cps.

Lemma rt_full_star:
  inclusion star rt(full).
Proof.
  induction 1; eauto with cps.
Qed.

Inductive inner: relation pseudoterm :=
  | inner_nonstatic_ctxjmp:
    (* TODO: move to a proper abstract rule. Perhaps (NONSTATIC_CTXJMP)? *)
    forall h xs ts c,
    nonstatic h ->
    length xs = length ts ->
    inner (bind (h (jump #h xs)) ts c)
      (bind
         (h (apply_parameters xs 0 (lift (S #h) (length ts) c)))
         ts c)
  (* | inner_gc:
    GC inner *)
  | inner_bind_left:
    LEFT inner
  | inner_bind_right:
    forall b ts c1 c2,
    full c1 c2 -> inner (bind b ts c1) (bind b ts c2).

Lemma full_characterization:
  same_relation full (union head inner).
Proof.
  split; unfold inclusion; intros.
  - induction H.
    + destruct context_static_nonstatic_dec with h.
      * left.
        apply head_longjmp with (r := context_hole); auto with cps.
      * right.
        constructor; auto.
    (* + right.
      constructor; auto. *)
    + destruct IHfull.
      * left.
        apply head_bind_left; auto.
      * right.
        constructor; auto.
    + right.
      constructor; auto.
  - destruct H.
    + destruct H.
      induction H0; simpl.
      * constructor; auto.
      * constructor; auto.
    + induction H.
      * constructor; auto.
      (* * constructor; auto. *)
      * constructor; auto.
      * constructor; auto.
Qed.

(* Hindley's local postponement lemma. *)

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

Axiom parallel_inner: relation pseudoterm.

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
  inclusion rt(full) (comp rt(head) rt(inner)).
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
      induction H0; eauto with cps.
      apply full_characterization in H.
      destruct H; auto with cps.
    + apply rt_inner_and_rt_parallel_inner_are_equivalent in H2.
      eauto with cps.
Qed.

Goal
  same_relation rt(full) (comp rt(head) rt(inner)).
Proof.
  split.
  - apply factorization.
  - (* This could be shown in the confluence file. *)
    intros x z ?.
    destruct H as (y, ?, ?).
    apply clos_rt_rt1n_iff in H.
    induction H; intros.
    + induction H0.
      * apply rt_step.
        induction H; auto with cps.
      * auto with cps.
      * eauto with cps.
    + apply clos_rt_rt1n_iff in H1.
      apply rt_trans with y.
      * clear H0 H1 IHclos_refl_trans_1n.
        apply rt_step.
        destruct H.
        induction H0; auto with cps.
      * firstorder.
Qed.
