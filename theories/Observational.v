(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Equality.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Axiomatic.
Require Import Local.Reduction.

(** ** Observational theory *)

Inductive converges: pseudoterm -> nat -> Prop :=
  | converges_jump:
    forall k xs,
    converges (jump (bound k) xs) k
  | converges_bind:
    forall b ts c k,
    converges b (S k) -> converges (bind b ts c) k.

Global Hint Constructors converges: cps.

Definition weakly_converges a n: Prop :=
  exists2 b,
  [a =>* b] & converges b n.

Global Hint Unfold weakly_converges: cps.

Lemma convergence_is_unique:
  forall e n,
  converges e n ->
  forall m,
  converges e m -> n = m.
Proof.
  induction 1; intros.
  (* Case: converges_jump. *)
  - inversion H; auto.
  (* Case: converges_bind. *)
  - dependent destruction H0.
    firstorder.
Qed.

(** ** Barbed relations *)

Definition barb: relation pseudoterm :=
  barbed_congruence step converges apply_context.

Notation "[ a ~~ b ]" := (barb a b)
  (at level 0, a, b at level 200): type_scope.

Lemma barb_refl:
  forall e,
  [e ~~ e].
Proof.
  intros.
  apply barbed_congruence_refl.
Qed.

Global Hint Resolve barb_refl: cps.

Lemma barb_sym:
  forall a b,
  [a ~~ b] -> [b ~~ a].
Proof.
  intros.
  apply barbed_congruence_sym; auto.
Qed.

Global Hint Resolve barb_sym: cps.

Lemma barb_trans:
  forall a b c,
  [a ~~ b] -> [b ~~ c] -> [a ~~ c].
Proof.
  intros.
  eapply barbed_congruence_trans; eauto.
Qed.

Global Hint Resolve barb_trans: cps.

Lemma barb_bind_left:
  LEFT barb.
Proof.
  unfold LEFT, barb; intros.
  set (r := context_left context_hole ts c).
  replace (bind b1 ts c) with (r b1); auto.
  replace (bind b2 ts c) with (r b2); auto.
  intro; do 2 rewrite <- compose_context_is_sound.
  apply H.
Qed.

Global Hint Resolve barb_bind_left: cps.

Lemma barb_bind_right:
  RIGHT barb.
Proof.
  unfold RIGHT, barb; intros.
  set (r := context_right b ts context_hole).
  replace (bind b ts c1) with (r c1); auto.
  replace (bind b ts c2) with (r c2); auto.
  intro; do 2 rewrite <- compose_context_is_sound.
  apply H.
Qed.

Global Hint Resolve barb_bind_right: cps.

Instance barb_is_a_congruence: Congruence barb.
Proof.
  split.
  - split.
    + exact barb_refl.
    + exact barb_sym.
    + exact barb_trans.
  - exact barb_bind_left.
  - exact barb_bind_right.
Defined.

Theorem barb_cong:
  forall a b,
  [a == b] -> [a ~~ b].
Proof.
  admit.
Admitted.

Corollary barb_conv:
  forall a b,
  [a <=> b] -> [a ~~ b].
Proof.
  intros.
  apply barb_cong.
  apply cong_conv.
  assumption.
Qed.
