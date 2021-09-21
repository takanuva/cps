(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Equality.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
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
    cut (S k = S k0); auto.
Qed.

(* Set theoretic definition of a barbed (bi)simulation... *)

Definition reduction_closed (R: relation pseudoterm): Prop :=
  forall a b,
  R a b ->
  forall c,
  [a => c] ->
  exists2 d,
  [b =>* d] & R c d.

Definition barb_preserving (R: relation pseudoterm): Prop :=
  forall a b,
  R a b ->
  forall n,
  converges a n -> weakly_converges b n.

Definition barbed_simulation (R: relation pseudoterm): Prop :=
  reduction_closed R /\ barb_preserving R.

Definition barbed_bisimulation (R: relation pseudoterm): Prop :=
  barbed_simulation R /\ barbed_simulation (transp R).

Definition bisi a b: Prop :=
  exists2 R, barbed_bisimulation R & R a b.

Lemma bisi_is_a_barbed_bisimulation_itself:
  barbed_bisimulation bisi.
Proof.
  split; split; do 5 intro.
  - destruct H as (R, ((C, P), X), I).
    destruct C with a b c as (d, ?, ?); auto.
    exists d; auto.
    exists R; auto.
    split; auto.
    split; auto.
  - destruct H as (R, ((C, P), X), I).
    eapply P; eauto.
  - destruct H as (R, (X, (C, P)), I).
    destruct C with a b c as (d, ?, ?); auto.
    exists d; auto.
    exists R; auto.
    split; auto.
    split; auto.
  - destruct H as (R, (X, (C, P)), I).
    eapply P; eauto.
Qed.

Lemma multistep_reduction_closed:
  forall R,
  reduction_closed R ->
  forall a b,
  R a b ->
  forall c,
  [a =>* c] ->
  exists2 d,
  [b =>* d] & R c d.
Proof.
  intros.
  generalize b H0; clear b H0.
  induction H1; simpl; intros.
  - eapply H; eauto.
  - exists b; auto with cps.
  - destruct IHclos_refl_trans1 with b as (w, ?, ?); auto.
    destruct IHclos_refl_trans2 with w as (v, ?, ?); auto.
    exists v; eauto with cps.
Qed.

(* I'd like to try a coinductive definition later on... but let's see... *)

Definition barb a b: Prop :=
  forall h: context,
  bisi (h a) (h b).

Notation "[ a ~~ b ]" := (barb a b)
  (at level 0, a, b at level 200): type_scope.

Lemma barb_refl:
  forall e,
  [e ~~ e].
Proof.
  intros.
  (* Consider, e.g., that our barbed relation is alpha equality. *)
  exists eq; auto.
  split; split; do 5 intro.
  - destruct H.
    exists c; auto with cps.
  - destruct H.
    split with a; auto with cps.
  - destruct H.
    exists c; auto with cps.
  - destruct H.
    split with b; auto with cps.
Qed.

Global Hint Resolve barb_refl: cps.

Lemma barb_sym:
  forall a b,
  [a ~~ b] -> [b ~~ a].
Proof.
  unfold barb; intros.
  destruct H with h as (R, (X, Y), I).
  exists (transp R); auto.
  split; auto.
Qed.

Global Hint Resolve barb_sym: cps.

Lemma barb_trans:
  forall a b c,
  [a ~~ b] -> [b ~~ c] -> [a ~~ c].
Proof.
  unfold barb at 3; intros.
  destruct H with h as (R, ?, ?).
  destruct H0 with h as (S, ?, ?).
  exists (comp R S).
  - clear a b c H H0 h H2 H4.
    split; split; do 5 intro.
    + destruct H as (d, ?, ?).
      destruct H1 as ((?, _), _).
      destruct H3 as ((?, _), _).
      destruct H1 with a d c as (x, ?, ?); auto.
      destruct multistep_reduction_closed with S d b x as (y, ?, ?); auto.
      exists y; auto.
      exists x; auto.
    + destruct H as (d, ?, ?).
      destruct H1 as ((_, ?), _).
      destruct H3 as ((?, ?), _).
      destruct H1 with a d n as (x, ?, ?); auto.
      destruct multistep_reduction_closed with S d b x as (y, ?, ?); auto.
      destruct H4 with x y n as (z, ?, ?); auto.
      exists z; eauto with cps.
    + destruct H as (d, ?, ?).
      destruct H1 as (_, (?, _)).
      destruct H3 as (_, (?, _)).
      destruct H3 with a d c as (x, ?, ?); auto.
      destruct multistep_reduction_closed with (transp R) d b x as (y, ?, ?);
        auto.
      exists y; auto.
      exists x; auto.
    + destruct H as (d, ?, ?).
      destruct H1 as (_, (?, ?)).
      destruct H3 as (_, (_, ?)).
      destruct H3 with a d n as (x, ?, ?); auto.
      destruct multistep_reduction_closed with (transp R) d b x as (y, ?, ?);
        auto.
      destruct H4 with x y n as (z, ?, ?); auto.
      exists z; eauto with cps.
  - exists (h b); auto.
Qed.

Global Hint Resolve barb_trans: cps.

Instance barb_is_an_equivalence: Equivalence barb.
Proof.
  split.
  - exact barb_refl.
  - exact barb_sym.
  - exact barb_trans.
Defined.
