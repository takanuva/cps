(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.

(** ** Type system *)

Definition env: Set :=
  list pseudoterm.

Inductive simple: pseudoterm -> Prop :=
  | simple_base:
    simple base
  | simple_negation:
    forall ts,
    Forall simple ts -> simple (negation ts).

Definition valid_env (g: env): Prop :=
  Forall simple g.

(* We are free to take a simpler definition here since we're only dealing with
   simple types. Reasoning about dependent types will require extra care! *)

Inductive typing: env -> relation pseudoterm :=
  | typing_bound:
    forall g n t,
    valid_env g ->
    item t g n ->
    typing g n t
  | typing_jump:
    forall g k xs ts,
    typing g k (negation ts) ->
    Forall2 (typing g) (rev xs) ts ->
    typing g (jump k xs) void
  | typing_bind:
    forall g b ts c,
    typing (negation ts :: g) b void ->
    typing (ts ++ g) c void ->
    typing g (bind b ts c) void.

Global Hint Constructors typing: cps.

Lemma typing_bound_is_simple:
  forall g n t,
  typing g (bound n) t ->
  simple t.
Proof.
  intros.
  dependent destruction H.
  replace t with (nth n g void).
  - apply Forall_nth.
    + assumption.
    + apply item_valid_index with t.
      assumption.
  - apply nth_item.
    assumption.
Qed.

Lemma typing_bound_cant_be_void:
  forall g n,
  ~typing g (bound n) void.
Proof.
  intros g n ?.
  apply typing_bound_is_simple in H.
  inversion H.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma typing_lift:
  forall e g t,
  typing g e t ->
  forall x n h,
  insert x n g h ->
  typing h (lift 1 n e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - rename n0 into m.
    admit.
  - inversion H0.
  - dependent destruction H0.
    rewrite lift_distributes_over_jump.
    econstructor.
    + apply IHe with g x.
      * eassumption.
      * assumption.
    + clear IHe H0.
      apply Forall_rev in H.
      rewrite <- map_rev.
      generalize dependent ts.
      induction xs using rev_ind; intros.
      * simpl in H, H1 |- *.
        dependent destruction H1.
        constructor.
      * rewrite rev_app_distr in H, H1 |- *; simpl in H, H1 |- *.
        dependent destruction H.
        dependent destruction H1.
        constructor; eauto.
  - dependent destruction H0.
    rewrite lift_distributes_over_bind.
    constructor.
    + apply IHe1 with (negation ts :: g) x.
      * assumption.
      * admit.
    + apply IHe2 with (ts ++ g) x.
      * assumption.
      * rewrite Nat.add_comm.
        admit.
Admitted.

Theorem weakening:
  forall e g,
  typing g e void ->
  forall t,
  simple t ->
  typing (t :: g) (lift 1 0 e) void.
Proof.
  intros.
  apply typing_lift with g t.
  - apply H.
  - constructor.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma typing_switch_bindings:
  forall e g t,
  typing g e t ->
  forall n h,
  switch n g h ->
  typing h (switch_bindings n e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - rename n0 into m.
    admit.
  - inversion H0.
  - admit.
  - admit.
Admitted.

Theorem exchange:
  forall e g,
  typing g e void ->
  forall n h,
  switch n g h ->
  typing h (switch_bindings n e) void.
Proof.
  intros.
  apply typing_switch_bindings with g.
  - assumption.
  - assumption.
Qed.
