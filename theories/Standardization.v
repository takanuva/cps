(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.AbstractRewriting.
Require Import Local.Reduction.

Fixpoint jump_count (e: pseudoterm): nat :=
  match e with
  | jump k xs =>
    1
  | bind b ts c =>
    jump_count b + jump_count c
  | _ =>
    (* We don't really have a jump, but neither should we have this in a
       context, so pretend it has a positive count. *)
    1
  end.

Fixpoint left_jump_count (h: context): nat :=
  match h with
  | context_hole =>
    0
  | context_left b ts c =>
    left_jump_count b
  | context_right b ts c =>
    jump_count b + left_jump_count c
  end.

Lemma left_jump_count_zero_imply_static:
  forall h,
  left_jump_count h = 0 <-> static h.
Proof.
  split.
  - induction h; simpl; intros.
    + constructor.
    + constructor; auto.
    + exfalso.
      clear IHh.
      induction b; simpl in H; lia.
  - induction 1; simpl.
    + reflexivity.
    + assumption.
Qed.

Inductive indexed_step: nat -> relation pseudoterm :=
  | indexed_step_ctxjmp:
    forall h xs ts c,
    length xs = length ts ->
    indexed_step (left_jump_count h)
      (bind (h (jump #h xs)) ts c)
      (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c)
  | indexed_step_bind_left:
    forall k b1 b2 ts c,
    indexed_step k b1 b2 ->
    indexed_step k (bind b1 ts c) (bind b2 ts c)
  | indexed_step_bind_right:
    forall k b ts c1 c2,
    indexed_step k c1 c2 ->
    indexed_step (jump_count b + k) (bind b ts c1) (bind b ts c2).

Goal
  same_relation head (indexed_step 0).
Proof.
  unfold same_relation, inclusion; split; intros.
  - destruct H.
    induction H0; simpl.
    + replace 0 with (left_jump_count h) at 1.
      * constructor.
        assumption.
      * apply left_jump_count_zero_imply_static.
        assumption.
    + apply indexed_step_bind_left.
      assumption.
  - dependent induction H.
    + apply head_longjmp with (r := context_hole).
      * apply left_jump_count_zero_imply_static.
        assumption.
      * constructor.
      * assumption.
    + apply head_bind_left; auto.
    + clear H IHindexed_step; exfalso.
      induction b; simpl in x; lia.
Qed.

Goal
  same_relation step (fun a b => exists k, indexed_step k a b).
Proof.
  unfold same_relation, inclusion; split; intros.
  - induction H.
    + exists (left_jump_count h).
      constructor.
      assumption.
    + destruct IHstep as (k, ?).
      exists k.
      constructor.
      assumption.
    + destruct IHstep as (k, ?).
      exists (jump_count b + k).
      constructor.
      assumption.
  - destruct H as (k, ?).
    dependent induction H.
    + constructor.
      assumption.
    + constructor.
      assumption.
    + constructor.
      assumption.
Qed.
