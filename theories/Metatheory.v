(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Local.Prelude.
Require Import Local.Syntax.

Lemma traverse_list_length:
  forall f k xs,
  length (traverse_list f k xs) = length xs.
Proof.
  intros.
  induction xs; simpl.
  - reflexivity.
  - f_equal; assumption.
Qed.

(** ** Lifting *)

Lemma lift_distributes_over_negation:
  forall i k ts,
  lift i k (negation ts) =
    negation (traverse_list (lift i) k ts).
Proof.
  auto.
Qed.

Lemma lift_distributes_over_jump:
  forall i k x xs,
  lift i k (jump x xs) =
    jump (lift i k x) (map (lift i k) xs).
Proof.
  auto.
Qed.

Lemma lift_distributes_over_bind:
  forall i k b ts c,
  lift i k (bind b ts c) =
    bind (lift i (S k) b) (map (lift i k) ts) (lift i (k + length ts) c).
Proof.
  auto.
Qed.

Lemma lift_zero_e_equals_e:
  forall e k,
  lift 0 k e = e.
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type.*)
  - reflexivity.
  (* Case: prop.*)
  - reflexivity.
  (* Case: base.*)
  - reflexivity.
  (* Case: void.*)
  - reflexivity.
  (* Case: bound. *)
  - unfold lift; simpl.
    destruct (le_gt_dec k n); auto.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    f_equal; list induction over H.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    f_equal; auto.
    list induction over H.
Qed.

Lemma lift_bound_ge:
  forall i k n,
  k <= n -> lift i k n = i + n.
Proof.
  intros.
  unfold lift; simpl.
  destruct (le_gt_dec k n).
  (* Case: k <= n. *)
  - reflexivity.
  (* Case: k > n. *)
  - absurd (k <= n); auto with arith.
Qed.

Lemma lift_bound_lt:
  forall i k n,
  k > n -> lift i k n = n.
Proof.
  intros; simpl.
  unfold lift; simpl.
  destruct (le_gt_dec k n).
  (* Case: k <= n. *)
  - absurd (k <= n); auto with arith.
  (* Case: k > n. *)
  - reflexivity.
Qed.

Lemma lift_lift_simplification:
  forall e i j k l,
  k <= l + j -> l <= k -> lift i k (lift j l e) = lift (i + j) l e.
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - destruct (le_gt_dec l n).
    + rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      f_equal; lia.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      reflexivity.
  (* Case: negation. *)
  - do 3 rewrite lift_distributes_over_negation; f_equal.
    induction H; simpl.
    + reflexivity.
    + f_equal.
      * do 3 rewrite traverse_list_length.
        apply H; lia.
      * assumption.
  (* Case: jump. *)
  - do 3 rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 3 rewrite lift_distributes_over_bind.
    f_equal; auto.
    + apply IHe1; lia.
    + list induction over H.
    + rewrite map_length.
      apply IHe2; lia.
Qed.

Lemma lift_lift_permutation:
  forall e i j k l,
  k <= l -> lift i k (lift j l e) = lift j (i + l) (lift i k e).
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - destruct (le_gt_dec l n); destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      f_equal; lia.
    + absurd (k <= n); lia.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_lt; try lia.
      reflexivity.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      reflexivity.
  (* Case: negation. *)
  - do 4 rewrite lift_distributes_over_negation; f_equal.
    induction H; simpl.
    + reflexivity.
    + f_equal.
      * do 4 rewrite traverse_list_length.
        replace (length l0 + (i + l)) with (i + (length l0 + l)); try lia.
        apply H; lia.
      * assumption.
  (* Case: jump. *)
  - do 4 rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 4 rewrite lift_distributes_over_bind.
    f_equal; auto.
    + replace (S (i + l)) with (i + S l); auto.
      apply IHe1; lia.
    + list induction over H.
    + do 2 rewrite map_length.
      rewrite plus_assoc_reverse.
      apply IHe2; lia.
Qed.
