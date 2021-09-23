(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
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

Lemma sequence_length:
  forall n b,
  length (sequence b n) = n.
Proof.
  induction n; simpl; auto.
Qed.

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
    bind (lift i (S k) b) (traverse_list (lift i) k ts)
      (lift i (k + length ts) c).
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
    + f_equal; auto.
      do 3 rewrite traverse_list_length.
      apply H; lia.
  (* Case: jump. *)
  - do 3 rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 3 rewrite lift_distributes_over_bind.
    f_equal; auto.
    + apply IHe1; lia.
    + induction H; simpl.
      * reflexivity.
      * f_equal; auto.
        do 3 rewrite traverse_list_length.
        apply H; lia.
    + rewrite traverse_list_length.
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
    + f_equal; auto.
      do 4 rewrite traverse_list_length.
      replace (length l0 + (i + l)) with (i + (length l0 + l)); try lia.
      apply H; lia.
  (* Case: jump. *)
  - do 4 rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 4 rewrite lift_distributes_over_bind.
    f_equal; auto.
    + replace (S (i + l)) with (i + S l); auto.
      apply IHe1; lia.
    + induction H; simpl.
      * reflexivity.
      * f_equal; auto.
        do 4 rewrite traverse_list_length.
        replace (length l0 + (i + l)) with (i + (length l0 + l)); try lia.
        apply H; lia.
    + do 2 rewrite traverse_list_length.
      rewrite plus_assoc_reverse.
      apply IHe2; lia.
Qed.

Lemma subst_distributes_over_negation:
  forall y k ts,
  subst y k (negation ts) =
    negation (traverse_list (subst y) k ts).
Proof.
  auto.
Qed.

Lemma subst_distributes_over_jump:
  forall y k x xs,
  subst y k (jump x xs) =
    jump (subst y k x) (map (subst y k) xs).
Proof.
  auto.
Qed.

Lemma subst_distributes_over_bind:
  forall y k b ts c,
  subst y k (bind b ts c) =
    bind (subst y (S k) b) (traverse_list (subst y) k ts)
      (subst y (k + length ts) c).
Proof.
  auto.
Qed.

Lemma subst_bound_gt:
  forall e k n,
  n > k -> subst e k n = pred n.
Proof.
  intros.
  unfold subst; simpl.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  (* Case: k < n. *)
  - reflexivity.
  (* Case: k = n. *)
  - exfalso; lia.
  (* Case: k > n. *)
  - exfalso; lia.
Qed.

Lemma subst_bound_eq:
  forall e k n,
  n = k -> subst e k n = lift n 0 e.
Proof.
  intros.
  unfold subst; simpl.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  (* Case: k < n. *)
  - exfalso; lia.
  (* Case: k = n. *)
  - congruence.
  (* Case: k > n. *)
  - exfalso; lia.
Qed.

Lemma subst_bound_lt:
  forall e k n,
  n < k -> subst e k n = n.
Proof.
  intros.
  unfold subst; simpl.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  (* Case: k < n. *)
  - exfalso; lia.
  (* Case: k = n. *)
  - exfalso; lia.
  (* Case: k > n. *)
  - reflexivity.
Qed.

Lemma lift_addition_distributes_over_subst:
  forall e y i p k,
  lift i (p + k) (subst y p e) = subst (lift i k y) p (lift i (S (p + k)) e).
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
  - destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct n; try lia.
      destruct (le_gt_dec (p + k) n).
      * rewrite lift_bound_ge; try lia.
        rewrite subst_bound_gt; try lia.
        rewrite lift_bound_ge; try lia.
        rewrite subst_bound_gt; try lia.
        f_equal; lia.
      * rewrite lift_bound_lt; auto with arith.
        rewrite subst_bound_gt; auto with arith.
        rewrite lift_bound_lt; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
    + destruct e.
      rewrite lift_bound_lt; try lia.
      rewrite subst_bound_eq; auto.
      rewrite subst_bound_eq; auto.
      symmetry; apply lift_lift_permutation; lia.
    + rewrite lift_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; auto.
      rewrite lift_bound_lt; try lia.
      reflexivity.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    do 2 rewrite subst_distributes_over_negation.
    rewrite lift_distributes_over_negation; f_equal.
    induction H; simpl.
    + reflexivity.
    + f_equal; auto.
      do 4 rewrite traverse_list_length.
      replace (length l + (p + k)) with (length l + p + k); try lia.
      replace (length l + S (p + k)) with (S (length l + p + k)); try lia.
      apply H.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    do 2 rewrite subst_distributes_over_jump.
    rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    f_equal.
    + replace (S (p + k)) with (S p + k); try lia.
      apply IHe1.
    + induction H; simpl.
      * reflexivity.
      * f_equal; auto.
        do 4 rewrite traverse_list_length.
        replace (length l + (p + k)) with (length l + p + k); try lia.
        replace (length l + S (p + k)) with (S (length l + p + k)); try lia.
        apply H.
    + do 2 rewrite traverse_list_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (S (p + k) + length ts) with (S (p + length ts + k)); try lia.
      apply IHe2.
Qed.

Lemma lift_distributes_over_subst:
  forall a b i k,
  lift i k (subst b 0 a) = subst (lift i k b) 0 (lift i (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply lift_addition_distributes_over_subst.
Qed.

Lemma subst_lift_simplification:
  forall e y i p k,
  p <= i + k ->
  k <= p -> subst y p (lift (S i) k e) = lift i k e.
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
  - destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      f_equal; lia.
    + rewrite lift_bound_lt; auto.
      rewrite lift_bound_lt; auto.
      rewrite subst_bound_lt; auto.
      lia.
  (* Case: negation. *)
  - do 2 rewrite lift_distributes_over_negation.
    rewrite subst_distributes_over_negation.
    f_equal; induction H; auto.
    simpl; f_equal; auto.
    do 3 rewrite traverse_list_length.
    apply H; lia.
  (* Case: jump. *)
  - do 2 rewrite lift_distributes_over_jump.
    rewrite subst_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 2 rewrite lift_distributes_over_bind.
    rewrite subst_distributes_over_bind.
    f_equal.
    + apply IHe1; lia.
    + induction H; auto.
      simpl; f_equal; auto.
      do 3 rewrite traverse_list_length.
      apply H; lia.
    + rewrite traverse_list_length.
      apply IHe2; lia.
Qed.

Lemma lift_and_subst_commute:
  forall e y i p k,
  k <= p ->
  lift i k (subst y p e) = subst y (i + p) (lift i k e).
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
  - destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ]; simpl.
    + rewrite lift_bound_ge; try lia.
      rewrite subst_bound_gt; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite subst_bound_gt; try lia.
      f_equal; lia.
    + rewrite lift_bound_ge; try lia.
      rewrite subst_bound_eq; try lia.
      rewrite subst_bound_eq; try lia.
      apply lift_lift_simplification; lia.
    + rewrite subst_bound_lt; auto.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge; auto.
        rewrite subst_bound_lt; try lia.
        reflexivity.
      * rewrite lift_bound_lt; auto.
        rewrite subst_bound_lt; auto.
        lia.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    do 2 rewrite subst_distributes_over_negation.
    rewrite lift_distributes_over_negation.
    f_equal; induction H; auto.
    simpl; f_equal; auto.
    do 4 rewrite traverse_list_length.
    replace (length l + (i + p)) with (i + (length l + p)); try lia.
    apply H; lia.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    do 2 rewrite subst_distributes_over_jump.
    rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    f_equal.
    + replace (S (i + p)) with (i + S p); try lia.
      apply IHe1; lia.
    + induction H; auto.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      replace (length l + (i + p)) with (i + (length l + p)); try lia.
      apply H; lia.
    + do 2 rewrite traverse_list_length.
      replace (i + p + length ts) with (i + (p + length ts)); try lia.
      apply IHe2; lia.
Qed.

Lemma subst_addition_distributes_over_itself:
  forall e y z p k,
  subst y (p + k) (subst z p e) = subst (subst y k z) p (subst y (S (p + k)) e).
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
  - destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct n; try lia.
      rewrite subst_bound_gt; try lia.
      destruct (lt_eq_lt_dec (p + k) n) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_gt; try lia.
        rewrite subst_bound_gt; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
      * rewrite subst_bound_eq; try lia.
        rewrite subst_bound_eq; try lia.
        rewrite subst_lift_simplification; try lia.
        reflexivity.
      * rewrite subst_bound_lt; try lia.
        rewrite subst_bound_lt; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
    + rewrite subst_bound_eq; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_eq; try lia.
      rewrite lift_and_subst_commute; try lia.
      f_equal; lia.
    + rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      reflexivity.
  (* Case: negation. *)
  - do 4 rewrite subst_distributes_over_negation.
    f_equal; induction H; auto.
    simpl; f_equal; auto.
    do 4 rewrite traverse_list_length.
    replace (length l + (p + k)) with (length l + p + k); try lia.
    replace (length l + S (p + k)) with (S (length l + p + k)); try lia.
    apply H.
  (* Case: jump. *)
  - do 4 rewrite subst_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 4 rewrite subst_distributes_over_bind.
    f_equal.
    + replace (S (p + k)) with (S p + k); try lia.
      apply IHe1; lia.
    + induction H; auto.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      replace (length l + (p + k)) with (length l + p + k); try lia.
      replace (length l + S (p + k)) with (S (length l + p + k)); try lia.
      apply H.
    + do 2 rewrite traverse_list_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (S (p + k) + length ts) with (S (p + length ts + k)); try lia.
      apply IHe2; lia.
Qed.

Lemma subst_distributes_over_itself:
  forall a b c k,
  subst c k (subst b 0 a) = subst (subst c k b) 0 (subst c (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply subst_addition_distributes_over_itself.
Qed.

Lemma apply_parameters_distributes_over_negation:
  forall ys k ts,
  apply_parameters ys k (negation ts) =
    negation (traverse_list (apply_parameters ys) k ts).
Proof.
  induction ys; simpl; intros.
  - f_equal; induction ts; auto.
    simpl; f_equal.
    assumption.
  - rewrite subst_distributes_over_negation.
    rewrite IHys.
    f_equal; clear IHys.
    induction ts; auto; simpl.
    do 3 rewrite traverse_list_length.
    f_equal; auto.
    f_equal; f_equal.
    lia.
Qed.

Lemma apply_parameters_distributes_over_jump:
  forall ys k x xs,
  apply_parameters ys k (jump x xs) =
    jump (apply_parameters ys k x) (map (apply_parameters ys k) xs).
Proof.
  induction ys; simpl; intros.
  - f_equal; induction xs; auto.
    simpl; f_equal.
    assumption.
  - rewrite subst_distributes_over_jump.
    rewrite IHys.
    f_equal; clear IHys.
    induction xs; auto; simpl.
    f_equal; assumption.
Qed.

Lemma apply_parameters_distributes_over_bind:
  forall ys k b ts c,
  apply_parameters ys k (bind b ts c) =
    bind (apply_parameters ys (S k) b)
      (traverse_list (apply_parameters ys) k ts)
        (apply_parameters ys (k + length ts) c).
Proof.
  induction ys; simpl; intros.
  - f_equal; induction ts; auto.
    simpl; f_equal.
    assumption.
  - rewrite subst_distributes_over_bind.
    rewrite IHys; clear IHys.
    rewrite traverse_list_length.
    f_equal.
    + induction ts; auto; simpl.
      do 3 rewrite traverse_list_length.
      f_equal; auto.
      f_equal; f_equal.
      lia.
    + f_equal; f_equal.
      lia.
Qed.

Lemma lift_addition_distributes_over_apply_parameters:
  forall ys i k p e,
  lift i (p + k) (apply_parameters ys p e) =
    apply_parameters (map (lift i k) ys) p (lift i (p + length ys + k) e).
Proof.
  induction ys; simpl; intros.
  (* Case: nil. *)
  - replace (p + 0) with p; auto.
  (* Case: cons. *)
  - rewrite IHys.
    rewrite lift_addition_distributes_over_subst.
    rewrite map_length.
    do 3 f_equal; lia.
Qed.

Lemma lift_distributes_over_apply_parameters:
  forall ys i k e,
  lift i k (apply_parameters ys 0 e) =
    apply_parameters (map (lift i k) ys) 0 (lift i (length ys + k) e).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply lift_addition_distributes_over_apply_parameters.
Qed.

Lemma subst_addition_distributes_over_apply_parameters:
  forall ys y k p e,
  subst y (p + k) (apply_parameters ys p e) =
    apply_parameters (map (subst y k) ys) p (subst y (p + length ys + k) e).
Proof.
  induction ys; simpl; intros.
  (* Case: nil. *)
  - replace (p + 0) with p; auto.
  (* Case: cons. *)
  - rewrite IHys.
    rewrite subst_addition_distributes_over_itself.
    rewrite map_length.
    do 3 f_equal; lia.
Qed.

Lemma subst_distributes_over_apply_parameters:
  forall ys y k e,
  subst y k (apply_parameters ys 0 e) =
    apply_parameters (map (subst y k) ys) 0 (subst y (length ys + k) e).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply subst_addition_distributes_over_apply_parameters.
Qed.

Lemma switch_bindings_behavior:
  forall e k,
  switch_bindings k e = right_cycle 1 k e.
Proof.
  unfold switch_bindings.
  unfold right_cycle; simpl.
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
  - destruct (le_gt_dec (S (S k)) n).
    + rewrite lift_bound_ge; auto.
      rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      rewrite subst_bound_gt; try lia.
      rewrite subst_bound_gt; try lia.
      reflexivity.
    + rewrite lift_bound_lt; auto.
      rewrite lift_bound_lt; auto.
      destruct (lt_eq_lt_dec n k) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_lt; auto.
        rewrite subst_bound_lt; try lia.
        rewrite subst_bound_lt; auto with arith.
      * rewrite subst_bound_eq; auto.
        rewrite subst_bound_lt; try lia.
        rewrite subst_bound_eq; eauto with arith.
        lia.
      * rewrite subst_bound_gt; auto.
        rewrite subst_bound_eq; try lia.
        rewrite lift_bound_ge; auto.
        rewrite subst_bound_gt; auto.
        lia.
  (* Case: negation. *)
  - do 2 rewrite lift_distributes_over_negation.
    do 3 rewrite subst_distributes_over_negation.
    f_equal; induction H; auto.
    simpl.
    do 5 rewrite traverse_list_length.
    f_equal; auto.
    replace (length l + S (S k)) with (S (S (length l + k))); try lia.
    do 2 rewrite plus_assoc.
    apply H.
  (* Case: jump. *)
  - do 2 rewrite lift_distributes_over_jump.
    do 3 rewrite subst_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 2 rewrite lift_distributes_over_bind.
    do 3 rewrite subst_distributes_over_bind.
    f_equal.
    + apply IHe1.
    + clear IHe1 IHe2.
      induction H; auto.
      simpl.
      do 5 rewrite traverse_list_length.
      f_equal; auto.
      replace (length l + S (S k)) with (S (S (length l + k))); try lia.
      do 2 rewrite plus_assoc.
      apply H.
    + do 3 rewrite traverse_list_length.
      replace (k + 0 + length ts) with (k + length ts + 0); try lia.
      replace (k + 1 + length ts) with (k + length ts + 1); try lia.
      apply IHe2.
Qed.

Lemma lifting_over_n_preserves_not_free_n:
  forall e n,
  not_free n e ->
  forall i k,
  k > n -> not_free n (lift i k e).
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - assumption.
  (* Case: prop. *)
  - assumption.
  (* Case: base. *)
  - assumption.
  (* Case: void. *)
  - assumption.
  (* Case: bound. *)
  - rename n0 into m.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      constructor; lia.
    + rewrite lift_bound_lt; auto.
  (* Case: negation. *)
  - induction H; simpl.
    + assumption.
    + rewrite lift_distributes_over_negation; simpl.
      dependent destruction H0.
      dependent destruction H0.
      apply not_free_negation in H1.
      apply IHForall in H1.
      rewrite lift_distributes_over_negation in H1.
      dependent destruction H1.
      constructor; constructor; auto.
      rewrite traverse_list_length.
      apply H; try lia.
      assumption.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    dependent destruction H0.
    constructor; auto.
    induction H; auto; simpl.
    dependent destruction H1.
    constructor; auto.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    dependent destruction H0; constructor.
    + apply IHe1; auto.
      lia.
    + clear IHe1 IHe2 H0_ H0_0.
      induction H; auto; simpl.
      dependent destruction H0.
      apply IHForall in H1.
      constructor; auto.
      rewrite traverse_list_length.
      apply H; auto.
      lia.
    + rewrite traverse_list_length.
      apply IHe2; auto.
      lia.
Qed.

(* Clearly, if we're lifiting [e]'s var above [k] by [i], anything equal or
   greater than [k] and smaller than [k + i] is free. *)
Lemma lifting_more_than_n_makes_not_free_n:
  forall e i k n,
  n >= k -> n < k + i -> not_free n (lift i k e).
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - constructor.
  (* Case: prop. *)
  - constructor.
  (* Case: base. *)
  - constructor.
  (* Case: void. *)
  - constructor.
  (* Case: bound. *)
  - rename n0 into m.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      constructor; lia.
    + rewrite lift_bound_lt; auto.
      constructor; lia.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    constructor.
    induction H; simpl; auto.
    + constructor.
    + constructor; auto.
      rewrite traverse_list_length.
      apply H; lia.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    constructor; auto.
    induction H; simpl; auto.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    constructor.
    + apply IHe1; lia.
    + induction H; simpl.
      * constructor.
      * constructor; auto.
        rewrite traverse_list_length.
        apply H; lia.
    + rewrite traverse_list_length.
      apply IHe2; lia.
Qed.

Lemma substing_over_n_preserves_not_free_n:
  forall e n,
  not_free n e ->
  forall x k,
  k > n -> not_free n (subst x k e).
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - assumption.
  (* Case: prop. *)
  - assumption.
  (* Case: base. *)
  - assumption.
  (* Case: void. *)
  - assumption.
  (* Case: bound. *)
  - rename n0 into m.
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_gt; auto.
      constructor; lia.
    + rewrite subst_bound_eq; auto.
      apply lifting_more_than_n_makes_not_free_n; lia.
    + rewrite subst_bound_lt; auto.
  (* Case: negation. *)
  - induction H; simpl.
    + assumption.
    + rewrite subst_distributes_over_negation; simpl.
      dependent destruction H0.
      dependent destruction H0.
      apply not_free_negation in H1.
      apply IHForall in H1.
      rewrite subst_distributes_over_negation in H1.
      dependent destruction H1.
      constructor; constructor; auto.
      rewrite traverse_list_length.
      apply H; try lia.
      assumption.
  (* Case: jump. *)
  - rewrite subst_distributes_over_jump.
    dependent destruction H0.
    constructor; auto.
    induction H; auto; simpl.
    dependent destruction H1.
    constructor; auto.
  (* Case: bind. *)
  - rewrite subst_distributes_over_bind.
    dependent destruction H0; constructor.
    + apply IHe1; auto.
      lia.
    + clear IHe1 IHe2 H0_ H0_0.
      induction H; auto; simpl.
      dependent destruction H0.
      apply IHForall in H1.
      constructor; auto.
      rewrite traverse_list_length.
      apply H; auto.
      lia.
    + rewrite traverse_list_length.
      apply IHe2; auto.
      lia.
Qed.

Lemma lift_preserved_by_useless_subst:
  forall e i k p x,
  not_free p e ->
  lift i (p + k) (subst x p e) = subst x p (lift i (p + S k) e).
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
  - destruct (lt_eq_lt_dec n p) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_lt; auto.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite subst_bound_lt; auto.
    + exfalso.
      inversion H; auto.
    + rewrite subst_bound_gt; auto.
      destruct (le_gt_dec n (p + k)).
      * rewrite lift_bound_lt; try lia.
        rewrite lift_bound_lt; try lia.
        rewrite subst_bound_gt; auto.
      * rewrite lift_bound_ge; try lia.
        rewrite lift_bound_ge; try lia.
        rewrite subst_bound_gt; try lia.
        f_equal; lia.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    do 2 rewrite subst_distributes_over_negation.
    rewrite lift_distributes_over_negation.
    dependent destruction H0.
    f_equal.
    induction H; auto.
    dependent destruction H0.
    simpl; f_equal; auto.
    do 4 rewrite traverse_list_length.
    do 2 rewrite plus_assoc.
    apply H; auto.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    do 2 rewrite subst_distributes_over_jump.
    rewrite lift_distributes_over_jump.
    dependent destruction H0.
    f_equal; auto.
    induction H; auto.
    dependent destruction H1.
    simpl; f_equal; auto.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    inversion_clear H0.
    simpl; f_equal.
    + replace (S (p + k)) with (S p + k); try lia.
      replace (S (p + S k)) with (S p + S k); try lia.
      apply IHe1; auto.
    + clear IHe1 IHe2 H1 H3.
      induction H; auto.
      inversion_clear H2.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      do 2 rewrite plus_assoc.
      apply H; auto.
    + do 2 rewrite traverse_list_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHe2; auto.
      rewrite plus_comm; auto.
Qed.

Lemma remove_closest_binding_and_lift_commute:
  forall e i k,
  not_free 0 e ->
  lift i k (remove_binding 0 e) = remove_binding 0 (lift i (S k) e).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply lift_preserved_by_useless_subst.
  assumption.
Qed.

Lemma subst_preserved_by_useless_subst:
  forall e y k p x,
  not_free p e ->
  subst y (p + k) (subst x p e) = subst x p (subst y (p + S k) e).
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
  - destruct (lt_eq_lt_dec n p) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_lt; auto.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; auto.
    + exfalso.
      inversion H; auto.
    + rewrite subst_bound_gt; auto.
      destruct (lt_eq_lt_dec n (p + S k)) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_lt; try lia.
        rewrite subst_bound_lt; try lia.
        rewrite subst_bound_gt; auto.
      * rewrite subst_bound_eq; try lia.
        rewrite subst_bound_eq; try lia.
        replace n with (S (p + k)) at 2; try lia.
        rewrite subst_lift_simplification; try lia.
        f_equal; lia.
      * rewrite subst_bound_gt; try lia.
        rewrite subst_bound_gt; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
  (* Case: negation. *)
  - do 4 rewrite subst_distributes_over_negation.
    dependent destruction H0.
    f_equal.
    induction H; auto.
    dependent destruction H0.
    simpl; f_equal; auto.
    do 4 rewrite traverse_list_length.
    do 2 rewrite plus_assoc.
    apply H; auto.
  (* Case: jump. *)
  - do 4 rewrite subst_distributes_over_jump.
    dependent destruction H0.
    f_equal; auto.
    induction H; auto.
    dependent destruction H1.
    simpl; f_equal; auto.
  (* Case: bind. *)
  - do 4 rewrite subst_distributes_over_bind.
    inversion_clear H0.
    simpl; f_equal.
    + replace (S (p + k)) with (S p + k); try lia.
      replace (S (p + S k)) with (S p + S k); try lia.
      apply IHe1; auto.
    + clear IHe1 IHe2 H1 H3.
      induction H; auto.
      inversion_clear H2.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      do 2 rewrite plus_assoc.
      apply H; auto.
    + do 2 rewrite traverse_list_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHe2; auto.
      rewrite plus_comm; auto.
Qed.

Lemma remove_closest_binding_and_subst_commute:
  forall e y k,
  not_free 0 e ->
  subst y k (remove_binding 0 e) = remove_binding 0 (subst y (S k) e).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply subst_preserved_by_useless_subst.
  assumption.
Qed.

Lemma lifting_over_n_doesnt_change_sequence_n:
  forall n i k (b: bool),
  (if b then k > n else k >= n) ->
  map (lift i k) (sequence b n) = sequence b n.
Proof.
  induction n; intros.
  (* Case: zero. *)
  - reflexivity.
  (* Case: succ. *)
  - simpl; f_equal.
    + rewrite lift_bound_lt; auto.
      destruct b; lia.
    + apply IHn.
      destruct b; lia.
Qed.

Lemma lifting_over_n_doesnt_change_high_sequence_n:
  forall n i k,
  k > n ->
  map (lift i k) (high_sequence n) = high_sequence n.
Proof.
  intros.
  apply lifting_over_n_doesnt_change_sequence_n with (b := true); auto.
Qed.

Lemma lifting_over_n_doesnt_change_low_sequence_n:
  forall n i k,
  k >= n ->
  map (lift i k) (low_sequence n) = low_sequence n.
Proof.
  intros.
  apply lifting_over_n_doesnt_change_sequence_n with (b := false); auto.
Qed.

Lemma substing_over_n_doesnt_change_sequence_n:
  forall n x k (b: bool),
  (if b then k > n else k >= n) ->
  map (subst x k) (sequence b n) = sequence b n.
Proof.
  induction n; intros.
  (* Case: zero. *)
  - reflexivity.
  (* Case: succ. *)
  - simpl; f_equal.
    + rewrite subst_bound_lt; auto.
      destruct b; lia.
    + apply IHn.
      destruct b; lia.
Qed.

Lemma substing_over_n_doesnt_change_high_sequence_n:
  forall n x k,
  k > n ->
  map (subst x k) (high_sequence n) = high_sequence n.
Proof.
  intros.
  apply substing_over_n_doesnt_change_sequence_n with (b := true); auto.
Qed.

Lemma substing_over_n_doesnt_change_low_sequence_n:
  forall n x k,
  k >= n ->
  map (subst x k) (low_sequence n) = low_sequence n.
Proof.
  intros.
  apply substing_over_n_doesnt_change_sequence_n with (b := false); auto.
Qed.

Lemma lift_and_right_cycle_commute:
  forall e n i k p,
  k > n ->
  lift i (p + k) (right_cycle n p e) = right_cycle n p (lift i (p + k) e).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_addition_distributes_over_apply_parameters.
  do 2 f_equal.
  - apply lifting_over_n_doesnt_change_high_sequence_n; auto.
  - rewrite lift_addition_distributes_over_subst; f_equal.
    + rewrite lift_bound_lt; auto; lia.
    + rewrite sequence_length; symmetry.
      rewrite lift_lift_permutation; try lia.
      f_equal; lia.
Qed.

Lemma lift_and_switch_bindings_commute:
  forall i k e,
  lift i (S (S k)) (switch_bindings 0 e) =
    switch_bindings 0 (lift i (S (S k)) e).
Proof.
  intros.
  do 2 rewrite switch_bindings_behavior.
  apply lift_and_right_cycle_commute with (p := 0) (n := 1); lia.
Qed.

Lemma subst_and_right_cycle_commute:
  forall e n x k p,
  k > n ->
  subst x (p + k) (right_cycle n p e) =
    right_cycle n p (subst x (p + k) e).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite subst_addition_distributes_over_apply_parameters.
  f_equal.
  - apply substing_over_n_doesnt_change_high_sequence_n; auto.
  - rewrite subst_addition_distributes_over_itself; f_equal.
    + rewrite subst_bound_lt; auto.
      lia.
    + rewrite sequence_length.
      rewrite lift_and_subst_commute; try lia.
      f_equal; lia.
Qed.

Lemma subst_and_switch_bindings_commute:
  forall x k e,
  subst x (2 + k) (switch_bindings 0 e) =
    switch_bindings 0 (subst x (2 + k) e).
Proof.
  intros.
  do 2 rewrite switch_bindings_behavior.
  apply subst_and_right_cycle_commute with (p := 0) (n := 1); lia.
Qed.

Lemma apply_parameters_lift_e_equals_e:
  forall xs k e,
  apply_parameters xs k (lift (length xs) k e) = e.
Proof.
  induction xs; intros.
  - apply lift_zero_e_equals_e.
  - simpl.
    rewrite subst_lift_simplification; try lia.
    apply IHxs.
Qed.

Lemma apply_parameters_bound_lt:
  forall xs n,
  length xs > n ->
  forall x,
  item x (rev xs) n -> apply_parameters xs 0 n = x.
Proof.
  induction xs; simpl; intros.
  - exfalso.
    inversion H0.
  - destruct (le_gt_dec (length xs) n).
    + assert (n = length xs); try lia.
      rewrite subst_bound_eq; auto.
      apply item_ignore_head in H0.
      * rewrite rev_length in H0.
        rewrite H1 in H0 |- *.
        replace (length xs - length xs) with 0 in H0; try lia.
        inversion_clear H0.
        apply apply_parameters_lift_e_equals_e.
      * rewrite rev_length; auto.
    + rewrite subst_bound_lt; auto.
      apply IHxs; auto.
      eapply item_ignore_tail; eauto.
      rewrite rev_length; auto.
Qed.

Lemma apply_parameters_bound_ge:
  forall xs n,
  length xs <= n ->
  apply_parameters xs 0 (bound n) = n - length xs.
Proof.
  induction xs; intros.
  - simpl; f_equal; lia.
  - simpl in H |- *.
    rewrite subst_bound_gt; auto.
    rewrite IHxs; try lia.
    f_equal; lia.
Qed.

Lemma high_sequence_rev_lifts_by_one:
  forall n k,
  n < k -> item (bound (S n)) (rev (high_sequence k)) n.
Proof.
  intros.
  induction k; simpl.
  - exfalso.
    inversion H.
  - destruct (le_gt_dec k n).
    + cut (n = k); try lia.
      destruct 1.
      replace n with (length (rev (high_sequence n))) at 4.
      * apply item_insert_head with (k := 0).
        constructor.
      * rewrite rev_length.
        rewrite sequence_length.
        reflexivity.
    + apply item_insert_tail.
      apply IHk; lia.
Qed.

Lemma right_cycle_bound_lt:
  forall k n,
  n < k -> right_cycle k 0 (bound n) = S n.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_lt; try lia.
  rewrite sequence_length.
  rewrite subst_bound_lt; auto.
  apply apply_parameters_bound_lt.
  - rewrite sequence_length; auto.
  - apply high_sequence_rev_lifts_by_one; auto.
Qed.

Lemma right_cycle_bound_eq:
  forall k n,
  n = k -> right_cycle k 0 (bound n) = 0.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_lt; try lia.
  rewrite sequence_length.
  rewrite subst_bound_eq; auto.
  rewrite lift_bound_ge; auto.
  rewrite apply_parameters_bound_ge.
  - rewrite sequence_length.
    f_equal; lia.
  - rewrite sequence_length.
    lia.
Qed.

Lemma right_cycle_bound_gt:
  forall k n,
  n > k -> right_cycle k 0 (bound n) = n.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_ge; try lia.
  rewrite sequence_length.
  rewrite subst_bound_gt; try lia.
  rewrite apply_parameters_bound_ge; simpl.
  - rewrite sequence_length.
    f_equal; lia.
  - rewrite sequence_length.
    lia.
Qed.

Lemma right_cycle_distributes_over_negation:
  forall n k ts,
  right_cycle n k (negation ts) =
    negation (traverse_list (right_cycle n) k ts).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_distributes_over_negation.
  rewrite subst_distributes_over_negation.
  rewrite apply_parameters_distributes_over_negation.
  f_equal.
  induction ts; auto.
  simpl; f_equal; auto.
  do 4 rewrite traverse_list_length.
  f_equal; f_equal; try lia.
  f_equal; lia.
Qed.

Lemma right_cycle_distributes_over_jump:
  forall n p k xs,
  right_cycle n p (jump k xs) =
    jump (right_cycle n p k) (map (right_cycle n p) xs).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_distributes_over_jump.
  rewrite subst_distributes_over_jump.
  rewrite apply_parameters_distributes_over_jump; simpl.
  f_equal; list induction over xs.
Qed.

Lemma right_cycle_distributes_over_bind:
  forall n k b ts c,
  right_cycle n k (bind b ts c) =
    bind (right_cycle n (S k) b)
      (traverse_list (right_cycle n) k ts)
      (right_cycle n (k + length ts) c).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_distributes_over_bind.
  rewrite subst_distributes_over_bind.
  rewrite apply_parameters_distributes_over_bind.
  f_equal.
  - f_equal; f_equal; f_equal.
    lia.
  - induction ts; auto.
    simpl; f_equal; auto.
    do 4 rewrite traverse_list_length.
    f_equal; f_equal; try lia.
    f_equal; lia.
  - do 2 rewrite traverse_list_length.
    f_equal; f_equal; try lia.
    f_equal; lia.
Qed.

Lemma switch_bindings_distributes_over_negation:
  forall k ts,
  switch_bindings k (negation ts) =
    negation (traverse_list switch_bindings k ts).
Proof.
  intros.
  rewrite switch_bindings_behavior.
  rewrite right_cycle_distributes_over_negation.
  f_equal.
  induction ts; auto.
  simpl; f_equal; auto.
  rewrite switch_bindings_behavior.
  do 2 rewrite traverse_list_length.
  reflexivity.
Qed.

Lemma switch_bindings_distributes_over_jump:
  forall p k xs,
  switch_bindings p (jump k xs) =
    jump (switch_bindings p k) (map (switch_bindings p) xs).
Proof.
  intros.
  rewrite switch_bindings_behavior.
  rewrite right_cycle_distributes_over_jump.
  f_equal.
  - rewrite switch_bindings_behavior.
    reflexivity.
  - induction xs; auto.
    simpl; f_equal; auto.
    rewrite switch_bindings_behavior.
    reflexivity.
Qed.

Lemma switch_bindings_distributes_over_bind:
  forall k b ts c,
  switch_bindings k (bind b ts c) =
    bind (switch_bindings (S k) b)
      (traverse_list switch_bindings k ts)
        (switch_bindings (k + length ts) c).
Proof.
  intros.
  rewrite switch_bindings_behavior.
  rewrite right_cycle_distributes_over_bind.
  f_equal.
  - rewrite switch_bindings_behavior.
    reflexivity.
  - induction ts; auto.
    simpl; f_equal; auto.
    rewrite switch_bindings_behavior.
    do 2 rewrite traverse_list_length.
    reflexivity.
  - rewrite switch_bindings_behavior.
    reflexivity.
Qed.

Lemma switch_bindings_bound_eq:
  forall k n,
  k = n ->
  switch_bindings k n = S n.
Proof.
  intros.
  unfold switch_bindings.
  rewrite lift_bound_lt; try lia.
  rewrite subst_bound_eq; auto.
  rewrite lift_bound_ge; try lia.
  f_equal; lia.
Qed.

Lemma switch_bindings_is_involutive:
  forall e k,
  switch_bindings k (switch_bindings k e) = e.
Proof.
  unfold switch_bindings.
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (le_gt_dec (2 + k) n); simpl.
    + rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      f_equal; lia.
    + rewrite lift_bound_lt; try lia.
      destruct (lt_eq_lt_dec n k) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_lt; auto.
        rewrite lift_bound_lt; auto.
        rewrite subst_bound_lt; auto.
      * rewrite subst_bound_eq; auto.
        rewrite lift_bound_ge; auto.
        rewrite lift_bound_lt; try lia.
        rewrite subst_bound_gt; try lia.
        f_equal; lia.
      * rewrite subst_bound_gt; auto.
        rewrite lift_bound_lt; try lia.
        rewrite subst_bound_eq; try lia.
        rewrite lift_bound_ge; auto.
        f_equal; lia.
  - rewrite lift_distributes_over_negation.
    rewrite subst_distributes_over_negation.
    rewrite lift_distributes_over_negation.
    rewrite subst_distributes_over_negation.
    f_equal.
    induction H; auto.
    simpl; f_equal; auto.
    do 4 rewrite traverse_list_length.
    replace (length l + S (S k)) with (2 + (length l + k)); try lia.
    apply H.
  - rewrite lift_distributes_over_jump.
    rewrite subst_distributes_over_jump.
    rewrite lift_distributes_over_jump.
    rewrite subst_distributes_over_jump.
    f_equal.
    + apply IHe.
    + list induction over H.
      apply H.
  - rewrite lift_distributes_over_bind.
    rewrite subst_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite subst_distributes_over_bind.
    f_equal.
    + apply IHe1.
    + clear IHe1 IHe2.
      induction H; auto.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      replace (length l + S (S k)) with (2 + (length l + k)); try lia.
      apply H.
    + do 3 rewrite traverse_list_length.
      apply IHe2.
Qed.

Lemma map_switch_bindings_is_involutive:
  forall k xs,
  map (switch_bindings k) (map (switch_bindings k) xs) = xs.
Proof.
  induction xs; auto.
  simpl; f_equal; auto.
  apply switch_bindings_is_involutive.
Qed.

Lemma right_cycle_low_sequence_n_equals_high_sequence_n:
  forall n m,
  m >= n ->
  map (right_cycle m 0) (low_sequence n) = high_sequence n.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl.
    rewrite IHn; auto with arith.
    simpl; f_equal.
    apply right_cycle_bound_lt; auto.
Qed.
