(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

(* TODO: as we move to a substitution algebra, most of this file will be either
   removed or rewritten. It was about time! *)

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

(* TODO: move the two following lemmas about sequences elsewhere, as we might
   need those for other calculi... I'm guessing. *)

Lemma sequence_length:
  forall n b,
  length (sequence b n) = n.
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - now rewrite IHn.
Qed.

Lemma item_sequence:
  forall n m i,
  m < n ->
  item (bound (i + m)) (sequence i n) m.
Proof.
  induction n; intros.
  - inversion H.
  - destruct m; simpl.
    + rewrite Nat.add_0_r.
      constructor.
    + constructor.
      replace (i + S m) with (S i + m) by lia.
      apply IHn.
      lia.
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
      rewrite <- Nat.add_assoc.
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
  - rewrite IHys.
    rewrite subst_distributes_over_negation.
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
  - rewrite IHys.
    rewrite subst_distributes_over_jump.
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
  - rewrite IHys; clear IHys.
    rewrite subst_distributes_over_bind.
    rewrite traverse_list_length.
    f_equal.
    induction ts; auto; simpl.
    do 3 rewrite traverse_list_length.
    f_equal; auto.
    do 2 f_equal.
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
  - rewrite lift_addition_distributes_over_subst.
    replace (S (p + k)) with (S p + k) by lia.
    rewrite IHys.
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
  - rewrite subst_addition_distributes_over_itself.
    replace (S (p + k)) with (S p + k) by lia.
    rewrite IHys.
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

Lemma apply_parameters_app:
  forall xs ys k e,
  apply_parameters (xs ++ ys) k e =
    apply_parameters xs k (apply_parameters ys (length xs + k) e).
Proof.
  induction xs; simpl; intros.
  - reflexivity.
  - rewrite IHxs.
    do 3 f_equal.
    lia.
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
    rewrite H.
    do 2 f_equal.
    lia.
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
      rewrite H.
      do 2 f_equal.
      lia.
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
    do 2 rewrite Nat.add_assoc.
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
      do 2 rewrite Nat.add_assoc.
      apply H; auto.
    + do 2 rewrite traverse_list_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHe2; auto.
      rewrite Nat.add_comm; auto.
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
    do 2 rewrite Nat.add_assoc.
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
      do 2 rewrite Nat.add_assoc.
      apply H; auto.
    + do 2 rewrite traverse_list_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHe2; auto.
      rewrite Nat.add_comm; auto.
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

Lemma lifting_over_n_doesnt_change_sequence_p_n:
  forall n p i k,
  k >= p + n ->
  map (lift i k) (sequence p n) = sequence p n.
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn by lia.
    f_equal.
    now rewrite lift_bound_lt by lia.
Qed.

Lemma substing_over_n_doesnt_change_sequence_p_n:
  forall n p x k,
  k >= p + n ->
  map (subst x k) (sequence p n) = sequence p n.
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn by lia.
    f_equal.
    now rewrite subst_bound_lt by lia.
Qed.

Lemma lift_and_right_cycle_commute:
  forall e n i k p,
  k > n ->
  lift i (p + k) (right_cycle n p e) = right_cycle n p (lift i (p + k) e).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_addition_distributes_over_apply_parameters.
  f_equal.
  - rewrite map_app; simpl.
    f_equal.
    + apply lifting_over_n_doesnt_change_sequence_p_n.
      lia.
    + now rewrite lift_bound_lt by lia.
  - rewrite app_length, sequence_length; symmetry.
    rewrite lift_lift_permutation; try lia.
    simpl; f_equal.
    lia.
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
  - rewrite map_app; simpl.
    f_equal.
    + apply substing_over_n_doesnt_change_sequence_p_n.
      lia.
    + now rewrite subst_bound_lt by lia.
  - rewrite app_length, sequence_length; symmetry.
    rewrite lift_and_subst_commute; try lia.
    simpl; f_equal.
    lia.
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

Lemma apply_parameters_lift_simplification:
  forall xs k p e,
  k <= p ->
  apply_parameters xs k (lift (p + length xs) 0 e) = lift p 0 e.
Proof.
  induction xs; simpl; intros.
  - f_equal; lia.
  - replace (p + S (length xs)) with (S p + length xs) by lia.
    rewrite IHxs.
    + rewrite subst_lift_simplification; try lia.
      reflexivity.
    + lia.
Qed.

Lemma apply_parameters_bound_gt:
  forall xs n k,
  length xs + k <= n ->
  apply_parameters xs k (bound n) = n - length xs.
Proof.
  induction xs; intros.
  - simpl.
    f_equal; lia.
  - simpl in H |- *.
    rewrite IHxs; try lia.
    rewrite subst_bound_gt; try lia.
    f_equal; lia.
Qed.

Lemma apply_parameters_bound_lt:
  forall xs n k,
  k > n ->
  apply_parameters xs k (bound n) = n.
Proof.
  induction xs; intros.
  - simpl.
    reflexivity.
  - simpl in H |- *.
    rewrite IHxs; try lia.
    rewrite subst_bound_lt; try lia.
    reflexivity.
Qed.

Lemma apply_parameters_bound_in:
  forall n xs,
  length xs > n ->
  forall x,
  item x xs n ->
  forall k,
  apply_parameters xs k (k + n) = lift k 0 x.
Proof.
  induction n; intros.
  - dependent destruction H0.
    simpl in H |- *.
    rewrite apply_parameters_bound_lt; try lia.
    rewrite subst_bound_eq; try lia.
    f_equal; lia.
  - dependent destruction H0.
    simpl.
    replace (k + S n) with (S k + n) by lia.
    rewrite IHn with (x := x).
    + rewrite subst_lift_simplification; try lia.
      reflexivity.
    + simpl in H.
      lia.
    + assumption.
Qed.

Lemma right_cycle_bound_lt:
  forall k n,
  n < k -> right_cycle k 0 (bound n) = S n.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_lt; try lia.
  replace n with (0 + n) at 1 by lia.
  rewrite apply_parameters_bound_in with (x := S n).
  - rewrite lift_bound_ge by lia.
    f_equal; lia.
  - rewrite app_length, sequence_length; simpl.
    lia.
  - apply item_insert_tail.
    now apply item_sequence with (i := 1).
Qed.

Lemma right_cycle_bound_eq:
  forall k n,
  n = k -> right_cycle k 0 (bound n) = 0.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_lt; try lia.
  replace n with (0 + n) by lia.
  rewrite apply_parameters_bound_in with (x := 0).
  - rewrite lift_zero_e_equals_e.
    reflexivity.
  - rewrite app_length, sequence_length; simpl.
    lia.
  - replace n with (0 + length (high_sequence k)).
    + apply item_insert_head.
      constructor.
    + now rewrite sequence_length.
Qed.

Lemma right_cycle_bound_gt:
  forall k n,
  n > k -> right_cycle k 0 (bound n) = n.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_ge; try lia.
  rewrite apply_parameters_bound_gt.
  - rewrite app_length, sequence_length; simpl.
    rewrite Nat.add_comm; simpl.
    f_equal; lia.
  - rewrite app_length, sequence_length; simpl.
    lia.
Qed.

Lemma apply_parameters_type:
  forall xs k,
  apply_parameters xs k type = type.
Proof.
  induction xs; simpl; intros.
  - reflexivity.
  - rewrite IHxs.
    reflexivity.
Qed.

Lemma right_cycle_type:
  forall i k,
  right_cycle i k type = type.
Proof.
  intros.
  apply apply_parameters_type.
Qed.

Lemma apply_parameters_prop:
  forall xs k,
  apply_parameters xs k prop = prop.
Proof.
  induction xs; simpl; intros.
  - reflexivity.
  - rewrite IHxs.
    reflexivity.
Qed.

Lemma right_cycle_prop:
  forall i k,
  right_cycle i k prop = prop.
Proof.
  intros.
  apply apply_parameters_prop.
Qed.

Lemma apply_parameters_base:
  forall xs k,
  apply_parameters xs k base = base.
Proof.
  induction xs; simpl; intros.
  - reflexivity.
  - rewrite IHxs.
    reflexivity.
Qed.

Lemma right_cycle_base:
  forall i k,
  right_cycle i k base = base.
Proof.
  intros.
  apply apply_parameters_base.
Qed.

Lemma apply_parameters_void:
  forall xs k,
  apply_parameters xs k void = void.
Proof.
  induction xs; simpl; intros.
  - reflexivity.
  - rewrite IHxs.
    reflexivity.
Qed.

Lemma right_cycle_void:
  forall i k,
  right_cycle i k void = void.
Proof.
  intros.
  apply apply_parameters_void.
Qed.

Lemma right_cycle_distributes_over_negation:
  forall n k ts,
  right_cycle n k (negation ts) =
    negation (traverse_list (right_cycle n) k ts).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_distributes_over_negation.
  rewrite apply_parameters_distributes_over_negation.
  f_equal.
  induction ts; auto.
  simpl; f_equal; auto.
  do 3 rewrite traverse_list_length.
  repeat f_equal.
  lia.
Qed.

Lemma right_cycle_distributes_over_jump:
  forall n p k xs,
  right_cycle n p (jump k xs) =
    jump (right_cycle n p k) (map (right_cycle n p) xs).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_distributes_over_jump.
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
  rewrite apply_parameters_distributes_over_bind.
  f_equal.
  - repeat f_equal.
    lia.
  - induction ts; auto.
    simpl; f_equal; auto.
    do 3 rewrite traverse_list_length.
    repeat f_equal.
    lia.
  - rewrite traverse_list_length.
    repeat f_equal.
    lia.
Qed.

Lemma right_cycle_zero_e_equals_e:
  forall e k,
  right_cycle 0 k e = e.
Proof.
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold right_cycle; simpl.
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      reflexivity.
    + rewrite lift_bound_lt; try lia.
      rewrite subst_bound_eq; try lia.
      rewrite lift_bound_ge; try lia.
      f_equal; lia.
    + rewrite lift_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      reflexivity.
  - rewrite right_cycle_distributes_over_negation.
    induction H; simpl; auto.
    rewrite traverse_list_length.
    dependent destruction IHForall.
    f_equal; f_equal; auto.
  - rewrite right_cycle_distributes_over_jump; f_equal.
    + apply IHe.
    + list induction over H.
  - rewrite right_cycle_distributes_over_bind; f_equal.
    + apply IHe1.
    + induction H; simpl; auto.
      rewrite traverse_list_length.
      dependent destruction IHForall.
      f_equal; f_equal; auto.
    + apply IHe2.
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

Lemma apply_parameters_high_sequence_bound_in:
  forall n i k,
  n >= k ->
  i + k > n ->
  apply_parameters (high_sequence i) k n = S n.
Proof.
  intros.
  replace n with (k + (n - k)); try lia.
  rewrite apply_parameters_bound_in with (x := S (n - k)).
  - rewrite lift_bound_ge; try lia.
    f_equal; lia.
  - rewrite sequence_length; try lia.
  - apply item_sequence with (i := 1).
    lia.
Qed.

Lemma right_cycle_right_cycle_simplification:
  forall e k p i,
  right_cycle i k (right_cycle p (i + k) e) =
    right_cycle (i + p) k e.
Proof.
  induction e using pseudoterm_deepind; intros.
  - repeat rewrite right_cycle_type.
    reflexivity.
  - repeat rewrite right_cycle_prop.
    reflexivity.
  - repeat rewrite right_cycle_base.
    reflexivity.
  - repeat rewrite right_cycle_void.
    reflexivity.
  - remember (i + k) as l.
    unfold right_cycle; simpl.
    (* I'm too tired to think the proper conditions here, so this was kinda
       written by trial and error... I probably should have automated this.
       TODO: automate this. *)
    assert (n < k
         \/ n >= k /\ n < i + p
         \/ n >= i + p) as [ ? | [ [ ? ? ] | ? ] ]; try lia.
    + rewrite lift_bound_lt; try lia.
      rewrite apply_parameters_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite apply_parameters_bound_lt; try lia.
      rewrite apply_parameters_bound_lt; try lia.
      reflexivity.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      admit.
    + admit.
  - do 3 rewrite right_cycle_distributes_over_negation.
    f_equal.
    induction H; simpl; auto.
    do 3 rewrite traverse_list_length.
    f_equal; auto.
    replace (length l + (i + k)) with (i + (length l + k)); try lia.
    apply H.
  - do 3 rewrite right_cycle_distributes_over_jump.
    f_equal.
    + apply IHe.
    + list induction over H.
  - do 3 rewrite right_cycle_distributes_over_bind.
    f_equal.
    + replace (S (i + k)) with (i + S k); try lia.
      apply IHe1.
    + induction H; simpl; auto.
      do 3 rewrite traverse_list_length.
      f_equal; auto.
      replace (length l + (i + k)) with (i + (length l + k)); try lia.
      apply H.
    + rewrite traverse_list_length.
      replace (i + k + length ts) with (i + (k + length ts)); try lia.
      apply IHe2.
Admitted.

Lemma right_cycle_switch_bindings_simplification:
  forall e i k,
  right_cycle i k (switch_bindings (k + i) e) =
    right_cycle (S i) k e.
Proof.
  intros.
  rewrite switch_bindings_behavior.
  rewrite Nat.add_comm.
  replace (S i) with (i + 1); try lia.
  apply right_cycle_right_cycle_simplification.
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
    + list induction over H;
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
  intros.
  assert (exists2 p, p = 0 & p + n <= m) as (p, ?, ?) by eauto with arith.
  rewrite <- H0 at 2 3; clear H0.
  generalize dependent p.
  generalize dependent m.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn by lia.
    simpl; do 2 f_equal.
    apply right_cycle_bound_lt.
    lia.
Qed.

Lemma left_cycle_zero_e_equals_e:
  forall e k,
  left_cycle 0 k e = e.
Proof.
  unfold left_cycle; simpl.
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + rewrite lift_bound_ge by lia.
      rewrite subst_bound_gt by lia.
      reflexivity.
    + rewrite lift_bound_lt by lia.
      rewrite subst_bound_eq by lia.
      rewrite lift_bound_ge by lia.
      f_equal; lia.
    + rewrite lift_bound_lt by lia.
      rewrite subst_bound_lt by lia.
      reflexivity.
  - rewrite lift_distributes_over_negation.
    rewrite subst_distributes_over_negation.
    f_equal.
    induction H; simpl.
    + reflexivity.
    + f_equal; auto.
      do 2 rewrite traverse_list_length.
      replace (length l + S k) with (S (length l + k)) by lia.
      apply H.
  - rewrite lift_distributes_over_jump.
    rewrite subst_distributes_over_jump.
    f_equal.
    + apply IHe.
    + clear IHe.
      induction H; simpl.
      * reflexivity.
      * f_equal; auto.
  - rewrite lift_distributes_over_bind.
    rewrite subst_distributes_over_bind.
    f_equal.
    + apply IHe1.
    + clear IHe1 IHe2.
      induction H; simpl.
      * constructor.
      * f_equal; auto.
        do 2 rewrite traverse_list_length.
        replace (length l + S k) with (S (length l + k)) by lia.
        apply H.
    + rewrite traverse_list_length.
      apply IHe2.
Qed.

Lemma left_cycle_switch_bindings_simplification:
  forall e i k,
  left_cycle i (S k) (switch_bindings k e) = left_cycle (S i) k e.
Proof.
  unfold left_cycle; simpl.
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold switch_bindings.
    destruct (le_gt_dec (2 + k) n).
    + rewrite lift_bound_ge by lia.
      rewrite subst_bound_gt by lia; simpl.
      destruct (le_gt_dec (2 + i + k) n).
      * rewrite lift_bound_ge by lia.
        rewrite subst_bound_gt by lia.
        rewrite lift_bound_ge by lia.
        rewrite subst_bound_gt by lia.
        reflexivity.
      * rewrite lift_bound_lt by lia.
        rewrite subst_bound_gt by lia.
        rewrite lift_bound_lt by lia.
        rewrite subst_bound_gt by lia.
        reflexivity.
    + rewrite lift_bound_lt by lia.
      destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_gt by lia.
        rewrite lift_bound_lt by lia.
        rewrite subst_bound_lt by lia.
        rewrite lift_bound_lt by lia.
        rewrite subst_bound_gt by lia.
        reflexivity.
      * rewrite subst_bound_eq by lia.
        rewrite lift_bound_ge by lia.
        rewrite lift_bound_lt by lia.
        rewrite subst_bound_eq by lia.
        rewrite lift_bound_ge by lia.
        rewrite lift_bound_lt by lia.
        rewrite subst_bound_eq by lia.
        rewrite lift_bound_ge by lia.
        f_equal; lia.
      * rewrite subst_bound_lt by lia.
        rewrite lift_bound_lt by lia.
        rewrite subst_bound_lt by lia.
        rewrite lift_bound_lt by lia.
        rewrite subst_bound_lt by lia.
        reflexivity.
  - rewrite switch_bindings_distributes_over_negation.
    do 2 rewrite lift_distributes_over_negation.
    do 2 rewrite subst_distributes_over_negation.
    f_equal.
    induction H; simpl.
    + reflexivity.
    + f_equal; auto.
      do 5 rewrite traverse_list_length.
      replace (length l + S k) with (S (length l + k)) by lia.
      replace (length l + S (i + S k)) with (1 + i + S (length l + k)) by lia.
      replace (length l + S (S (i + k))) with (1 + S i + (length l + k))
        by lia.
      apply H.
  - rewrite switch_bindings_distributes_over_jump.
    do 2 rewrite lift_distributes_over_jump.
    do 2 rewrite subst_distributes_over_jump.
    f_equal.
    + apply IHe.
    + clear IHe.
      induction H; simpl.
      * constructor.
      * f_equal; auto.
  - rewrite switch_bindings_distributes_over_bind.
    do 2 rewrite lift_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    f_equal.
    + replace (S (i + S k)) with (i + S (S k)) by lia.
      replace (S (i + k)) with (i + S k) by lia.
      apply IHe1.
    + clear IHe1 IHe2.
      induction H; simpl.
      * constructor.
      * f_equal; auto.
        do 5 rewrite traverse_list_length.
        replace (length l + S k) with (S (length l + k)) by lia.
        replace (length l + S (i + S k)) with
          (S (i + (S (length l + k)))) by lia.
        replace (length l + S (S (i + k))) with
          (S (S (i + (length l + k)))) by lia.
        apply H.
    + do 3 rewrite traverse_list_length.
      replace (S k + length ts) with (S (k + length ts)) by lia.
      replace (S (i + S k) + length ts) with
        (S (i + S (k + length ts))) by lia.
      replace (S (S (i + k)) + length ts) with
        (S (S (i + (k + length ts)))) by lia.
      apply IHe2.
Qed.

Lemma not_free_lift:
  forall c p k j,
  not_free (p + j) c ->
  not_free (p + k + j) (lift k j c).
Proof.
  induction c using pseudoterm_deepind; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct (le_gt_dec j n).
    + rewrite lift_bound_ge; auto.
      dependent destruction H.
      constructor; lia.
    + rewrite lift_bound_lt; auto.
      constructor; lia.
  - dependent destruction H0.
    rewrite lift_distributes_over_negation.
    constructor.
    induction H; simpl.
    + constructor.
    + dependent destruction H0.
      constructor; auto.
      rewrite traverse_list_length.
      replace (length l + (p + k + j)) with (p + k + (length l + j)); try lia.
      apply H.
      replace (p + (length l + j)) with (length l + (p + j)); try lia.
      assumption.
  - dependent destruction H0.
    rewrite lift_distributes_over_jump.
    constructor; auto.
    clear IHc H0 c.
    induction H; simpl.
    + constructor.
    + dependent destruction H1.
      constructor; auto.
  - dependent destruction H0.
    rewrite lift_distributes_over_bind.
    constructor.
    + replace (S (p + k + j)) with (p + k + S j); try lia.
      apply IHc1.
      replace (p + S j) with (S (p + j)); try lia.
      assumption.
    + clear IHc1 IHc2 H0_ H0_0 c1 c2.
      induction H; simpl.
      * constructor.
      * dependent destruction H0.
        constructor; auto.
        rewrite traverse_list_length.
        replace (length l + (p + k + j)) with (p + k + (length l + j)); try lia.
        apply H.
        replace (p + (length l + j)) with (length l + (p + j)); try lia.
        assumption.
    + rewrite traverse_list_length.
      replace (length ts + (p + k + j)) with (p + k + (j + length ts)); try lia.
      apply IHc2.
      replace (p + (j + length ts)) with (length ts + (p + j)); try lia.
      assumption.
Qed.

Local Lemma not_free_apply_parameters_bound:
  forall (n: nat) k p xs,
  Forall (not_free p) xs ->
  not_free (p + k + length xs) n ->
  not_free (p + k) (apply_parameters xs k n).
Proof.
  intros.
  destruct (le_gt_dec k n).
  - destruct (le_gt_dec (k + length xs) n).
    + rewrite apply_parameters_bound_gt; try lia.
      dependent destruction H0.
      constructor; lia.
    + replace n with (k + (n - k)); try lia.
      assert (exists x, item x xs (n - k)) as (x, ?).
      * apply item_exists.
        lia.
      * rewrite apply_parameters_bound_in with (x := x); auto; try lia.
        replace (p + k) with (p + k + 0) by lia.
        apply not_free_lift.
        rewrite Nat.add_0_r.
        (* TODO: should we make a tactic for that? I think so! *)
        apply nth_item with (y := void) in H1.
        rewrite <- H1.
        apply Forall_nth; auto.
        lia.
  - rewrite apply_parameters_bound_lt; auto.
    constructor; lia.
Qed.

Lemma not_free_apply_parameters:
  forall c k p xs,
  Forall (not_free p) xs ->
  not_free (p + k + length xs) c ->
  not_free (p + k) (apply_parameters xs k c).
Proof.
  induction c using pseudoterm_deepind; intros.
  - clear H H0.
    rewrite apply_parameters_type.
    constructor.
  - clear H H0.
    rewrite apply_parameters_prop.
    constructor.
  - clear H H0.
    rewrite apply_parameters_base.
    constructor.
  - clear H H0.
    rewrite apply_parameters_void.
    constructor.
  - apply not_free_apply_parameters_bound; auto.
  - dependent destruction H1.
    rewrite apply_parameters_distributes_over_negation.
    constructor.
    induction H; simpl.
    + constructor.
    + rewrite traverse_list_length.
      dependent destruction H1.
      constructor; auto.
      rewrite traverse_list_length.
      replace (length l + (p + k)) with (p + (length l + k)); try lia.
      apply H; auto.
      replace (p + (length l + k) + length xs) with
        (length l + (p + k + length xs)); try lia.
      assumption.
  - dependent destruction H1.
    rewrite apply_parameters_distributes_over_jump.
    constructor; auto.
    clear H1 IHc c.
    induction H; simpl.
    + constructor.
    + dependent destruction H2.
      constructor; auto.
  - dependent destruction H1.
    rewrite apply_parameters_distributes_over_bind.
    constructor.
    + replace (S (p + k)) with (p + S k); try lia.
      apply IHc1; auto.
      replace (p + S k + length xs) with (S (p + k + length xs)); try lia.
      assumption.
    + clear IHc1 IHc2 H1_ H1_0 c1 c2.
      induction H; simpl.
      * constructor.
      * rewrite traverse_list_length.
        dependent destruction H1.
        constructor; auto.
        rewrite traverse_list_length.
        replace (length l + (p + k)) with (p + (length l + k)); try lia.
        apply H; auto.
        replace (p + (length l + k) + length xs) with
          (length l + (p + k + length xs)); try lia.
        assumption.
    + rewrite traverse_list_length.
      replace (length ts + (p + k)) with (p + (k + length ts)); try lia.
      apply IHc2; auto.
      replace (p + (k + length ts) + length xs) with
        (length ts + (p + k + length xs)); try lia.
      assumption.
Qed.

Lemma remove_binding_size:
  forall b k,
  not_free k b ->
  size (remove_binding k b) = size b.
Proof.
  induction b; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold remove_binding.
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_gt; simpl; lia.
    + dependent destruction H.
      contradiction.
    + rewrite subst_bound_lt; lia.
  - reflexivity.
  - reflexivity.
  - dependent destruction H.
    unfold remove_binding.
    rewrite subst_distributes_over_bind; simpl.
    do 2 f_equal.
    + apply IHb1.
      assumption.
    + apply IHb2.
      rewrite Nat.add_comm.
      assumption.
Qed.
