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

(** ** Substitution *)

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

(** ** Free Variables *)

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

Lemma substing_over_n_preserves_not_free_in_n:
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
