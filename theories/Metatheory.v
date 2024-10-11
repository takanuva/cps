(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

(* TODO: as we move to a substitution algebra, most of this file will be either
   removed or rewritten. It was about time! *)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Syntax.

Local Ltac modulo_arith :=
  repeat (progress f_equal; try lia).

Lemma traverse_list_length:
  forall f k xs,
  length (traverse_list f k xs) = length xs.
Proof.
  intros.
  induction xs; simpl.
  - reflexivity.
  - f_equal; assumption.
Qed.

Global Instance pseudoterm_dbVarLaws: dbVarLaws pseudoterm.
Proof.
  split; auto.
Qed.

Global Instance pseudoterm_dbTraverseLaws: dbTraverseLaws pseudoterm pseudoterm.
Proof.
  split; unfold Substitution.traverse; intros.
  - generalize dependent k.
    induction x using pseudoterm_deepind; eauto with cps; simpl; intros.
    + f_equal.
      list induction over H0.
    + f_equal; auto.
      list induction over H0.
    + f_equal; auto.
      list induction over H0.
  - apply H with (x := n).
  - generalize dependent j.
    generalize dependent k.
    induction x using pseudoterm_deepind; eauto with cps; simpl; intros.
    + apply H with (l := 0).
    + f_equal.
      list induction over H.
      repeat rewrite traverse_list_length.
      apply H; intros h n.
      now do 2 rewrite Nat.add_assoc.
    + f_equal; auto.
      list induction over H.
    + f_equal; auto.
      * apply IHx1; intros.
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H0.
      * list induction over H.
        repeat rewrite traverse_list_length.
        apply H; intros h n.
        now do 2 rewrite Nat.add_assoc.
      * apply IHx2; intros.
        replace (l + (k + length ts)) with
          (l + length ts + k) by lia.
        replace (l + (j + length ts)) with
          (l + length ts + j) by lia.
        apply H0.
  - generalize dependent k.
    induction x using pseudoterm_deepind; eauto with cps; simpl; intros.
    + f_equal.
      list induction over H.
      repeat rewrite traverse_list_length.
      apply H.
    + f_equal; auto.
      list induction over H.
    + f_equal; auto.
      * induction H; auto.
        simpl.
        repeat rewrite traverse_list_length.
        f_equal; auto.
      * repeat rewrite traverse_list_length.
        apply IHx2.
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
  intros.
  now sigma.
Qed.

Lemma lift_bound_ge:
  forall i k n,
  k <= n ->
  lift i k (bound n) = bound (i + n).
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma lift_bound_lt:
  forall i k n,
  k > n ->
  lift i k (bound n) = bound n.
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma lift_lift_simplification:
  forall e i j k l,
  k <= l + j ->
  l <= k ->
  lift i k (lift j l e) = lift (i + j) l e.
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma lift_lift_permutation:
  forall e i j k l,
  k <= l ->
  lift i k (lift j l e) = lift j (i + l) (lift i k e).
Proof with modulo_arith.
  intros.
  sigma...
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
  n > k ->
  subst e k (bound n) = bound (pred n).
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma subst_bound_eq:
  forall e k n,
  n = k ->
  subst e k (bound n) = lift n 0 e.
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma subst_bound_lt:
  forall e k n,
  n < k ->
  subst e k (bound n) = bound n.
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma lift_addition_distributes_over_subst:
  forall e y i p k,
  lift i (p + k) (subst y p e) = subst (lift i k y) p (lift i (S (p + k)) e).
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma lift_distributes_over_subst:
  forall a b i k,
  lift i k (subst b 0 a) = subst (lift i k b) 0 (lift i (S k) a).
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma subst_lift_simplification:
  forall e y i p k,
  p <= i + k ->
  k <= p ->
  subst y p (lift (S i) k e) = lift i k e.
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma lift_and_subst_commute:
  forall e y i p k,
  k <= p ->
  lift i k (subst y p e) = subst y (i + p) (lift i k e).
Proof with modulo_arith.
  intros.
  sigma...
Qed.

Lemma subst_addition_distributes_over_itself:
  forall e y z p k,
  subst y (p + k) (subst z p e) = subst (subst y k z) p (subst y (S (p + k)) e).
Proof with modulo_arith.
  intros.
  sigma...
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
  auto.
Qed.

Lemma apply_parameters_distributes_over_jump:
  forall ys k x xs,
  apply_parameters ys k (jump x xs) =
    jump (apply_parameters ys k x) (map (apply_parameters ys k) xs).
Proof.
  auto.
Qed.

Lemma apply_parameters_distributes_over_bind:
  forall ys k b ts c,
  apply_parameters ys k (bind b ts c) =
    bind (apply_parameters ys (S k) b)
      (traverse_list (apply_parameters ys) k ts)
        (apply_parameters ys (k + length ts) c).
Proof.
  auto.
Qed.

Lemma lift_addition_distributes_over_apply_parameters:
  forall ys i k p e,
  lift i (p + k) (apply_parameters ys p e) =
    apply_parameters (map (lift i k) ys) p (lift i (p + length ys + k) e).
Proof with modulo_arith.
  intros.
  unfold apply_parameters.
  (* TODO: fix lemma statement instead! *)
  replace (map (lift i k)) with (smap (subst_lift i) k) by auto.
  sigma...
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
Proof with modulo_arith.
  intros.
  unfold apply_parameters.
  (* TODO: fix lemma statement instead! *)
  replace (map (subst y k)) with (smap (subst_cons y subst_ids) k) by auto.
  sigma...
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
  intros.
  unfold apply_parameters.
  now sigma.
Qed.

Lemma switch_bindings_behavior:
  forall e k,
  switch_bindings k e = right_cycle 1 k e.
Proof.
  intros.
  unfold switch_bindings.
  unfold right_cycle.
  simpl sequence.
  now sigma.
Qed.

Lemma lifting_over_n_preserves_not_free_n:
  forall e n,
  not_free n e ->
  forall i k,
  k > n ->
  not_free n (lift i k e).
Proof.
  sigma.
  induction e using pseudoterm_deepind; intros.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - dependent destruction H.
    rename n0 into m.
    destruct (le_gt_dec k n).
    + sigma.
      constructor.
      lia.
    + sigma.
      constructor.
      assumption.
  - dependent destruction H0.
    sigma; constructor.
    induction H.
    + constructor.
    + dependent destruction H0.
      sigma; constructor.
      * rewrite bsmap_length.
        apply H; auto.
        lia.
      * now apply IHForall.
  - dependent destruction H0.
    sigma; constructor.
    + now apply IHe.
    + induction H.
      * constructor.
      * dependent destruction H1.
        sigma; constructor; auto.
  - dependent destruction H0.
    sigma; constructor.
    + apply IHe1; auto.
      lia.
    + clear H0_ H0_0.
      induction H.
      * constructor.
      * dependent destruction H0.
        sigma; constructor; auto.
        rewrite bsmap_length.
        apply H; auto.
        lia.
    + rewrite bsmap_length.
      apply IHe2; auto.
      lia.
Qed.

(* Clearly, if we're lifiting [e]'s var above [k] by [i], anything equal or
   greater than [k] and smaller than [k + i] is free. *)
Lemma lifting_more_than_n_makes_not_free_n:
  forall e i k n,
  n >= k ->
  n < k + i ->
  not_free n (lift i k e).
Proof.
  sigma.
  induction e using pseudoterm_deepind; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - rename n0 into m.
    destruct (le_gt_dec k n).
    + sigma.
      constructor.
      lia.
    + sigma.
      constructor.
      lia.
  - sigma; constructor.
    induction H.
    + constructor.
    + sigma; constructor; auto.
      rewrite bsmap_length.
      apply H; lia.
  - sigma; constructor.
    + now apply IHe.
    + induction H.
      * constructor.
      * sigma; constructor; auto.
  - sigma; constructor.
    + apply IHe1; lia.
    + induction H.
      * constructor.
      * sigma; constructor; auto.
        rewrite bsmap_length.
        apply H; lia.
    + rewrite bsmap_length.
      apply IHe2; lia.
Qed.

Lemma substing_over_n_preserves_not_free_n:
  forall e n,
  not_free n e ->
  forall x k,
  k > n ->
  not_free n (subst x k e).
Proof.
  sigma.
  induction e using pseudoterm_deepind; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - dependent destruction H.
    rename n0 into m.
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + sigma.
      constructor.
      lia.
    + sigma.
      (* Oh... *)
      replace (inst (subst_lift k)) with (lift k 0) by auto.
      apply lifting_more_than_n_makes_not_free_n; lia.
    + sigma.
      now constructor.
  - dependent destruction H0.
    sigma; constructor.
    induction H.
    + constructor.
    + dependent destruction H0.
      sigma; constructor; auto.
      rewrite bsmap_length.
      apply H; auto; lia.
  - dependent destruction H0.
    sigma; constructor.
    + now apply IHe.
    + induction H.
      * constructor.
      * dependent destruction H1.
        sigma; constructor; auto.
  - dependent destruction H0.
    sigma; constructor.
    + apply IHe1; auto; lia.
    + clear H0_ H0_0.
      induction H.
      * constructor.
      * dependent destruction H0.
        sigma; constructor; auto.
        rewrite bsmap_length.
        apply H; auto; lia.
    + rewrite bsmap_length.
      apply IHe2; auto; lia.
Qed.

Lemma lift_preserved_by_useless_subst:
  forall e i k p x,
  not_free p e ->
  lift i (p + k) (subst x p e) = subst x p (lift i (p + S k) e).
Proof with modulo_arith.
  sigma; intros.
  (* TODO: ideally, sigma should also try to normalize arithmetic... *)
  replace (p + k - p) with k by lia.
  replace (S (p + k) - p - 1) with k by lia.
  (* Gotta generalize everything again... *)
  generalize dependent x.
  generalize dependent p.
  generalize dependent k.
  generalize dependent i.
  (* There we go... *)
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - dependent destruction H.
    rename n0 into m.
    destruct (le_gt_dec m n).
    + now sigma.
    + now sigma.
  - dependent destruction H0.
    sigma; f_equal.
    induction H.
    + reflexivity.
    + dependent destruction H0.
      sigma; f_equal; auto.
  - dependent destruction H0.
    sigma; f_equal; auto.
    induction H.
    + reflexivity.
    + dependent destruction H1.
      sigma; f_equal; auto.
  - dependent destruction H0.
    sigma; f_equal.
    + now apply IHe1.
    + clear H0_ H0_0.
      induction H.
      * reflexivity.
      * dependent destruction H0.
        sigma; f_equal; auto.
    + now apply IHe2.
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
  sigma; intros.
  (* TODO: ideally, sigma should also try to normalize arithmetic... *)
  replace (p + k - p) with k by lia.
  replace (S (p + k) - p - 1) with k by lia.
  (* Same as above... *)
  generalize dependent x.
  generalize dependent p.
  generalize dependent k.
  generalize dependent y.
  (* There we go... *)
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - dependent destruction H.
    rename n0 into m.
    destruct (le_gt_dec m n).
    + now sigma.
    + now sigma.
  - dependent destruction H0.
    sigma; f_equal.
    induction H.
    + reflexivity.
    + dependent destruction H0.
      sigma; f_equal; auto.
  - dependent destruction H0.
    sigma; f_equal; auto.
    induction H.
    + reflexivity.
    + dependent destruction H1.
      sigma; f_equal; auto.
  - dependent destruction H0.
    sigma; f_equal.
    + now apply IHe1.
    + clear H0_ H0_0.
      induction H.
      * reflexivity.
      * dependent destruction H0.
        sigma; f_equal; auto.
    + now apply IHe2.
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
    f_equal; now sigma.
Qed.

Lemma substing_over_n_doesnt_change_sequence_p_n:
  forall n p x k,
  k >= p + n ->
  map (subst x k) (sequence p n) = sequence p n.
Proof.
  induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn by lia.
    f_equal; now sigma.
Qed.

Lemma lift_and_right_cycle_commute:
  forall e n i k p,
  k > n ->
  lift i (p + k) (right_cycle n p e) = right_cycle n p (lift i (p + k) e).
Proof with modulo_arith.
  intros.
  unfold right_cycle.
  assert (length (high_sequence n) = n) by apply sequence_length.
  sigma...
  replace (p + k - p) with k by lia.
  replace (smap (subst_lift i) k) with (map (lift i k)) by auto.
  rewrite map_app; f_equal.
  - apply lifting_over_n_doesnt_change_sequence_p_n; lia.
  - simpl; f_equal.
    now sigma.
Qed.

Lemma lift_and_switch_bindings_commute:
  forall i k e,
  lift i (S (S k)) (switch_bindings 0 e) =
    switch_bindings 0 (lift i (S (S k)) e).
Proof.
  intros.
  unfold switch_bindings.
  now sigma.
Qed.

Lemma subst_and_right_cycle_commute:
  forall e n x k p,
  k > n ->
  subst x (p + k) (right_cycle n p e) =
    right_cycle n p (subst x (p + k) e).
Proof with modulo_arith.
  intros.
  unfold right_cycle.
  assert (length (high_sequence n) = n) by apply sequence_length.
  sigma...
  replace (p + k - p) with k by lia.
  replace (smap (subst_cons x subst_ids) k) with (map (subst x k)) by auto.
  rewrite map_app; f_equal.
  - apply substing_over_n_doesnt_change_sequence_p_n; lia.
  - simpl; f_equal.
    now sigma.
Qed.

Lemma subst_and_switch_bindings_commute:
  forall x k e,
  subst x (2 + k) (switch_bindings 0 e) =
    switch_bindings 0 (subst x (2 + k) e).
Proof.
  intros.
  unfold switch_bindings.
  now sigma.
Qed.

Lemma apply_parameters_lift_simplification:
  forall xs k p e,
  k <= p ->
  apply_parameters xs k (lift (p + length xs) 0 e) = lift p 0 e.
Proof with modulo_arith.
  intros.
  unfold apply_parameters.
  sigma...
Qed.

Lemma apply_parameters_bound_gt:
  forall xs n k,
  length xs + k <= n ->
  apply_parameters xs k (bound n) = n - length xs.
Proof with modulo_arith.
  intros.
  unfold apply_parameters.
  sigma...
Qed.

Lemma apply_parameters_bound_lt:
  forall xs n k,
  k > n ->
  apply_parameters xs k (bound n) = n.
Proof.
  intros.
  unfold apply_parameters.
  now sigma.
Qed.

Lemma apply_parameters_bound_in:
  forall n xs,
  length xs > n ->
  forall x,
  item x xs n ->
  forall k,
  apply_parameters xs k (bound (k + n)) = lift k 0 x.
Proof.
  intros.
  unfold apply_parameters.
  sigma.
  replace (k + n - k) with n by lia.
  generalize dependent k.
  induction H0; intros.
  - now sigma.
  - sigma.
    apply IHitem.
    simpl in H; lia.
Qed.

Lemma right_cycle_bound_lt:
  forall k n,
  n < k ->
  right_cycle k 0 (bound n) = S n.
Proof.
  intros.
  unfold right_cycle; sigma.
  replace (S n) with (n + 1) by lia.
  replace (S k) with (1 + k) by lia.
  generalize 1 as p.
  generalize dependent k.
  induction n; intros.
  - destruct k; try lia.
    simpl; now sigma.
  - destruct k; try lia.
    simpl; sigma.
    rewrite IHn.
    + modulo_arith.
    + lia.
Qed.

Lemma right_cycle_bound_eq:
  forall k n,
  n = k ->
  right_cycle k 0 (bound n) = 0.
Proof.
  intros; subst.
  unfold right_cycle; sigma.
  replace (S k) with (1 + k) by lia.
  generalize 1 as p.
  induction k; intros.
  - simpl; now sigma.
  - simpl; sigma.
    now rewrite IHk.
Qed.

Lemma right_cycle_bound_gt:
  forall k n,
  n > k ->
  right_cycle k 0 (bound n) = n.
Proof with modulo_arith.
  intros.
  unfold right_cycle.
  assert (length (high_sequence k) = k) by apply sequence_length.
  sigma; f_equal.
  rewrite app_length, H0; simpl.
  lia.
Qed.

Lemma apply_parameters_type:
  forall xs k,
  apply_parameters xs k type = type.
Proof.
  auto.
Qed.

Lemma right_cycle_type:
  forall i k,
  right_cycle i k type = type.
Proof.
  auto.
Qed.

Lemma apply_parameters_prop:
  forall xs k,
  apply_parameters xs k prop = prop.
Proof.
  auto.
Qed.

Lemma right_cycle_prop:
  forall i k,
  right_cycle i k prop = prop.
Proof.
  auto.
Qed.

Lemma apply_parameters_base:
  forall xs k,
  apply_parameters xs k base = base.
Proof.
  auto.
Qed.

Lemma right_cycle_base:
  forall i k,
  right_cycle i k base = base.
Proof.
  auto.
Qed.

Lemma apply_parameters_void:
  forall xs k,
  apply_parameters xs k void = void.
Proof.
  auto.
Qed.

Lemma right_cycle_void:
  forall i k,
  right_cycle i k void = void.
Proof.
  auto.
Qed.

Lemma right_cycle_distributes_over_negation:
  forall n k ts,
  right_cycle n k (negation ts) =
    negation (traverse_list (right_cycle n) k ts).
Proof.
  auto.
Qed.

Lemma right_cycle_distributes_over_jump:
  forall n p k xs,
  right_cycle n p (jump k xs) =
    jump (right_cycle n p k) (map (right_cycle n p) xs).
Proof.
  auto.
Qed.

Lemma right_cycle_distributes_over_bind:
  forall n k b ts c,
  right_cycle n k (bind b ts c) =
    bind (right_cycle n (S k) b)
      (traverse_list (right_cycle n) k ts)
      (right_cycle n (k + length ts) c).
Proof.
  auto.
Qed.

Lemma right_cycle_zero_e_equals_e:
  forall e k,
  right_cycle 0 k e = e.
Proof.
  intros.
  unfold right_cycle.
  simpl.
  now sigma.
Qed.

Lemma switch_bindings_distributes_over_negation:
  forall k ts,
  switch_bindings k (negation ts) =
    negation (traverse_list switch_bindings k ts).
Proof.
  auto.
Qed.

Lemma switch_bindings_distributes_over_jump:
  forall p k xs,
  switch_bindings p (jump k xs) =
    jump (switch_bindings p k) (map (switch_bindings p) xs).
Proof.
  auto.
Qed.

Lemma switch_bindings_distributes_over_bind:
  forall k b ts c,
  switch_bindings k (bind b ts c) =
    bind (switch_bindings (S k) b)
      (traverse_list switch_bindings k ts)
        (switch_bindings (k + length ts) c).
Proof.
  auto.
Qed.

Lemma switch_bindings_bound_eq:
  forall k n,
  k = n ->
  switch_bindings k (bound n) = bound (S n).
Proof with modulo_arith.
  intros.
  unfold switch_bindings.
  sigma...
Qed.

Lemma apply_parameters_high_sequence_bound_in:
  forall n i k,
  n >= k ->
  i + k > n ->
  apply_parameters (high_sequence i) k (bound n) = bound (S n).
Proof.
  intros.
  replace n with (k + (n - k)); try lia.
  rewrite apply_parameters_bound_in with (x := S (n - k)).
  - now sigma.
  - rewrite sequence_length; lia.
  - apply item_sequence with (i := 1).
    lia.
Qed.

Lemma right_cycle_right_cycle_simplification:
  forall e k p i,
  right_cycle i k (right_cycle p (i + k) e) =
    right_cycle (i + p) k e.
Proof.
  intros.
  unfold right_cycle.
  assert (length (high_sequence i) = i) by apply sequence_length.
  assert (length (high_sequence p) = p) by apply sequence_length.
  assert (length (high_sequence (i + p)) = i + p) by apply sequence_length.
  sigma; do 3 f_equal.
  - clear H H0 H1.
    replace (smap _ 0 _) with (sequence (1 + i) p ++ [bound 0]).
    + generalize 1.
      induction i; simpl; intros.
      * now rewrite Nat.add_0_r.
      * f_equal.
        replace (n + S i) with (S n + i) by lia.
        now rewrite IHi.
    + generalize dependent i.
      replace 1 with (0 + 1) by auto.
      generalize 0 at 1 6.
      induction p; simpl; intros.
      * now sigma.
      * simpl; sigma.
        rewrite Nat.add_comm; f_equal.
        replace (S (S (i + n))) with (S n + 1 + i) by lia.
        rewrite IHp.
        repeat f_equal; lia.
  - modulo_arith.
Qed.

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
Proof with modulo_arith.
  intros.
  unfold switch_bindings.
  sigma.
  replace (k - k) with 0 by lia; simpl.
  replace (k - k) with 0 by lia; simpl.
  generalize dependent k.
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (le_gt_dec k n).
    + destruct (le_gt_dec (S k) n).
      * sigma...
      * sigma...
    + sigma...
  - sigma; f_equal.
    induction H.
    + reflexivity.
    + sigma; f_equal; auto.
  - sigma; f_equal.
    + apply IHe.
    + induction H.
      * reflexivity.
      * sigma; f_equal; auto.
  - sigma; f_equal.
    + apply IHe1.
    + induction H.
      * reflexivity.
      * sigma; f_equal; auto.
    + apply IHe2.
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
  intros.
  unfold left_cycle.
  now sigma.
Qed.

Lemma left_cycle_switch_bindings_simplification:
  forall e i k,
  left_cycle i (S k) (switch_bindings k e) = left_cycle (S i) k e.
Proof with modulo_arith.
  intros.
  unfold left_cycle.
  unfold switch_bindings.
  sigma.
  replace (S k - k + i) with (1 + i) by lia.
  replace (S (S (i + k)) - k - 2) with i by lia.
  replace (S (2 - (S k - k) - 1 + k) - k) with 1 by lia.
  replace (S i) with (1 + i) by lia.
  replace (S (S (i + k)) - k - 1) with (1 + i) by lia.
  generalize dependent k.
  generalize dependent i.
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (le_gt_dec k n);
    destruct (le_gt_dec (S k) n);
    destruct (le_gt_dec (S (S k)) n);
    destruct (le_gt_dec i (n - k - 2));
    try (exfalso; lia);
    sigma...
  - sigma; f_equal.
    induction H.
    + reflexivity.
    + sigma; f_equal; auto.
  - sigma; f_equal.
    + apply IHe.
    + induction H.
      * reflexivity.
      * sigma; f_equal; auto.
  - sigma; f_equal.
    + apply IHe1.
    + induction H.
      * reflexivity.
      * sigma; f_equal; auto.
    + apply IHe2.
Qed.

Lemma not_free_lift:
  forall c p k j,
  not_free (p + j) c ->
  not_free (p + k + j) (lift k j c).
Proof.
  intros.
  remember (p + j) as a.
  replace (p + k + j) with (a + k) by lia.
  remember (a + k) as b.
  generalize dependent j.
  generalize dependent k.
  generalize dependent b.
  generalize dependent a.
  sigma.
  induction c using pseudoterm_deepind; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct (le_gt_dec j n).
    + dependent destruction H.
      sigma; constructor; lia.
    + sigma; constructor; lia.
  - dependent destruction H0.
    sigma; constructor.
    induction H.
    + constructor.
    + dependent destruction H0.
      sigma; constructor; auto.
      rewrite bsmap_length.
      eapply H; eauto; lia.
  - dependent destruction H0.
    sigma; constructor.
    + eapply IHc; eauto.
    + induction H.
      * constructor.
      * dependent destruction H1.
        sigma; constructor; eauto.
  - dependent destruction H0.
    sigma; constructor.
    + eapply IHc1; eauto; lia.
    + clear H0_ H0_0.
      induction H.
      * constructor.
      * dependent destruction H0.
        sigma; constructor; auto.
        rewrite bsmap_length.
        eapply H; eauto; lia.
    + rewrite bsmap_length.
      eapply IHc2; eauto; lia.
Qed.

(* Local Lemma not_free_apply_parameters_bound:
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
Qed. *)

Lemma not_free_apply_parameters:
  forall c k p xs,
  Forall (not_free p) xs ->
  not_free (p + k + length xs) c ->
  not_free (p + k) (apply_parameters xs k c).
Proof.
  intros.
  remember (p + k) as a.
  remember (a + length xs) as b.
  generalize dependent xs.
  generalize dependent k.
  generalize dependent b.
  generalize dependent a.
  sigma.
  induction c using pseudoterm_deepind; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - unfold apply_parameters.
    destruct (le_gt_dec k n).
    + sigma.
      dependent destruction H0.
      destruct (le_gt_dec (length xs) (n - k)).
      * sigma; constructor.
        lia.
      * (* TODO: refactor me, please? *)
        subst.
        remember (n - k) as o.
        clear H l Heqo.
        generalize dependent o.
        induction H0; intros.
        --- inversion g.
        --- simpl in *.
            destruct o.
            +++ sigma.
                replace (inst (subst_lift k)) with (lift k 0) by auto.
                replace (p + k) with (p + k + 0) by lia.
                apply not_free_lift.
                rewrite Nat.add_0_r.
                assumption.
            +++ sigma.
                apply IHForall; lia.
    + sigma; constructor; lia.
  - dependent destruction H0.
    sigma; constructor.
    induction H.
    + constructor.
    + dependent destruction H0.
      sigma; constructor; auto.
      rewrite bsmap_length.
      eapply H; eauto; lia.
  - dependent destruction H0.
    sigma; constructor.
    + eapply IHc; eauto.
    + induction H.
      * constructor.
      * dependent destruction H1.
        sigma; constructor; auto.
        eapply H; eauto.
  - dependent destruction H0.
    sigma; constructor.
    + eapply IHc1; eauto; lia.
    + clear H0_ H0_0.
      induction H.
      * constructor.
      * dependent destruction H0.
        sigma; constructor; auto.
        rewrite bsmap_length.
        eapply H; eauto; lia.
    + rewrite bsmap_length.
      eapply IHc2; eauto; lia.
Qed.

Lemma remove_binding_size:
  forall b k,
  not_free k b ->
  size (remove_binding k b) = size b.
Proof with modulo_arith.
  induction b; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold remove_binding.
    destruct (le_gt_dec k n).
    + dependent destruction H.
      now sigma.
    + now sigma.
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

Lemma apply_parameters_cons:
  forall y ys k e,
  apply_parameters (y :: ys) k e = subst y k (apply_parameters ys (1 + k) e).
Proof.
  intros.
  unfold apply_parameters.
  now sigma.
Qed.

Lemma apply_parameters_nil:
  forall k e,
  apply_parameters [] k e = e.
Proof.
  intros.
  unfold apply_parameters.
  now sigma.
Qed.

Lemma right_cycle_characterization:
  forall i k e,
  right_cycle i k e =
    apply_parameters (high_sequence i ++ [bound 0]) k (lift (S i) (S i + k) e).
Proof.
  intros.
  unfold right_cycle.
  unfold apply_parameters.
  assert (length (high_sequence i) = i) by apply sequence_length.
  now sigma.
Qed.

Lemma switch_bindings_characterization:
  forall k e,
  switch_bindings k e = subst (bound 1) k (lift 1 (2 + k) e).
Proof with modulo_arith.
  intros.
  sigma.
  replace (S (S k) - k - 1) with 1 by lia.
  generalize dependent k.
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold switch_bindings.
    destruct (le_gt_dec k n).
    + remember (n - k) as o.
      destruct o.
      * now sigma.
      * destruct o; sigma...
    + now sigma.
  - sigma; f_equal.
    induction H; auto.
    sigma; f_equal; auto.
  - sigma; f_equal; auto.
    induction H; auto.
    sigma; f_equal; auto.
  - sigma; f_equal; auto.
    induction H; auto.
    sigma; f_equal; auto.
Qed.
