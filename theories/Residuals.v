(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.
Require Import Local.Reduction.

(** ** Residuals *)

Inductive redexes: Set :=
  | redexes_type
  | redexes_prop
  | redexes_base
  | redexes_void
  | redexes_bound (n: nat)
  | redexes_negation (ts: list pseudoterm)
  | redexes_jump (r: bool) (f: pseudoterm) (xs: list pseudoterm)
  | redexes_placeholder (f: pseudoterm) (xs: list pseudoterm)
  | redexes_bind (b: redexes) (ts: list pseudoterm) (c: redexes).

Fixpoint mark (e: pseudoterm): redexes :=
  match e with
  | type =>
    redexes_type
  | prop =>
    redexes_prop
  | base =>
    redexes_base
  | void =>
    redexes_void
  | bound n =>
    redexes_bound n
  | negation ts =>
    redexes_negation ts
  | jump f xs =>
    redexes_jump false f xs
  | bind b ts c =>
    redexes_bind (mark b) ts (mark c)
  end.

Fixpoint unmark (e: redexes): pseudoterm :=
  match e with
  | redexes_type =>
    type
  | redexes_prop =>
    prop
  | redexes_base =>
    base
  | redexes_void =>
    void
  | redexes_bound n =>
    n
  | redexes_negation ts =>
    negation ts
  | redexes_jump r f xs =>
    jump f xs
  | redexes_placeholder f xs =>
    jump f xs
  | redexes_bind b ts c =>
    bind (unmark b) ts (unmark c)
  end.

Lemma unmark_mark_is_sound:
  forall e,
  unmark (mark e) = e.
Proof.
  induction e; simpl; auto.
  rewrite IHe1, IHe2; auto.
Qed.

Fixpoint redexes_lift i k e: redexes :=
  match e with
  | redexes_jump r f xs =>
    redexes_jump r (lift i k f) (map (lift i k) xs)
  | redexes_placeholder f xs =>
    redexes_placeholder (lift i k f) (map (lift i k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_lift i (S k) b)
      (traverse_list (lift i) k ts)
      (redexes_lift i (k + length ts) c)
  | _ =>
    mark (lift i k (unmark e))
  end.

Fixpoint redexes_subst y k e: redexes :=
  match e with
  | redexes_jump r f xs =>
    redexes_jump r (subst y k f) (map (subst y k) xs)
  | redexes_placeholder f xs =>
    redexes_placeholder (subst y k f) (map (subst y k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_subst y (S k) b)
      (traverse_list (subst y) k ts)
      (redexes_subst y (k + length ts) c)
  | _ =>
    mark (subst y k (unmark e))
  end.

Fixpoint redexes_apply_parameters ys k e: redexes :=
  match ys with
  | [] => e
  | y :: ys => redexes_apply_parameters ys k (redexes_subst y (k + length ys) e)
  end.

Fixpoint redexes_flow y a k e: redexes :=
  match e with
  | redexes_placeholder (bound n) xs =>
    if Nat.eq_dec n k then
      if Nat.eq_dec a (length xs) then
        redexes_apply_parameters xs 0
          (redexes_lift (S n) (length xs) y)
      else
        e
    else
      e
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_flow y a (S k) b)
      ts
      (redexes_flow y a (k + length ts) c)
  | _ =>
    e
  end.

Fixpoint redexes_full e: redexes :=
  match e with
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_flow (redexes_full c) (length ts) 0
        (redexes_full b)) ts (redexes_full c)
  | _ =>
    e
  end.

(* -------------------------------------------------------------------------- *)

(*
Lemma redexes_lift_lift_permutation:
  forall e i j k l,
  k <= l ->
  redexes_lift i k (redexes_lift j l e) =
    redexes_lift j (i + l) (redexes_lift i k e).
Proof.
  induction e; simpl; intros.
  - f_equal.
    apply lift_lift_permutation; auto.
  - f_equal.
    + apply lift_lift_permutation; auto.
    + induction xs; auto.
      simpl; f_equal; auto.
      apply lift_lift_permutation; auto.
  - f_equal.
    + apply lift_lift_permutation; auto.
    + induction xs; auto.
      simpl; f_equal; auto.
      apply lift_lift_permutation; auto.
  - f_equal.
    + replace (S (i + l)) with (i + S l); try lia.
      apply IHe1; lia.
    + clear IHe1 IHe2.
      induction ts; auto.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      rewrite lift_lift_permutation; try lia.
      f_equal; lia.
    + do 2 rewrite traverse_list_length.
      replace (i + l + length ts) with (i + (l + length ts)); try lia.
      apply IHe2; lia.
Qed.

Lemma redexes_lift_addition_distributes_over_flow:
  forall b i k p a c,
  redexes_lift i (p + S k) (redexes_flow c a p b) =
    redexes_flow (redexes_lift i (k + a) c) a p (redexes_lift i (p + S k) b).
Proof.
  induction b; simpl; intros.
  - reflexivity.
  - reflexivity.
  - destruct f; try reflexivity.
    destruct (Nat.eq_dec n p).
    + rewrite lift_bound_lt; try lia.
      rewrite map_length.
      destruct (Nat.eq_dec a (length xs)).
      * destruct (Nat.eq_dec n p); try lia.
        rewrite redexes_lift_distributes_over_apply_parameters.
        f_equal; symmetry.
        rewrite redexes_lift_lift_permutation; try lia.
        f_equal; lia.
      * destruct (Nat.eq_dec n p); try lia.
        simpl.
        rewrite lift_bound_lt; try lia.
        reflexivity.
    + destruct (le_gt_dec (p + S k) n).
      * rewrite lift_bound_ge; try lia.
        destruct (Nat.eq_dec (i + n) p); try lia.
        simpl.
        rewrite lift_bound_ge; try lia.
        reflexivity.
      * rewrite lift_bound_lt; try lia.
        destruct (Nat.eq_dec n p); try lia.
        simpl.
        rewrite lift_bound_lt; try lia.
        reflexivity.
  - f_equal.
    + replace (S (p + S k)) with (S p + S k); try lia.
      apply IHb1.
    + rewrite traverse_list_length.
      replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHb2.
Qed.

Lemma redexes_lift_distributes_over_flow:
  forall b i k a c,
  redexes_lift i (S k) (redexes_flow c a 0 b) =
    redexes_flow (redexes_lift i (k + a) c) a 0 (redexes_lift i (S k) b).
Proof.
  intros.
  apply redexes_lift_addition_distributes_over_flow with (p := 0).
Qed.
*)

Lemma redexes_lift_addition_distributes_over_apply_parameters:
  forall ys i k p e,
  redexes_lift i (p + k) (redexes_apply_parameters ys p e) =
    redexes_apply_parameters (map (lift i k) ys) p
      (redexes_lift i (p + length ys + k) e).
Proof.
  induction ys; simpl; intros.
  - f_equal; lia.
  - rewrite IHys; f_equal.
    rewrite map_length.
    admit.
Admitted.

Lemma redexes_lift_distributes_over_apply_parameters:
  forall ys i k e,
  redexes_lift i k (redexes_apply_parameters ys 0 e) =
  redexes_apply_parameters (map (lift i k) ys) 0
    (redexes_lift i (length ys + k) e).
Proof.
  intros.
  apply redexes_lift_addition_distributes_over_apply_parameters with (p := 0).
Qed.

Lemma redexex_lift_lift_simplification:
  forall e i j k l,
  k <= l + j ->
  l <= k ->
  redexes_lift i k (redexes_lift j l e) = redexes_lift (i + j) l e.
Proof.
  induction e; simpl; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (le_gt_dec l n).
    + rewrite lift_bound_ge; auto.
      rewrite lift_bound_ge; auto.
      simpl.
      rewrite lift_bound_ge; try lia.
      simpl; f_equal; lia.
    + rewrite lift_bound_lt; auto.
      rewrite lift_bound_lt; auto.
      simpl.
      rewrite lift_bound_lt; try lia.
      simpl; auto.
  - f_equal.
    induction ts; simpl; auto.
    f_equal; auto.
    do 3 rewrite traverse_list_length.
    apply lift_lift_simplification; lia.
  - rewrite map_map.
    rewrite lift_lift_simplification; auto.
    f_equal; list induction over xs.
    apply lift_lift_simplification; auto.
  - rewrite lift_lift_simplification; auto.
    f_equal; list induction over xs.
    apply lift_lift_simplification; auto.
  - f_equal.
    + apply IHe1; lia.
    + list induction over ts.
      do 3 rewrite traverse_list_length.
      rewrite lift_lift_simplification; try lia.
      reflexivity.
    + rewrite traverse_list_length.
      apply IHe2; lia.
Qed.

Lemma redexes_flow_and_lift_commute:
  forall e y a k p i,
  k <= p ->
  redexes_flow y a (i + p) (redexes_lift i k e) =
    redexes_lift i k (redexes_flow y a p e).
Proof.
  induction e; simpl; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
    + rewrite lift_bound_lt; auto.
  - reflexivity.
  - reflexivity.
  - destruct f; auto.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; try lia.
      rewrite map_length.
      destruct (Nat.eq_dec a (length xs));
      destruct (Nat.eq_dec n p);
      destruct (Nat.eq_dec (i + n) (i + p));
      simpl; try lia.
      * rewrite redexes_lift_distributes_over_apply_parameters.
        rewrite redexex_lift_lift_simplification; try lia.
        f_equal; f_equal; lia.
      * rewrite lift_bound_ge; auto.
      * rewrite lift_bound_ge; auto.
      * rewrite lift_bound_ge; auto.
    + rewrite lift_bound_lt; try lia.
      rewrite map_length.
      destruct (Nat.eq_dec a (length xs));
      destruct (Nat.eq_dec n p);
      destruct (Nat.eq_dec n (i + p));
      simpl; try lia.
      * rewrite lift_bound_lt; auto.
      * rewrite lift_bound_lt; auto.
  - f_equal.
    + rewrite plus_n_Sm.
      apply IHe1; lia.
    + rewrite traverse_list_length.
      rewrite <- plus_assoc.
      apply IHe2; lia.
Qed.

Lemma redexes_flow_addition_distributes_over_itself:
  forall b a1 a2 p k c1 c2,
  redexes_flow c2 a1 (p + S k) (redexes_flow c1 a2 p b) =
    redexes_flow (redexes_flow c2 a1 (k + a2) c1)
      a2 p (redexes_flow c2 a1 (p + S k) b).
Proof.
  induction b; simpl; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* Huh, some ugly case analysis... I should have a math simpl tactic! *)
    destruct f; auto;
    do 2 (destruct (Nat.eq_dec n p);
          destruct (Nat.eq_dec n (p + S k));
          destruct (Nat.eq_dec a1 (length xs));
          destruct (Nat.eq_dec a2 (length xs));
          simpl; auto; try lia).
    + admit.
    + admit.
    + admit.
    + admit.
  - f_equal.
    + replace (S (p + S k)) with (S p + S k); try lia.
      apply IHb1.
    + replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHb2.
Admitted.

Lemma redexes_flow_commute:
  forall b a1 a2 k c1 c2,
  redexes_flow c2 a1 (S k) (redexes_flow c1 a2 0 b) =
    redexes_flow (redexes_flow c2 a1 (k + a2) c1)
      a2 0 (redexes_flow c2 a1 (S k) b).
Proof.
  intros.
  apply redexes_flow_addition_distributes_over_itself with (p := 0).
Qed.

Lemma redexes_lift_is_sound:
  forall e i k,
  redexes_lift i k (mark e) = mark (lift i k e).
Proof.
  induction e; simpl; auto; intros.
  f_equal.
  - apply IHe1.
  - apply IHe2.
Qed.

Lemma redexes_subst_is_sound:
  forall e y k,
  redexes_subst y k (mark e) = mark (subst y k e).
Proof.
  induction e; simpl; auto; intros.
  f_equal.
  - apply IHe1.
  - apply IHe2.
Qed.

Lemma redexes_apply_parameters_is_sound:
  forall xs k e,
  redexes_apply_parameters xs k (mark e) = mark (apply_parameters xs k e).
Proof.
  induction xs; simpl; intros.
  - reflexivity.
  - rewrite redexes_subst_is_sound.
    rewrite IHxs; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive compatible: relation redexes :=
  | compatible_type:
    compatible redexes_type redexes_type
  | compatible_prop:
    compatible redexes_prop redexes_prop
  | compatible_base:
    compatible redexes_base redexes_base
  | compatible_void:
    compatible redexes_void redexes_void
  | compatible_bound:
    forall n,
    compatible (redexes_bound n) (redexes_bound n)
  | compatible_negation:
    forall ts,
    compatible (redexes_negation ts) (redexes_negation ts)
  | compatible_jump:
    forall r1 r2 f xs,
    compatible (redexes_jump r1 f xs) (redexes_jump r2 f xs)
  | compatible_placeholder:
    forall f xs,
    compatible (redexes_placeholder f xs) (redexes_placeholder f xs)
  | compatible_bind:
    forall b1 b2 ts c1 c2,
    compatible b1 b2 ->
    compatible c1 c2 ->
    compatible (redexes_bind b1 ts c1) (redexes_bind b2 ts c2).

Global Hint Constructors compatible: cps.

Lemma compatible_refl:
  forall e,
  compatible e e.
Proof.
  induction e; auto with cps.
Qed.

Global Hint Resolve compatible_refl: cps.

Lemma compatible_sym:
  forall a b,
  compatible a b -> compatible b a.
Proof.
  induction 1; auto with cps.
Qed.

Global Hint Resolve compatible_sym: cps.

Lemma compatible_trans:
  forall a b,
  compatible a b ->
  forall c,
  compatible b c -> compatible a c.
Proof.
  induction 1; inversion_clear 1; auto with cps.
Qed.

Global Hint Resolve compatible_trans: cps.

Lemma compatible_lift:
  forall a b,
  compatible a b ->
  forall i k,
  compatible (redexes_lift i k a) (redexes_lift i k b).
Proof.
  induction 1; simpl; auto with cps.
Qed.

Lemma compatible_subst:
  forall a b,
  compatible a b ->
  forall y k,
  compatible (redexes_subst y k a) (redexes_subst y k b).
Proof.
  induction 1; simpl; auto with cps.
Qed.

Lemma compatible_apply_parameters:
  forall ys k a b,
  compatible a b ->
  compatible (redexes_apply_parameters ys k a)
    (redexes_apply_parameters ys k b).
Proof.
  induction ys; simpl; intros.
  - assumption.
  - apply IHys.
    apply compatible_subst.
    assumption.
Qed.

Lemma compatible_flow:
  forall b1 b2 c1 c2 a,
  compatible c1 c2 ->
  compatible b1 b2 ->
  forall k,
  compatible (redexes_flow c1 a k b1) (redexes_flow c2 a k b2).
Proof.
  induction 2; simpl; auto with cps.
  (* Case: placeholder. *)
  intros.
  destruct f; try constructor.
  destruct (Nat.eq_dec n k); try constructor.
  destruct (Nat.eq_dec a (length xs)); try constructor.
  apply compatible_apply_parameters.
  apply compatible_lift.
  assumption.
Qed.

Inductive residuals: redexes -> redexes -> redexes -> Prop :=
  | residuals_type:
    residuals redexes_type redexes_type redexes_type
  | residuals_prop:
    residuals redexes_prop redexes_prop redexes_prop
  | residuals_base:
    residuals redexes_base redexes_base redexes_base
  | residuals_void:
    residuals redexes_void redexes_void redexes_void
  | residuals_bound:
    forall n,
    residuals (redexes_bound n) (redexes_bound n) (redexes_bound n)
  | residuals_negation:
    forall ts,
    residuals (redexes_negation ts) (redexes_negation ts) (redexes_negation ts)
  | residuals_jump:
    forall r k xs,
    residuals
      (redexes_jump r k xs)
      (redexes_jump false k xs)
      (redexes_jump r k xs)
  | residuals_mark:
    forall r k xs,
    residuals
      (redexes_jump r k xs)
      (redexes_jump true k xs)
      (redexes_placeholder k xs)
  | residuals_placeholder:
    forall k xs,
    residuals
      (redexes_placeholder k xs)
      (redexes_placeholder k xs)
      (redexes_placeholder k xs)
  | residuals_bind:
    forall b1 b2 b3 ts c1 c2 c3,
    residuals b1 b2 b3 ->
    residuals c1 c2 c3 ->
    residuals
      (redexes_bind b1 ts c1)
      (redexes_bind b2 ts c2)
      (* We shall postpone replacements in b3 here. *)
      (redexes_bind b3 ts c3).

Global Hint Constructors residuals: cps.

Lemma residuals_is_unique:
  forall a b c1,
  residuals a b c1 ->
  forall c2,
  residuals a b c2 -> c1 = c2.
Proof.
  induction 1; intros.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H1.
    replace b5 with b3; auto.
    replace c5 with c3; auto.
Qed.

Lemma compatible_residuals:
  forall a b c,
  residuals a b c ->
  compatible a b.
Proof.
  induction 1; auto with cps.
Qed.

Global Hint Resolve compatible_residuals: cps.

Lemma residuals_preserve_compatible:
  forall a1 a2,
  compatible a1 a2 ->
  forall b c1,
  residuals a1 b c1 ->
  forall c2,
  residuals a2 b c2 -> compatible c1 c2.
Proof.
  induction 1; intros.
  - dependent destruction H.
    dependent destruction H0.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    constructor.
  - dependent destruction H.
    + dependent destruction H0.
      constructor.
    + dependent destruction H0.
      constructor.
  - dependent destruction H.
    dependent destruction H0.
    constructor.
  - dependent destruction H1.
    dependent destruction H2.
    assert (compatible b4 b6); eauto.
    assert (compatible c4 c6); eauto.
    constructor; auto.
Qed.

Global Hint Resolve residuals_preserve_compatible: cps.

Lemma residuals_mark_term:
  forall e,
  residuals (mark e) (mark e) (mark e).
Proof.
  induction e; simpl; constructor; auto.
Qed.

Global Hint Resolve residuals_mark_term: cps.

Lemma residuals_lift:
  forall a b c,
  residuals a b c ->
  forall i k,
  residuals (redexes_lift i k a) (redexes_lift i k b) (redexes_lift i k c).
Proof.
  induction 1; simpl; auto with cps.
Qed.

Global Hint Resolve residuals_lift: cps.

Lemma residuals_subst:
  forall a b c,
  residuals a b c ->
  forall y k,
  residuals (redexes_subst y k a) (redexes_subst y k b) (redexes_subst y k c).
Proof.
  induction 1; simpl; auto with cps.
Qed.

Global Hint Resolve residuals_subst: cps.

Lemma residuals_apply_parameters:
  forall ys k a b c,
  residuals a b c ->
  residuals (redexes_apply_parameters ys k a) (redexes_apply_parameters ys k b)
    (redexes_apply_parameters ys k c).
Proof.
  induction ys; simpl; auto with cps.
Qed.

Global Hint Resolve residuals_apply_parameters: cps.

Lemma residuals_compatible:
  forall b1 b2,
  compatible b1 b2 ->
  exists b3,
  residuals b1 b2 b3.
Proof.
  induction 1; simpl; intros.
  - eexists; constructor.
  - eexists; constructor.
  - eexists; constructor.
  - eexists; constructor.
  - eexists; constructor.
  - eexists; constructor.
  - destruct r2.
    + eexists; constructor.
    + eexists; constructor.
  - eexists; constructor.
  - destruct IHcompatible1 as (b3, ?); auto.
    destruct IHcompatible2 as (c3, ?); auto.
    eexists; constructor; eauto.
Qed.

Global Hint Resolve residuals_compatible: cps.

Lemma cube:
  forall a r b,
  residuals a r b ->
  forall p c,
  residuals a p c ->
  forall rp,
  residuals r p rp ->
  forall pr,
  residuals p r pr ->
  forall d,
  residuals b pr d -> residuals c rp d.
Proof.
  induction 1; inversion_clear 1; intros.
  (* Case: (type, type). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (prop, prop). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (base, base). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (void, void). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (bound, bound). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (negation, negation). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (jump, jump). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (jump, mark). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (mark, jump). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (mark, mark). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (placeholder, placeholder). *)
  - dependent destruction H.
    dependent destruction H0.
    assumption.
  (* Case: (bind, bind). *)
  - dependent destruction H1.
    dependent destruction H4.
    dependent destruction H5.
    (* Replacements are postponed... *)
    constructor; eauto.
Qed.

Inductive paving_result b c r p: Prop :=
  paving_result_mk
    (pr: redexes)
    (rp: redexes)
    (d: redexes)
    (H1: residuals p r pr)
    (H2: residuals r p rp)
    (H3: residuals b pr d)
    (H4: residuals c rp d).

Lemma paving:
  forall a r b,
  residuals a r b ->
  forall p c,
  residuals a p c ->
  paving_result b c r p.
Proof.
  intros.
  assert (compatible p r).
  - apply compatible_trans with a.
    + apply compatible_sym.
      apply compatible_residuals with c.
      assumption.
    + apply compatible_residuals with b.
      assumption.
  - assert (exists pr, residuals p r pr) as (pr, ?); eauto with cps.
    assert (exists rp, residuals r p rp) as (rp, ?); eauto with cps.
    assert (exists d, residuals b pr d) as (d, ?); eauto with cps.
    apply paving_result_mk with pr rp d; auto.
    apply cube with a r b p pr; auto.
Qed.

Lemma redexes_flow_mark_equals_mark:
  forall e y a k,
  redexes_flow y a k (mark e) = mark e.
Proof.
  induction e; auto; intros.
  simpl.
  rewrite IHe1.
  rewrite IHe2.
  reflexivity.
Qed.

Lemma redexes_full_mark_equals_mark:
  forall e,
  redexes_full (mark e) = mark e.
Proof.
  induction e; auto; simpl.
  rewrite IHe1.
  rewrite IHe2.
  rewrite redexes_flow_mark_equals_mark.
  reflexivity.
Qed.

(* TODO: these definitions should probably be moved up. *)

Definition residuals_full a b c: Prop :=
  exists2 c',
  residuals a b c' & redexes_full c' = c.

Inductive redexes_context: Set :=
  | redexes_context_hole
  | redexes_context_left
      (b: redexes_context) (ts: list pseudoterm) (c: redexes)
  | redexes_context_right
      (b: redexes) (ts: list pseudoterm) (c: redexes_context).

Fixpoint apply_redexes_context h e: redexes :=
  match h with
  | redexes_context_hole =>
    e
  | redexes_context_left b ts c =>
    redexes_bind (apply_redexes_context b e) ts c
  | redexes_context_right b ts c =>
    redexes_bind b ts (apply_redexes_context c e)
  end.

Coercion apply_redexes_context: redexes_context >-> Funclass.

Fixpoint mark_context h: redexes_context :=
  match h with
  | context_hole =>
    redexes_context_hole
  | context_left b ts c =>
    redexes_context_left (mark_context b) ts (mark c)
  | context_right b ts c =>
    redexes_context_right (mark b) ts (mark_context c)
  end.

Lemma mark_context_is_sound:
  forall h e,
  mark_context h (mark e) = mark (h e).
Proof.
  induction h; simpl; congruence.
Qed.

Inductive redexes_same_path: relation redexes_context :=
  | redexes_same_path_hole:
    redexes_same_path redexes_context_hole redexes_context_hole
  | redexes_same_path_left:
    forall h r ts1 ts2 c1 c2,
    redexes_same_path h r ->
    length ts1 = length ts2 ->
    redexes_same_path
      (redexes_context_left h ts1 c1)
      (redexes_context_left r ts2 c2)
  | redexes_same_path_right:
    forall b1 b2 ts1 ts2 h r,
    redexes_same_path h r ->
    length ts1 = length ts2 ->
    redexes_same_path
      (redexes_context_right b1 ts1 h)
      (redexes_context_right b2 ts2 r).

Global Hint Constructors redexes_same_path: cps.

Lemma compatible_context_left_inversion:
  forall (h: redexes_context) e1 b,
  compatible (h e1) b ->
  exists r e2,
  redexes_same_path h r /\ b = r e2.
Proof.
  induction h; simpl; intros.
  - exists redexes_context_hole; simpl.
    exists b; auto with cps.
  - dependent destruction H.
    destruct IHh with e1 b2 as (r, (e2, (?, ?))); auto.
    exists (redexes_context_left r ts c2), e2; simpl.
    dependent destruction H2.
    firstorder with cps.
  - dependent destruction H.
    destruct IHh with e1 c2 as (r, (e2, (?, ?))); auto.
    exists (redexes_context_right b2 ts r), e2; simpl.
    dependent destruction H2.
    firstorder with cps.
Qed.

Lemma compatible_context_changing_hole:
  forall h r,
  redexes_same_path h r ->
  forall a b,
  compatible (h a) (r b) ->
  forall c d,
  compatible c d -> compatible (h c) (r d).
Proof.
  induction 1; simpl; intros.
  - assumption.
  - dependent destruction H1.
    constructor; auto.
    eapply IHredexes_same_path; eauto.
  - dependent destruction H1.
    constructor; auto.
    eapply IHredexes_same_path; eauto.
Qed.

Lemma redexes_flow_redexes_context:
  forall h c a k e,
  redexes_flow c a k (mark_context h e) =
    mark_context h (redexes_flow c a (k + #h) e).
Proof.
  induction h; simpl; intros.
  - f_equal; lia.
  - f_equal.
    + rewrite IHh; f_equal; f_equal.
      lia.
    + apply redexes_flow_mark_equals_mark.
  - f_equal.
    + apply redexes_flow_mark_equals_mark.
    + rewrite IHh; f_equal; f_equal.
      lia.
Qed.

Lemma redexes_full_redexes_context_simplification:
  forall h n,
  n >= #h ->
  forall xs,
  redexes_full (mark_context h (redexes_placeholder n xs)) =
    mark_context h (redexes_placeholder n xs).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal.
    + rewrite IHh; try lia.
      rewrite redexes_flow_redexes_context.
      f_equal; simpl.
      destruct (Nat.eq_dec n #h); try lia.
      reflexivity.
    + apply redexes_full_mark_equals_mark.
  - f_equal.
    + rewrite IHh; try lia.
      rewrite redexes_full_mark_equals_mark.
      apply redexes_flow_mark_equals_mark.
    + apply IHh; lia.
Qed.

Lemma residuals_preserve_hole:
  forall h r a b,
  redexes_same_path h r ->
  forall c,
  residuals (h a) (r b) c ->
  exists s e,
  redexes_same_path h s /\ residuals a b e /\ c = s e.
Proof.
  induction 1; simpl; intros.
  - exists redexes_context_hole; simpl.
    exists c; firstorder with cps.
  - dependent destruction H1.
    destruct IHredexes_same_path with b3 as (s, (e, (?, (?, ?)))); auto.
    exists (redexes_context_left s ts2 c4), e; simpl.
    split; [| split ].
    + auto with cps.
    + assumption.
    + congruence.
  - dependent destruction H1.
    destruct IHredexes_same_path with c3 as (s, (e, (?, (?, ?)))); auto.
    exists (redexes_context_right b4 ts2 s), e; simpl.
    split; [| split ].
    + auto with cps.
    + assumption.
    + congruence.
Qed.

(* Huh, this is a mess. TODO: Clean up this file please. *)

Definition arities: Set :=
  list (option nat).

Inductive regular: arities -> redexes -> Prop :=
  | regular_type:
    forall g,
    regular g (redexes_type)
  | regular_prop:
    forall g,
    regular g (redexes_prop)
  | regular_base:
    forall g,
    regular g (redexes_base)
  | regular_void:
    forall g,
    regular g (redexes_void)
  | regular_bound:
    forall g n,
    regular g (redexes_bound n)
  | regular_negation:
    forall g ts,
    regular g (redexes_negation ts)
  | regular_jump:
    forall g n xs,
    regular g (redexes_jump false n xs)
  | regular_mark:
    forall g a n xs,
    item (Some a) g n ->
    a = length xs ->
    regular g (redexes_jump true n xs)
  | regular_placeholder:
    forall g a n xs,
    item (Some a) g n ->
    a = length xs ->
    regular g (redexes_placeholder n xs)
  | regular_bind:
    forall g b ts c,
    regular (Some (length ts) :: g) b ->
    regular (repeat None (length ts) ++ g) c ->
    regular g (redexes_bind b ts c).

Global Hint Constructors regular: cps.

Lemma regular_tail:
  forall g1 e,
  regular g1 e ->
  forall g2,
  regular (g1 ++ g2) e.
Proof.
  induction 1; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - econstructor; eauto.
    apply item_insert_tail; auto.
  - econstructor; eauto.
    apply item_insert_tail; auto.
  - constructor.
    + simpl in IHregular1; auto.
    + rewrite app_assoc; auto.
Qed.

Lemma regular_mark_term:
  forall g e,
  regular g (mark e).
Proof.
  intros.
  replace g with ([] ++ g); auto.
  apply regular_tail.
  induction e; simpl; auto with cps.
  constructor.
  + eapply regular_tail in IHe1; eauto.
  + eapply regular_tail in IHe2; eauto.
Qed.

Lemma regular_single_jump:
  forall h g xs,
  regular (g ++ [Some (length xs)])
    (mark_context h (redexes_jump true (length g + #h) xs)).
Proof.
  induction h; simpl; intros.
  - rewrite plus_comm.
    econstructor; eauto.
    apply item_insert_head.
    constructor.
  - constructor.
    + rewrite app_comm_cons.
      rewrite <- plus_Snm_nSm.
      apply IHh.
    + apply regular_mark_term.
  - constructor.
    + apply regular_mark_term.
    + rewrite app_assoc.
      replace (length g + (#h + length ts)) with
        (length (repeat None (length ts) ++ g) + #h).
      * apply IHh.
      * rewrite app_length.
        rewrite repeat_length.
        lia.
Qed.

Fixpoint redexes_context_bvars h: nat :=
  match h with
  | redexes_context_hole =>
    0
  | redexes_context_left b _ _ =>
    S (redexes_context_bvars b)
  | redexes_context_right _ ts c =>
    redexes_context_bvars c + length ts
  end.

Lemma regular_cant_jump_too_far:
  forall n h g,
  n = length g + redexes_context_bvars h ->
  forall xs,
  ~regular g (h (redexes_jump true n xs)).
Proof.
  induction h; simpl; intros.
  - intro.
    dependent destruction H0.
    assert (n < length g).
    + eapply item_valid_index.
      eassumption.
    + lia.
  - intro.
    dependent destruction H0.
    eapply IHh; eauto; simpl.
    lia.
  - intro.
    dependent destruction H0.
    eapply IHh; eauto.
    rewrite app_length.
    rewrite repeat_length.
    lia.
Qed.

Lemma residuals_preserve_regular:
  forall a b c,
  residuals a b c ->
  forall g,
  regular g a -> regular g b -> regular g c.
Proof.
  induction 1; intros.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - dependent destruction H0.
    econstructor; eauto.
  - assumption.
  - dependent destruction H1.
    dependent destruction H2.
    constructor; auto.
Qed.

Lemma redexes_flow_regular_simplification:
  forall g x,
  regular g x ->
  forall c a k,
  k >= length g ->
  redexes_flow c a k x = x.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (n < length g).
    + eapply item_valid_index.
      eassumption.
    + destruct (Nat.eq_dec n k); try lia.
      reflexivity.
  - f_equal.
    + apply IHregular1; simpl.
      lia.
    + apply IHregular2; simpl.
      rewrite app_length, repeat_length.
      lia.
Qed.

Lemma redexes_flow_preserve_regular:
  forall a g b h,
  regular (h ++ Some a :: g) b ->
  forall c,
  regular (repeat None a ++ g) c ->
  forall k,
  k = length h ->
  regular (h ++ Some a :: g) (redexes_flow c a k b).
Proof.
  induction b; simpl; intros.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - destruct f; auto.
    destruct (Nat.eq_dec n k); auto.
    destruct (Nat.eq_dec a (length xs)); auto.
    dependent destruction H.
    (* Aw crap, this must be true but it'll be annoying to prove. *)
    admit.
  - dependent destruction H.
    constructor.
    + rewrite app_comm_cons.
      apply IHb1; simpl; auto.
    + rewrite app_assoc.
      apply IHb2.
      * rewrite <- app_assoc.
        assumption.
      * assumption.
      * rewrite app_length, repeat_length.
        lia.
Admitted.

Lemma redexes_full_preserves_regular:
  forall g x,
  regular g x ->
  regular g (redexes_full x).
Proof.
  induction 1; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor.
    + apply redexes_flow_preserve_regular with (h := []); auto.
    + assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* TODO: organize this file. So far, everything above is used to prove that   *)
(* parallel includes step. Everything below is needed to prove that star      *)
(* includes parallel. There might be a few unused lemmas I forgot to remove.  *)
(* -------------------------------------------------------------------------- *)

Fixpoint redexes_mark_count k r: nat :=
  match r with
  | redexes_jump true (bound n) _ =>
    if Nat.eq_dec k n then
      1
    else
      0
  | redexes_placeholder (bound n) _ =>
    if Nat.eq_dec k n then
      1
    else
      0
  | redexes_bind b ts c =>
    redexes_mark_count (S k) b + redexes_mark_count (k + length ts) c
  | _ =>
    0
  end.

Fixpoint redexes_mark_count_total r: nat :=
  match r with
  | redexes_jump true f xs =>
    1
  | redexes_placeholder f xs =>
    1
  | redexes_bind b ts c =>
    redexes_mark_count_total b + redexes_mark_count_total c
  | _ =>
    0
  end.

Lemma redexes_structural_mark_ind:
  forall P: redexes -> Prop,
  forall f1: (P redexes_type),
  forall f2: (P redexes_prop),
  forall f3: (P redexes_base),
  forall f4: (P redexes_void),
  forall f5: (forall n, P (redexes_bound n)),
  forall f6: (forall ts, P (redexes_negation ts)),
  forall f7: (forall r f xs, P (redexes_jump r f xs)),
  forall f8: (forall f xs, P (redexes_placeholder f xs)),
  forall f9: (forall b,
              P b ->
              forall ts c,
              P c ->
              (forall x,
               redexes_mark_count_total x <
                 redexes_mark_count_total (redexes_bind b ts c) ->
               P x) -> P (redexes_bind b ts c)),
  forall r, P r.
Proof.
  intros.
  assert (exists n, n >= redexes_mark_count_total r) as (n, ?); eauto.
  generalize dependent r.
  induction n using lt_wf_ind.
  induction r; intros.
  - apply f1.
  - apply f2.
  - apply f3.
  - apply f4.
  - apply f5.
  - apply f6.
  - apply f7.
  - apply f8.
  - simpl in H0.
    apply f9; intros.
    + apply IHr1; lia.
    + apply IHr2; lia.
    + simpl in H1.
      apply H with (redexes_mark_count_total x); lia.
Qed.

Lemma regular_ignore_unused_tail:
  forall e a g,
  regular (g ++ repeat None a) e ->
  regular g e.
Proof.
  induction e; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct r.
    + dependent destruction H.
      econstructor; eauto.
      destruct (le_gt_dec (length g) n).
      * exfalso.
        apply item_ignore_head in H; auto.
        apply item_repeat in H.
        discriminate.
      * eapply item_ignore_tail; auto.
        eauto.
    + constructor.
  - dependent destruction H.
    econstructor; eauto.
    destruct (le_gt_dec (length g) n).
    + exfalso.
      apply item_ignore_head in H; auto.
      apply item_repeat in H.
      discriminate.
    + eapply item_ignore_tail; auto.
      eauto.
  - dependent destruction H; constructor.
    + eapply IHe1; eauto.
    + rewrite app_assoc in H0.
      eapply IHe2; eauto.
Qed.

Lemma redexes_flow_ignore_unused_mark:
  forall e1 k,
  redexes_mark_count k e1 = 0 ->
  forall c a e2,
  redexes_flow c a k e1 = e2 ->
  e1 = e2.
Proof.
  induction e1; simpl; intros.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - destruct f; auto.
    destruct (Nat.eq_dec k n); try lia.
    destruct (Nat.eq_dec n k); try lia.
    assumption.
  - destruct e2; try discriminate.
    dependent destruction H0.
    f_equal.
    + eapply IHe1_1; eauto.
      lia.
    + eapply IHe1_2; eauto.
      lia.
Qed.

Lemma regular_ignore_unmarked_tail:
  forall a e g,
  regular (g ++ [Some a]) e ->
  redexes_mark_count (length g) e = 0 ->
  regular g e.
Proof.
  induction e; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct r.
    + simpl in H0.
      dependent destruction H.
      destruct (Nat.eq_dec (length g) n); try lia.
      econstructor; eauto.
      assert (n < length (g ++ [Some a])).
      * eapply item_valid_index; eauto.
      * rewrite app_length in H1; simpl in H1.
        eapply item_ignore_tail; try lia.
        eassumption.
    + constructor.
  - simpl in H0.
    dependent destruction H.
    destruct (Nat.eq_dec (length g) n); try lia.
    econstructor; eauto.
    assert (n < length (g ++ [Some a])).
    + eapply item_valid_index; eauto.
    + rewrite app_length in H1; simpl in H1.
      eapply item_ignore_tail; try lia.
      eassumption.
  - simpl in H0.
    dependent destruction H.
    constructor.
    + rewrite app_comm_cons in H.
      apply IHe1; auto.
      simpl; lia.
    + rewrite app_assoc in H0.
      apply IHe2; auto.
      rewrite app_length.
      rewrite repeat_length.
      rewrite plus_comm; lia.
Qed.

(*
Lemma residuals_preserve_no_mark:
  forall a b c,
  residuals a b c ->
  forall k,
  redexes_mark_count k a = 0 ->
  redexes_mark_count k b = 0 ->
  redexes_mark_count k c = 0.
Proof.
  induction 1; intros.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - simpl in H1, H2 |- *.
    replace (redexes_mark_count (S k) b3) with 0; simpl.
    + apply IHresiduals2; lia.
    + symmetry.
      apply IHresiduals1; lia.
Qed.
*)

Lemma residuals_full_preserve_no_mark:
  forall a,
  redexes_mark_count_total a = 0 ->
  forall b c,
  residuals_full a b c ->
  forall g,
  regular g b ->
  redexes_mark_count_total c = 0.
Proof.
  (* Hmm, by the structure and number of marks in b? *)
  admit.
Admitted.

Lemma redexes_mark_leaves_unmarked:
  forall e k,
  redexes_mark_count k (mark e) = 0.
Proof.
  induction e; simpl; intros; auto.
  replace (redexes_mark_count (S k) (mark e1)) with 0; simpl.
  - apply IHe2.
  - symmetry.
    apply IHe1.
Qed.

Lemma regular_doesnt_jump_to_free_vars:
  forall e g,
  regular g e ->
  forall k,
  k >= length g ->
  redexes_mark_count k e = 0.
Proof.
  induction e; simpl; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct r; auto.
    destruct f; auto.
    destruct (Nat.eq_dec k n); auto.
    exfalso.
    dependent induction H.
    assert (n < length g).
    + eapply item_valid_index; eauto.
    + lia.
  - destruct f; auto.
    destruct (Nat.eq_dec k n); auto.
    exfalso.
    dependent induction H.
    assert (n < length g).
    + eapply item_valid_index; eauto.
    + lia.
  - dependent destruction H.
    replace (redexes_mark_count (S k) e1) with 0; simpl.
    + eapply IHe2; eauto.
      rewrite app_length.
      rewrite repeat_length.
      lia.
    + symmetry.
      eapply IHe1; eauto.
      simpl; lia.
Qed.

Lemma residuals_partial_full_application:
  forall x y z,
  residuals_full x y z ->
  forall g,
  regular g x ->
  regular g y ->
  residuals_full (redexes_full x) (redexes_full y) z.
Proof.
  intros until 1.
  destruct H as (z', ?, ?).
  generalize dependent z.
  induction H; simpl; intros.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H0.
    eexists; eauto with cps.
  - dependent destruction H1.
    dependent destruction H2.
    dependent destruction H3.
    edestruct IHresiduals1 as (b3', ?, ?); eauto.
    edestruct IHresiduals2 as (c3', ?, ?); eauto.
    clear IHresiduals1 IHresiduals2.
    (* Hmm... what now...? *)
    admit.
Admitted.

Lemma positive_mark_count_implies_context:
  forall a b c,
  residuals (mark a) b c ->
  forall k,
  redexes_mark_count k b > 0 ->
  exists h r xs,
  redexes_same_path (mark_context h) r /\
    a = h (jump (k + #h) xs) /\
    b = r (redexes_jump true (k + #h) xs).
Proof.
  intros until 1.
  dependent induction H; simpl; intros.
  - exfalso; lia.
  - exfalso; lia.
  - exfalso; lia.
  - exfalso; lia.
  - exfalso; lia.
  - exfalso; lia.
  - exfalso; lia.
  - destruct a; try discriminate.
    dependent destruction x.
    destruct a; try lia.
    destruct (Nat.eq_dec k0 n); try lia.
    exists context_hole; simpl.
    rewrite Nat.add_0_r; destruct e.
    exists redexes_context_hole, xs0; eauto with cps.
  - exfalso.
    destruct a; discriminate.
  - destruct a; try discriminate.
    dependent destruction x.
    destruct (Nat.eq_dec (redexes_mark_count (k + length ts0) c2) 0).
    + clear IHresiduals2.
      edestruct IHresiduals1 with (k := S k); auto; try lia.
      destruct H2 as (r, (xs, (?, (?, ?)))).
      eexists (context_left _ _ _); simpl.
      eexists; eexists; simpl.
      split; [ | split ].
      * constructor; eauto.
      * f_equal.
        replace (k + S #x) with (S k + #x); try lia.
        eassumption.
      * simpl; f_equal.
        replace (k + S #x) with (S k + #x); try lia.
        assumption.
    + clear IHresiduals1.
      edestruct IHresiduals2 with (k := k + length ts0); auto; try lia.
      destruct H2 as (r, (xs, (?, (?, ?)))).
      eexists (context_right _ _ _); simpl.
      eexists; eexists; simpl.
      split; [ | split ].
      * constructor; eauto.
      * f_equal.
        replace (k + (#x + length ts0)) with (k + length ts0 + #x); try lia.
        eassumption.
      * simpl; f_equal.
        replace (k + (#x + length ts0)) with (k + length ts0 + #x); try lia.
        assumption.
Qed.

(*
Lemma redexes_mark_count_replacing_mark:
  forall (h: redexes_context) k xs n,
  redexes_mark_count k (h (redexes_jump true
    (k + redexes_context_bvars h) xs)) = 1 + n ->
  forall e m,
  redexes_mark_count (k + redexes_context_bvars h) e = m ->
  redexes_mark_count k (h e) = m + n.
Proof.
  induction h; simpl; intros.
  - rewrite Nat.add_0_r in H, H0.
    destruct (Nat.eq_dec k k); lia.
  - remember (h (redexes_jump true (k + S (redexes_context_bvars h)) xs)) as b.
    assert (exists o, redexes_mark_count (S k) b = S o) as (o, ?).
    + admit.
    + replace (redexes_mark_count (k + length ts) c) with (n - o); try lia.
      assert (redexes_mark_count (S k) (h e) = m + o).
      * rewrite <- plus_Snm_nSm in Heqb, H0.
        dependent destruction Heqb.
        eapply IHh; eauto.
      * lia.
  - remember (h (redexes_jump true
      (k + (redexes_context_bvars h + length ts)) xs)) as c.
    assert (exists o, redexes_mark_count (k + length ts) c = S o) as (o, ?).
    + admit.
    + replace (redexes_mark_count (S k) b) with (n - o); try lia.
      assert (redexes_mark_count (k + length ts) (h e) = m + o).
      * replace (k + (redexes_context_bvars h + length ts)) with
          (k + length ts + redexes_context_bvars h) in Heqc, H0; try lia.
        dependent destruction Heqc.
        eapply IHh; eauto.
      * lia.
Admitted.

Lemma redexes_mark_count_total_zero_implies_count_zero:
  forall e,
  redexes_mark_count_total e = 0 ->
  forall k,
  redexes_mark_count k e = 0.
Proof.
  induction e; simpl; intros.
  - reflexivity.
  - destruct r; auto.
    destruct f; auto.
    discriminate.
  - destruct f; auto.
    discriminate.
  - replace (redexes_mark_count (S k) e1) with 0; simpl.
    + apply IHe2; lia.
    + symmetry.
      apply IHe1; lia.
Qed.
*)

Lemma redexes_mark_count_total_lt_context:
  forall a b,
  redexes_mark_count_total a < redexes_mark_count_total b ->
  forall h: redexes_context,
  redexes_mark_count_total (h a) < redexes_mark_count_total (h b).
Proof.
  induction h; simpl; intros.
  - assumption.
  - lia.
  - lia.
Qed.

Lemma redexes_mark_count_total_mark_is_zero:
  forall e,
  redexes_mark_count_total (mark e) = 0.
Proof.
  induction e; simpl; lia.
Qed.

Lemma residuals_replacing_hole:
  forall h s,
  redexes_same_path h s ->
  forall t,
  redexes_same_path h t ->
  forall a b c,
  residuals (h a) (s b) (t c) ->
  forall x y z,
  residuals x y z ->
  residuals (h x) (s y) (t z).
Proof.
  induction 1; intros.
  - dependent destruction H; simpl.
    assumption.
  - dependent destruction H1.
    dependent destruction H3; simpl; constructor.
    + eapply IHredexes_same_path; eauto.
    + assumption.
  - dependent destruction H1.
    dependent destruction H3; simpl; constructor.
    + assumption.
    + eapply IHredexes_same_path; eauto.
Qed.

Lemma regular_jump_imply_correct_arity:
  forall (h: redexes_context) g a n xs,
  regular (g ++ [Some a]) (h (redexes_jump true n xs)) ->
  n = length g + redexes_context_bvars h ->
  length xs = a.
Proof.
  induction h; simpl; intros.
  - dependent destruction H.
    dependent destruction H0.
    apply item_ignore_head in H; try lia.
    replace (length g + 0 - length g) with 0 in H; try lia.
    dependent destruction H.
    reflexivity.
  - dependent destruction H.
    rewrite app_comm_cons in H.
    eapply IHh; eauto; simpl.
    dependent destruction H1.
    f_equal; lia.
  - dependent destruction H.
    rewrite app_assoc in H0.
    eapply IHh; eauto; simpl.
    dependent destruction H1.
    rewrite app_length.
    rewrite repeat_length.
    f_equal; lia.
Qed.

Lemma mark_context_bvars_and_path_are_sound:
  forall h s,
  redexes_same_path (mark_context h) s ->
  #h = redexes_context_bvars s.
Proof.
  intros.
  dependent induction H; simpl.
  - destruct h; try discriminate; auto.
  - destruct h; try discriminate; simpl.
    dependent destruction x; auto.
  - destruct h; try discriminate; simpl.
    dependent destruction x; auto.
Qed.

Lemma regular_preserved_replacing_jump_by_mark:
  forall (h: redexes_context) g a n xs,
  regular (g ++ [Some a]) (h (redexes_jump true n xs)) ->
  n = length g + redexes_context_bvars h ->
  forall e,
  regular (g ++ [Some a]) (h (mark e)).
Proof.
  induction h; simpl; intros.
  - apply regular_mark_term.
  - dependent destruction H.
    constructor; auto.
    rewrite app_comm_cons in H |- *.
    eapply IHh; eauto.
    dependent destruction H1; f_equal.
    simpl; lia.
  - dependent destruction H.
    constructor; auto.
    rewrite app_assoc in H0 |- *.
    eapply IHh; eauto.
    dependent destruction H1; f_equal.
    rewrite app_length.
    rewrite repeat_length.
    lia.
Qed.

(* In fact this could be generalized by any regular [] y, instead of simply
   having no marks. But I don't think we'll need that. *)

Lemma redexes_flow_preserved_by_single_unmarked_jump:
  forall h k n,
  n = k + redexes_context_bvars h ->
  forall y xs e,
  redexes_flow (mark y) (length xs) k
    (redexes_full (h (redexes_placeholder n xs))) = e ->
  redexes_flow (mark y) (length xs) k
    (redexes_full (h (mark (apply_parameters xs 0
      (lift (S n) (length xs) y))))) = e.
Proof.
  induction h; simpl; intros.
  - destruct (Nat.eq_dec n k); try lia.
    destruct (Nat.eq_dec (length xs) (length xs)); try lia.
    rewrite redexes_full_mark_equals_mark.
    rewrite redexes_flow_mark_equals_mark.
    rewrite <- redexes_apply_parameters_is_sound.
    rewrite <- redexes_lift_is_sound.
    assumption.
  - dependent destruction H0.
    f_equal.
    do 2 rewrite redexes_flow_commute.
    f_equal.
    apply IHh; auto.
    lia.
  - dependent destruction H0.
    f_equal.
    + do 2 rewrite redexes_flow_commute.
      f_equal.
      apply IHh; auto.
      lia.
    + apply IHh; auto.
      lia.
Qed.

(* -------------------------------------------------------------------------- *)

Goal
  forall e,
  redexes_mark_count_total e = 0 ->
  e = mark (unmark e).
Proof.
  induction e; simpl; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct r.
    + discriminate.
    + reflexivity.
  - discriminate.
  - rewrite <- IHe1; try lia.
    rewrite <- IHe2; try lia.
    reflexivity.
Qed.
