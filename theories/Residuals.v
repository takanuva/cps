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
(* TODO: logic on confluence should be moved there! *)
Require Import Local.Confluency.

(** ** Residuals *)

Inductive redexes: Set :=
  | redexes_term (e: pseudoterm)
  | redexes_jump (r: bool) (f: pseudoterm) (xs: list pseudoterm)
  | redexes_placeholder (f: pseudoterm) (xs: list pseudoterm)
  | redexes_bind (b: redexes) (ts: list pseudoterm) (c: redexes).

Fixpoint mark (e: pseudoterm): redexes :=
  match e with
  | jump f xs =>
    redexes_jump false f xs
  | bind b ts c =>
    redexes_bind (mark b) ts (mark c)
  | _ =>
    redexes_term e
  end.

Fixpoint unmark (e: redexes): pseudoterm :=
  match e with
  | redexes_term e =>
    e
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
  | redexes_term e =>
    redexes_term (lift i k e)
  | redexes_jump r f xs =>
    redexes_jump r (lift i k f) (map (lift i k) xs)
  | redexes_placeholder f xs =>
    redexes_placeholder (lift i k f) (map (lift i k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_lift i (S k) b)
      (traverse_list (lift i) k ts)
      (redexes_lift i (k + length ts) c)
  end.

Fixpoint redexes_subst y k e: redexes :=
  match e with
  | redexes_term e =>
    redexes_term (subst y k e)
  | redexes_jump r f xs =>
    redexes_jump r (subst y k f) (map (subst y k) xs)
  | redexes_placeholder f xs =>
    redexes_placeholder (subst y k f) (map (subst y k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_subst y (S k) b)
      (traverse_list (subst y) k ts)
      (redexes_subst y (k + length ts) c)
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

Lemma redexes_lift_distributes_over_apply_parameters:
  forall ys i k e,
  redexes_lift i k (redexes_apply_parameters ys 0 e) =
  redexes_apply_parameters (map (lift i k) ys) 0
    (redexes_lift i (length ys + k) e).
Proof.
  induction ys; simpl; intros.
  - reflexivity.
  - rewrite IHys; f_equal.
    (* Oh those indices... *)
    admit.
Admitted.

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

Lemma redexes_flow_addition_commute:
  forall b a1 a2 p k c1 c2,
  redexes_flow c2 a1 (p + S k) (redexes_flow c1 a2 p b) =
    redexes_flow (redexes_flow c2 a1 (k + a2) c1)
      a2 p (redexes_flow c2 a1 (p + S k) b).
Proof.
  induction b; simpl; intros.
  - constructor.
  - constructor.
  - admit.
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
  apply redexes_flow_addition_commute with (p := 0).
Qed.

Inductive compatible: relation redexes :=
  | compatible_term:
    forall e,
    compatible (redexes_term e) (redexes_term e)
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
  induction 1; simpl; constructor; auto.
Qed.

Lemma compatible_subst:
  forall a b,
  compatible a b ->
  forall y k,
  compatible (redexes_subst y k a) (redexes_subst y k b).
Proof.
  induction 1; simpl; constructor; auto.
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
  induction 2; simpl; intros.
  - constructor.
  - constructor.
  - destruct f; try constructor.
    destruct (Nat.eq_dec n k); try constructor.
    destruct (Nat.eq_dec a (length xs)); try constructor.
    apply compatible_apply_parameters.
    apply compatible_lift.
    assumption.
  - constructor; auto.
Qed.

Inductive union: redexes -> redexes -> redexes -> Prop :=
  | union_term:
    forall e,
    union (redexes_term e) (redexes_term e) (redexes_term e)
  | union_jump:
    forall r1 r2 k xs,
    union
      (redexes_jump r1 k xs)
      (redexes_jump r2 k xs)
      (redexes_jump (orb r1 r2) k xs)
  | union_placeholder:
    forall k xs,
    union
      (redexes_placeholder k xs)
      (redexes_placeholder k xs)
      (redexes_placeholder k xs)
  | union_bind:
    forall b1 b2 b3 ts c1 c2 c3,
    union b1 b2 b3 ->
    union c1 c2 c3 ->
    union
      (redexes_bind b1 ts c1)
      (redexes_bind b2 ts c2)
      (redexes_bind b3 ts c3).

Global Hint Constructors union: cps.

Lemma union_sym:
  forall a b c,
  union a b c ->
  union b a c.
Proof.
  induction 1; auto with cps.
  destruct r1, r2; simpl; constructor.
Qed.

Global Hint Resolve union_sym: cps.

Lemma union_mark_inversion:
  forall a b c,
  union (mark a) b c ->
  c = b.
Proof.
  induction a; inversion_clear 1; auto.
  f_equal; auto.
Qed.

Global Hint Resolve union_mark_inversion: cps.

Lemma union_compatible:
  forall a b,
  compatible a b ->
  exists c,
  union a b c.
Proof.
  induction 1.
  - eexists; eauto with cps.
  - destruct r1, r2; eexists; eauto with cps.
  - eexists; eauto with cps.
  - destruct IHcompatible1.
    destruct IHcompatible2.
    eexists; eauto with cps.
Qed.

Inductive residuals: redexes -> redexes -> redexes -> Prop :=
  | residuals_term:
    forall e,
    residuals (redexes_term e) (redexes_term e) (redexes_term e)
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
  - dependent destruction H.
    reflexivity.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H.
    reflexivity.
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

Lemma residuals_lift:
  forall a b c,
  residuals a b c ->
  forall i k,
  residuals (redexes_lift i k a) (redexes_lift i k b) (redexes_lift i k c).
Proof.
  induction 1; intros; simpl; auto with cps.
Qed.

Lemma residuals_subst:
  forall a b c,
  residuals a b c ->
  forall y k,
  residuals (redexes_subst y k a) (redexes_subst y k b) (redexes_subst y k c).
Proof.
  induction 1; intros; simpl; auto with cps.
Qed.

Lemma residuals_apply_parameters:
  forall ys k a b c,
  residuals a b c ->
  residuals (redexes_apply_parameters ys k a) (redexes_apply_parameters ys k b)
    (redexes_apply_parameters ys k c).
Proof.
  induction ys; simpl; intros.
  - assumption.
  - apply IHys.
    apply residuals_subst.
    assumption.
Qed.

Lemma residuals_compatible:
  forall b1 b2,
  compatible b1 b2 ->
  exists b3,
  residuals b1 b2 b3.
Proof.
  induction 1; simpl; intros.
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
  (* Case: (term, term). *)
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

Lemma paving:
  forall a r b,
  residuals a r b ->
  forall p c,
  residuals a p c ->
  exists pr rp d,
  residuals b pr d /\ residuals c rp d.
Proof.
  intros.
  assert (compatible p r); eauto with cps.
  assert (exists pr, residuals p r pr) as (pr, ?); eauto with cps.
  assert (exists rp, residuals r p rp) as (rp, ?); eauto with cps.
  assert (exists d, residuals b pr d) as (d, ?); eauto with cps.
  exists pr, rp, d; split.
  - assumption.
  - apply cube with a r b p pr; auto.
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
  forall h: redexes_context,
  forall e1 b,
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

Lemma compatible_compatible_same_path:
  forall h r,
  redexes_same_path h r ->
  forall a b,
  compatible (h a) (r b) -> compatible a b.
Proof.
  induction 1; simpl; intros.
  - assumption.
  - dependent destruction H1; auto.
  - dependent destruction H1; auto.
Qed.

Global Hint Resolve compatible_compatible_same_path: cps.

(* Lemma redexes_flow_redexes_context:
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
Qed. *)

Goal
  forall a b,
  parallel a b ->
  exists2 r,
  residuals_full (mark a) r (mark b) & True (* has one jump to each binding *).
Proof.
  induction 1; simpl.
  - exists (mark e).
    + exists (mark e).
      * induction e; simpl; auto with cps.
      * apply redexes_full_mark_equals_mark.
    + trivial.
  - clear H1 H2.
    destruct IHparallel1 as (p, (b', ?, ?), ?).
    destruct IHparallel2 as (q, (c', ?, ?), ?).
    rewrite <- mark_context_is_sound in H1.
    edestruct compatible_context_left_inversion
      with (h := mark_context h) (b := p)
      as (h', (k, (?, ?))); eauto with cps.
    dependent destruction H8; simpl in H1.
    (* ..... *)
    assert (exists p',
      union (mark_context h (redexes_jump true #h xs)) (h' k) p').
    apply union_compatible.
    eapply compatible_context_changing_hole.
    assumption.
    eapply compatible_residuals.
    eassumption.
    assert (compatible (redexes_jump false #h xs) k).
    eapply compatible_compatible_same_path; eauto.
    eapply compatible_residuals.
    eassumption.
    eauto with cps.
    (* ..... *)
    destruct H8 as (p', ?).
    eexists (redexes_bind p' ts q).
    + eexists (redexes_bind _ ts c').
      * constructor; auto.
        admit.
      * simpl; f_equal; auto.
        (* Fine! *)
        admit.
    + trivial.
  - destruct IHparallel1 as (p, (b', ?, ?), ?).
    destruct IHparallel2 as (q, (c', ?, ?), ?).
    exists (redexes_bind p ts q).
    + exists (redexes_bind b' ts c').
      * auto with cps.
      * simpl; rewrite H2, H5; f_equal.
        apply redexes_flow_mark_equals_mark.
    + trivial.
Admitted.
