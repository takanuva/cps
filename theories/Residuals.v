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

(*
Lemma compatible_preserved_at_hole:
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

Global Hint Resolve compatible_preserved_at_hole: cps.
*)

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
  | regular_term:
    forall g e,
    regular g (redexes_term e)
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

Lemma regular_union:
  forall a b c,
  union a b c ->
  forall g,
  regular g a -> regular g b -> regular g c.
Proof.
  induction 1; intros.
  - constructor.
  - dependent destruction H.
    + dependent destruction H0; simpl.
      * constructor.
      * econstructor; eauto.
    + dependent destruction H0; simpl.
      * econstructor; eauto.
      * econstructor; eauto.
  - assumption.
  - dependent destruction H1.
    dependent destruction H2.
    constructor; auto.
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

Fixpoint redexes_context_depth h: nat :=
  match h with
  | redexes_context_hole =>
    0
  | redexes_context_left b _ _ =>
    S (redexes_context_depth b)
  | redexes_context_right _ ts c =>
    redexes_context_depth c + length ts
  end.

Lemma regular_cant_jump_too_far:
  forall n h g,
  n = length g + redexes_context_depth h ->
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

Local Lemma technical1:
  forall h h',
  redexes_same_path (mark_context h) h' ->
  forall k,
  regular [] (h' k) ->
  forall xs e,
  residuals (redexes_jump false #h xs) k e ->
  k = redexes_jump false #h xs.
Proof.
  intros.
  dependent destruction H1.
  - reflexivity.
  - exfalso.
    eapply regular_cant_jump_too_far with (g := []) (h := h');
      eauto; simpl.
    (* Huh, this is a bit ugly... TODO: should we move this? *)
    replace (redexes_context_depth h') with #h.
    + eassumption.
    + clear H0.
      dependent induction H; destruct h; try discriminate; simpl.
      * reflexivity.
      * dependent destruction x; eauto.
      * dependent destruction x; eauto.
Qed.

Local Lemma technical2:
  forall h r,
  redexes_same_path h r ->
  forall a b,
  compatible (h a) (r b) ->
  forall n xs,
  exists p,
  union (h (redexes_jump true n xs)) (r (redexes_jump false n xs)) p.
Proof.
  intros.
  apply union_compatible.
  eapply compatible_context_changing_hole; eauto.
  constructor.
Qed.

Local Lemma technical3:
  forall h r,
  redexes_same_path (mark_context h) r ->
  forall s,
  redexes_same_path (mark_context h) s ->
  forall n xs,
  residuals (mark_context h (redexes_jump false n xs))
            (r (redexes_jump false n xs))
            (s (redexes_jump false n xs)) ->
  forall p,
  union (mark_context h (redexes_jump true n xs))
        (r (redexes_jump false n xs)) p ->
  residuals (mark_context h (redexes_jump false n xs)) p
            (s (redexes_placeholder n xs)).
Proof.
  intros until 1.
  dependent induction H; simpl; intros.
  - destruct h; try discriminate.
    dependent destruction H0.
    dependent destruction H1.
    destruct s; try discriminate.
    simpl; constructor.
  - destruct h; try discriminate.
    dependent destruction H1.
    dependent destruction H3.
    dependent destruction H4.
    simpl; constructor; auto.
    assert (c4 = c2).
    + apply union_mark_inversion with c.
      assumption.
    + dependent destruction H0.
      assumption.
  - destruct h; try discriminate.
    dependent destruction H1.
    dependent destruction H3.
    dependent destruction H4.
    simpl; constructor; auto.
    assert (b4 = b2).
    + apply union_mark_inversion with b.
      assumption.
    + dependent destruction H0.
      assumption.
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

(* -------------------------------------------------------------------------- *)

Inductive redexes_multicontext: Set :=
  | redexes_multicontext_context
      (h: redexes_context)
  | redexes_multicontext_left
      (b: redexes_multicontext) (ts: list pseudoterm) (c: redexes)
  | redexes_multicontext_right
      (b: redexes) (ts: list pseudoterm) (c: redexes_multicontext)
  | redexes_multicontext_both
      (b: redexes_multicontext) (ts: list pseudoterm) (c: redexes_multicontext).

Fixpoint apply_redexes_multicontext h f: redexes :=
  match h with
  | redexes_multicontext_context h =>
    h (f (redexes_context_depth h))
  | redexes_multicontext_left b ts c =>
    redexes_bind (apply_redexes_multicontext b (fun n => f (S n))) ts c
  | redexes_multicontext_right b ts c =>
    redexes_bind b ts (apply_redexes_multicontext c
      (fun n => f (length ts + n)))
  | redexes_multicontext_both b ts c =>
    redexes_bind (apply_redexes_multicontext b (fun n => f (S n))) ts
      (apply_redexes_multicontext c (fun n => f (length ts + n)))
  end.

Coercion apply_redexes_multicontext: redexes_multicontext >-> Funclass.

Lemma apply_redexes_multicontext_extensional:
  forall h f g,
  (forall x, f x = g x) ->
  apply_redexes_multicontext h f = apply_redexes_multicontext h g.
Proof.
  induction h; simpl; intros.
  - generalize (redexes_context_depth h).
    induction h; simpl; intros.
    + apply H.
    + f_equal; auto.
    + f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Fixpoint redexes_context_flow y a k h: redexes_context :=
  match h with
  | redexes_context_hole =>
    redexes_context_hole
  | redexes_context_left b ts c =>
    redexes_context_left (redexes_context_flow y a (S k) b) ts
      (redexes_flow y a (k + length ts) c)
  | redexes_context_right b ts c =>
    redexes_context_right (redexes_flow y a (S k) b) ts
      (redexes_context_flow y a (k + length ts) c)
  end.

Lemma redexes_context_flow_is_sound:
  forall h e a y k,
  redexes_context_flow a y k h
    (redexes_flow a y (k + redexes_context_depth h) e) =
      redexes_flow a y k (h e).
Proof.
  induction h; simpl; intros.
  - rewrite Nat.add_0_r.
    reflexivity.
  - f_equal.
    replace (k + S (redexes_context_depth h)) with
      (S k + redexes_context_depth h); try lia.
    apply IHh.
  - f_equal.
    replace (k + (redexes_context_depth h + length ts)) with
      (k + length ts + redexes_context_depth h); try lia.
    apply IHh.
Qed.

Lemma redexes_context_flow_depth:
  forall h y a k,
  redexes_context_depth (redexes_context_flow a y k h) =
    redexes_context_depth h.
Proof.
  induction h; simpl; eauto.
Qed.

Fixpoint redexes_multicontext_flow y a k h: redexes_multicontext :=
  match h with
  | redexes_multicontext_context h =>
    redexes_multicontext_context (redexes_context_flow y a k h)
  | redexes_multicontext_left b ts c =>
    redexes_multicontext_left (redexes_multicontext_flow y a (S k) b) ts
      (redexes_flow y a (k + length ts) c)
  | redexes_multicontext_right b ts c =>
    redexes_multicontext_right (redexes_flow y a (S k) b) ts
      (redexes_multicontext_flow y a (k + length ts) c)
  | redexes_multicontext_both b ts c =>
    redexes_multicontext_both
      (redexes_multicontext_flow y a (S k) b) ts
      (redexes_multicontext_flow y a (k + length ts) c)
  end.

Lemma redexes_multicontext_flow_is_sound:
  forall h f a y k,
  redexes_multicontext_flow a y k h
    (fun p => redexes_flow a y (k + p) (f p)) =
      redexes_flow a y k (h f).
Proof.
  induction h; simpl; intros.
  - rewrite <- redexes_context_flow_is_sound; f_equal.
    rewrite redexes_context_flow_depth.
    reflexivity.
  - f_equal.
    erewrite apply_redexes_multicontext_extensional.
    + apply IHh.
    + intros; f_equal; simpl.
      f_equal; lia.
  - f_equal.
    erewrite apply_redexes_multicontext_extensional.
    + apply IHh.
    + intros; f_equal; simpl.
      f_equal; lia.
  - f_equal.
    + erewrite apply_redexes_multicontext_extensional.
      * apply IHh1.
      * intros; f_equal; simpl.
        f_equal; lia.
    + erewrite apply_redexes_multicontext_extensional.
      * apply IHh2.
      * intros; f_equal; simpl.
        f_equal; lia.
Qed.

(*
(*
redexes_full = 
fix redexes_full (e : redexes) : redexes :=
  match e with
  | redexes_bind b ts c =>
      redexes_bind
        (redexes_flow (redexes_full c) (length ts) 0
           (redexes_full b)) ts (redexes_full c)
  | _ => e
  end
*)

Fixpoint redexes_context_full h: redexes_multicontext :=
  match h with
  | redexes_context_hole =>
    redexes_multicontext_hole


  | redexes_context_left b ts c =>
    redexes_multicontext_left (
      redexes_context_flow (redexes_full c) (length ts) 0
        (redexes_context_full b)) ts (redexes_full c)


  | redexes_context_right b ts c =>
    redexes_multicontext_both
      (redexes_multicontext_flow (redexes_full c) (length ts) 0
        (redexes_context_full b))
      ts
      (redexes_context_full c)
  end.

Lemma redexes_context_full_is_sound:
  forall h e1,
  exists e2,
  redexes_context_full h e2 =
    redexes_full (h e1).
Proof.
  induction h; simpl; intros.
  - eexists; eauto.
  - edestruct IHh as (e2, ?).
    eexists; f_equal.
    rewrite redexes_context_flow_is_sound; f_equal.
    eassumption.

*)

Lemma redexes_full_preserves_regular:
  forall g x,
  regular g x ->
  regular g (redexes_full x).
Proof.
  induction 1; simpl.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - constructor.
    + apply redexes_flow_preserve_regular with (h := []); auto.
    + assumption.
Qed.

Local Lemma technical4:
  forall (r: redexes_context) g x,
  regular g (r x) ->
  forall c a k,
  k = length g ->
  redexes_flow (mark c) a k
    (redexes_full (r x)) =
  (redexes_full (r (redexes_flow (mark c) a
    (k + redexes_context_depth r) x))).
Proof.
  induction r; simpl; intros.
  - rewrite redexes_flow_regular_simplification with (g := g).
    + rewrite redexes_flow_regular_simplification with (g := g).
      * reflexivity.
      * assumption.
      * lia.
    + apply redexes_full_preserves_regular.
      assumption.
    + lia.
  - dependent destruction H.
    f_equal.
    + (* First flow commute (as it has no marks, then induction). *)
      admit.
    + apply redexes_full_preserves_regular in H0.
      erewrite redexes_flow_regular_simplification; eauto.
      rewrite app_length, repeat_length.
      lia.
  - dependent destruction H.
    f_equal.
    + admit.
    + admit.
Admitted.

Goal
  forall a b,
  [a => b] ->
  exists2 r,
  residuals_full (mark a) r (mark b) & regular [] r.
Proof.
  induction 1.
  - simpl.
    do 2 rewrite <- mark_context_is_sound; simpl.
    eexists (redexes_bind (mark_context h (redexes_jump true #h xs)) ts (mark c)).
    + eexists (redexes_bind (mark_context h (redexes_placeholder #h xs)) ts (mark c)).
      * generalize #h.
        constructor.
        induction h; simpl; auto with cps.
        constructor.
        assumption.
        induction c0; simpl; auto with cps.
        constructor.
        induction b; simpl; auto with cps.
        assumption.
        induction c; simpl; auto with cps.
      * admit.
    + constructor.
      * rewrite <- H.
        apply regular_single_jump with (g := []).
      * apply regular_mark_term.
  - destruct IHstep as (p, (b2', ?, ?), ?).
    exists (redexes_bind p ts (mark c)); simpl.
    + exists (redexes_bind b2' ts (mark c)); simpl.
      * constructor; auto.
        induction c; simpl; auto with cps.
      * f_equal.
        rewrite H1.
        rewrite redexes_flow_mark_equals_mark; auto.
        rewrite redexes_full_mark_equals_mark; auto.
    + constructor.
      * eapply regular_tail in H2; eauto.
      * apply regular_mark_term.
  - destruct IHstep as (p, (c2', ?, ?), ?).
    exists (redexes_bind (mark b) ts p); simpl.
    + exists (redexes_bind (mark b) ts c2'); simpl.
      * constructor; auto.
        induction b; simpl; auto with cps.
      * f_equal.
        rewrite redexes_full_mark_equals_mark; auto.
        rewrite redexes_flow_mark_equals_mark; auto.
        assumption.
    + constructor.
      * apply regular_mark_term.
      * eapply regular_tail in H2; eauto.
Admitted.

(*
Goal
  forall a b,
  parallel a b ->
  exists2 r,
  (* We also need to show that at most ONE jump to each binding is marked! *)
  residuals_full (mark a) r (mark b) & regular [] r.
Proof.
  induction 1; simpl.
  - exists (mark e).
    + exists (mark e).
      * induction e; simpl; auto with cps.
      * apply redexes_full_mark_equals_mark.
    + apply regular_mark_term.
  - clear H1 H2.
    (* Split our inductive hypotheses... *)
    destruct IHparallel1 as (p, (b', ?, ?), ?).
    destruct IHparallel2 as (q, (c', ?, ?), ?).
    rewrite <- mark_context_is_sound in H1, H2.
    (* Since h[x]/p = b', p must be a compatible context. *)
    edestruct compatible_context_left_inversion
      with (h := mark_context h) (b := p)
      as (h', (k, (?, ?))); eauto with cps.
    dependent destruction H8; simpl in H1, H2.
    (* Accordingly, so should b'... *)
    edestruct residuals_preserve_hole as (r', (e, (?, (?, ?)))); eauto.
    dependent destruction H10.
    (* H'[k] is regular; k can't be marked, as it'll be a jump to a free var. *)
    assert (k = redexes_jump false #h xs);
      try (eapply technical1 with (h' := h'); eauto).
    dependent destruction H10.
    (* This allows us to simplify the result of the residual as well. *)
    dependent destruction H9.
    (* Since H and H' are compatible, H having no marks, we can add a single new
       mark to H' by taking a union with a mark in H's hole. We already saw H'
       didn't have such mark. *)
    edestruct technical2 with (h := mark_context h) (r := h') as (p', ?);
      eauto with cps.
    (* We now have properly calculated our marks and can proceed. *)
    eexists (redexes_bind p' ts q).
    + eexists (redexes_bind (r' (redexes_placeholder #h xs)) ts c').
      * constructor; auto.
        rewrite <- mark_context_is_sound; simpl.
        apply technical3 with (r := h'); eauto.
      * simpl; f_equal; auto.
        rewrite <- mark_context_is_sound; simpl.
        (* Too much information here!!! *)
        rewrite H5.
        (* ................ *)
        assert (redexes_same_path (mark_context r) r').
        admit.
        admit.
    + constructor.
      * eapply regular_tail in H3.
        eapply regular_union; eauto.
        rewrite <- H0.
        apply regular_single_jump with (g := []).
      * eapply regular_tail in H6; eauto.
  - destruct IHparallel1 as (p, (b', ?, ?), ?).
    destruct IHparallel2 as (q, (c', ?, ?), ?).
    exists (redexes_bind p ts q).
    + exists (redexes_bind b' ts c').
      * auto with cps.
      * simpl; rewrite H2, H5; f_equal.
        apply redexes_flow_mark_equals_mark.
    + constructor.
      * eapply regular_tail in H3; eauto.
      * eapply regular_tail in H6; eauto.
Admitted.
*)

Inductive redexes_subterm: relation redexes :=
  | redexes_subterm_left:
    forall b ts c,
    redexes_subterm b (redexes_bind b ts c)
  | redexes_subterm_right:
    forall b ts c,
    redexes_subterm c (redexes_bind b ts c).

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

Lemma regular_ignore_unused_tail:
  forall e a g,
  regular (g ++ repeat None a) e ->
  regular g e.
Proof.
  induction e; intros.
  - constructor.
  - destruct r.
    + dependent destruction H.
      econstructor; eauto.
      admit.
    + constructor.
  - dependent destruction H.
    econstructor; eauto.
    admit.
  - dependent destruction H; constructor.
    + eapply IHe1; eauto.
    + rewrite app_assoc in H0.
      eapply IHe2; eauto.
Admitted.

Lemma regular_ignore_unmarked_tail:
  forall a e g,
  regular (g ++ [Some a]) e ->
  redexes_mark_count (length g) e = 0 ->
  regular g e.
Proof.
  induction e; intros.
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
  - simpl in H1, H2 |- *.
    replace (redexes_mark_count (S k) b3) with 0; simpl.
    + apply IHresiduals2; lia.
    + symmetry.
      apply IHresiduals1; lia.
Qed.

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
  forall a g,
  regular g a ->
  forall b,
  regular g b ->
  forall c,
  residuals_full a b c ->
  residuals_full (redexes_full a) (redexes_full b) c.
Proof.
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
  - destruct a; try discriminate.
    dependent destruction x.
    destruct a; try lia.
    destruct (Nat.eq_dec k0 n); try lia.
    exists context_hole; simpl.
    rewrite Nat.add_0_r; destruct e.
    exists redexes_context_hole, xs0; eauto with cps.
  - exfalso.
    destruct a; discriminate.
  - admit.
Admitted.

Goal
  forall n r,
  n = redexes_mark_count 0 r ->
  forall b1 b2,
  (regular [] r -> [b1 =>* b2]) ->
  forall ts,
  regular [Some (length ts)] r ->
  forall b1',
  residuals (mark b1) r b1' ->
  forall c,
  redexes_flow (mark c) (length ts) 0 (redexes_full b1') = mark b2 ->
  [bind b1 ts c =>* bind b2 ts c].
Proof.
  induction n; intros.
  (* Case: no marks left. *)
  - (* Conclude by our hypothesis. *)
    apply star_bind_left.
    apply H0.
    eapply regular_ignore_unmarked_tail; eauto.
  (* Case: at least one mark left. *)
  - (* Find any mark to reduce. *)
    edestruct positive_mark_count_implies_context with (k := 0)
      as (h, (s, (xs, ?))); eauto; try lia.
    simpl in H4.
    destruct H4 as (?, (?, ?)).
    dependent destruction H5.
    dependent destruction H6.
    rewrite <- mark_context_is_sound in H2.
    (* Since there's a context, it should exists in our result as well. *)
    edestruct residuals_preserve_hole as (t, (e, (?, (?, ?)))); eauto.
    dependent destruction H6.
    dependent destruction H7.
    eapply star_trans.
    + apply star_ctxjmp.
      (* We can derive that from H1! *)
      admit.
    + (* Follow with IHn... somehow... *)
      admit.
Admitted.

Goal
  forall r a b,
  residuals_full (mark a) r (mark b) ->
  regular [] r ->
  [a =>* b].
Proof.
  intros until 1.
  destruct H as (b', ?, ?).
  generalize dependent b'.
  generalize a b; clear a b.
  induction r; intros.
  - dependent destruction H.
    destruct a;
    destruct b;
    destruct e;
    try discriminate;
    auto with cps;
    dependent destruction H0;
    auto with cps.
  - dependent destruction H.
    + destruct a; try discriminate.
      destruct b; try discriminate.
      dependent destruction H0.
      auto with cps.
    + exfalso.
      dependent destruction H1.
      dependent destruction H.
  - exfalso.
    dependent destruction H.
    destruct a; discriminate.
  - dependent destruction H.
    destruct a; try discriminate.
    destruct b; try discriminate.
    dependent destruction x.
    dependent destruction H1.
    dependent destruction H2.
    rewrite app_nil_r in H2_0.
    apply regular_ignore_unused_tail with (g := []) in H2_0.
    apply star_trans with (bind a1 ts1 b4).
    + apply star_bind_right.
      eapply IHr2; eauto.
    + clear IHr2.
      symmetry in x0; destruct x0.
      (* TODO: fix this, of course. *)
      eapply Unnamed_thm0; eauto.
      intros; eapply IHr1; eauto.
      eapply redexes_flow_ignore_unused_mark.
      * eapply regular_doesnt_jump_to_free_vars; eauto.
        apply redexes_full_preserves_regular.
        eapply residuals_preserve_regular; eauto.
        apply regular_mark_term.
      * eassumption.
Qed.
