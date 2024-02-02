(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.

Import ListNotations.

Inductive type: Set :=
  | base
  | arrow (a: type) (b: type).

Inductive term: Set :=
  | bound (n: nat)
  | abstraction (t: type) (b: term)
  | application (f: term) (x: term).

Coercion bound: nat >-> term.

Inductive value: term -> Prop :=
  | value_bound:
    forall n: nat,
    value n
  | value_abstraction:
    forall t b,
    value (abstraction t b).

Global Hint Constructors value: cps.

(* TODO: I have to fix a naming convention, either "_dec" or "_is_decidable". *)

Lemma value_dec:
  forall e,
  { value e } + { ~value e }.
Proof.
  destruct e.
  - left; auto with cps.
  - left; auto with cps.
  - right; intro.
    inversion H.
Qed.

Fixpoint lift (i: nat) (k: nat) (e: term): term :=
  match e with
  | bound n =>
    if le_gt_dec k n then
      bound (i + n)
    else
      bound n
  | abstraction t b =>
    abstraction t (lift i (S k) b)
  | application f x =>
    application (lift i k f) (lift i k x)
  end.

Fixpoint subst (p: term) (k: nat) (q: term): term :=
  match q with
  | bound n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => bound (pred n)
    | inleft (right _) => lift k 0 p
    | inright _ => bound n
    end
  | abstraction t b =>
    abstraction t (subst p (S k) b)
  | application f x =>
    application (subst p k f) (subst p k x)
  end.

Lemma lift_zero_e_equals_e:
  forall e k,
  lift 0 k e = e.
Proof.
  admit.
Admitted.

Lemma lift_lift_permutation:
  forall e i j k l,
  k <= l ->
  lift i k (lift j l e) =
    lift j (i + l) (lift i k e).
Proof.
  induction e; simpl; intros.
  - destruct (le_gt_dec l n);
    simpl;
    destruct (le_gt_dec k n);
    simpl;
    destruct (le_gt_dec k (j + n));
    simpl;
    destruct (le_gt_dec (i + l) (i + n));
    simpl;
    destruct (le_gt_dec (i + l) n);
    simpl;
    try lia;
    f_equal; lia.
  - f_equal.
    replace (S (i + l)) with (i + S l); try lia.
    apply IHe; lia.
  - f_equal.
    + apply IHe1; auto.
    + apply IHe2; auto.
Qed.

Lemma lift_lift_simplification:
  forall e i j k l,
  k <= l + j ->
  l <= k ->
  lift i k (lift j l e) =
  lift (i + j) l e.
Proof.
  induction e; simpl; intros.
  - destruct (le_gt_dec l n); simpl;
    destruct (le_gt_dec k (j + n)); simpl;
    destruct (le_gt_dec k n); simpl;
    f_equal; lia.
  - f_equal.
    apply IHe; lia.
  - f_equal.
    + apply IHe1; lia.
    + apply IHe2; lia.
Qed.

Lemma subst_lift_simplification:
  forall e y i p k,
  p <= i + k ->
  k <= p ->
  subst y p (lift (S i) k e) =
  lift i k e.
Proof.
  admit.
Admitted.

Fixpoint size (e: term): nat :=
  match e with
  | bound n =>
    1
  | abstraction t b =>
    1 + size b
  | application f x =>
    1 + size f + size x
  end.

Lemma size_lift:
  forall e i k,
  size (lift i k e) = size e.
Proof.
  induction e; simpl; intros.
  - destruct (le_gt_dec k n); auto.
  - auto.
  - auto.
Qed.

Inductive subterm: relation term :=
  | subterm_abstraction:
    forall t b,
    subterm b (abstraction t b)
  | subterm_application_left:
    forall f x,
    subterm f (application f x)
  | subterm_application_right:
    forall f x,
    subterm x (application f x).

Global Hint Constructors subterm: cps.

Lemma subterm_is_well_founded:
  forall e,
  Acc subterm e.
Proof.
  induction e.
  - constructor.
    inversion 1.
  - constructor.
    inversion_clear 1; auto.
  - constructor.
    inversion_clear 1; auto.
Qed.

Inductive context: Set :=
  | context_hole
  | context_abstraction (t: type) (b: context)
  | context_application_left (f: context) (x: term)
  | context_application_right (f: term) (x: context).

Fixpoint apply_context h e :=
  match h with
  | context_hole =>
    e
  | context_abstraction t b =>
    abstraction t (apply_context b e)
  | context_application_left f x =>
    application (apply_context f e) x
  | context_application_right f x =>
    application f (apply_context x e)
  end.

Coercion apply_context: context >-> Funclass.

Fixpoint context_bvars h: nat :=
  match h with
  | context_hole =>
    0
  | context_abstraction t b =>
    1 + context_bvars b
  | context_application_left f x =>
    context_bvars f
  | context_application_right f x =>
    context_bvars x
  end.

Fixpoint context_depth h: nat :=
  match h with
  | context_hole =>
    0
  | context_abstraction t b =>
    1 + context_depth b
  | context_application_left f x =>
    1 + context_depth f
  | context_application_right f x =>
    1 + context_depth x
  end.

Fixpoint context_lift i k h: context :=
  match h with
  | context_hole =>
    context_hole
  | context_abstraction t b =>
    context_abstraction t (context_lift i (S k) b)
  | context_application_left f x =>
    context_application_left
      (context_lift i k f) (lift i k x)
  | context_application_right f x =>
    context_application_right
      (lift i k f) (context_lift i k x)
  end.

Lemma context_lift_is_sound:
  forall (h: context) i k e,
  lift i k (h e) =
    context_lift i k h (lift i (context_bvars h + k) e).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal; rewrite plus_n_Sm.
    apply IHh.
  - f_equal.
    apply IHh.
  - f_equal.
    apply IHh.
Qed.

Lemma context_lift_depth:
  forall h i k,
  context_depth (context_lift i k h) = context_depth h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
Qed.

Lemma context_lift_bvars:
  forall h i k,
  context_bvars (context_lift i k h) = context_bvars h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
Qed.

Fixpoint context_subst y k h: context :=
  match h with
  | context_hole =>
    context_hole
  | context_abstraction t b =>
    context_abstraction t (context_subst y (S k) b)
  | context_application_left f x =>
    context_application_left
      (context_subst y k f) (subst y k x)
  | context_application_right f x =>
    context_application_right
      (subst y k f) (context_subst y k x)
  end.

Lemma context_subst_is_sound:
  forall (h: context) y k e,
  subst y k (h e) =
    context_subst y k h (subst y (context_bvars h + k) e).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal; rewrite plus_n_Sm.
    apply IHh.
  - f_equal.
    apply IHh.
  - f_equal.
    apply IHh.
Qed.

Lemma context_subst_depth:
  forall h y k,
  context_depth (context_subst y k h) = context_depth h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
Qed.

Lemma context_subst_bvars:
  forall h y k,
  context_bvars (context_subst y k h) = context_bvars h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
Qed.

Inductive not_free: nat -> term -> Prop :=
  | not_free_bound:
    forall n m,
    n <> m -> not_free n m
  | not_free_abstraction:
    forall t b n,
    not_free (S n) b ->
    not_free n (abstraction t b)
  | not_free_application:
    forall f x n,
    not_free n f ->
    not_free n x ->
    not_free n (application f x).

Definition free (n: nat) (e: term): Prop :=
  ~not_free n e.

Definition closed (e: term): Prop :=
  forall n, not_free n e.

Lemma closed_application_left:
  forall f x,
  closed (application f x) ->
  closed f.
Proof.
  intros f x ? n.
  specialize (H n).
  dependent destruction H.
  assumption.
Qed.

Lemma closed_application_right:
  forall f x,
  closed (application f x) ->
  closed x.
Proof.
  intros f x ? n.
  specialize (H n).
  dependent destruction H.
  assumption.
Qed.

(* TODO: this is a bi-implication in here. Should we make the same for the
   CPS-calculus? Also, applying this is a nightmare! *)

Lemma not_free_lift:
  forall e p k j,
  not_free (p + j) e <-> not_free (p + k + j) (lift k j e).
Proof.
  induction e; split; intros.
  - simpl.
    destruct (le_gt_dec j n).
    + dependent destruction H.
      constructor; lia.
    + constructor; lia.
  - simpl in H.
    destruct (le_gt_dec j n).
    + dependent destruction H.
      constructor; lia.
    + constructor; lia.
  - dependent destruction H.
    simpl; constructor.
    replace (S (p + k + j)) with (p + k + S j); try lia.
    apply IHe.
    replace (p + S j) with (S (p + j)); try lia.
    assumption.
  - dependent destruction H.
    constructor.
    replace (S (p + j)) with (p + S j); try lia.
    apply IHe with (k := k).
    replace (p + k + S j) with (S (p + k + j)); try lia.
    assumption.
  - dependent destruction H.
    simpl; constructor.
    + apply IHe1.
      assumption.
    + apply IHe2.
      assumption.
  - dependent destruction H.
    constructor.
    + apply IHe1 with k.
      assumption.
    + apply IHe2 with k.
      assumption.
Qed.

(* TODO: Does the CPS-calculus need something like this? *)

Lemma not_free_lift_zero:
  forall e p k,
  not_free p e <-> not_free (k + p) (lift k 0 e).
Proof.
  split; intros.
  - replace (k + p) with (p + k + 0); try lia.
    apply not_free_lift.
    rewrite Nat.add_0_r.
    assumption.
  - replace p with (p + 0); try lia.
    apply not_free_lift with (k := k).
    replace (p + k + 0) with (k + p); try lia.
    assumption.
Qed.

Inductive free_count: nat -> nat -> term -> Prop :=
  | free_count_match:
    forall n,
    free_count 1 n n
  | free_count_mismatch:
    forall n m,
    n <> m ->
    free_count 0 n m
  | free_count_abstraction:
    forall i t b n,
    free_count i (S n) b ->
    free_count i n (abstraction t b)
  | free_count_application:
    forall i j f x n,
    free_count i n f ->
    free_count j n x ->
    free_count (i + j) n (application f x).

Lemma not_free_count_zero_iff:
  forall n e,
  not_free n e <-> free_count 0 n e.
Proof.
  split; intros.
  - induction H.
    + now constructor.
    + now constructor.
    + replace 0 with (0 + 0) by auto.
      now constructor.
  - dependent induction H.
    + now constructor.
    + constructor.
      now apply IHfree_count.
    + assert (i = 0) by lia; subst.
      assert (j = 0) by lia; subst.
      constructor.
      * now apply IHfree_count1.
      * now apply IHfree_count2.
Qed.

Lemma free_count_is_decidable:
  forall e n,
  exists k,
  free_count k n e.
Proof.
  induction e; intros.
  + rename n0 into m.
    destruct (Nat.eq_dec m n) as [ ?H | ?H ]; subst.
    * exists 1.
      constructor.
    * exists 0.
      now constructor.
  + destruct IHe with (S n) as (k, ?).
    exists k.
    now constructor.
  + destruct IHe1 with n as (k, ?).
    destruct IHe2 with n as (j, ?).
    exists (k + j).
    now constructor.
Qed.

(* Full beta reduction relation. TODO: consider eta? *)

Inductive full: relation term :=
  | full_beta:
    forall t b x,
    full
      (application (abstraction t b) x)
      (subst x 0 b)
  | full_abs:
    forall t b1 b2,
    full b1 b2 ->
    full (abstraction t b1) (abstraction t b2)
  | full_app1:
    forall f1 f2 x,
    full f1 f2 ->
    full (application f1 x) (application f2 x)
  | full_app2:
    forall f x1 x2,
    full x1 x2 ->
    full (application f x1) (application f x2).

Global Hint Constructors full: cps.

(* TODO: is this one being used? *)

Lemma full_normal_dec:
  forall e,
  { normal full e } + { ~normal full e }.
Proof.
  induction e.
  - left; inversion 1.
  - destruct IHe.
    + left; intros b ?.
      dependent destruction H.
      eapply n; eauto.
    + right; intros ?.
      eapply n; intros b ?.
      eapply H.
      apply full_abs.
      eassumption.
  - destruct IHe1.
    + destruct IHe2.
      * destruct e1.
        (* TODO: refactor me, please. *)
        --- left.
            intros b ?.
            dependent destruction H.
            +++ inversion H.
            +++ eapply n0; eauto.
        --- right; intro.
            eapply H.
            apply full_beta.
        --- left.
            intros b ?.
            dependent destruction H.
            +++ eapply n; eauto.
            +++ eapply n0; eauto.
      * clear n; rename n0 into n; right.
        intros ?; eapply n.
        intros b ?; eapply H.
        apply full_app2.
        eassumption.
    + clear IHe2; right.
      intros ?; eapply n.
      intros b ?; eapply H.
      apply full_app1.
      eassumption.
Qed.

Inductive whr: relation term :=
  | whr_beta:
    forall t b x,
    whr
      (application (abstraction t b) x)
      (subst x 0 b)
  | whr_app1:
    forall f1 f2 x,
    whr f1 f2 ->
    whr (application f1 x) (application f2 x).

Lemma full_whr:
  inclusion whr full.
Proof.
  induction 1; simpl.
  - constructor.
  - constructor; auto.
Qed.

Lemma whr_is_a_function:
  forall a b1,
  whr a b1 ->
  forall b2,
  whr a b2 -> b1 = b2.
Proof.
  induction 1; intros.
  - dependent destruction H.
    + reflexivity.
    + inversion H.
  - dependent destruction H0.
    + inversion H.
    + f_equal; eauto.
Qed.

Lemma whr_is_decidable:
  forall e,
  { normal whr e } + { exists f, whr e f }.
Proof.
  induction e; simpl.
  - left.
    inversion 1.
  - left.
    inversion 1.
  - clear IHe2.
    destruct e1.
    + clear IHe1.
      left.
      inversion_clear 1.
      inversion H0.
    + right; eexists.
      constructor.
    + destruct IHe1.
      * left; intros x ?.
        dependent destruction H.
        firstorder.
      * right.
        destruct e as (x, ?).
        eexists.
        constructor.
        eassumption.
Qed.

Definition whnf: term -> Prop :=
  normal whr.

Lemma whnf_application_left:
  forall f x,
  whnf (application f x) ->
  whnf f.
Proof.
  intros f1 x ? f2 ?.
  eapply H; constructor.
  eassumption.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive compatible (R: relation term): relation term :=
  | compatible_step:
    forall e f,
    R e f -> compatible R e f
  | compatible_abs:
    forall t b1 b2,
    compatible R b1 b2 ->
    compatible R (abstraction t b1) (abstraction t b2)
  | compatible_app1:
    forall f1 f2 x,
    compatible R f1 f2 ->
    compatible R (application f1 x) (application f2 x)
  | compatible_app2:
    forall f x1 x2,
    compatible R x1 x2 ->
    compatible R (application f x1) (application f x2).

(* -------------------------------------------------------------------------- *)

Definition env: Set :=
  list type.

Inductive typing: env -> term -> type -> Prop :=
  | typing_bound:
    forall g n t,
    item t g n ->
    typing g n t
  | typing_abstraction:
    forall g t b s,
    typing (t :: g) b s ->
    typing g (abstraction t b) (arrow t s)
  | typing_application:
    forall g t s f x,
    typing g f (arrow t s) ->
    typing g x t ->
    typing g (application f x) s.

Example id :=
  fix id n t :=
    match n with
    | 0 => abstraction t 0
    | S m => application (id m (arrow t t)) (abstraction t 0)
    end.

Goal
  forall n t,
  typing [] (id n t) (arrow t t).
Proof.
  induction n; simpl; intros.
  - repeat constructor.
  - econstructor.
    + apply IHn.
    + repeat constructor.
Qed.
