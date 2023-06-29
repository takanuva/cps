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

Lemma lift_lift_permutation:
  forall e (i j k l : nat),
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
