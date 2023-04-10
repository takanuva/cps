(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.

Inductive lambda_type: Set :=
  | lambda_base
  | lambda_arrow (a: lambda_type) (b: lambda_type).

Inductive lambda_term: Set :=
  | lambda_bound (n: nat)
  | lambda_abstraction (t: lambda_type) (b: lambda_term)
  | lambda_application (f: lambda_term) (x: lambda_term).

Coercion lambda_bound: nat >-> lambda_term.

Inductive lambda_value: lambda_term -> Prop :=
  | lambda_value_bound:
    forall n: nat,
    lambda_value n
  | lambda_value_abstraction:
    forall t b,
    lambda_value (lambda_abstraction t b).

Global Hint Constructors lambda_value: cps.

Lemma lambda_value_dec:
  forall e,
  { lambda_value e } + { ~lambda_value e }.
Proof.
  destruct e.
  - left; auto with cps.
  - left; auto with cps.
  - right; intro.
    inversion H.
Qed.

Fixpoint lambda_lift (i: nat) (k: nat) (e: lambda_term): lambda_term :=
  match e with
  | lambda_bound n =>
    if le_gt_dec k n then
      lambda_bound (i + n)
    else
      lambda_bound n
  | lambda_abstraction t b =>
    lambda_abstraction t (lambda_lift i (S k) b)
  | lambda_application f x =>
    lambda_application (lambda_lift i k f) (lambda_lift i k x)
  end.

Fixpoint lambda_subst (p: lambda_term) (k: nat) (q: lambda_term): lambda_term :=
  match q with
  | lambda_bound n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => lambda_bound (pred n)
    | inleft (right _) => lambda_lift k 0 p
    | inright _ => lambda_bound n
    end
  | lambda_abstraction t b =>
    lambda_abstraction t (lambda_subst p (S k) b)
  | lambda_application f x =>
    lambda_application (lambda_subst p k f) (lambda_subst p k x)
  end.

Lemma lambda_lift_lift_permutation:
  forall e (i j k l : nat),
  k <= l ->
  lambda_lift i k (lambda_lift j l e) =
    lambda_lift j (i + l) (lambda_lift i k e).
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

Fixpoint lambda_size (e: lambda_term): nat :=
  match e with
  | lambda_bound n =>
    1
  | lambda_abstraction t b =>
    1 + lambda_size b
  | lambda_application f x =>
    1 + lambda_size f + lambda_size x
  end.

Lemma lambda_size_lift:
  forall e i k,
  lambda_size (lambda_lift i k e) = lambda_size e.
Proof.
  induction e; simpl; intros.
  - destruct (le_gt_dec k n); auto.
  - auto.
  - auto.
Qed.

Inductive lambda_context: Set :=
  | lambda_context_hole
  | lambda_context_abstraction (t: lambda_type) (b: lambda_context)
  | lambda_context_application_left (f: lambda_context) (x: lambda_term)
  | lambda_context_application_right (f: lambda_term) (x: lambda_context).

Fixpoint lambda_apply_context h e :=
  match h with
  | lambda_context_hole =>
    e
  | lambda_context_abstraction t b =>
    lambda_abstraction t (lambda_apply_context b e)
  | lambda_context_application_left f x =>
    lambda_application (lambda_apply_context f e) x
  | lambda_context_application_right f x =>
    lambda_application f (lambda_apply_context x e)
  end.

Coercion lambda_apply_context: lambda_context >-> Funclass.

Fixpoint lambda_context_bvars h: nat :=
  match h with
  | lambda_context_hole =>
    0
  | lambda_context_abstraction t b =>
    1 + lambda_context_bvars b
  | lambda_context_application_left f x =>
    lambda_context_bvars f
  | lambda_context_application_right f x =>
    lambda_context_bvars x
  end.

Fixpoint lambda_context_depth h: nat :=
  match h with
  | lambda_context_hole =>
    0
  | lambda_context_abstraction t b =>
    1 + lambda_context_depth b
  | lambda_context_application_left f x =>
    1 + lambda_context_depth f
  | lambda_context_application_right f x =>
    1 + lambda_context_depth x
  end.

Fixpoint lambda_context_lift i k h: lambda_context :=
  match h with
  | lambda_context_hole =>
    lambda_context_hole
  | lambda_context_abstraction t b =>
    lambda_context_abstraction t (lambda_context_lift i (S k) b)
  | lambda_context_application_left f x =>
    lambda_context_application_left
      (lambda_context_lift i k f) (lambda_lift i k x)
  | lambda_context_application_right f x =>
    lambda_context_application_right
      (lambda_lift i k f) (lambda_context_lift i k x)
  end.

Lemma lambda_context_lift_is_sound:
  forall (h: lambda_context) i k e,
  lambda_lift i k (h e) =
    lambda_context_lift i k h (lambda_lift i (lambda_context_bvars h + k) e).
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

Lemma lambda_context_lift_depth:
  forall h i k,
  lambda_context_depth (lambda_context_lift i k h) = lambda_context_depth h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
  - rewrite IHh; auto.
Qed.

Inductive lambda_not_free: nat -> lambda_term -> Prop :=
  | lambda_not_free_bound:
    forall n m,
    n <> m -> lambda_not_free n m
  | lambda_not_free_abstraction:
    forall t b n,
    lambda_not_free (S n) b ->
    lambda_not_free n (lambda_abstraction t b)
  | lambda_not_free_application:
    forall f x n,
    lambda_not_free n f ->
    lambda_not_free n x ->
    lambda_not_free n (lambda_application f x).

(* Full beta reduction relation. TODO: consider eta? *)

Inductive lambda_full: relation lambda_term :=
  | lambda_full_beta:
    forall t b x,
    lambda_full
      (lambda_application (lambda_abstraction t b) x)
      (lambda_subst x 0 b)
  | lambda_full_abs:
    forall t b1 b2,
    lambda_full b1 b2 ->
    lambda_full (lambda_abstraction t b1) (lambda_abstraction t b2)
  | lambda_full_app1:
    forall f1 f2 x,
    lambda_full f1 f2 ->
    lambda_full (lambda_application f1 x) (lambda_application f2 x)
  | lambda_full_app2:
    forall f x1 x2,
    lambda_full x1 x2 ->
    lambda_full (lambda_application f x1) (lambda_application f x2).
