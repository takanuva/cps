(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.AbstractRewriting.

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

(* The definitions of call by name and call by value reductions are standard,
   as of this moment, they were taken from Plotkin's paper. *)

Inductive lambda_cbn: relation lambda_term :=
  | lambda_cbn_beta:
    forall t b x,
    lambda_cbn
      (lambda_application (lambda_abstraction t b) x)
      (lambda_subst x 0 b)
  | lambda_cbn_app1:
    forall f1 f2 x,
    lambda_cbn f1 f2 ->
    lambda_cbn (lambda_application f1 x) (lambda_application f2 x)
  | lambda_cbn_app2:
    forall (f: nat) x1 x2,
    lambda_cbn x1 x2 ->
    lambda_cbn (lambda_application f x1) (lambda_application f x2).

Lemma lambda_full_cbn:
  inclusion lambda_cbn lambda_full.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma lambda_cbn_implies_nonvalue:
  forall a b,
  lambda_cbn a b -> ~lambda_value a.
Proof.
  induction 1; inversion 1.
Qed.

Lemma lambda_cbn_is_a_function:
  forall a b1,
  lambda_cbn a b1 ->
  forall b2,
  lambda_cbn a b2 -> b1 = b2.
Proof.
  induction 1; intros.
  - dependent destruction H.
    + reflexivity.
    + exfalso.
      inversion H.
  - dependent destruction H0.
    + exfalso.
      inversion H.
    + f_equal; auto.
    + exfalso.
      inversion H.
  - dependent destruction H0.
    + exfalso.
      inversion H0.
    + f_equal; auto.
Qed.

Inductive lambda_cbv: relation lambda_term :=
  | lambda_cbv_beta:
    forall t b x,
    lambda_value x ->
    lambda_cbv
      (lambda_application (lambda_abstraction t b) x)
      (lambda_subst x 0 b)
  | lambda_cbv_app1:
    forall f1 f2 x,
    lambda_cbv f1 f2 ->
    lambda_cbv (lambda_application f1 x) (lambda_application f2 x)
  | lambda_cbv_app2:
    forall f x1 x2,
    lambda_value f ->
    lambda_cbv x1 x2 ->
    lambda_cbv (lambda_application f x1) (lambda_application f x2).

Lemma lambda_full_cbv:
  inclusion lambda_cbv lambda_full.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma lambda_cbv_implies_nonvalue:
  forall a b,
  lambda_cbv a b -> ~lambda_value a.
Proof.
  induction 1; inversion 1.
Qed.

Lemma lambda_cbv_is_a_function:
  forall a b1,
  lambda_cbv a b1 ->
  forall b2,
  lambda_cbv a b2 -> b1 = b2.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    + reflexivity.
    + exfalso.
      inversion H0.
    + exfalso.
      apply lambda_cbv_implies_nonvalue with x x2; auto.
  - dependent destruction H0.
    + exfalso.
      apply lambda_cbv_implies_nonvalue in H.
      auto with cps.
    + f_equal; auto.
    + exfalso.
      apply lambda_cbv_implies_nonvalue in H.
      auto with cps.
  - dependent destruction H1.
    + exfalso.
      apply lambda_cbv_implies_nonvalue in H0.
      auto with cps.
    + exfalso.
      apply lambda_cbv_implies_nonvalue in H1.
      auto with cps.
    + f_equal; auto.
Qed.
