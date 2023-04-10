(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
(* TODO: remove this one. *)
Require Import Local.Axiomatic.
Require Import Local.Reduction.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Observational.
Require Import Local.Lambda.Calculus.

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

(* TODO: fix typing on the following! *)

Inductive cbv_cps: lambda_term -> pseudoterm -> Prop :=
  | cbv_cps_bound:
    (* [x](k) = k<x> *)
    forall n: nat,
    (* TODO: assume k is fresh! *)
    cbv_cps n (jump 0 [bound n])
  | cbv_cps_abstraction:
    (* [\x.M](k) = k<f> { f<x, h> = [M](h) } *)
    forall t b b',
    cbv_cps (lambda_lift 1 0 b) b' ->
    cbv_cps
      (lambda_abstraction t b)
      (bind
        (jump 1 [bound 0])
        [void; void]
        b')
  | cbv_cps_application:
    (* [M N](k) = [M](m) { m<f> = [N](n) { n<a> = f<a, k> } } *)
    forall f x f' x',
    cbv_cps (lambda_lift 1 0 f) f' ->
    cbv_cps (lambda_lift 2 0 x) x' ->
    cbv_cps
      (lambda_application f x)
      (bind
        f'
        [void]
        (bind
          x'
          [void]
          (jump 1 [bound 0; bound 2]))).

Lemma cbv_cps_is_a_function:
  forall e c1,
  cbv_cps e c1 ->
  forall c2,
  cbv_cps e c2 -> c1 = c2.
Proof.
  induction 1; intros.
  - dependent destruction H; auto.
  - dependent destruction H0.
    f_equal; auto.
  - dependent destruction H1.
    f_equal; auto.
    f_equal; auto.
Qed.

Local Hint Resolve cbv_cps_is_a_function: cps.

Lemma cbv_cps_lift:
  forall e c,
  cbv_cps e c ->
  forall i k,
  k > 0 ->
  cbv_cps (lambda_lift i k e) (lift i k c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k n).
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_ge; try lia.
      constructor.
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      constructor.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    rewrite lambda_lift_lift_permutation; try lia.
    replace (k + 2) with (2 + k); simpl; try lia.
    apply IHcbv_cps; lia.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    + rewrite lambda_lift_lift_permutation; try lia.
      apply IHcbv_cps1; lia.
    + rewrite lambda_lift_lift_permutation; try lia.
      replace (S (k + 1)) with (2 + k); try lia.
      apply IHcbv_cps2; lia.
Qed.

Lemma cbv_cps_is_compositional:
  forall c1 c2,
  [c1 ~~ c2] ->
  forall e1 e2,
  lambda_not_free 0 e1 ->
  lambda_not_free 0 e2 ->
  cbv_cps e1 c1 ->
  cbv_cps e2 c2 ->
  forall (h: lambda_context) c3 c4,
  cbv_cps (h e1) c3 ->
  cbv_cps (h e2) c4 ->
  [c3 ~~ c4].
Proof.
  admit.
Admitted.
