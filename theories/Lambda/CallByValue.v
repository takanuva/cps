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
Require Export Local.Lambda.Calculus.

Include Lambda.Calculus.
Module CPS := Local.Syntax.

Inductive cbv: relation term :=
  | cbv_beta:
    forall t b x,
    value x ->
    cbv
      (application (abstraction t b) x)
      (subst x 0 b)
  | cbv_app1:
    forall f1 f2 x,
    cbv f1 f2 ->
    cbv (application f1 x) (application f2 x)
  | cbv_app2:
    forall f x1 x2,
    value f ->
    cbv x1 x2 ->
    cbv (application f x1) (application f x2).

Lemma full_cbv:
  inclusion cbv full.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma cbv_implies_nonvalue:
  forall a b,
  cbv a b -> ~value a.
Proof.
  induction 1; inversion 1.
Qed.

Lemma cbv_is_a_function:
  forall a b1,
  cbv a b1 ->
  forall b2,
  cbv a b2 -> b1 = b2.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    + reflexivity.
    + exfalso.
      inversion H0.
    + exfalso.
      apply cbv_implies_nonvalue with x x2; auto.
  - dependent destruction H0.
    + exfalso.
      apply cbv_implies_nonvalue in H.
      auto with cps.
    + f_equal; auto.
    + exfalso.
      apply cbv_implies_nonvalue in H.
      auto with cps.
  - dependent destruction H1.
    + exfalso.
      apply cbv_implies_nonvalue in H0.
      auto with cps.
    + exfalso.
      apply cbv_implies_nonvalue in H1.
      auto with cps.
    + f_equal; auto.
Qed.

(* TODO: fix typing on the following! *)

Inductive cbv_cps: term -> pseudoterm -> Prop :=
  | cbv_cps_bound:
    (* [x](k) = k<x> *)
    forall n: nat,
    cbv_cps (S n) (jump 0 [CPS.bound (S n)])
  | cbv_cps_abstraction:
    (* [\x.M](k) = k<f> { f<x, h> = [M](h) } *)
    forall t b b',
    cbv_cps (lift 1 0 b) b' ->
    cbv_cps
      (abstraction t b)
      (bind
        (jump 1 [CPS.bound 0])
        [void; void]
        b')
  | cbv_cps_application:
    (* [M N](k) = [M](m) { m<f> = [N](n) { n<a> = f<a, k> } } *)
    forall f x f' x',
    cbv_cps (lift 1 0 f) f' ->
    cbv_cps (lift 2 0 x) x' ->
    cbv_cps
      (application f x)
      (bind
        f'
        [void]
        (bind
          x'
          [void]
          (jump 1 [CPS.bound 0; CPS.bound 2]))).

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
  cbv_cps (lift i k e) (CPS.lift i k c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k (S n)).
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_ge; try lia.
      replace (i + S n) with (S (i + n)); try lia.
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
    rewrite lift_lift_permutation; try lia.
    replace (k + 2) with (2 + k); simpl; try lia.
    apply IHcbv_cps; lia.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    + rewrite lift_lift_permutation; try lia.
      apply IHcbv_cps1; lia.
    + rewrite lift_lift_permutation; try lia.
      replace (S (k + 1)) with (2 + k); try lia.
      apply IHcbv_cps2; lia.
Qed.

Lemma cbv_cps_is_compositional:
  forall c1 c2,
  [c1 ~~ c2] ->
  forall e1 e2,
  not_free 0 e1 ->
  not_free 0 e2 ->
  cbv_cps e1 c1 ->
  cbv_cps e2 c2 ->
  forall (h: context) c3 c4,
  cbv_cps (h e1) c3 ->
  cbv_cps (h e2) c4 ->
  [c3 ~~ c4].
Proof.
  admit.
Admitted.

(* -------------------------------------------------------------------------- *)

(* Add lemma about administrative redexes in here, similar to [CallByName.v]! *)

(* -------------------------------------------------------------------------- *)

(*
  Let's try to reason about simulation. The proof should follow in a similar way
  from the call-by-name one. Recall the call-by-value translation:

    1) [x] = k<x>
    2) [\x.M] = k<f> { f<x, k> = [M] }
    3) [M N](k) = [M] { k<f> = [N] { k<v> = f<v, k> } }

  Again, we have a term as [(\x.a) b], which will translate into:

    k<f>
    { f<x, k> =
        [a] }
    { k<f> =
        [b]
        { k<v> =
            f<v, k> } }

  We immediately have two linear jump redexes (only the first at head position):

    [b]
    { k<x> =
        [a] }

  This is the opposite of the call-by-name! Of course, I should have expected
  that. If [a] contains a free occurrence of x and is thus equal to C[x], we
  will then have:

    [b]
    { k<x> =
        D[k<x>] }

  This is way more problematic. Does Plotkin prove simulation for the full beta
  reduction in here, or just for the call-by-value beta reduction? AAAAAAAAAAA.

  It seems this simply isn't true for the full beta... could we think of a
  counter example? Anyways, let's consider, thus, that b is a value. We have two
  cases then. The first one, where b is a variable:

    k<y>
    { k<x> =
      D[k<x>] }

  This will simplify in one linear head reduction to:

    D[k<y>]

  Ok, this seems fine. I've replaced one variable by the other. Now, the other
  case is when b is an abstraction. We should then have:

    k<f>
    { f<y, k> =
      [c] }
    { k<x> =
      D[k<x>] }

  This will simply reduce to:

    D[k<f>]
    { f<y, k> =
      [c] }

  As we'd have the reduction be from [(\x.a) (\y.c)] to [a[\y.c/x]], if for
  simplicity we assume there's a single x in there, we'd want to have:

    D[k<f> { f<y, k> = [c] }]

  This is just floating! However, the problem is that f can appear free multiple
  times, so we can't just float this in there. We can duplicate it, of course,
  if we are not trying to reduce but rather show that the terms are equal. This
  is enough to show adequacy, but we don't have one-step simulation anymore. We
  would still have it if we allowed for specialization, just like it's done in
  linear logic! But we'd like to have contraction instead for the CPS-calculus.

  Other notions of reduction: though the call-by-name translation can't validate
  eta (we don't want it to!), the call-by-value translation should validate some
  extra notions of reduction. The call-by-value eta reduction can be simulated,
  but it does need the (ETA) rule. It seems that the id-reduction from Moggi's
  calculus, (\x.x) e, can also be simulated, but it requires floating.

*)
