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
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Observational.
Require Import Local.Conservation.
(* TODO: will we need this one...? *)
Require Import Local.Structural.
Require Import Local.Shrinking.
Require Export Local.Lambda.Calculus.

Include Lambda.Calculus.
Module CPS := Local.Syntax.

Inductive cbv: relation term :=
  | cbv_betav:
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

Local Hint Constructors cbv: cps.

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

Lemma cbv_is_decidable:
  forall e,
  { normal cbv e } + { exists f, cbv e f }.
Proof.
  induction e; simpl.
  - left.
    inversion 1.
  - left.
    inversion 1.
  - destruct e1.
    + clear IHe1.
      destruct IHe2.
      * left.
        (* TODO: damn OCD... *)
        inversion_clear 1; [ easy | firstorder ].
      * right.
        destruct e as (x, ?).
        exists (application n x).
        constructor 3; auto.
        constructor.
    + destruct value_dec with e2.
      * right; eexists.
        now constructor.
      * destruct IHe2.
        (* TODO: refactor me, please? *)
        left.
        inversion_clear 1.
        contradiction.
        inversion H0.
        firstorder.
        right.
        destruct e as (x, ?).
        eexists.
        constructor 3.
        constructor.
        eassumption.
    + destruct IHe1.
      * left; intros x ?.
        dependent destruction H.
        (* TODO: refactor... *)
        firstorder.
        inversion H.
      * right.
        destruct e as (x, ?).
        eexists; eauto with cps.
Qed.

Lemma closed_normal_cbv_implies_value:
  forall e,
  closed e ->
  normal cbv e ->
  value e.
Proof.
  intros.
  destruct value_dec with e as [ ?H | ?H ].
  - assumption.
  - exfalso.
    induction e.
    + apply H1.
      constructor.
    + apply H1.
      constructor.
    + clear H1.
      destruct e1.
      * specialize (H n).
        dependent destruction H.
        dependent destruction H.
        contradiction.
      * eapply H0.
        constructor.
        destruct value_dec with e2 as [ ?H | ?H ]; auto.
        exfalso.
        apply IHe2.
        (* TODO: refactor me, please... *)
        intros n.
        specialize (H n).
        now dependent destruction H.
        intros x ?.
        eapply H0.
        constructor 3; eauto.
        constructor.
        assumption.
      * apply IHe1.
        (* TODO: refactor... *)
        intro.
        specialize (H n).
        dependent destruction H.
        assumption.
        intros x ?.
        eapply H0.
        constructor.
        eassumption.
        inversion 1.
Qed.

(* TODO: fix typing on the following! *)

Local Notation VAR n :=
  (* [x] = k<x> *)
  (jump 0 [CPS.bound (S n)]).

Local Notation ABS b :=
  (* [\x.e] = k<f> { f<x, k> = [e] } *)
  (bind (jump 1 [CPS.bound 0]) [void; void] b).

Local Notation APP b c :=
  (* [e f] = [e] { k<f> = [f] { k<v> = f<v, k> } } *)
  (bind b [void] (bind c [void] (jump 1 [CPS.bound 2; CPS.bound 0]))).

(* TODO: these lifts should be moved from source to target! *)

Inductive cbv_cps: term -> pseudoterm -> Prop :=
  | cbv_cps_bound:
    forall n: nat,
    cbv_cps n (VAR n)
  | cbv_cps_abstraction:
    forall t e b,
    cbv_cps (lift 1 1 e) b ->
    cbv_cps (abstraction t e) (ABS b)
  | cbv_cps_application:
    forall f x b c,
    cbv_cps (lift 1 0 f) b ->
    cbv_cps (lift 2 0 x) c ->
    cbv_cps (application f x) (APP b c).

Local Hint Constructors cbv_cps: cps.

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
  cbv_cps (lift i k e) (CPS.lift i (S k) c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k n).
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
      replace (k + 1) with (1 + k); try lia.
      apply IHcbv_cps2; lia.
Qed.

Local Hint Resolve cbv_cps_lift: cps.

Lemma cbv_cps_is_total:
  forall e,
  exists c,
  cbv_cps e c.
Proof.
  induction e.
  - eauto with cps.
  - destruct IHe as (c, ?).
    eauto with cps.
  - destruct IHe1 as (b, ?).
    destruct IHe2 as (c, ?).
    eauto with cps.
Qed.

Local Hint Resolve cbv_cps_is_total: cps.

Lemma cbv_cps_lift_inversion:
  forall i k e b,
  cbv_cps (lift i k e) b ->
  exists2 c,
  cbv_cps e c & b = CPS.lift i (S k) c.
Proof.
  intros.
  assert (exists c, cbv_cps e c) as (c, ?).
  - eauto with cps.
  - eauto with cps.
Qed.

Local Hint Resolve cbv_cps_lift_inversion: cps.

Lemma cbv_cps_not_free:
  forall e c,
  cbv_cps e c ->
  forall n,
  not_free n e <-> CPS.not_free (S n) c.
Proof.
  induction 1; split; intros.
  - dependent destruction H.
    rename n0 into m.
    constructor.
    + constructor; lia.
    + do 2 constructor; lia.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H0.
    rename n0 into m.
    constructor; lia.
  - constructor; simpl.
    + constructor.
      * constructor; lia.
      * do 2 constructor; lia.
    + do 3 constructor.
    + dependent destruction H0.
      apply IHcbv_cps; try lia.
      replace (S n) with (n + 1) in H0; try lia.
      apply not_free_lift with (k := 1) in H0.
      replace (n + 1 + 1) with (2 + n) in H0; try lia.
      assumption.
  - constructor.
    dependent destruction H0.
    simpl in H0_0.
    apply IHcbv_cps in H0_0; auto.
    replace (S (S n)) with (n + 1 + 1) in H0_0; try lia.
    apply not_free_lift in H0_0.
    replace (n + 1) with (1 + n) in H0_0; try lia.
    assumption.
  - dependent destruction H1.
    constructor; simpl.
    + apply IHcbv_cps1; auto.
      replace (S n) with (n + 1 + 0); try lia.
      apply not_free_lift.
      rewrite Nat.add_comm.
      assumption.
    + do 2 constructor.
    + repeat (simpl; try constructor; try lia).
      simpl; eapply IHcbv_cps2; auto.
      replace (S (S n)) with (n + 2 + 0); try lia.
      apply not_free_lift.
      rewrite Nat.add_comm.
      assumption.
  - dependent destruction H1.
    dependent destruction H1_0.
    simpl in H2, H1_0_1, H1_0_2.
    constructor.
    + apply IHcbv_cps1 in H1_; auto.
      replace (S n) with (n + 1 + 0) in H1_; try lia.
      apply not_free_lift in H1_.
      rewrite Nat.add_comm in H1_.
      assumption.
    + apply IHcbv_cps2 in H1_0_1; auto.
      replace (S (S n)) with (n + 2 + 0) in H1_0_1; try lia.
      apply not_free_lift in H1_0_1.
      rewrite Nat.add_comm in H1_0_1.
      assumption.
Qed.

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

Axiom R: relation pseudoterm.

Conjecture R_bind_left:
  LEFT R.

Conjecture R_bind_right:
  RIGHT R.

Conjecture R_lift:
  forall b c,
  R b c ->
  forall i k,
  R (CPS.lift i k b) (CPS.lift i k c).

Lemma rt_R_bind_left:
  LEFT rt(R).
Proof.
  induction 1.
  - apply rt_step.
    now apply R_bind_left.
  - apply rt_refl.
  - now apply rt_trans with (bind y ts c).
Qed.

Lemma rt_R_bind_right:
  RIGHT rt(R).
Proof.
  induction 1.
  - apply rt_step.
    now apply R_bind_right.
  - apply rt_refl.
  - now apply rt_trans with (bind b ts y).
Qed.

Lemma rt_R_lift:
  forall b c,
  rt(R) b c ->
  forall i k,
  rt(R) (CPS.lift i k b) (CPS.lift i k c).
Proof.
  induction 1; intros.
  - apply rt_step.
    now apply R_lift.
  - apply rt_refl.
  - now apply rt_trans with (CPS.lift i k y).
Qed.

Lemma cbv_simulates_betav:
  forall t e x b c,
  value x ->
  cbv_cps (application (abstraction t e) x) b ->
  cbv_cps (subst x 0 e) c ->
  rt(R) b c.
Proof.
  (* This should follow the description above. *)
  admit.
Admitted.

Lemma cbv_simulates_cbv:
  forall e f,
  cbv e f ->
  forall b c,
  cbv_cps e b ->
  cbv_cps f c ->
  rt(R) b c.
Proof.
  induction 1; intros.
  - rename b into e, b0 into b.
    now apply cbv_simulates_betav with t e x.
  - dependent destruction H0.
    dependent destruction H1.
    assert (c0 = c) by eauto with cps.
    clear H1_0; subst.
    apply cbv_cps_lift_inversion in H0_ as (b1, ?, ?).
    apply cbv_cps_lift_inversion in H1_ as (b2, ?, ?).
    specialize (IHcbv b1 b2); subst.
    apply rt_R_bind_left.
    apply rt_R_lift.
    now apply IHcbv.
  - dependent destruction H1.
    dependent destruction H2.
    assert (b0 = b) by eauto with cps.
    clear H1_; subst.
    apply cbv_cps_lift_inversion in H1_0 as (c1, ?, ?).
    apply cbv_cps_lift_inversion in H2_0 as (c2, ?, ?).
    specialize (IHcbv c1 c2); subst.
    apply rt_R_bind_right.
    apply rt_R_bind_left.
    apply rt_R_lift.
    now apply IHcbv.
Qed.

Lemma cbv_simulation:
  forall e f,
  compatible cbv e f ->
  forall b c,
  cbv_cps e b ->
  cbv_cps f c ->
  rt(R) b c.
Proof.
  induction 1; intros.
  - now apply cbv_simulates_cbv with e f.
  - dependent destruction H0.
    dependent destruction H1.
    apply cbv_cps_lift_inversion in H0 as (c1, ?, ?).
    apply cbv_cps_lift_inversion in H1 as (c2, ?, ?).
    specialize (IHcompatible c1 c2); subst.
    apply rt_R_bind_right.
    apply rt_R_lift.
    now apply IHcompatible.
  - dependent destruction H0.
    dependent destruction H1.
    assert (c0 = c) by eauto with cps.
    clear H1_0; subst.
    apply cbv_cps_lift_inversion in H0_ as (b1, ?, ?).
    apply cbv_cps_lift_inversion in H1_ as (b2, ?, ?).
    specialize (IHcompatible b1 b2); subst.
    apply rt_R_bind_left.
    apply rt_R_lift.
    now apply IHcompatible.
  - dependent destruction H0.
    dependent destruction H1.
    assert (b0 = b) by eauto with cps.
    clear H0_; subst.
    apply cbv_cps_lift_inversion in H0_0 as (c1, ?, ?).
    apply cbv_cps_lift_inversion in H1_0 as (c2, ?, ?).
    specialize (IHcompatible c1 c2); subst.
    apply rt_R_bind_right.
    apply rt_R_bind_left.
    apply rt_R_lift.
    now apply IHcompatible.
Qed.

Local Lemma technical1:
  forall n m,
  weakly_converges
    (bind (jump 0 [CPS.bound (2 + n)]) [void]
       (bind (jump 0 [CPS.bound (3 + m)]) [void]
          (jump 1 [CPS.bound 2; CPS.bound 0])))
    (1 + n).
Proof.
  intros.
  (* Here our term is of the form:

       k<x> { k<f> = k<y> { k<v> = f<v, k> } }

     This will reduce to:

       k<y> { k<v> = x<v, k> } { k<f> = k<y> { k<v> = f<v, k> } }

     Then to:

      x<y, k> { k<v> = x<v, k> } { k<f> = k<y> { k<v> = f<v, k> } }

     Which will then halt at x.
  *)
  eexists; [ eapply star_trans |].
  - (* TODO: we need to automate this... *)
    set (c := jump 1 [CPS.bound 2; CPS.bound 0]).
    set (b := bind (jump 0 [CPS.bound (3 + m)]) [void] c).
    replace (bind (jump 0 [CPS.bound (2 + n)]) [void] b) with
      (context_left Context.context_hole [void] b (jump 0 [CPS.bound (2 + n)]))
      by auto.
    apply star_ctxjmp.
    reflexivity.
  - (* TODO: not the best way, but hopefully I'll replace this by sigma. *)
    compute.
    set (b := jump 1 [CPS.bound 2; CPS.bound 0]).
    set (c := bind (jump 0 [CPS.bound (S (S (S m)))]) [void] b).
    set (d := jump (S (S (S n))) [CPS.bound 2; CPS.bound 0]).
    apply star_bind_left.
    replace (jump 0 [CPS.bound (S (S (S m)))]) with
      (Context.context_hole (jump 0 [CPS.bound (S (S (S m)))])) by auto.
    apply star_ctxjmp.
    reflexivity.
  - (* TODO: ditto... *)
    compute.
    do 3 constructor.
Qed.

Local Lemma technical2:
  forall n b,
  weakly_converges
    (bind (jump 0 [CPS.bound (S (S n))]) [void]
      (bind
        (CPS.lift 2 1 (bind (jump 1 [CPS.bound 0])
          [void; void] (CPS.lift 1 2 b)))
        [void] (jump 1 [CPS.bound 2; CPS.bound 0]))) (1 + n).
Proof.
  intros.
  (* Here our term is of the form:

       k<x> { k<f> = k<f> { f<x, k> = [e] } { k<v> = f<v, k> } }

     This will reduce to:

       k<f> { f<x, k> = [e] } { k<v> = x<v, k> } { ... }

     Then to:

       x<f, k> { f<x, k> = [e] } { k<v> = x<v, k> } { ... }

     Which will then halt at x.
  *)
  eexists; [ eapply star_trans |].
  - replace (jump 0 [CPS.bound (S (S n))]) with
      (Context.context_hole (jump 0 [CPS.bound (S (S n))])) by auto.
    apply star_ctxjmp.
    reflexivity.
  - simpl.
    apply star_bind_left.
    rewrite lift_distributes_over_bind; simpl.
    rewrite Metatheory.lift_lift_simplification by lia; simpl.
    rewrite subst_distributes_over_bind; simpl.
    rewrite subst_lift_simplification by lia.
    rewrite lift_distributes_over_bind; simpl.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt by lia.
    rewrite lift_bound_lt by lia.
    replace (Syntax.subst (CPS.bound (S (S n))) 0 (Syntax.lift 1 1 void))
      with void by now compute.
    replace (Syntax.lift 2 2 void) with void by now compute.
    replace (Syntax.lift 2 1 void) with void by now compute.
    rewrite Metatheory.lift_lift_simplification by lia; simpl.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt by lia.
    rewrite lift_bound_ge by lia; simpl.
    rewrite lift_bound_lt by lia; simpl.
    rewrite subst_distributes_over_jump; simpl.
    rewrite subst_bound_eq by lia.
    rewrite lift_bound_ge by lia; simpl.
    rewrite subst_bound_gt by lia; simpl.
    rewrite subst_bound_lt by lia; simpl.
    set (c := (jump (S (S (S n))) [CPS.bound 2; CPS.bound 0])).
    replace (bind (jump 1 [CPS.bound 0]) [void; void] (Syntax.lift 3 2 b)) with
      (context_left Context.context_hole [void; void] (Syntax.lift 3 2 b)
      (jump 1 [CPS.bound 0])) by auto.
    apply star_ctxjmp.
    reflexivity.
  - simpl.
    do 4 constructor.
Qed.

Local Lemma technical3:
  forall b k n,
  weakly_converges b (1 + k) ->
  weakly_converges
    (bind (jump 0 [CPS.bound (S (S n))]) [void]
       (bind (CPS.lift 2 1 b) [void]
          (jump 1 [CPS.bound 2; CPS.bound 0])))
    (1 + k).
Proof.
  intros.
  (* Here our term is of the form:

      k<x> { k<f> = [e] { k<v> = f<v, k> } }

     Where we know that [e] halts at some variable free y. This reduces to:

       [e] { k<v> = x<v, k> } { ... }

     Which we know, by the renaming conventions, will still jump to y.
   *)
  destruct H as (c, ?, ?).
  eexists; [ eapply star_trans |].
  - apply star_bind_right.
    apply star_bind_left.
    apply star_lift.
    eassumption.
  - replace (jump 0 [CPS.bound (S (S n))]) with
      (Context.context_hole (jump 0 [CPS.bound (S (S n))])) by auto.
    apply star_ctxjmp.
    reflexivity.
  - constructor; simpl.
    rewrite lift_distributes_over_bind.
    rewrite subst_distributes_over_bind.
    constructor.
    rewrite Metatheory.lift_lift_simplification by lia; simpl.
    eapply converges_subst.
    + eapply converges_lift.
      * eassumption.
      * rewrite lift_bound_ge by lia; simpl.
        reflexivity.
    + now rewrite subst_bound_gt by lia.
Qed.

Local Lemma technical4:
  forall b c k,
  weakly_converges c (1 + k) ->
  weakly_converges
    (bind (bind (jump 1 [CPS.bound 0]) [void; void] b)
       [void]
       (bind (CPS.lift 2 1 c) [void]
          (jump 1 [CPS.bound 2; CPS.bound 0])))
    (1 + k).
Proof.
  intros.
  (* Here our term is of the form:

       k<f> { f<x, k> = [e] } { k<f> = [f] { k<v> = f<v, k> } }

     And we know that [f] halts to a free variable y. This will reduce to:

       [f] { k<v> = f<v, k> } { f<x, k> = [e] } { ... }

     Immediately we know that this halts to y due to the renaming conventions.
   *)
   destruct H as (d, ?, ?).
   eexists; [ eapply star_trans |].
   - apply star_bind_right.
     apply star_bind_left.
     apply star_lift.
     eassumption.
   - replace (bind (jump 1 [CPS.bound 0]) [void; void] b) with
       (context_left Context.context_hole [void; void] b (jump 1 [CPS.bound 0]))
       by auto.
     apply star_ctxjmp.
     reflexivity.
   - simpl.
     do 2 constructor.
     rewrite lift_distributes_over_bind.
     rewrite Metatheory.lift_lift_simplification by lia; simpl.
     rewrite subst_distributes_over_bind; simpl.
     rewrite subst_lift_simplification by lia.
     constructor.
     eapply converges_lift.
     + eassumption.
     + now rewrite lift_bound_ge by lia.
Qed.

Local Lemma technical5:
  forall b c k,
  weakly_converges b (1 + k) ->
  weakly_converges
    (bind (CPS.lift 1 1 b) [void]
       (bind c [void]
          (jump 1 [CPS.bound 2; CPS.bound 0])))
    (1 + k).
Proof.
  intros.
  (* Here our term is simply of the form:

       [e f](k) = [e] { k<f> = [f] { k<v> = f<v, k> } }

     And we know that [e] halts to a free variable y. Thus we know that by the
     renaming conventions we will reduce to y after applying just the steps that
     [e] requires to get there.
   *)
  destruct H as (d, ?, ?).
  eexists.
  - apply star_bind_left.
    apply star_lift.
    eassumption.
  - constructor.
    eapply converges_lift.
    + eassumption.
    + now rewrite lift_bound_ge by lia.
Qed.

Lemma termination_nonvalue:
  forall e,
  ~value e ->
  normal cbv e ->
  forall c,
  cbv_cps e c ->
  exists2 k,
  weakly_converges c (1 + k) & free k e.
Proof.
  (* This one is way more annoying than the CBN one... however, we still follow
     by case analysis. *)
  induction e; intros.
  - exfalso.
    apply H.
    constructor.
  - exfalso.
    apply H.
    constructor.
  - clear H.
    destruct e1.
    + clear IHe1.
      dependent destruction H1.
      dependent destruction H1_.
      apply cbv_cps_lift_inversion in H1_0 as (b, ?, ?); subst.
      destruct e2.
      * (* In here, the expression is like x y. *)
        dependent destruction H.
        rewrite lift_distributes_over_jump; simpl.
        rewrite lift_bound_lt by lia.
        rewrite lift_bound_ge by lia; simpl.
        exists n.
        (* TODO: refactor, please? *)
        apply technical1.
        inversion_clear 1.
        inversion_clear H1.
        contradiction.
      * (* In here, the expression is like x (\y.e). *)
        dependent destruction H.
        apply cbv_cps_lift_inversion in H as (c, ?, ?); subst.
        exists n.
        (* TODO: refactor...? *)
        apply technical2.
        inversion_clear 1.
        inversion_clear H2.
        contradiction.
      * (* In here, the expression is like x (e f). This thus follows by the
           inductive hypothesis. TODO: refactor... *)
        destruct IHe2 with b as (k, ?, ?).
        inversion 1.
        intros e3 ?H.
        apply H0 with (application n e3).
        constructor 3.
        constructor.
        assumption.
        assumption.
        exists k.
        now apply technical3.
        inversion_clear 1.
        contradiction.
    + (* In here, the expression is like (\x.e) f. So, the only way this is not
         a redex is if f is not a value (and can't become one). So this will
         follow directly by the inductive hypothesis. *)
      clear IHe1.
      dependent destruction H1.
      apply cbv_cps_lift_inversion in H1_0 as (d, ?, ?); subst.
      destruct IHe2 with d as (k, ?, ?).
      * intros ?.
        apply H0 with (subst e2 0 e1).
        now constructor.
      * intros e3 ?.
        apply H0 with (application (abstraction t e1) e3).
        constructor 3; auto with cps.
      * assumption.
      * exists k.
        (* TODO: refactor... *)
        dependent destruction H1_.
        now apply technical4.
        inversion_clear 1.
        contradiction.
    + (* In here, the expression is like (e f) g. So this clearly follows by
         the inductive hypothesis on the left. *)
      clear IHe2.
      dependent destruction H1.
      apply cbv_cps_lift_inversion in H1_ as (d, ?, ?); subst.
      destruct IHe1 with d as (k, ?, ?).
      * inversion 1.
      * intros e3 ?.
        apply H0 with (application e3 e2).
        now constructor 2.
      * assumption.
      * exists k.
        (* TODO: refactor... *)
        now apply technical5.
        inversion_clear 1.
        contradiction.
Qed.

Lemma termination:
  forall e,
  normal cbv e ->
  forall c,
  cbv_cps e c ->
  exists k,
  weakly_converges c k.
Proof.
  intros.
  destruct value_dec with e as [ ?H | ?H ].
  - exists 0, c.
    + apply star_refl.
    + destruct H1.
      * dependent destruction H0.
        constructor.
      * dependent destruction H0.
        do 2 constructor.
  - destruct termination_nonvalue with e c as (k, ?, ?).
    + assumption.
    + assumption.
    + assumption.
    + exists (1 + k).
      assumption.
Qed.

Lemma normal_form_preservation:
  forall e,
  normal (compatible cbv) e ->
  forall c,
  cbv_cps e c ->
  SN step c.
Proof.
  intros.
  apply SN_subset with (union beta smol).
  - apply step_characterization.
  - apply shrinking_preserves_strong_normalization.
    + exact smol_is_shrinking.
    + apply uniform_normalization.
      admit.
Admitted.

(* -------------------------------------------------------------------------- *)

Definition cbv_terminates (e: term): Prop :=
  exists2 v,
  value v & rt(cbv) e v.

Lemma sn_cbv_terminates:
  forall e,
  cbv_terminates e -> SN cbv e.
Proof.
  intros.
  destruct H as (v, ?, ?).
  apply clos_rt_rt1n in H0.
  induction H0.
  - rename x into e.
    constructor; intros f ?.
    exfalso.
    eapply cbv_implies_nonvalue with e f; auto.
  - clear H1.
    constructor; intros w ?.
    assert (y = w).
    + apply cbv_is_a_function with x; auto.
    + subst; firstorder.
Qed.

(* -------------------------------------------------------------------------- *)

Fixpoint cbv_type (t: type): pseudoterm :=
  match t with
  | base =>
    CPS.base
  | arrow t s =>
    negation [negation [cbv_type s]; cbv_type t]
  end.

Definition cbv_env (g: env): list pseudoterm :=
  map (fun t => cbv_type t) g.

(* -------------------------------------------------------------------------- *)

(* This should ideally be moved to a new file. Anyway, the naive one-pass CPS
   translation of Danvy and Filinski's that Kennedy describes in his paper is
   given as follows:

     [-]: term -> (var -> pseudoterm) -> pseudoterm

                            +------------+
     [x] K = K(x)          \|/           |
     [\x.e] K = K(f) { f<x, k> = [e] (\z.k<z>) }
     [e1 e2] K = [e1] (\z1.
                   [e2] (\z2.
                    z1<z2, k> { k<v> = K(v) }))
                                  |     /|\
                                  +------+

   As of writing, I'm still not sure how to handle the de Bruijn indexes in here
   correctly. Probably applying a substitution would be a nice way, as we don't
   know in advance how far the variable will be pushed inside a term... can we
   calculate that? Sigh...

   The final version, which avoids the introduction of tail-calls, i.e., (ETA)
   redexes, can be defined by modifying the above with:

     [\x.e] K = K(f) { f<x, k> = (e) k }

   Along with the introduction of an auxiliary definition:

     (-): term -> var -> pseudoterm

     (x) k = k<x>
     (\x.e) k = k<f> { f<x, j> = (e) j }
     (e1 e2) k = [e1] (\z1.[e2] (\z2.z1<z2, k>))

   Ideally, we would like to show that we can get from Plotkin's translation to
   the naive one by performing some jumps, then from the naive one to the final
   one by performing some tail-call eliminations. The combination would lead to
   the result that these translations are adequate and that they give a sound
   denotational semantics for the lambda calculus. *)
