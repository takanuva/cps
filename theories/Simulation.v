(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Observational.

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

(* Full beta reduction relation. *)

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

(* The definitions of call by name and call by value reductions are standard;
   as of this development, they were taken from Plotkin's paper. *)

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

(* The CPS translations are given in Thielecke's dissertation, and are based on
   those of Plotkin's paper as well. We note that both translations receive the
   returning continuation as a parameter, but the translation will always set
   this to be the most recently bound continuation, i.e., the de Bruijn index 0,
   so this parameter is taken implictly in our setting.

   TODO: fix typing on the following! *)

Inductive cbn_cps: lambda_term -> pseudoterm -> Prop :=
  | cbn_cps_bound:
    (* [x](k) = x<k> *)
    forall n: nat,
    (* TODO: assume k is fresh! *)
    cbn_cps n (jump n [bound 0])
  | cbn_cps_abstraction:
    (* [\x.M](k) = k<f> { f<x, h> = [M](h) } *)
    forall t b b',
    cbn_cps (lambda_lift 1 0 b) b' ->
    cbn_cps
      (lambda_abstraction t b)
      (bind
        (jump 1 [bound 0])
        [void; void]
        b')
  | cbn_cps_application:
    (* [M N](k) = [M](m) { m<f> = f<n, k> { n<h> = [N](h) } } *)
    forall f x f' x',
    cbn_cps (lambda_lift 1 0 f) f' ->
    cbn_cps (lambda_lift 2 0 x) x' ->
    cbn_cps
      (lambda_application f x)
      (bind
        f'
        [void]
        (bind
          (jump 1 [bound 2; bound 0])
          [void]
          x')).

Lemma cbn_cps_is_a_function:
  forall e c1,
  cbn_cps e c1 ->
  forall c2,
  cbn_cps e c2 -> c1 = c2.
Proof.
  induction 1; intros.
  - dependent destruction H; auto.
  - dependent destruction H0.
    f_equal; auto.
  - dependent destruction H1.
    f_equal; auto.
    f_equal; auto.
Qed.

Local Hint Resolve cbn_cps_is_a_function: cps.

Lemma cbn_cps_lift:
  forall e c,
  cbn_cps e c ->
  forall i k,
  k > 0 ->
  cbn_cps (lambda_lift i k e) (lift i k c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k n).
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_lt; try lia.
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
    apply IHcbn_cps; lia.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    + rewrite lambda_lift_lift_permutation; try lia.
      apply IHcbn_cps1; lia.
    + rewrite lambda_lift_lift_permutation; try lia.
      replace (k + 1 + 1) with (2 + k); try lia.
      apply IHcbn_cps2; lia.
Qed.

Lemma cbn_cps_is_compositional:
  forall c1 c2,
  [c1 ~~ c2] ->
  forall e1 e2,
  lambda_not_free 0 e1 ->
  lambda_not_free 0 e2 ->
  cbn_cps e1 c1 ->
  cbn_cps e2 c2 ->
  forall (h: lambda_context) c3 c4,
  cbn_cps (h e1) c3 ->
  cbn_cps (h e2) c4 ->
  [c3 ~~ c4].
Proof.
  intros until h.
  (* Do some reordering to help with unification... *)
  move H0 after H2.
  move H1 after H3.
  generalize dependent e2.
  generalize dependent e1.
  generalize dependent c2.
  generalize dependent c1.
  (* We'll do induction on the depth of h, not on h itself. *)
  remember (lambda_context_depth h) as k.
  generalize dependent h.
  induction k using lt_wf_ind; intros.
  dependent destruction Heqk.
  (* There we go. *)
  destruct h; simpl in H.
  (* Case: lambda_context_hole. *)
  - assert (c1 = c3); eauto with cps.
    destruct H7.
    assert (c2 = c4); eauto with cps.
    destruct H7.
    assumption.
  (* Case: lambda_context_abstraction. *)
  - dependent destruction H5.
    dependent destruction H6.
    rewrite lambda_context_lift_is_sound in H5.
    rewrite lambda_context_lift_is_sound in H6.
    rewrite Nat.add_0_r in H5, H6.
    apply barb_bind_right.
    (* We notice that 0 can't be free in e1 or e2, so, if h happens to bind no
       var, so that we have lambda_lift 1 0 e1 in H3 (and ... e2 in H4), those
       may be freely replaced with lambda_lift 1 1, thus fixing what we need. *)
    destruct (lambda_context_bvars h).
    + admit.
    + eapply H with (m := lambda_context_depth (lambda_context_lift 1 0 h)).
      * (* Clearly. *)
        admit.
      * reflexivity.
      * apply barb_lift with (k := S n).
        exact H0.
      * apply cbn_cps_lift; try lia.
        exact H2.
      * (* Clearly. *)
        admit.
      * apply cbn_cps_lift; try lia.
        exact H3.
      * (* Clearly. *)
        admit.
      * exact H5.
      * exact H6.
  (* Case: lambda_context_abstraction_left. *)
  - dependent destruction H5.
    dependent destruction H6.
    assert (x' = x'0); eauto with cps.
    dependent destruction H5.
    apply barb_bind_left.
    admit.
  (* Case: lambda_context_abstraction_right. *)
  - dependent destruction H5.
    dependent destruction H6.
    assert (f' = f'0); eauto with cps.
    dependent destruction H5.
    apply barb_bind_right.
    apply barb_bind_right.
    admit.
Admitted.

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
          (jump 1 [bound 2; bound 0]))).

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

(* Note: if the CPS-calculus properly simulates CBN/CBV reduction, then, by the
   factorization lemma, it's possible to show that we'll reach the desired value
   only by using head redutions! They are enough to simulate the results. *)
