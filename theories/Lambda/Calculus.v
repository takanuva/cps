(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.

Import ListNotations.

Inductive type: Set :=
  | base
  | arrow (a: type) (b: type)
  (* | thunk (a: type) *).

Inductive term: Set :=
  | bound (n: nat)
  | abstraction (t: type) (b: term)
  | application (f: term) (x: term)
  | delay (e: term)
  | force (e: term).

Coercion bound: nat >-> term.

Inductive value: term -> Prop :=
  | value_bound:
    forall n: nat,
    value n
  | value_abstraction:
    forall t b,
    value (abstraction t b)
  | value_delay:
    forall e,
    value (delay e).

Global Hint Constructors value: cps.

(* TODO: I have to fix a naming convention, either "_dec" or "_is_decidable"! *)

Lemma value_dec:
  forall e,
  { value e } + { ~value e }.
Proof.
  induction e.
  - left; auto with cps.
  - left; auto with cps.
  - right; intro.
    inversion H.
  - left; auto with cps.
  - right; intro.
    inversion H.
Qed.

Fixpoint traverse g k e: term :=
  match e with
  | bound n =>
    g k n 
  | abstraction t b =>
    abstraction t (traverse g (S k) b)
  | application f x =>
    application (traverse g k f) (traverse g k x)
  | delay e =>
    delay (traverse g k e)
  | force e =>
    force (traverse g k e)
  end.

Global Instance lambda_dbVar: dbVar term :=
  bound.

Global Instance lambda_dbTraverse: dbTraverse term term :=
  traverse.

Global Instance lambda_dbVarLaws: dbVarLaws term.
Proof.
  split; auto.
Qed.

Global Instance lambda_dbTraverseLaws: dbTraverseLaws term term.
Proof.
  split; unfold Substitution.traverse; intros.
  - generalize dependent k.
    induction x; simpl; auto; intros;
    f_equal; auto.
  - apply (H k (bound n)).
  - generalize dependent j.
    generalize dependent k.
    induction x; simpl; auto; intros;
    try now (f_equal; auto).
    + apply (H 0).
    + f_equal.
      apply IHx; intros.
      replace (l + S k) with (S l + k) by lia.
      replace (l + S j) with (S l + j) by lia.
      apply H.
  - generalize dependent k.
    induction x; simpl; intros; auto;
    f_equal; auto.
Qed.

Lemma bound_var_equality_stuff:
  forall n,
  bound n = var n.
Proof.
  auto.
Qed.

Lemma inst_distributes_over_abstraction:
  forall s t b,
  inst s (abstraction t b) = abstraction t (s 1 b).
Proof.
  auto.
Qed.

Lemma inst_distributes_over_application:
  forall s f x,
  inst s (application f x) = application (inst s f) (inst s x).
Proof.
  auto.
Qed.

Lemma inst_distributes_over_delay:
  forall s e,
  inst s (delay e) = delay (inst s e).
Proof.
  auto.
Qed.

Lemma inst_distributes_over_force:
  forall s e,
  inst s (force e) = force (inst s e).
Proof.
  auto.
Qed.

Global Hint Rewrite bound_var_equality_stuff using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_abstraction using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_application using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_delay using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_force using sigma_solver: sigma.

Lemma lift_zero_e_equals_e:
  forall e k,
  lift 0 k e = e.
Proof.
  intros.
  now sigma.
Qed.

Lemma lift_lift_permutation:
  forall e i j k l,
  k <= l ->
  lift i k (lift j l e) =
    lift j (i + l) (lift i k e).
Proof.
  intros.
  sigma.
  repeat (progress f_equal; try lia).
Qed.

Lemma lift_lift_simplification:
  forall e i j k l,
  k <= l + j ->
  l <= k ->
  lift i k (lift j l e) =
  lift (i + j) l e.
Proof.
  intros.
  sigma.
  repeat (progress f_equal; try lia).
Qed.

Lemma subst_lift_simplification:
  forall e y i p k,
  p <= i + k ->
  k <= p ->
  subst y p (lift (S i) k e) =
  lift i k e.
Proof.
  intros.
  sigma.
  repeat (progress f_equal; try lia).
Qed.

Fixpoint size (e: term): nat :=
  match e with
  | bound n =>
    1
  | abstraction t b =>
    1 + size b
  | application f x =>
    1 + size f + size x
  | delay e =>
    1 + size e
  | force e =>
    1 + size e
  end.

Lemma size_lift:
  forall e i k,
  size (lift i k e) = size e.
Proof.
  sigma.
  induction e; simpl; intros.
  - destruct (le_gt_dec k n); now sigma.
  - sigma; simpl; auto.
  - sigma; simpl; auto.
  - sigma; simpl; auto.
  - sigma; simpl; auto.
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
    subterm x (application f x)
  | subterm_delay:
    forall e,
    subterm e (delay e)
  | subterm_force:
    forall e,
    subterm e (force e).

Global Hint Constructors subterm: cps.

Lemma subterm_is_well_founded:
  forall e,
  Acc subterm e.
Proof.
  induction e.
  - constructor.
    inversion 1.
  - constructor.
    now inversion_clear 1.
  - constructor.
    now inversion_clear 1.
  - constructor.
    now inversion_clear 1.
  - constructor.
    now inversion_clear 1.
Qed.

Inductive context: Set :=
  | context_hole
  | context_abstraction (t: type) (b: context)
  | context_application_left (f: context) (x: term)
  | context_application_right (f: term) (x: context)
  | context_delay (e: context)
  | context_force (e: context).

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
  | context_delay x =>
    delay (apply_context x e)
  | context_force x =>
    force (apply_context x e)
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
  | context_delay e =>
    context_bvars e
  | context_force e =>
    context_bvars e
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
  | context_delay e =>
    1 + context_depth e
  | context_force e =>
    1 + context_depth e
  end.

Fixpoint context_lift i k h: context :=
  match h with
  | context_hole =>
    context_hole
  | context_abstraction t b =>
    context_abstraction t (context_lift i (S k) b)
  | context_application_left f x =>
    context_application_left (context_lift i k f) (lift i k x)
  | context_application_right f x =>
    context_application_right (lift i k f) (context_lift i k x)
  | context_delay e =>
    context_delay (context_lift i k e)
  | context_force e =>
    context_force (context_lift i k e)
  end.

Lemma context_lift_is_sound:
  forall (h: context) i k e,
  lift i k (h e) =
    context_lift i k h (lift i (context_bvars h + k) e).
Proof.
  sigma.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite plus_n_Sm.
    sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
  - sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
  - sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
  - sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
  - sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
Qed.

Lemma context_lift_depth:
  forall h i k,
  context_depth (context_lift i k h) = context_depth h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
Qed.

Lemma context_lift_bvars:
  forall h i k,
  context_bvars (context_lift i k h) = context_bvars h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
Qed.

Fixpoint context_subst y k h: context :=
  match h with
  | context_hole =>
    context_hole
  | context_abstraction t b =>
    context_abstraction t (context_subst y (S k) b)
  | context_application_left f x =>
    context_application_left (context_subst y k f) (subst y k x)
  | context_application_right f x =>
    context_application_right (subst y k f) (context_subst y k x)
  | context_delay e =>
    context_delay (context_subst y k e)
  | context_force e =>
    context_force (context_subst y k e)
  end.

Lemma context_subst_is_sound:
  forall (h: context) y k e,
  subst y k (h e) =
    context_subst y k h (subst y (context_bvars h + k) e).
Proof.
  sigma.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite plus_n_Sm.
    sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
  - sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
  - sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
  - sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
  - sigma; rewrite IHh.
    repeat (progress f_equal; try lia).
Qed.

Lemma context_subst_depth:
  forall h y k,
  context_depth (context_subst y k h) = context_depth h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
Qed.

Lemma context_subst_bvars:
  forall h y k,
  context_bvars (context_subst y k h) = context_bvars h.
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
  - now rewrite IHh.
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
    not_free n (application f x)
  | not_free_delay:
    forall e n,
    not_free n e ->
    not_free n (delay e)
  | not_free_force:
    forall e n,
    not_free n e ->
    not_free n (force e).

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
  sigma.
  induction e; split; sigma; intros.
  - destruct (le_gt_dec j n).
    + dependent destruction H.
      sigma.
      constructor; lia.
    + sigma.
      constructor; lia.
  - (* TODO: we might rewrite this once I make a "sigma in" tactic... *)
    generalize dependent H.
    destruct (le_gt_dec j n).
    + sigma; intros.
      dependent destruction H.
      constructor; lia.
    + sigma; intros.
      constructor; lia.
  - dependent destruction H.
    constructor.
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
    constructor.
    + now apply IHe1.
    + now apply IHe2.
  - dependent destruction H.
    constructor.
    + now apply IHe1 with k.
    + now apply IHe2 with k.
  - dependent destruction H.
    constructor.
    now apply IHe.
  - dependent destruction H.
    constructor.
    now apply IHe with k.
  - dependent destruction H.
    constructor.
    now apply IHe.
  - dependent destruction H.
    constructor.
    now apply IHe with k.
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

Lemma lifting_more_than_n_makes_not_free_n:
  forall e i k n,
  n >= k ->
  n < k + i ->
  not_free n (lift i k e).
Proof.
  sigma.
  induction e; intros.
  - destruct (le_gt_dec k n).
    + sigma; constructor; lia.
    + sigma; constructor; lia.
  - sigma; constructor.
    apply IHe; lia.
  - sigma; constructor.
    + apply IHe1; lia.
    + apply IHe2; lia.
  - sigma; constructor.
    apply IHe; lia.
  - sigma; constructor.
    apply IHe; lia.
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
    free_count (i + j) n (application f x)
  | free_count_delay:
    forall i e n,
    free_count i n e ->
    free_count i n (delay e)
  | free_count_force:
    forall i e n,
    free_count i n e ->
    free_count i n (force e).

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
    + replace 0 with (0 + 0) by auto.
      now constructor.
    + now constructor.
  - dependent induction H.
    + now constructor.
    + constructor.
      now apply IHfree_count.
    + assert (i = 0) by lia; subst.
      assert (j = 0) by lia; subst.
      constructor.
      * now apply IHfree_count1.
      * now apply IHfree_count2.
    + constructor; auto.
    + constructor; auto.
Qed.

Lemma free_count_is_decidable:
  forall e n,
  { k & free_count k n e }.
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
  + destruct IHe with n as (k, ?).
    exists k; now constructor.
  + destruct IHe with n as (k, ?).
    exists k; now constructor.
Qed.

Lemma free_usage:
  forall e k n,
  free_count k n e ->
  k > 0 ->
  exists h: context,
  e = h (context_bvars h + n).
Proof.
  induction 1; intros.
  - exists context_hole.
    now simpl.
  - exfalso.
    inversion H0.
  - destruct IHfree_count as (h, ?); auto; subst.
    exists (context_abstraction t h).
    simpl; do 3 f_equal.
    lia.
  - destruct i.
    + simpl in H1.
      destruct IHfree_count2 as (h, ?); auto; subst.
      exists (context_application_right f h).
      now simpl.
    + clear H1.
      destruct IHfree_count1 as (h, ?); auto with arith; subst.
      exists (context_application_left h x).
      now simpl.
  - destruct IHfree_count as (h, ?); auto; subst.
    exists (context_delay h); now simpl.
  - destruct IHfree_count as (h, ?); auto; subst.
    exists (context_force h); now simpl.
Qed.

Lemma subst_linear_substitution:
  forall (h: context) y k,
  subst y k (h (k + context_bvars h)) =
  subst y k (h (lift (1 + k + context_bvars h) 0 y)).
Proof.
  sigma.
  induction h; intros.
  - rewrite Nat.add_0_r.
    destruct (lt_eq_lt_dec k k) as [ [ ? | _ ] | ? ].
    + exfalso; lia.
    + simpl; sigma.
      repeat (progress f_equal; try lia).
    + exfalso; lia.
  - replace (k + S (context_bvars h)) with (S k + (context_bvars h)) by lia.
    simpl; sigma.
    now rewrite IHh.
  - simpl; sigma.
    now rewrite IHh.
  - simpl; sigma.
    now rewrite IHh.
  - simpl; sigma.
    now rewrite IHh.
  - simpl; sigma.
    now rewrite IHh.
Qed.

Lemma free_usage_isnt_zero:
  forall (h: context) k,
  ~free_count 0 k (h (k + context_bvars h)).
Proof.
  induction h; simpl; intros k ?.
  - dependent destruction H.
    lia.
  - dependent destruction H.
    apply IHh with (S n); simpl.
    now rewrite plus_n_Sm.
  - dependent destruction H.
    assert (i = 0) by lia; subst.
    now apply IHh with n.
  - dependent destruction H.
    assert (j = 0) by lia; subst.
    now apply IHh with n.
  - dependent destruction H.
    now apply IHh with n.
  - dependent destruction H.
    now apply IHh with n.
Qed.

Lemma free_count_linear_substitution:
  forall (h: context) n k e,
  free_count (1 + n) k (h (k + context_bvars h)) ->
  free_count n k (h (lift (1 + k + context_bvars h) 0 e)).
Proof.
  induction h; simpl; intros.
  - rewrite Nat.add_0_r in H |- *.
    dependent destruction H.
    apply not_free_count_zero_iff.
    rename n0 into k.
    apply lifting_more_than_n_makes_not_free_n; lia.
  - dependent destruction H; constructor.
    rename n0 into k.
    replace (k + S (context_bvars h)) with
      (S k + context_bvars h) in H |- * by lia.
    now apply IHh.
  - dependent destruction H.
    rename n0 into k.
    destruct i.
    + exfalso.
      eapply free_usage_isnt_zero; eauto.
    + replace n with (i + j) by lia.
      constructor; auto;
      now apply IHh.
  - dependent destruction H.
    rename n0 into k.
    destruct j.
    + exfalso.
      eapply free_usage_isnt_zero; eauto.
    + replace n with (i + j) by lia.
      constructor; auto;
      now apply IHh.
  - dependent destruction H.
    rename n0 into k.
    constructor.
    now apply IHh.
  - dependent destruction H.
    rename n0 into k.
    constructor.
    now apply IHh.
Qed.

(* Full beta reduction relation. Note that we do not consider eta because it is
   not justified by Plotkin's CBN translation, which captures the observational
   equivalence for the intensional lambda calculus, where eta does not hold. As
   an example, note that \x.e x has halted, it is a value, even if e contains
   any redexes in it. *)

Inductive full: relation term :=
  (* TODO: thunks. *)
  | full_beta:
    forall t b x,
    full
      (application (abstraction t b) x)
      (subst x 0 b)
  | full_abstraction:
    forall t b1 b2,
    full b1 b2 ->
    full (abstraction t b1) (abstraction t b2)
  | full_application_left:
    forall f1 f2 x,
    full f1 f2 ->
    full (application f1 x) (application f2 x)
  | full_application_right:
    forall f x1 x2,
    full x1 x2 ->
    full (application f x1) (application f x2)
  | full_delay:
    forall e1 e2,
    full e1 e2 ->
    full (delay e1) (delay e2)
  | full_force:
    forall e1 e2,
    full e1 e2 ->
    full (force e1) (force e2).

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
      now apply n with b2.
    + right; intros ?.
      apply n; intros b ?.
      apply H with (abstraction t b).
      now apply full_abstraction.
  - destruct IHe1.
    + destruct IHe2.
      * destruct e1.
        (* TODO: refactor me, please. *)
        --- left; intros b ?.
            dependent destruction H.
            +++ inversion H.
            +++ now apply n0 with x2.
        --- right; intro.
            apply H with (subst e2 0 e1).
            apply full_beta.
        --- left; intros b ?.
            dependent destruction H.
            +++ now apply n with f2.
            +++ now apply n0 with x2.
        --- left; intros b ?.
            dependent destruction H.
            +++ now apply n with f2.
            +++ now apply n0 with x2.
        --- left; intros b ?.
            dependent destruction H.
            +++ now apply n with f2.
            +++ now apply n0 with x2.
      * clear n; rename n0 into n; right.
        repeat intro; apply n; intros e3 ?.
        apply H with (application e1 e3).
        now apply full_application_right.
    + clear IHe2; right.
      repeat intro; apply n; intros e3 ?.
      apply H with (application e3 e2).
      now apply full_application_left.
  - destruct IHe.
    + left; repeat intro.
      dependent destruction H.
      now apply n with e2.
    + right; repeat intro.
      apply n; repeat intro.
      apply H with (delay b).
      now apply full_delay.
  - destruct IHe.
    + left; repeat intro.
      dependent destruction H.
      now apply n with e2.
    + right; repeat intro.
      apply n; repeat intro.
      apply H with (force b).
      now apply full_force.
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
    + left; inversion_clear 1.
      inversion H0.
    + left; inversion_clear 1.
      inversion H0.
  - left; inversion_clear 1.
  - left; inversion_clear 1.
Qed.

Definition whnf: term -> Prop :=
  normal whr.

Lemma whnf_application_left:
  forall f x,
  whnf (application f x) ->
  whnf f.
Proof.
  intros f1 f3 ? f2 ?.
  apply H with (application f2 f3).
  now constructor.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive compatible (R: relation term): relation term :=
  | compatible_step:
    forall e f,
    R e f -> compatible R e f
  | compatible_abstraction:
    forall t b1 b2,
    compatible R b1 b2 ->
    compatible R (abstraction t b1) (abstraction t b2)
  | compatible_application_left:
    forall f1 f2 x,
    compatible R f1 f2 ->
    compatible R (application f1 x) (application f2 x)
  | compatible_application_right:
    forall f x1 x2,
    compatible R x1 x2 ->
    compatible R (application f x1) (application f x2)
  | compatible_delay:
    forall e1 e2,
    compatible R e1 e2 ->
    compatible R (delay e1) (delay e2)
  | compatible_force:
    forall e1 e2,
    compatible R e1 e2 ->
    compatible R (force e1) (force e2).

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
