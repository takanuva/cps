(******************************************************************************)
(* Copyright (c) Paulo Torrens.                                               *)
(* Licensed under the New BSD license.                                        *)
(******************************************************************************)
(** * The Simply Typed CPS Calculus *)

Require Import List.
Require Import Arith.
Require Import Omega.
Require Import Setoid.
Require Import Equality.
Require Import Morphisms.
Require Import Relations.

Module STCC.
Import ListNotations.

(** ** Syntax

    Inspired by the lambda cube, we use [type] and [prop] as our universes, and
    we keep [base] as our only base type. We also use [void] as the type of
    commands, though it won't appear on any actual terms. As standard, we use de
    Bruijn indexes on the [bound] constructor for variables. Types are simple;
    our only type constructor is [negation], a polyadic type which represents
    the negation of an N-tuple of types.

    The commands in our language are either a [jump], written as [k<x, ...>], or
    a [bind], written as [b { k<x: t, ...> = c }]. *)

Inductive pseudoterm: Set :=
  | type
  | prop
  | base
  | void
  | bound (n: nat)
  | negation (ts: list pseudoterm)
  | jump (f: pseudoterm) (xs: list pseudoterm)
  | bind (b: pseudoterm) (ts: list pseudoterm) (c: pseudoterm).

Coercion bound: nat >-> pseudoterm.

(** As we have lists inside our pseudoterms, we'll need a stronger induction
    principle for it, stating that propositions are kept inside those lists. *)

Definition pseudoterm_deepind:
  forall P: pseudoterm -> Prop,
  forall f1: P type,
  forall f2: P prop,
  forall f3: P base,
  forall f4: P void,
  forall f5: (forall n, P (bound n)),
  forall f6: (forall ts, Forall P ts -> P (negation ts)),
  forall f7: (forall f xs, P f -> Forall P xs -> P (jump f xs)),
  forall f8: (forall b ts c, P b -> Forall P ts -> P c -> P (bind b ts c)),
  forall e, P e.
Proof.
  do 9 intro; fix H 1.
  destruct e.
  (* Case: type. *)
  - apply f1.
  (* Case: prop. *)
  - apply f2.
  (* Case: base. *)
  - apply f3.
  (* Case: void. *)
  - apply f4.
  (* Case: bound. *)
  - apply f5.
  (* Case: negation. *)
  - apply f6.
    induction ts; auto.
  (* Case: jump. *)
  - apply f7; auto.
    induction xs; auto.
  (* Case: bind. *)
  - apply f8; auto.
    induction ts; auto.
Defined.

(** A lot of proofs on pseudoterm lists may be solved by simple induction on the
    [Forall P] proposition over them, so we'll add a tactic for that. *)

Tactic Notation "list" "induction" "over" hyp(H) :=
  induction H; simpl;
  [ reflexivity
  | f_equal; auto ].

(** We will be using a single inductive type to represent pseudoterms in order
    to facilitate the proofs; actual terms will be split into a few syntactic
    classes (namely: kinds, types, values and commands), giving a somewhat more
    elegant formalization. Later on we'd like to show that any typed pseudoterms
    will actually respect these syntactic classes. *)

Inductive kind_class: pseudoterm -> Prop :=
  | prop_is_a_kind:
    kind_class prop.

Inductive type_class: pseudoterm -> Prop :=
  | base_is_a_type:
    type_class base
  | negation_is_a_type:
    forall ts,
    Forall type_class ts -> type_class (negation ts).

Inductive value_class: pseudoterm -> Prop :=
  | bound_is_a_value:
    forall n: nat,
    value_class n.

Inductive command_class: pseudoterm -> Prop :=
  | jump_is_a_command:
    forall k xs,
    value_class k -> Forall value_class xs ->
    command_class (jump k xs)
  | bind_is_a_command:
    forall b ts c,
    command_class b -> Forall type_class ts -> command_class c ->
    command_class (bind b ts c).

(** *)

Inductive subterm: relation pseudoterm :=
  | subterm_bind_left:
    forall b ts c,
    subterm b (bind b ts c)
  | subterm_bind_right:
    forall b ts c,
    subterm c (bind b ts c).

Hint Constructors subterm: cps.

(** ** Lifting

    As we're dealing with de Bruijn indexes, we need a notion of lifting in our
    calculus. On the simply typed CPS calculus, most lifing is standard and
    straightforward, with the notable exception of the binding operation. On a
    term of the form [b { k<x: t, ...> = c }], we need to bind the continuation
    [k] on the [b] term, and we need to bind [N] variables on the [c] term. *)

Fixpoint lift (i: nat) (k: nat) (e: pseudoterm): pseudoterm :=
  match e with
  | type =>
    type
  | prop =>
    prop
  | base =>
    base
  | void =>
    void
  | bound n =>
    if le_gt_dec k n then
      bound (i + n)
    else
      bound n
  | negation ts =>
    negation (map (lift i k) ts)
  | jump f xs =>
    jump (lift i k f) (map (lift i k) xs)
  | bind b ts c =>
    bind (lift i (S k) b) (map (lift i k) ts) (lift i (k + length ts) c)
  end.

Lemma lift_zero_e_equals_e:
  forall e k,
  lift 0 k e = e.
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type.*)
  - reflexivity.
  (* Case: prop.*)
  - reflexivity.
  (* Case: base.*)
  - reflexivity.
  (* Case: void.*)
  - reflexivity.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec k n); reflexivity.
  (* Case: negation. *)
  - simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - simpl; f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - simpl; f_equal; auto.
    list induction over H.
Qed.

Lemma lift_bound_ge:
  forall i k n,
  k <= n -> lift i k n = i + n.
Proof.
  intros; simpl.
  destruct (le_gt_dec k n).
  (* Case: k <= n. *)
  - reflexivity.
  (* Case: k > n. *)
  - absurd (k <= n); auto with arith.
Qed.

Lemma lift_bound_lt:
  forall i k n,
  k > n -> lift i k n = n.
Proof.
  intros; simpl.
  destruct (le_gt_dec k n).
  (* Case: k <= n. *)
  - absurd (k <= n); auto with arith.
  (* Case: k > n. *)
  - reflexivity.
Qed.

Lemma lift_i_lift_j_equals_lift_i_plus_j:
  forall e i j k,
  lift i k (lift j k e) = lift (i + j) k e.
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto with arith; omega.
    + rewrite lift_bound_lt; auto.
  (* Case: negation. *)
  - simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - simpl; f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - simpl; f_equal.
    + apply IHe1.
    + list induction over H.
    + rewrite map_length; apply IHe2.
Qed.

Hint Resolve lift_i_lift_j_equals_lift_i_plus_j: cps.

Lemma lift_succ_n_equals_lift_1_lift_n:
  forall n k e,
  lift (S n) k e = lift 1 k (lift n k e).
Proof.
  intros.
  replace (S n) with (1 + n); auto.
  rewrite lift_i_lift_j_equals_lift_i_plus_j; auto.
Qed.

Hint Resolve lift_succ_n_equals_lift_1_lift_n: cps.

Lemma lift_lift_simplification:
  forall e i j k l,
  k <= l + j -> l <= k -> lift i k (lift j l e) = lift (i + j) l e.
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec l n).
    + rewrite lift_bound_ge; auto with arith; omega.
    + rewrite lift_bound_lt; eauto with arith.
  (* Case: negation. *)
  - simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - simpl; f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - simpl; f_equal.
    + rewrite IHe1; auto; omega.
    + list induction over H.
    + rewrite map_length.
      rewrite IHe2; auto; omega.
Qed.

Lemma lift_lift_permutation:
  forall e i j k l,
  k <= l -> lift i k (lift j l e) = lift j (i + l) (lift i k e).
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec l n); destruct (le_gt_dec k n); intros.
    + rewrite lift_bound_ge.
      * rewrite lift_bound_ge; auto with arith.
        do 2 elim plus_assoc_reverse; auto with arith.
      * omega.
    + absurd (k <= n); eauto with arith.
    + rewrite lift_bound_ge; auto.
      rewrite lift_bound_lt; auto.
      auto with arith.
    + rewrite lift_bound_lt; auto.
      rewrite lift_bound_lt; auto.
      eauto with arith.
  (* Case: negation. *)
  - simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - simpl; f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - simpl; f_equal.
    + rewrite IHe1; auto with arith.
      replace (i + S l) with (S (i + l)); auto with arith.
    + list induction over H.
    + do 2 rewrite map_length.
      rewrite IHe2; auto with arith.
      replace (i + (l + length ts)) with (i + l + length ts); auto with arith.
Qed.

(** ** Substitution *)

Fixpoint subst (p: pseudoterm) (k: nat) (q: pseudoterm): pseudoterm :=
  match q with
  | type =>
    type
  | prop =>
    prop
  | base =>
    base
  | void =>
    void
  | bound n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => bound (pred n)
    | inleft (right _) => lift k 0 p
    | inright _ => bound n
    end
  | negation ts =>
    negation (map (subst p k) ts)
  | jump f xs =>
    jump (subst p k f) (map (subst p k) xs)
  | bind b ts c =>
    bind (subst p (S k) b) (map (subst p k) ts) (subst p (k + length ts) c)
  end.

Lemma subst_bound_gt:
  forall e k n,
  n > k -> subst e k n = pred n.
Proof.
  intros; simpl.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  - reflexivity.
  - elim gt_irrefl with k; congruence.
  - absurd (k <= n); auto with arith.
Qed.

Lemma subst_bound_eq:
  forall e k n,
  n = k -> subst e k n = lift n 0 e.
Proof.
  destruct 1; simpl.
  destruct (lt_eq_lt_dec n n) as [ [ ? | ? ] | ? ].
  - destruct (gt_irrefl n); auto.
  - reflexivity.
  - destruct (lt_irrefl n); auto.
Qed.

Lemma subst_bound_lt:
  forall e k n,
  n < k -> subst e k n = n.
Proof.
  intros; simpl.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  - absurd (k <= n); auto with arith.
  - elim lt_irrefl with k; congruence.
  - reflexivity.
Qed.

Lemma lift_addition_distributes_over_subst:
  forall a b i p k,
  lift i (p + k) (subst b p a) = subst (lift i k b) p (lift i (S (p + k)) a).
Proof.
  induction a using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - unfold subst at 1.
    destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct n.
      inversion l.
      unfold lift at 1, pred.
      destruct (le_gt_dec (p + k) n).
      * rewrite lift_bound_ge; auto with arith.
        rewrite subst_bound_gt; eauto with arith.
        replace (i + S n) with (S (i + n)); auto.
      * rewrite lift_bound_lt; auto with arith.
        rewrite subst_bound_gt; auto with arith.
    + destruct e.
      elim lift_lift_permutation; auto with arith.
      rewrite lift_bound_lt; auto with arith.
      rewrite subst_bound_eq; auto with arith.
    + rewrite lift_bound_lt; auto with arith.
      rewrite lift_bound_lt; auto with arith.
      rewrite subst_bound_lt; auto.
  (* Case: negation. *)
  - simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - simpl; f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - simpl; f_equal.
    + replace (S (p + k)) with (S p + k); auto.
    + list induction over H.
    + do 2 rewrite map_length.
      replace (p + k + length ts) with ((p + length ts) + k); auto.
      omega.
Qed.

Lemma lift_distributes_over_subst:
  forall a b i k,
  lift i k (subst b 0 a) = subst (lift i k b) 0 (lift i (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply lift_addition_distributes_over_subst.
Qed.

Lemma subst_lift_simplification:
   forall a b i p k,
   p <= i + k ->
   k <= p -> subst b p (lift (S i) k a) = lift i k a.
Proof.
  induction a using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec k n).
    + rewrite subst_bound_gt; auto; omega.
    + rewrite subst_bound_lt; auto; omega.
  (* Case: negation. *)
  - simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - simpl; f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - simpl; f_equal.
    + apply IHa1; omega.
    + list induction over H.
    + rewrite map_length.
      apply IHa2; omega.
Qed.

Lemma lift_and_subst_commute:
  forall a b i p k,
  k <= p ->
  lift i k (subst b p a) = subst b (i + p) (lift i k a).
Proof.
  induction a using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - simpl.
    destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ]; simpl.
    + destruct (le_gt_dec k n).
      * rewrite subst_bound_gt; eauto with arith.
        destruct (le_gt_dec k (pred n)).
        inversion l.
        replace (i + S p) with (S (i + p)); auto.
        replace (i + S m) with (S (i + m)); auto.
        absurd (k < n); omega.
      * absurd (n > p); eauto with arith.
    + destruct (le_gt_dec k n).
      * rewrite subst_bound_eq; auto.
        rewrite lift_lift_simplification; auto with arith.
        congruence.
      * destruct e.
        absurd (k > p); auto with arith.
    + destruct (le_gt_dec k n).
      * rewrite subst_bound_lt; auto with arith.
      * rewrite subst_bound_lt; eauto with arith.
  (* Case: negation. *)
  - simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - simpl; f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - simpl; f_equal.
    + replace (S (i + p)) with (i + S p); auto with arith.
    + list induction over H.
    + do 2 rewrite map_length.
      replace (i + p + length ts) with (i + (p + length ts)); auto with arith.
Qed.

Hint Resolve lift_and_subst_commute: cps.

Lemma subst_addition_distributes_over_itself:
  forall a b c p k,
  subst c (p + k) (subst b p a) = subst (subst c k b) p (subst c (S (p + k)) a).
Proof.
  induction a using pseudoterm_deepind; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - unfold subst at 2.
    destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct n.
      inversion l.
      unfold pred, subst at 1.
      destruct (lt_eq_lt_dec (p + k) n) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_gt; auto with arith.
        rewrite subst_bound_gt; eauto with arith.
      * rewrite e; clear e.
        rewrite subst_bound_eq; auto.
        rewrite subst_lift_simplification; auto with arith.
      * rewrite subst_bound_lt; eauto with arith.
        rewrite subst_bound_gt; eauto with arith.
    + destruct e.
      rewrite subst_bound_lt; auto with arith.
      rewrite subst_bound_eq; auto.
      rewrite lift_and_subst_commute; auto with arith.
    + rewrite subst_bound_lt; auto with arith.
      rewrite subst_bound_lt; auto with arith.
      rewrite subst_bound_lt; auto with arith.
  (* Case: negation. *)
  - simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - simpl; f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - simpl; f_equal.
    + replace (S (p + k)) with (S p + k); auto.
    + list induction over H.
    + do 2 rewrite map_length.
      replace (p + k + length ts) with (p + length ts + k); auto.
      omega.
Qed.

Lemma subst_distributes_over_itself:
  forall a b c k,
  subst c k (subst b 0 a) = subst (subst c k b) 0 (subst c (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply subst_addition_distributes_over_itself.
Qed.

(** *)

Inductive not_free_in: nat -> pseudoterm -> Prop :=
  | not_free_type:
    forall n,
    not_free_in n type
  | not_free_prop:
    forall n,
    not_free_in n prop
  | not_free_base:
    forall n,
    not_free_in n base
  | not_free_void:
    forall n,
    not_free_in n void
  | not_free_bound:
    forall n m,
    n <> m -> not_free_in n m
  | not_free_negation:
    forall n ts,
    Forall (not_free_in n) ts ->
    not_free_in n (negation ts)
  | not_free_jump:
    forall n x,
    not_free_in n x ->
    forall ts,
    Forall (not_free_in n) ts -> not_free_in n (jump x ts)
  | not_free_bind:
    forall n b,
    not_free_in (S n) b ->
    forall ts,
    Forall (not_free_in n) ts ->
    forall c,
    not_free_in (n + length ts) c ->
    not_free_in n (bind b ts c).

Hint Constructors not_free_in: cps.

Lemma lifting_over_n_preserves_not_free_in_n:
  forall e n,
  not_free_in n e ->
  forall i k,
  k > n -> not_free_in n (lift i k e).
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - assumption.
  (* Case: prop. *)
  - assumption.
  (* Case: base. *)
  - assumption.
  (* Case: void. *)
  - assumption.
  (* Case: bound. *)
  - rename n0 into m; simpl.
    destruct (le_gt_dec k n).
    + constructor.
      omega.
    + assumption.
  (* Case: negation. *)
  - simpl; constructor.
    dependent induction H.
    + simpl; constructor.
    + inversion_clear H1.
      inversion_clear H3.
      simpl; auto with cps.
  (* Case: jump. *)
  - inversion_clear H0.
    simpl; constructor; auto.
    dependent induction H; auto.
    inversion_clear H3.
    simpl; auto.
  (* Case: bind. *)
  - inversion_clear H0.
    simpl; constructor.
    + apply IHe1; auto.
      omega.
    + clear e1 e2 IHe1 IHe2 H2 H4.
      dependent induction H; auto.
      inversion_clear H3.
      simpl; constructor; auto.
    + rewrite map_length.
      apply IHe2; auto.
      omega.
Qed.

(******************************************************************************)
(* TODO: proofs are starting to get a bit more complicated after this point,  *)
(* so add a few comments and documentation before I forget what I'm doing.    *)
(******************************************************************************)

(** *)

Fixpoint apply_parameters (xs: list pseudoterm) (k: nat) (c: pseudoterm) :=
  match xs with
  | nil => lift 1 k c
  | cons x xs => subst (lift k 0 x) 0 (apply_parameters xs (S k) c)
  end.

Hint Unfold apply_parameters: cps.

Definition switch_bindings e: pseudoterm :=
  subst 1 0 (lift 1 2 e).

Hint Unfold switch_bindings: cps.

Fixpoint sequence n :=
  match n with
  | 0 => nil
  | S m => cons (bound n) (sequence m)
  end.

Hint Unfold sequence: cps.

Definition right_cycle (n: nat) e :=
  apply_parameters (cons (bound 0) (sequence n)) 0 (lift n (S n) e).

Hint Unfold right_cycle: cps.

Fixpoint nat_fold {T} n (f: T -> T) e :=
  match n with
  | 0 => e
  | S m => f (nat_fold m f e)
  end.

Hint Unfold nat_fold: cps.

Definition remove_closest_binding e :=
  subst 0 0 e.

Lemma lift_distributes_over_apply_parameters_at_any_depth:
  forall i xs k c n,
  lift i (n + S k) (apply_parameters xs n c) =
    apply_parameters (map (lift i (S k)) xs) n
      (lift i (n + k + length xs) c).
Proof.
  induction xs; intros; simpl.
  (* Case: nil. *)
  - replace (n + k + 0) with (n + k); auto.
    rewrite lift_lift_permutation with (k := n).
    + replace (1 + (n + k)) with (n + S k); auto.
    + omega.
  (* Case: cons. *)
  - replace (n + S k) with (0 + (n + S k)); auto.
    rewrite lift_addition_distributes_over_subst.
    simpl; f_equal.
    + rewrite lift_lift_permutation with (k := 0).
      * reflexivity.
      * omega.
    + replace (S (n + S k)) with (S n + S k); auto.
      rewrite IHxs.
      replace (n + k + S (length xs)) with (S n + k + length xs).
      * reflexivity.
      * omega.
Qed.

Lemma lift_distributes_over_apply_parameters:
  forall i xs k c,
  lift i (S k) (apply_parameters xs 0 c) =
    apply_parameters (map (lift i (S k)) xs) 0 (lift i (k + length xs) c).
Proof.
  intros.
  apply lift_distributes_over_apply_parameters_at_any_depth with (n := 0).
Qed.

Lemma subst_distributes_over_apply_parameters_at_any_depth:
  forall i xs k c n,
  subst i (n + S k) (apply_parameters xs n c) =
    apply_parameters (map (subst i (S k)) xs) n
      (subst i (n + k + length xs) c).
Proof.
  induction xs; intros; simpl.
  (* Case: nil. *)
  - replace (n + k + 0) with (n + k); auto.
    rewrite lift_and_subst_commute.
    + simpl.
      replace (S (n + k)) with (n + S k); auto.
    + omega.
  (* Case: cons. *)
  - rewrite subst_distributes_over_itself.
    f_equal.
    + rewrite lift_and_subst_commute.
      * reflexivity.
      * omega.
    + replace (S (n + S k)) with (S n + S k); auto.
      rewrite IHxs.
      replace (n + k + S (length xs)) with (S n + k + length xs).
      * reflexivity.
      * omega.
Qed.

Lemma subst_distributes_over_apply_parameters:
  forall i xs k c,
  subst i (S k) (apply_parameters xs 0 c) =
    apply_parameters (map (subst i (S k)) xs) 0
      (subst i (k + length xs) c).
Proof.
  intros.
  apply subst_distributes_over_apply_parameters_at_any_depth with (n := 0).
Qed.

Lemma switch_bindings_at_any_depth:
  forall e n,
  subst 1 n (lift 1 (2 + n) e) = subst 0 n (subst 2 n (lift 2 (2 + n) e)).
Proof.
  simpl; induction e using pseudoterm_deepind; intro m.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - unfold lift.
    destruct (le_gt_dec (S (S m)) n).
    + unfold subst at 1 3.
      destruct (lt_eq_lt_dec m (1 + n)) as [ [ ? | ? ] | ? ];
        destruct (lt_eq_lt_dec m (2 + n)) as [ [ ? | ? ] | ? ];
          simpl; try (exfalso; omega).
      destruct (lt_eq_lt_dec m (S n)) as [ [ ? | ? ] | ? ];
        simpl; try (exfalso; omega).
      reflexivity.
    + unfold subst at 1 3.
      destruct (lt_eq_lt_dec m n) as [ [ ? | ? ] | ? ]; simpl.
      * destruct (lt_eq_lt_dec m (pred n)) as [ [ ? | ? ] | ? ];
          simpl; try (exfalso; omega).
        replace (m + 0) with m; auto.
      * destruct (lt_eq_lt_dec m (m + 2)) as [ [ ? | ? ] | ? ];
          simpl; try (exfalso; omega).
        replace (m + 1) with (1 + m); auto with arith.
        replace (m + 2) with (2 + m); auto with arith.
      * destruct (lt_eq_lt_dec m n) as [ [ ? | ? ] | ? ];
          simpl; try (exfalso; omega).
        reflexivity.
  (* Case: negation. *)
  - intros; simpl; f_equal.
    list induction over H.
  (* Case: jump. *)
  - intros; simpl; f_equal.
    + apply IHe.
    + list induction over H.
  (* Case: bind. *)
  - intros; simpl; f_equal.
    + apply IHe1.
    + list induction over H.
    + do 3 rewrite map_length.
      apply IHe2.
Qed.

Lemma switch_bindings_behavior:
  forall e,
  switch_bindings e = right_cycle 1 e.
Proof.
  intro.
  unfold switch_bindings.
  unfold right_cycle; simpl.
  rewrite lift_lift_simplification; auto with arith.
  apply switch_bindings_at_any_depth.
Qed.

Lemma apply_parameters_sequence_equals_nat_fold:
  forall e n m,
  apply_parameters (sequence n) (S m) (lift (m + n) (S m + n) e) =
    nat_fold n (subst (S m + n) 0) (lift (S m + n) (S m + n) e).
Proof.
  induction n; intros; simpl.
  (* Case: zero. *)
  - replace (m + 0) with m; auto.
    rewrite lift_lift_simplification; auto with arith.
  (* Case: succ. *)
  - f_equal.
    replace (S m + S n) with (S (S m) + n).
    + replace (m + S n) with (S m + n).
      * apply IHn.
      * omega.
    + omega.
Qed.

Lemma right_cycle_behavior:
  forall n e,
  right_cycle n e =
    subst 0 0 (nat_fold n (subst (S n) 0) (lift (S n) (S n) e)).
Proof.
  intros.
  unfold right_cycle.
  unfold apply_parameters; fold apply_parameters.
  rewrite lift_zero_e_equals_e; f_equal.
  apply apply_parameters_sequence_equals_nat_fold.
Qed.

Lemma subst_removes_abstraction_if_not_free:
  forall e i k p x,
  not_free_in p e ->
  lift i (p + k) (subst x p e) = subst x p (lift i (p + S k) e).
Proof.
  induction e using pseudoterm_deepind; simpl; intros.
  (* Case: type. *)
  - reflexivity.
  (* Case: prop. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: void. *)
  - reflexivity.
  (* Case: bound. *)
  - destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct (le_gt_dec (p + S k)); simpl.
      * destruct (le_gt_dec (p + k) (pred n));
          try (exfalso; omega).
        destruct (lt_eq_lt_dec p (i + n)) as [ [ ? | ? ] | ? ];
          try (exfalso; omega).
        (* If n is zero this equation won't be correct, but we'll have an absurd
           assumption then, so that's ok. Otherwise we can rewrite the term
           below so that it is indeed correct. *)
        destruct n;
          try (exfalso; omega).
        replace (i + S n) with (S (i + n)); auto.
      * destruct (le_gt_dec (p + k) (pred n)); simpl;
          try (exfalso; omega).
        destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ];
          try (exfalso; omega).
        reflexivity.
    + absurd (p = n).
      * inversion H; assumption.
      * assumption.
    + destruct (le_gt_dec (p + S k) n); try omega; simpl.
      destruct (le_gt_dec (p + k) n); simpl;
        try (exfalso; omega).
      destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ];
        try (exfalso; omega).
      reflexivity.
  (* Case: negation. *)
  - inversion_clear H0; f_equal.
    dependent induction H; simpl.
    + reflexivity.
    + inversion_clear H1.
      f_equal; auto.
  (* Case: jump. *)
  - inversion_clear H0.
    simpl; f_equal; auto.
    dependent induction H; simpl.
    + reflexivity.
    + inversion_clear H2.
      f_equal; auto.
  (* Case: bind. *)
  - inversion_clear H0.
    simpl; f_equal.
    + replace (S (p + k)) with (S p + k); auto.
      replace (S (p + S k)) with (S p + S k); auto.
    + clear IHe1 IHe2 H1 H3.
      dependent induction H; simpl.
      * reflexivity.
      * inversion_clear H2.
        f_equal; auto.
    + do 2 rewrite map_length.
      replace (p + k + length ts) with (p + length ts + k); try omega.
      replace (p + S k + length ts) with (p + length ts + S k); try omega.
      auto.
Qed.

Lemma remove_closest_binding_and_lift_commute:
  forall e i k,
  not_free_in 0 e ->
  lift i k (remove_closest_binding e) = remove_closest_binding (lift i (S k) e).
Proof.
  intros.
  apply subst_removes_abstraction_if_not_free with (p := 0).
  assumption.
Qed.

Lemma sequence_succ:
  forall n,
  sequence (S n) = bound (S n) :: sequence n.
Proof.
  reflexivity.
Qed.

Lemma lifting_over_n_doesnt_change_sequence_n:
  forall n i k,
  map (lift i (S (n + k))) (sequence n) = sequence n.
Proof.
  induction n; intros.
  (* Case: zero. *)
  - reflexivity.
  (* Case: succ. *)
  - rewrite sequence_succ.
    rewrite map_cons.
    f_equal.
    + rewrite lift_bound_lt; auto.
      omega.
    + replace (S n + k) with (n + S k); auto.
      omega.
Qed.

Lemma length_sequence:
  forall n,
  length (sequence n) = n.
Proof.
  induction n; simpl; auto.
Qed.

(** ** Structural congruence *)

(*
  For (DISTR):

  \j.\x.\y.\z.                       \j.\x.\y.\z.
    h@1<x@4, k@0, y@3>                 h@0<x@4, k@1, y@3>
    { k<a, b> =                        { h<c, d, e> =
        h@2<a@1, j@6, b@0> }    ~=~        d@1<z@4, e@0> }
    { h<c, d, e> =                     { k<a, b> =
        d@1<z@3, e@0> }                    h@0<a@2, j@6, b@1>
                                           { h<c, d, e> =
                                               d@1<z@5, e@0> } }

  That's an annoying reduction to do... let's see...
*)

Definition distr b ms m ns n: pseudoterm :=
  (bind (bind
    (switch_bindings b)
    (map (lift 1 0) ns)
      (lift 1 (length ns) n))
    (map remove_closest_binding ms) (bind
      (right_cycle (length ms) m)
      (map (lift (length ms) 0) ns)
        (lift (length ms) (length ns) n))).

Inductive struct: relation pseudoterm :=
  | struct_distr:
    forall b ms m ns n,
    Forall (not_free_in 0) ms ->
    struct (bind (bind b ms m) ns n) (distr b ms m ns n).

Hint Constructors struct: cps.

(* We define [cong] as the smallest congruence relation closed under the rules
   of [struct] above. *)
Definition cong: relation pseudoterm :=
  clos_refl_sym_trans _ struct.

Hint Unfold cong: cps.
Hint Constructors clos_refl_sym_trans: cps.
Notation "[ a ~=~ b ]" := (cong a b)
  (at level 0, a, b at level 200): type_scope.

(******************************************************************************)

Example ex1: pseudoterm :=
  (bind (bind
    (jump 1 [bound 4; bound 0; bound 3])
    [base; base]
      (jump 2 [bound 1; bound 6; bound 0]))
    [base; negation [base; base]; base]
      (jump 1 [bound 3; bound 0])).

Example ex2: pseudoterm :=
  (bind (bind
    (jump 0 [bound 4; bound 1; bound 3])
    [base; negation [base; base]; base]
      (jump 1 [bound 4; bound 0]))
    [base; base]
      (bind
        (jump 0 [bound 2; bound 6; bound 1])
        [base; negation [base; base]; base]
          (jump 1 [bound 5; bound 0]))).

Lemma foo:
  forall e n i k,
  lift i (n + S k) (right_cycle n e) =
    right_cycle n (lift i (n + S k) e).
Proof.
  intros.
  (* Intuitively we know that we'll only lift variables strictly above n, so it
     won't be affecting any of the variables shifted by right_cycle; thus it
     won't matter whether we lift those after or before we shift the variables
     around. Now we have to convince Coq of that. *)
  unfold right_cycle; simpl.
  rewrite lift_distributes_over_subst.
  rewrite lift_bound_lt; eauto with arith.
  replace (S (n + S k)) with (1 + S (n + k)); auto with arith.
  rewrite lift_distributes_over_apply_parameters_at_any_depth.
  (* The lifts inside the map won't change the values, so the parameters will be
     kept the same. Later we must show that the different lifts on the body are
     also equivalent, by rewriting the lifts on the body. *)
  do 2 f_equal.
  - apply lifting_over_n_doesnt_change_sequence_n.
  - rewrite length_sequence.
    simpl; symmetry.
    rewrite lift_lift_permutation.
    + f_equal.
      omega.
    + omega.
Qed.

Lemma bar:
  forall i k e,
  lift i (S (S k)) (switch_bindings e) =
    switch_bindings (lift i (S (S k)) e).
Proof.
  intros.
  do 2 rewrite switch_bindings_behavior.
  apply foo with (n := 1).
Qed.

Lemma struct_distr_helper:
  forall b ms m ns n,
  forall x1 x2 x3 x4 x5 x6 x7,
  x1 = switch_bindings b ->
  x2 = lift 1 (length ns) n ->
  x3 = right_cycle (length ms) m ->
  x4 = lift (length ms) (length ns) n ->
  x5 = map (lift 1 0) ns ->
  x6 = map (lift (length ms) 0) ns ->
  x7 = map remove_closest_binding ms ->
  Forall (not_free_in 0) ms ->
  struct
    (bind (bind b ms m) ns n)
    (bind (bind x1 x5 x2) x7 (bind x3 x6 x4)).
Proof.
  intros.
  rewrite H, H0, H1, H2, H3, H4, H5.
  apply struct_distr.
  assumption.
Qed.

Lemma lift_preserves_struct:
  forall a b,
  struct a b ->
  forall i k,
  struct (lift i k a) (lift i k b).
Proof.
  induction 1; intros.
  (* Case: struct_distr. *)
  - simpl.
    (* This is a complicated case; upon simplifying the lift operation, we will
       have a valid distr here already, but the subterms are not in the right
       form yet. We use a helper lemma to add the needed equalities as subgoals,
       then proceed to prove them individualy. *)
    apply struct_distr_helper.
    + apply bar.
    + symmetry.
      rewrite map_length.
      rewrite lift_lift_permutation.
      * rewrite map_length.
        reflexivity.
      * omega.
    + do 2 rewrite map_length.
      replace (S (k + length ms)) with (length ms + S k).
      * apply foo.
      * omega.
    + do 4 rewrite map_length.
      symmetry.
      rewrite lift_lift_permutation.
      * f_equal.
        omega.
      * omega.
    + induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        symmetry.
        rewrite lift_lift_permutation; auto with arith.
    + do 2 rewrite map_length.
      induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        symmetry.
        rewrite lift_lift_permutation; auto with arith.
        replace (length ms + k) with (k + length ms); auto with arith.
    + dependent induction H; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite remove_closest_binding_and_lift_commute; auto.
    + induction ms; simpl; auto.
      inversion_clear H.
      constructor; auto.
      apply lifting_over_n_preserves_not_free_in_n; auto with arith.
Qed.

Hint Resolve lift_preserves_struct: cps.

(* As [cong] is a congruence, it should be preserved by lift. *)
Lemma lift_preserves_cong:
  forall a b,
  [a ~=~ b] ->
  forall i k,
  [lift i k a ~=~ lift i k b].
Proof.
  induction 1.
  (* Case: step. *)
  - auto with cps.
  (* Case: refl. *)
  - auto with cps.
  (* Case: symm. *)
  - intros; apply rst_sym.
    apply IHclos_refl_sym_trans.
  (* Case: tran. *)
  - intros; eapply rst_trans.
    + apply IHclos_refl_sym_trans1.
    + apply IHclos_refl_sym_trans2.
Qed.

Hint Resolve lift_preserves_cong: cps.

(** ** One-step reduction. *)

(*
  We have four assumptions: j, x, y, z.

  For (JMP):

  \j.\x.\y.\z.                       \j.\x.\y.\z.
    k@0<x@3, y@2>                      j@4<x@3, y@2, z@1>
    { k<a, b> =                 =>     { k<a, b> =
        j@5<a@1, b@0, z@2> }               j@5<a@1, b@0, z@2> }

  Does it make sense to keep the continuation binding there on a simply typed
  environment? I.e., does k<..., k, ...> ever make sense? I don't think there
  can be a (simple) type for that... oh, now I get it!
*)

Reserved Notation "[ a => b ]" (at level 0, a, b at level 200).

Inductive step: relation pseudoterm :=
  | step_beta:
    forall xs ts c,
    length xs = length ts ->
    [bind (jump 0 xs) ts c => bind (apply_parameters xs 0 c) ts c]
  | step_bind_left:
    forall b1 b2 ts c,
    [b1 => b2] -> [bind b1 ts c => bind b2 ts c]
  | step_bind_right:
    forall b ts c1 c2,
    [c1 => c2] -> [bind b ts c1 => bind b ts c2]
  | step_cong:
    forall a b c d,
    [a ~=~ b] -> [b => c] -> [c ~=~ d] -> [a => d]

where "[ a => b ]" := (step a b): type_scope.

Hint Constructors step: cps.

(** ** Multi-step reduction *)

Definition star: relation pseudoterm :=
  clos_refl_trans _ step.

Hint Unfold star: cps.
Hint Constructors clos_refl_trans: cps.
Notation "[ a =>* b ]" := (star a b)
  (at level 0, a, b at level 200): type_scope.

Lemma star_beta:
  forall xs ts c,
  length xs = length ts ->
  [bind (jump 0 xs) ts c =>* bind (apply_parameters xs 0 c) ts c].
Proof.
  auto with cps.
Qed.

Hint Resolve star_beta: cps.

Lemma star_step:
  forall a b,
  [a => b] -> [a =>* b].
Proof.
  auto with cps.
Qed.

Hint Resolve star_step: cps.

Lemma star_refl:
  forall e,
  [e =>* e].
Proof.
  auto with cps.
Qed.

Hint Resolve star_refl: cps.

Lemma star_tran:
  forall a b c,
  [a =>* b] -> [b =>* c] -> [a =>* c].
Proof.
  eauto with cps.
Qed.

Hint Resolve star_tran: cps.

Lemma star_bind_left:
  forall b1 b2 ts c,
  [b1 =>* b2] -> [bind b1 ts c =>* bind b2 ts c].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve star_bind_left: cps.

Lemma star_bind_right:
  forall b ts c1 c2,
  [c1 =>* c2] -> [bind b ts c1 =>* bind b ts c2].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve star_bind_right: cps.

(** ** Pseudoterm conversion *)

Definition conv: relation pseudoterm :=
  clos_refl_sym_trans _ step.

Hint Unfold conv: cps.
Notation "[ a <=> b ]" := (conv a b)
  (at level 0, a, b at level 200): type_scope.

Lemma conv_beta:
  forall xs ts c,
  length xs = length ts ->
  [bind (jump 0 xs) ts c <=> bind (apply_parameters xs 0 c) ts c].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_beta: cps.

Lemma conv_step:
  forall a b,
  [a => b] -> [a <=> b].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_step: cps.

Lemma conv_star:
  forall a b,
  [a =>* b] -> [a <=> b].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve conv_star: cps.

Lemma conv_refl:
  forall e,
  [e <=> e].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_refl: cps.

Lemma conv_symm:
  forall a b,
  [a <=> b] -> [b <=> a].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_symm: cps.

Lemma conv_tran:
  forall a b c,
  [a =>* b] -> [b =>* c] -> [a =>* c].
Proof.
  eauto with cps.
Qed.

Hint Resolve conv_tran: cps.

Lemma conv_bind_left:
  forall b1 b2 ts c,
  [b1 =>* b2] -> [bind b1 ts c <=> bind b2 ts c].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve conv_bind_left: cps.

Lemma conv_bind_right:
  forall b ts c1 c2,
  [c1 =>* c2] -> [bind b ts c1 <=> bind b ts c2].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve conv_bind_right: cps.

(** *)

Hint Unfold transp: cps.

Lemma subterm_and_step_commute:
  commut _ subterm (transp _ step).
Proof.
  induction 1; eauto with cps.
Qed.

(** *)

Inductive parallel: relation pseudoterm :=
  | parallel_beta:
    forall xs ts c1 c2,
    length xs = length ts -> parallel c1 c2 ->
    parallel (bind (jump 0 xs) ts c1) (bind (apply_parameters xs 0 c2) ts c2)
  | parallel_type:
    parallel type type
  | parallel_prop:
    parallel prop prop
  | parallel_base:
    parallel base base
  | parallel_void:
    parallel void void
  | parallel_bound:
    forall n,
    parallel (bound n) (bound n)
  | parallel_negation:
    forall ts,
    parallel (negation ts) (negation ts)
  | parallel_jump:
    forall k xs,
    parallel (jump k xs) (jump k xs)
  | parallel_bind:
    forall b1 b2 ts c1 c2,
    parallel b1 b2 -> parallel c1 c2 ->
    parallel (bind b1 ts c1) (bind b2 ts c2)
  | parallel_cong:
    forall a b c d,
    [a ~=~ b] -> parallel b c -> [c ~=~ d] -> parallel a d.

Hint Constructors parallel: cps.

Lemma parallel_refl:
  forall e,
  parallel e e.
Proof.
  induction e; auto with cps.
Qed.

Hint Resolve parallel_refl: cps.

Lemma parallel_step:
  forall a b,
  [a => b] -> parallel a b.
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve parallel_step: cps.

Lemma parallel_lift:
  forall a b,
  parallel a b ->
  forall i k,
  parallel (lift i k a) (lift i k b).
Proof.
  induction 1; intros.
  (* Case: parallel_beta. *)
  - simpl.
    rewrite lift_distributes_over_apply_parameters.
    rewrite H; apply parallel_beta.
    + do 2 rewrite map_length.
      assumption.
    + apply IHparallel.
  (* Case: parallel_type. *)
  - apply parallel_type.
  (* Case: parallel_prop. *)
  - apply parallel_prop.
  (* Case: parallel_base. *)
  - apply parallel_base.
  (* Case: parallel_void. *)
  - apply parallel_void.
  (* Case: parallel_bound. *)
  - apply parallel_refl.
  (* Case: parallel_negation. *)
  - apply parallel_negation.
  (* Case: parallel_jump. *)
  - apply parallel_jump.
  (* Case: parallel_bind. *)
  - simpl.
    apply parallel_bind.
    + apply IHparallel1.
    + apply IHparallel2.
  (* Case: parallel_cong. *)
  - apply parallel_cong with (lift i k b) (lift i k c).
    + apply lift_preserves_cong; auto.
    + apply IHparallel.
    + apply lift_preserves_cong; auto.
Qed.

Hint Resolve parallel_lift: cps.

(*

(* We would usually like to have two different substition values (c and d), that
   should be parallel, but we don't do that as we know reductions never happen
   inside of parameter packs. If we ever have something other than variables as
   values this should not be the case. *)
Lemma parallel_subst:
  forall a b,
  parallel a b ->
  forall c k,
  parallel (subst c k a) (subst c k b).
Proof.
  induction 1; intros.
  (* Case: parallel_beta. *)
  - simpl.
    rewrite subst_distributes_over_apply_parameters.
    rewrite H; apply parallel_beta.
    + do 2 rewrite map_length.
      assumption.
    + apply IHparallel.
  (* Case: parallel_type. *)
  - apply parallel_type.
  (* Case: parallel_prop. *)
  - apply parallel_prop.
  (* Case: parallel_base. *)
  - apply parallel_base.
  (* Case: parallel_void. *)
  - apply parallel_void.
  (* Case: parallel_bound. *)
  - apply parallel_refl.
  (* Case: parallel_negation. *)
  - apply parallel_negation.
  (* Case: parallel_jump. *)
  - apply parallel_jump.
  (* Case: parallel_bind. *)
  - simpl.
    apply parallel_bind.
    + apply IHparallel1.
    + apply IHparallel2.
Qed.

Hint Resolve parallel_subst: cps.

Lemma parallel_apply_parameters:
  forall xs a b,
  parallel a b ->
  forall k,
  parallel (apply_parameters xs k a) (apply_parameters xs k b).
Proof.
  induction xs; simpl; auto with cps.
Qed.

Hint Resolve parallel_apply_parameters: cps.

Lemma star_parallel:
  forall a b,
  parallel a b -> [a =>* b].
Proof.
  induction 1; intros.
  (* Case: parallel_beta. *)
  - eapply star_tran.
    + apply star_bind_right.
      eassumption.
    + apply star_beta.
      assumption.
  (* Case: parallel_type. *)
  - apply star_refl.
  (* Case: parallel_prop. *)
  - apply star_refl.
  (* Case: parallel_base. *)
  - apply star_refl.
  (* Case: parallel_void. *)
  - apply star_refl.
  (* Case: parallel_bound. *)
  - apply star_refl.
  (* Case: parallel_negation. *)
  - apply star_refl.
  (* Case: parallel_jump. *)
  - apply star_refl.
  (* Case: parallel_bind. *)
  - eapply star_tran.
    + apply star_bind_left.
      eassumption.
    + apply star_bind_right.
      assumption.
Qed.

Hint Resolve star_parallel: cps.

*)

End STCC.
