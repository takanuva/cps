(******************************************************************************)
(*      Copyright (c) 2019 - Paulo Torrens <paulotorrens AT gnu DOT org>      *)
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

Example ex1: pseudoterm :=
  (bind (bind
    (jump 1 [bound 4; bound 0; bound 3])
    [base; base]
      (jump 2 [bound 1; bound 6; bound 0]))
    [base; negation [base; base]; base]
      (jump 1 [bound 3; bound 0])).

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

(* Clearly, if we're lifiting [e]'s var above [k] by [i], anything equal or
   greater than [k] and smaller than [k + i] is free. *)
Lemma lifting_more_than_n_makes_not_free_in_n:
  forall e i k n,
  n >= k -> n < k + i -> not_free_in n (lift i k e).
Proof.
  induction e using pseudoterm_deepind; intros.
  (* Case: type. *)
  - constructor.
  (* Case: prop. *)
  - constructor.
  (* Case: base. *)
  - constructor.
  (* Case: void. *)
  - constructor.
  (* Case: bound. *)
  - simpl; destruct (le_gt_dec k n); constructor; omega.
  (* Case: negation. *)
  - simpl; constructor.
    dependent induction H; simpl; auto.
  (* Case: jump. *)
  - simpl; constructor.
    + apply IHe; auto.
    + dependent induction H; simpl; auto.
  (* Case: bind. *)
  - simpl; constructor.
    + apply IHe1; omega.
    + dependent induction H; simpl; auto.
    + rewrite map_length.
      apply IHe2; omega.
Qed.

Lemma substing_over_n_preserves_not_free_in_n:
  forall e n,
  not_free_in n e ->
  forall x k,
  k > n -> not_free_in n (subst x k e).
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
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + constructor; omega.
    + apply lifting_more_than_n_makes_not_free_in_n; omega.
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
  forall x xs k c n,
  subst x (n + S k) (apply_parameters xs n c) =
    apply_parameters (map (subst x (S k)) xs) n
      (subst x (n + k + length xs) c).
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

Lemma lift_preserved_by_useless_subst:
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
  apply lift_preserved_by_useless_subst with (p := 0).
  assumption.
Qed.

Lemma subst_preserved_by_useless_subst:
  forall e y k p x,
  not_free_in p e ->
  subst y (p + k) (subst x p e) = subst x p (subst y (p + S k) e).
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
  - destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ];
      destruct (lt_eq_lt_dec (p + S k) n) as [ [ ? | ? ] | ? ];
        try (exfalso; omega).
    + rewrite subst_bound_gt; try omega.
      rewrite subst_bound_gt; try omega.
      reflexivity.
    + replace (p + S k) with (S (p + k)); auto.
      rewrite subst_bound_eq; try omega.
      rewrite subst_lift_simplification; try omega.
      f_equal; omega.
    + rewrite subst_bound_lt; try omega.
      rewrite subst_bound_gt; try omega.
      reflexivity.
    + absurd (p = n).
      * inversion H; assumption.
      * assumption.
    + simpl.
      destruct (lt_eq_lt_dec (p + k) n) as [ [ ? | ? ] | ? ];
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

Lemma remove_closest_binding_and_subst_commute:
  forall e x k,
  not_free_in 0 e ->
  subst x k (remove_closest_binding e) =
    remove_closest_binding (subst x (S k) e).
Proof.
  intros.
  apply subst_preserved_by_useless_subst with (p := 0).
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

Lemma substing_over_n_doesnt_change_sequence_n:
  forall n x k,
  map (subst x (S (n + k))) (sequence n) = sequence n.
Proof.
  induction n; intros.
  (* Case: zero. *)
  - reflexivity.
  (* Case: succ. *)
  - rewrite sequence_succ.
    rewrite map_cons.
    f_equal.
    + rewrite subst_bound_lt; auto.
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

                                         \j.\x.\y.\z.
    \j.\x.\y.\z.                           h@0<x@4, k@1, y@3>
      h@1<x@4, k@0, y@3>                   { h<c, d, e> =
      { k<a, b> =                 ==           d@1<z@4, e@0> }
          h@2<a@1, j@6, b@0> }             { k<a, b> =
      { h<c, d, e> =                           h@0<a@2, j@6, b@1>
          d@1<z@3, e@0> }                      { h<c, d, e> =
                                                 d@1<z@5, e@0> } }

    That's an annoying reduction to do... let's see...

  For (CONTR):

    \j.\x.\y.\z.
      j@5<k@0, h@1>                      \j.\x.\y.\z.
      { k<a, b> =                          j@4<k@0, k@0>
          a@1<x@5, b@0, z@3> }    ==       { k<a, b> =
      { h<c, d> =                              a@1<x@4, b@0, z@2> }
          c@1<x@4, d@0, z@2> }

    Hmm, this is also troublesome...
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

Hint Unfold distr: cps.

Definition contr b ts c: pseudoterm :=
  (bind (bind
    b
    (map (lift 1 0) ts) (lift 1 (length ts) c)) ts c).

Hint Unfold contr: cps.

(* As of now, I'm still unsure whether we'll need a directed, one-step struct
   relation or just it's congruence version. Just to be sure, we'll define it
   anyway. TODO: should we consider (JMP) here as well? *)

Inductive struct: relation pseudoterm :=
  | struct_distr:
    forall b ms m ns n,
    Forall (not_free_in 0) ms ->
    struct (bind (bind b ms m) ns n) (distr b ms m ns n)
  | struct_contr:
    forall b ts c,
    struct (contr b ts c) (bind (remove_closest_binding b) ts c)
  | struct_gc:
    forall b ts c,
    not_free_in 0 b ->
    struct (bind b ts c) (remove_closest_binding b)
  | struct_bind_left:
    forall b1 b2 ts c,
    struct b1 b2 -> struct (bind b1 ts c) (bind b2 ts c)
  | struct_bind_right:
    forall b ts c1 c2,
    struct c1 c2 -> struct (bind b ts c1) (bind b ts c2).

Hint Constructors struct: cps.

(* We'll just define our structural congruence as the smallest relation closed
   under the [struct] rules above. *)

Definition cong: relation pseudoterm :=
  clos_refl_sym_trans _ struct.

Hint Unfold cong: cps.
Hint Constructors clos_refl_sym_trans: cps.
Notation "[ a == b ]" := (cong a b) (at level 0, a, b at level 200).

Lemma cong_refl:
  forall e,
  [e == e].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_refl: cps.

Lemma cong_symm:
  forall a b,
  [a == b] -> [b == a].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_symm: cps.

Lemma cong_tran:
  forall a b c,
  [a == b] -> [b == c] -> [a == c].
Proof.
  eauto with cps.
Qed.

Hint Resolve cong_tran: cps.

Lemma cong_struct:
  forall a b,
  struct a b -> [a == b].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_struct: cps.

Lemma cong_distr:
  forall b ms m ns n,
  Forall (not_free_in 0) ms ->
  [bind (bind b ms m) ns n == distr b ms m ns n].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_distr: cps.

Lemma cong_contr:
  forall b ts c,
  [contr b ts c == bind (remove_closest_binding b) ts c].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_contr: cps.

Lemma cong_gc:
  forall b ts c,
  not_free_in 0 b ->
  [bind b ts c == remove_closest_binding b].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_gc: cps.

Lemma cong_bind_left:
  forall b1 b2 ts c,
  [b1 == b2] -> [bind b1 ts c == bind b2 ts c].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve cong_bind_left: cps.

Lemma cong_bind_right:
  forall b ts c1 c2,
  [c1 == c2] -> [bind b ts c1 == bind b ts c2].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve cong_bind_right: cps.

Instance cong_is_equiv: Equivalence cong.
Proof.
  split.
  - exact cong_refl.
  - exact cong_symm.
  - exact cong_tran.
Defined.

(******************************************************************************)

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

Goal [ex1 == ex2].
Proof.
  apply cong_distr.
  do 3 constructor.
Qed.

Lemma lift_and_right_cycle_commute:
  forall e n i k,
  lift i (n + S k) (right_cycle n e) = right_cycle n (lift i (n + S k) e).
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

Lemma lift_and_switch_bindings_commute:
  forall i k e,
  lift i (S (S k)) (switch_bindings e) = switch_bindings (lift i (S (S k)) e).
Proof.
  intros.
  do 2 rewrite switch_bindings_behavior.
  apply lift_and_right_cycle_commute with (n := 1).
Qed.

Lemma subst_and_right_cycle_commute:
  forall e n x k,
  subst x (n + S k) (right_cycle n e) =
    right_cycle n (subst x (n + S k) e).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite subst_distributes_over_itself.
  rewrite subst_bound_lt; eauto with arith.
  replace (S (n + S k)) with (1 + S (n + k)); auto with arith.
  rewrite subst_distributes_over_apply_parameters_at_any_depth.
  do 2 f_equal.
  - apply substing_over_n_doesnt_change_sequence_n.
  - rewrite length_sequence; simpl.
    rewrite lift_and_subst_commute.
    + f_equal.
      omega.
    + omega.
Qed.

Lemma subst_and_switch_bindings_commute:
  forall x k e,
  subst x (S (S k)) (switch_bindings e) = switch_bindings (subst x (S (S k)) e).
Proof.
  intros.
  do 2 rewrite switch_bindings_behavior.
  apply subst_and_right_cycle_commute with (n := 1).
Qed.

Lemma struct_distr_helper:
  forall b ms m ns n x1 x2 x3 x4 x5 x6 x7,
  x1 = switch_bindings b ->
  x2 = lift 1 (length ns) n ->
  x3 = right_cycle (length ms) m ->
  x4 = lift (length ms) (length ns) n ->
  x5 = map (lift 1 0) ns ->
  x6 = map (lift (length ms) 0) ns ->
  x7 = map remove_closest_binding ms ->
  Forall (not_free_in 0) ms ->
  struct (bind (bind b ms m) ns n) (bind (bind x1 x5 x2) x7 (bind x3 x6 x4)).
Proof.
  intros.
  rewrite H, H0, H1, H2, H3, H4, H5.
  apply struct_distr; auto.
Qed.

Lemma struct_contr_helper:
  forall b ms m ns n x1 x2 x3,
  ms = map (lift 1 0) ns ->
  x1 = remove_closest_binding b ->
  x2 = ns ->
  x3 = n ->
  m = lift 1 (length ns) n ->
  struct (bind (bind b ms m) ns n) (bind x1 x2 x3).
Proof.
  intros.
  rewrite H, H0, H1, H2, H3.
  apply struct_contr.
Qed.

Lemma struct_gc_helper:
  forall b ts c x1,
  x1 = remove_closest_binding b ->
  not_free_in 0 b ->
  struct (bind b ts c) x1.
Proof.
  intros.
  rewrite H.
  apply struct_gc; auto.
Qed.

Lemma struct_lift:
  forall a b,
  struct a b ->
  forall i k,
  struct (lift i k a) (lift i k b).
Proof.
  induction 1; intros.
  (* Case: struct_distr. *)
  - simpl; apply struct_distr_helper.
    + apply lift_and_switch_bindings_commute.
    + symmetry.
      do 2 rewrite map_length.
      rewrite lift_lift_permutation.
      * reflexivity.
      * omega.
    + do 2 rewrite map_length.
      replace (S (k + length ms)) with (length ms + S k).
      * apply lift_and_right_cycle_commute.
      * omega.
    + do 4 rewrite map_length.
      symmetry.
      rewrite lift_lift_permutation.
      * f_equal; omega.
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
        f_equal; omega.
    + dependent induction H; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite remove_closest_binding_and_lift_commute; auto.
    + induction ms; simpl; auto.
      inversion_clear H.
      constructor; auto.
      apply lifting_over_n_preserves_not_free_in_n; auto with arith.
  (* Case: struct_contr. *)
  - simpl; apply struct_contr_helper.
    + induction ts; simpl.
      * reflexivity.
      * f_equal; auto.
        symmetry.
        rewrite lift_lift_permutation; auto with arith.
    + unfold remove_closest_binding.
      rewrite lift_distributes_over_subst.
      rewrite lift_bound_lt; auto with arith.
    + reflexivity.
    + reflexivity.
    + do 2 rewrite map_length.
      symmetry.
      rewrite lift_lift_permutation; auto with arith.
  (* Case: struct_gc. *)
  - rewrite remove_closest_binding_and_lift_commute; auto.
    apply struct_gc.
    apply lifting_over_n_preserves_not_free_in_n; auto with arith.
  (* Case: struct_bind_left. *)
  - simpl; auto with cps.
  (* Case: struct_bind_right. *)
  - simpl; auto with cps.
Qed.

Hint Resolve struct_lift: cps.

Lemma cong_lift:
  forall a b,
  [a == b] ->
  forall i k,
  [lift i k a == lift i k b].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve cong_lift: cps.

Lemma struct_subst:
  forall a b,
  struct a b ->
  forall c k,
  struct (subst c k a) (subst c k b).
Proof.
  induction 1; intros.
  (* Case: struct_distr. *)
  - simpl; apply struct_distr_helper.
    + apply subst_and_switch_bindings_commute.
    + do 2 rewrite map_length.
      rewrite lift_and_subst_commute.
      * reflexivity.
      * omega.
    + do 2 rewrite map_length.
      replace (S (k + length ms)) with (length ms + S k).
      * apply subst_and_right_cycle_commute.
      * omega.
    + do 4 rewrite map_length.
      rewrite lift_and_subst_commute.
      * f_equal; omega.
      * omega.
    + induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite lift_and_subst_commute; auto with arith.
    + do 2 rewrite map_length.
      induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite lift_and_subst_commute; auto with arith.
        f_equal; omega.
    + dependent induction H; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite remove_closest_binding_and_subst_commute; auto.
    + induction ms; simpl; auto.
      inversion_clear H.
      constructor; auto.
      apply substing_over_n_preserves_not_free_in_n; auto with arith.
  (* Case: struct_contr. *)
  - simpl; apply struct_contr_helper.
    + induction ts; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite lift_and_subst_commute; auto with arith.
    + unfold remove_closest_binding.
      apply subst_addition_distributes_over_itself with (p := 0).
    + reflexivity.
    + reflexivity.
    + do 2 rewrite map_length.
      rewrite lift_and_subst_commute; auto with arith.
  (* Case: struct_gc. *)
  - rewrite remove_closest_binding_and_subst_commute; auto.
    apply struct_gc.
    apply substing_over_n_preserves_not_free_in_n; auto with arith.
  (* Case: struct_bind_left. *)
  - simpl; auto with cps.
  (* Case: struct_bind_right. *)
  - simpl; auto with cps.
Qed.

Hint Resolve struct_subst: cps.

Lemma cong_subst:
  forall a b,
  [a == b] ->
  forall x k,
  [subst x k a == subst x k b].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve cong_subst: cps.

Lemma cong_apply_parameters:
  forall a b,
  [a == b] ->
  forall xs k,
  [apply_parameters xs k a == apply_parameters xs k b].
Proof.
  induction xs; simpl; auto with cps.
Qed.

Hint Resolve cong_apply_parameters: cps.

Lemma cong_right_cycle:
  forall a b,
  [a == b] ->
  forall n,
  [right_cycle n a == right_cycle n b].
Proof.
  unfold right_cycle; auto with cps.
Qed.

Hint Resolve cong_right_cycle: cps.

(******************************************************************************)

Lemma nat_fold_subst_unlifts_bound:
  forall (n k: nat) x,
  k <= n -> nat_fold k (subst x 0) n = n - k.
Proof.
  induction k; intros.
  - simpl; auto with arith.
  - simpl; rewrite IHk; auto with arith.
    rewrite subst_bound_gt; try omega.
    rewrite minus_plus_simpl_l_reverse with (p := 1).
    replace (1 + n - (1 + k)) with (1 + (n - (1 + k))).
    + simpl; reflexivity.
    + omega.
Qed.

(* Float left: L { M } { N } == L { N } { M } if n doesn't appear in M. *)

Definition float_left b ms m ns n: pseudoterm :=
  (bind (bind
     (switch_bindings b)
     (map (lift 1 0) ns) (lift 1 (length ns) n))
     (map (subst 0 0) ms) (subst 0 (length ms) m)).

Lemma cong_float_left:
  forall b ms m ns n,
  not_free_in (length ms) m ->
  Forall (not_free_in 0) ms ->
  [bind (bind b ms m) ns n == float_left b ms m ns n].
Proof.
  intros.
  apply cong_tran with (distr b ms m ns n).
  - apply cong_distr.
    assumption.
  - apply cong_bind_right.
    apply cong_struct; apply struct_gc_helper.
    + admit.
    + admit.
Admitted.

(* Float right: L { M } { N } == L { M { N } } if n doesn't appear in L. *)

Definition float_right b ms m ns n: pseudoterm :=
  (bind
    (remove_closest_binding (switch_bindings b))
    (map remove_closest_binding ms) (bind
      (right_cycle (length ms) m)
      (map (lift (length ms) 0) ns) (lift (length ms) (length ns) n))).

Lemma cong_float_right:
  forall b ms m ns n,
  not_free_in 1 b ->
  Forall (not_free_in 0) ms ->
  [bind (bind b ms m) ns n == float_right b ms m ns n].
Proof.
  intros.
  apply cong_tran with (distr b ms m ns n).
  - apply cong_distr.
    assumption.
  - apply cong_bind_left.
    apply cong_gc.
    admit.
Admitted.

(******************************************************************************)

Definition body: Set :=
  list pseudoterm * pseudoterm.

Inductive long_form: pseudoterm -> pseudoterm -> list body -> Prop :=
  | long_form_jump:
    forall k xs,
    long_form (jump k xs) (jump k xs) []
  | long_form_bind:
    forall b h ts c cs,
    long_form b h cs ->
    long_form (bind b ts c) h (cs ++ [(ts, c)]).

Fixpoint rebuild b cs: pseudoterm :=
  match cs with
  | [] => b
  | (ts, c) :: cs => rebuild (bind b ts c) cs
  end.

Lemma rebuild_behavior:
  forall cs h ts c,
  rebuild h (cs ++ [(ts, c)]) = bind (rebuild h cs) ts c.
Proof.
  induction cs; intros.
  - reflexivity.
  - destruct a; simpl.
    rewrite IHcs; auto.
Qed.

Lemma rebuild_is_sound:
  forall e h cs,
  long_form e h cs -> e = rebuild h cs.
Proof.
  induction 1.
  - reflexivity.
  - rewrite IHlong_form.
    clear H IHlong_form.
    generalize h as g; intro.
    rewrite rebuild_behavior; auto.
Qed.

(******************************************************************************)

(** ** One-step reduction. *)

(*
  We have four assumptions: j, x, y, z.

  For (JMP):

    \j.\x.\y.\z.                         \j.\x.\y.\z.
      k@0<x@3, y@2>                        j@4<x@3, y@2, z@1>
      { k<a, b> =                 =>       { k<a, b> =
          j@5<a@1, b@0, z@2> }                 j@5<a@1, b@0, z@2> }

    Does it make sense to keep the continuation binding there on a simply typed
    environment? I.e., does k<..., k, ...> ever make sense? I don't think there
    can be a (simple) type for that... oh, now I get it!

  On our notion of reduction:

    In Thielecke's dissertation, he briefly suggested directed versions of the
    (DISTR) and (JMP) rules as the -` and -> relations and the reduction would
    be then given by -`* ->*. Notice of course that the (JMP) rule always jumps
    to the immediate (closest) continuation. Merro later studies the calculus
    and gives a long jump form, with ki<xs> { k1<ys> = K1 } ... { kn<ys> = Kn }
    reducing to Ki[xs/ys] { k1<ys> = K1 } ... { kn<ys> = Kn }, which is a really
    useful generalization. We'll probably take a similar notion of reduction, as
    distr-redexes always are possible and, worse, they duplicate jmp-redexes,
    thus -`* ->* may only be weakly normalizing at best (there's always an
    infinite sequence).

    Question: do those two notions of reduction commute? I.e., is it possible to
    get terms a -`* b ->* c such that for all a there exists b and c where there
    are no longjmp-redexes in c? I don't think so.
*)

Inductive hole: nat -> Set :=
  | hole_here:
    hole 0
  | hole_left:
    forall {n},
    hole n -> list pseudoterm -> pseudoterm -> hole (S n).

Fixpoint apply_hole {n} (h: hole n) (e: pseudoterm): pseudoterm :=
  match h with
  | hole_here => e
  | hole_left b ts c => bind (apply_hole b e) ts c
  end.

Coercion apply_hole: hole >-> Funclass.

Reserved Notation "[ a => b ]" (at level 0, a, b at level 200).

Inductive step: relation pseudoterm :=
  | step_ctxjmp:
    forall {k} (h: hole k),
    forall xs ts c,
    length xs = length ts ->
    [bind (h (jump k xs)) ts c =>
      bind (h (apply_parameters xs 0 (lift k (length ts) c))) ts c]
  | step_bind_left:
    forall b1 b2 ts c,
    [b1 => b2] -> [bind b1 ts c => bind b2 ts c]

where "[ a => b ]" := (step a b): type_scope.

Hint Constructors step: cps.

Lemma step_ctxjmp_helper:
  forall {k} (h: hole k),
  forall a b xs ts c,
  a = h (jump k xs) ->
  b = h (apply_parameters xs 0 (lift k (length ts) c)) ->
  length xs = length ts ->
  [bind a ts c => bind b ts c].
Proof.
  intros.
  rewrite H, H0.
  apply step_ctxjmp; auto.
Qed.

Lemma step_jmp:
  forall xs ts c,
  length xs = length ts ->
  [bind (jump 0 xs) ts c => bind (apply_parameters xs 0 c) ts c].
Proof.
  intros.
  eapply step_ctxjmp_helper with (h := hole_here).
  - reflexivity.
  - rewrite lift_zero_e_equals_e; auto.
  - assumption.
Qed.

(*
    \j.\x.\y.\z.                         \j.\x.\y.\z.
      h@1<x@4, k@0, y@3>                   k@0<z@2, y@3>
      { k<a, b> =                 =>       { k<a, b> =
          h@2<a@1, j@6, b@0> }                 h@2<a@1, j@6, b@0> }
      { h<c, d, e> =                       { h<c, d, e> =
          d@1<z@3, e@0> }                      d@1<z@3, e@0> }
*)

Example ex3: pseudoterm :=
  (bind (bind
    (jump 0 [bound 2; bound 3])
    [base; base]
      (jump 2 [bound 1; bound 6; bound 0]))
    [base; negation [base; base]; base]
      (jump 1 [bound 3; bound 0])).

Goal [ex1 => ex3].
Proof.
  compute.
  eapply step_ctxjmp_helper with (h := hole_left hole_here ?[ts] ?[c]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Inductive item {T} (e: T): list T -> nat -> Prop :=
  | item_car:
    forall cdr, item e (cons e cdr) 0
  | item_cdr:
    forall car cdr n, item e cdr n -> item e (cons car cdr) (S n).

Lemma item_app:
  forall {T} e xs n,
  @item T e xs n ->
  forall ys,
  @item T e (xs ++ ys) n.
Proof.
  induction 1; intros.
  - constructor.
  - simpl; constructor.
    apply IHitem.
Qed.

Inductive merro: relation pseudoterm :=
  | merro_step:
    forall e k xs ts c cs,
    item (ts, c) cs k ->
    length xs = length ts ->
    long_form e (jump k xs) cs ->
    merro e (rebuild (apply_parameters xs 0 (lift k (length ts) c)) cs).

Lemma rebuild_implies_hole:
  forall cs,
  exists h: hole (length cs),
  forall e, rebuild e cs = h e.
Proof.
  (* We need an inverse induction on lists. *)
  induction cs using rev_ind; simpl.
  (* Case: nil. *)
  - exists hole_here.
    reflexivity.
  (* Case: cons. *)
  - destruct x as (ts, c).
    destruct IHcs as (h, H).
    rewrite app_length.
    rewrite Nat.add_comm.
    exists (hole_left h ts c).
    intro; rewrite rebuild_behavior.
    rewrite H; auto.
Qed.

Lemma hole_implies_rebuild:
  forall k (h: hole k),
  exists2 cs,
  forall e, h e = rebuild e cs & length cs = k.
Proof.
  do 2 intro; dependent induction h.
  - exists []; auto.
  - destruct IHh as (cs, ?, ?).
    exists (cs ++ [(l, p)]).
    intro; simpl.
    rewrite H, rebuild_behavior.
    reflexivity.
    rewrite app_length, H0; simpl; omega.
Qed.

Lemma item_in_head:
  forall {T} x xs ys n,
  @item T x (xs ++ ys) n -> n < length xs ->
  @item T x xs n.
Proof.
  induction xs; simpl; intros.
  - inversion H0.
  - dependent destruction H.
    + constructor.
    + constructor.
      eapply IHxs; eauto.
      omega.
Qed.

Lemma item_app_rev:
  forall {T} xs x y,
  @item T x (xs ++ [y]) (length xs) -> x = y.
Proof.
  induction xs; intros.
  - inversion_clear H.
    reflexivity.
  - eapply IHxs.
    simpl in H.
    inversion_clear H.
    exact H0.
Qed.

Lemma item_too_far:
  forall {T} xs x k,
  length xs <= k ->
  ~@item T x xs k.
Proof.
  induction xs; intros.
  - inversion 1.
  - intro.
    dependent destruction H0.
    + simpl in H; omega.
    + eapply IHxs with (k := n).
      * simpl in H; omega.
      * eassumption.
Qed.

(* Argh, such an ugly proof! TODO: delete me and rewrite me later please! *)
Lemma step_longjmp:
  forall cs e k xs ts c,
  item (ts, c) cs k ->
  length xs = length ts ->
  long_form e (jump k xs) cs ->
  [e => rebuild (apply_parameters xs 0 (lift k (length ts) c)) cs].
Proof.
  induction cs using rev_ind; intros.
  - inversion H.
  - destruct x.
    inversion H1.
    + exfalso.
      eapply app_cons_not_nil; eauto.
    + rewrite rebuild_behavior.
      edestruct app_inj_tail; eauto.
      destruct H6, H7.
      destruct (lt_eq_lt_dec (length cs0) k) as [ [ ? | ? ] | ? ].
      * exfalso.
        clear IHcs H0 H2 H1 H3 H4 H5 l p b h.
        eapply item_too_far with (xs0 := cs0 ++ [(ts0, c0)]) (k0 := k).
        rewrite app_length.
        rewrite Nat.add_comm.
        simpl.
        omega.
        eassumption.
      * clear IHcs; destruct e0.
        edestruct rebuild_implies_hole with cs0 as (m, ?).
        replace b with (rebuild (jump (length cs0) xs) cs0).
        do 2 rewrite H6.
        pose (@item_app_rev _ _ _ _ H) as H7.
        dependent destruction H7.
        apply step_ctxjmp.
        assumption.
        erewrite rebuild_is_sound; eauto.
      * apply step_bind_left.
        apply IHcs; auto.
        eapply item_in_head; eauto.
Qed.

(* TODO: ditto!!! *)
Lemma longjmp_step:
  forall k (h: hole k) xs ts c,
  length xs = length ts ->
  merro (bind (h (jump k xs)) ts c)
    (bind (h (apply_parameters xs 0 (lift k (length ts) c))) ts c).
Proof.
  intros.
  edestruct hole_implies_rebuild.
  do 2 erewrite H0.
  do 2 rewrite <- rebuild_behavior.
  rewrite -> rebuild_behavior.
  apply merro_step.
  - rewrite <- H1.
    clear H0 H1.
    induction x; simpl.
    + constructor.
    + constructor.
      apply IHx.
  - assumption.
  - constructor.
    clear H0 H1.
    induction x using rev_ind; simpl.
    + constructor.
    + destruct x.
      rewrite rebuild_behavior.
      constructor; auto.
Qed.

(* This should be true while we consider only static contexts, i.e., never into
   the right (inner) side of a bind. Gotta prove this just to be sure I'm doing
   the right thing before introducing generalized contexts. *)
Lemma equiv:
  forall a b,
  [a => b] <-> merro a b.
Proof.
  split; induction 1.
  - apply longjmp_step; auto.
  - destruct IHstep.
    rewrite <- rebuild_behavior.
    apply merro_step.
    + apply item_app; auto.
    + assumption.
    + constructor; auto.
  - apply step_longjmp; auto.
Qed.

(******************************************************************************)

Definition confluent {T} (R: T -> T -> Prop): Prop :=
  commut _ R (transp _ R).

Inductive parallel: relation pseudoterm :=
  | parallel_refl:
    forall e,
    parallel e e
  | parallel_ctxjmp:
    forall {k} (h: hole k),
    forall xs ts c1 c2,
    length xs = length ts -> parallel c1 c2 ->
    parallel (bind (h (jump k xs)) ts c1)
      (bind (h (apply_parameters xs 0 (lift k (length ts) c2))) ts c2)
  | parallel_bind:
    forall b1 b2 ts c1 c2,
    parallel b1 b2 -> parallel c1 c2 ->
    parallel (bind b1 ts c1) (bind b2 ts c2).

Lemma parallel_step:
  forall a b,
  [a => b] -> parallel a b.
Proof.
  induction 1.
  - apply parallel_ctxjmp; auto.
    apply parallel_refl.
  - apply parallel_bind; auto.
    apply parallel_refl.
Qed.

Lemma hole_lift:
  forall {n} (h: hole n),
  forall i k,
  exists r: hole n,
  forall e, lift i k (h e) = r (lift i (n + k) e).
Proof.
  induction h; simpl; intros.
  - exists hole_here; auto.
  - edestruct IHh with i (S k) as (r, ?).
    exists (hole_left r (map (lift i k) l) (lift i (k + length l) p)); intro.
    simpl; f_equal.
    replace (S (n + k)) with (n + S k); try omega.
    apply H.
Qed.

Lemma parallel_lift:
  forall a b,
  parallel a b ->
  forall i k,
  parallel (lift i k a) (lift i k b).
Proof.
  induction 1; intros.
  - apply parallel_refl.
  - (* Dealing with de Bruijn indexes is really annoying... *)
    simpl; destruct @hole_lift with k h i (S k0) as (r, ?).
    do 2 rewrite H1.
    do 2 replace (k + S k0) with (S (k + k0)); try omega.
    rewrite lift_distributes_over_apply_parameters.
    replace (lift i (S (k + k0)) (jump k xs)) with
      (jump (lift i (S (k + k0)) k) (map (lift i (S (k + k0))) xs)); auto.
    rewrite lift_bound_lt; try omega.
    replace (lift i (k + k0 + length xs) (lift k (length ts) c2)) with
      (lift k (length (map (lift i k0) ts)) (lift i (k0 + length ts) c2)).
    + apply parallel_ctxjmp; auto.
      do 2 rewrite map_length; auto.
    + rewrite map_length, H.
      rewrite lift_lift_permutation; try omega.
      f_equal; try omega.
  - simpl.
    apply parallel_bind.
    + apply IHparallel1.
    + apply IHparallel2.
Qed.

Lemma parallel_is_confluent:
  confluent parallel.
Proof.
  compute.
  induction 1; intros.
  - exists z.
    + assumption.
    + apply parallel_refl.
  - dependent induction H1.
    + eexists.
      * apply parallel_refl.
      * apply parallel_ctxjmp; auto.
    + admit.
    + admit.
  - dependent destruction H1.
    + exists (bind b2 ts c2).
      * apply parallel_refl.
      * apply parallel_bind; auto.
    + destruct IHparallel2 with c3 as (c4, ?, ?); auto.
      (*
         The first reduction is [bind], the second is [ctxjmp], so...

                                          ->
               H[k<x>] { k<y> = c1 } ------------ b2 { k<y> = c2 }
                      |                             |
                      |                             |
                    | |                             | |
                    V |                             | V
                      |                             |
                      |                             |
            H[c3[x/y]] { k<y> = c3 } ------------- ???
                                          ->

         Where H[k<x>] -> b2,
                    c2 -> c4,
                    c3 -> c4.

         First we need to find an I such that b2 = I[k<x>]...

         We'll then know that:
           H[k<x>] -> I[k<x>]
         And we'll need to show that:
           H[c3[x/y]] -> I[c4[x/y]]

         Not sure how to do that...
      *)
      admit.
    + destruct IHparallel1 with b3 as (b4, ?, ?); auto.
      destruct IHparallel2 with c3 as (c4, ?, ?); auto.
      exists (bind b4 ts c4).
      * apply parallel_bind; auto.
      * apply parallel_bind; auto.
Admitted.

(*

(** ** Multi-step reduction *)

Definition star: relation pseudoterm :=
  clos_refl_trans _ (union _ cong step).

Hint Unfold star: cps.
Hint Unfold union: cps.
Hint Constructors clos_refl_trans: cps.
Notation "[ a =>* b ]" := (star a b)
  (at level 0, a, b at level 200): type_scope.

Lemma star_step:
  forall a b,
  [a => b] -> [a =>* b].
Proof.
  auto with cps.
Qed.

Hint Resolve star_step: cps.

Lemma star_cong:
  forall a b,
  [a == b] -> [a =>* b].
Proof.
  auto with cps.
Qed.

Hint Resolve star_cong: cps.

Lemma star_beta:
  forall xs ts c,
  length xs = length ts ->
  [bind (jump 0 xs) ts c =>* bind (apply_parameters xs 0 c) ts c].
Proof.
  auto with cps.
Qed.

Hint Resolve star_beta: cps.

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
  induction 1.
  - destruct H; auto with cps.
  - apply star_refl.
  - apply star_tran with (bind y ts c); auto.
Qed.

Hint Resolve star_bind_left: cps.

Lemma star_bind_right:
  forall b ts c1 c2,
  [c1 =>* c2] -> [bind b ts c1 =>* bind b ts c2].
Proof.
  induction 1.
  - destruct H; auto with cps.
  - apply star_refl.
  - apply star_tran with (bind b ts y); auto.
Qed.

Hint Resolve star_bind_right: cps.

(** ** Pseudoterm conversion *)

Definition conv: relation pseudoterm :=
  clos_refl_sym_trans _ (union _ cong step).

Hint Unfold conv: cps.
Notation "[ a <=> b ]" := (conv a b)
  (at level 0, a, b at level 200): type_scope.

Lemma conv_step:
  forall a b,
  [a => b] -> [a <=> b].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_step: cps.

Lemma conv_cong:
  forall a b,
  [a == b] -> [a <=> b].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_cong: cps.

Lemma conv_beta:
  forall xs ts c,
  length xs = length ts ->
  [bind (jump 0 xs) ts c <=> bind (apply_parameters xs 0 c) ts c].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_beta: cps.

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
  [a <=> b] -> [b <=> c] -> [a <=> c].
Proof.
  eauto with cps.
Qed.

Hint Resolve conv_tran: cps.

Lemma conv_bind_left:
  forall b1 b2 ts c,
  [b1 <=> b2] -> [bind b1 ts c <=> bind b2 ts c].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve conv_bind_left: cps.

Lemma conv_bind_right:
  forall b ts c1 c2,
  [c1 <=> c2] -> [bind b ts c1 <=> bind b ts c2].
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve conv_bind_right: cps.

Instance conv_is_equiv: Equivalence conv.
Proof.
  split.
  - exact conv_refl.
  - exact conv_symm.
  - exact conv_tran.
Defined.

(** *)

Hint Unfold transp: cps.

Lemma subterm_and_step_commute:
  commut _ subterm (transp _ step).
Proof.
  induction 1; eauto with cps.
Qed.

Lemma subterm_and_cong_commute:
  commut _ subterm (transp _ cong).
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
    [a == b] -> parallel b c -> [c == d] -> parallel a d.

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
  (* Case: parallel_cong. *)
  - rename c0 into x.
    apply parallel_cong with (subst x k b) (subst x k c).
    + apply subst_preserves_cong; auto.
    + apply IHparallel.
    + apply subst_preserves_cong; auto.
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
  (* Case: parallel_cong. *)
  - apply star_tran with c.
    + apply star_tran with b.
      * apply star_cong.
        assumption.
      * assumption.
    + apply star_cong.
      assumption.
Qed.

Hint Resolve star_parallel: cps.

*)

End STCC.
