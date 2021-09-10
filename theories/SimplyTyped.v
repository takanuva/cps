(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)
(** * The Simply Typed CPS Calculus *)

Require Import Lia.
Require Import List.
Require Import Arith.
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

(*
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
*)

(** ** Metatheory *)

Lemma pseudoterm_eq_dec:
  forall a b: pseudoterm,
  { a = b } + { a <> b }.
Proof.
  fix H 1.
  destruct a; destruct b; try (right; intro; discriminate).
  - left; reflexivity.
  - left; reflexivity.
  - left; reflexivity.
  - left; reflexivity.
  - destruct Nat.eq_dec with n n0.
    + left; congruence.
    + right; congruence.
  - destruct list_eq_dec with pseudoterm ts ts0.
    + exact H.
    + left; congruence.
    + right; congruence.
  - destruct list_eq_dec with pseudoterm xs xs0.
    + exact H.
    + destruct H with a b; try (right; congruence).
      left; congruence.
    + right; congruence.
  - destruct list_eq_dec with pseudoterm ts ts0.
    + exact H.
    + destruct H with a1 b1; try (right; congruence).
      destruct H with a2 b2; try (right; congruence).
      left; congruence.
    + right; congruence.
Qed.

Fixpoint traverse f k e: pseudoterm :=
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
    f k n
  | negation ts =>
    negation (map (traverse f k) ts)
  | jump x xs =>
    jump (traverse f k x) (map (traverse f k) xs)
  | bind b ts c =>
    bind (traverse f (S k) b) (map (traverse f k) ts)
      (traverse f (k + length ts) c)
  end.

Lemma traverse_bound:
  forall f k n,
  traverse f k (bound n) = f k n.
Proof.
  auto.
Qed.

Opaque traverse.

(* TODO: make rewrite database! *)

(** ** Lifting *)

Definition lift i: nat -> pseudoterm -> pseudoterm :=
  traverse (fun k n =>
    if le_gt_dec k n then
      bound (i + n)
    else
      bound n).

Lemma lift_distributes_over_negation:
  forall i k ts,
  lift i k (negation ts) =
    negation (map (lift i k) ts).
Proof.
  auto.
Qed.

Lemma lift_distributes_over_jump:
  forall i k x xs,
  lift i k (jump x xs) =
    jump (lift i k x) (map (lift i k) xs).
Proof.
  auto.
Qed.

Lemma lift_distributes_over_bind:
  forall i k b ts c,
  lift i k (bind b ts c) =
    bind (lift i (S k) b) (map (lift i k) ts) (lift i (k + length ts) c).
Proof.
  auto.
Qed.

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
  - unfold lift.
    rewrite traverse_bound.
    destruct (le_gt_dec k n); auto.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    f_equal; list induction over H.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    f_equal; auto.
    list induction over H.
Qed.

Lemma lift_bound_ge:
  forall i k n,
  k <= n -> lift i k n = i + n.
Proof.
  intros.
  unfold lift; rewrite traverse_bound.
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
  unfold lift; rewrite traverse_bound.
  destruct (le_gt_dec k n).
  (* Case: k <= n. *)
  - absurd (k <= n); auto with arith.
  (* Case: k > n. *)
  - reflexivity.
Qed.

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
  - destruct (le_gt_dec l n).
    + rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      f_equal; lia.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      reflexivity.
  (* Case: negation. *)
  - do 3 rewrite lift_distributes_over_negation.
    f_equal; list induction over H.
  (* Case: jump. *)
  - do 3 rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 3 rewrite lift_distributes_over_bind.
    f_equal; auto.
    + apply IHe1; lia.
    + list induction over H.
    + rewrite map_length.
      apply IHe2; lia.
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
  - destruct (le_gt_dec l n); destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      f_equal; lia.
    + absurd (k <= n); lia.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_lt; try lia.
      reflexivity.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      reflexivity.
  (* Case: negation. *)
  - do 4 rewrite lift_distributes_over_negation.
    f_equal; list induction over H.
  (* Case: jump. *)
  - do 4 rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 4 rewrite lift_distributes_over_bind.
    f_equal; auto.
    + replace (S (i + l)) with (i + S l); auto.
      apply IHe1; lia.
    + list induction over H.
    + do 2 rewrite map_length.
      rewrite plus_assoc_reverse.
      apply IHe2; lia.
Qed.

Lemma lift_lift_permutation_inverse:
  forall e i j k l,
  k <= l -> lift j (i + l) (lift i k e) = lift i k (lift j l e).
Proof.
  intros.
  symmetry.
  apply lift_lift_permutation; auto.
Qed.

Opaque lift.

(** ** Substitution *)

Definition subst y: nat -> pseudoterm -> pseudoterm :=
  traverse (fun k n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => bound (pred n)
    | inleft (right _) => lift k 0 y
    | inright _ => bound n
    end).

Lemma subst_distributes_over_negation:
  forall y k ts,
  subst y k (negation ts) =
    negation (map (subst y k) ts).
Proof.
  auto.
Qed.

Lemma subst_distributes_over_jump:
  forall y k x xs,
  subst y k (jump x xs) =
    jump (subst y k x) (map (subst y k) xs).
Proof.
  auto.
Qed.

Lemma subst_distributes_over_bind:
  forall y k b ts c,
  subst y k (bind b ts c) =
    bind (subst y (S k) b) (map (subst y k) ts) (subst y (k + length ts) c).
Proof.
  auto.
Qed.

Lemma subst_bound_gt:
  forall e k n,
  n > k -> subst e k n = pred n.
Proof.
  intros.
  unfold subst; rewrite traverse_bound.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  - reflexivity.
  - elim gt_irrefl with k; congruence.
  - absurd (k <= n); auto with arith.
Qed.

Lemma subst_bound_eq:
  forall e k n,
  n = k -> subst e k n = lift n 0 e.
Proof.
  destruct 1.
  unfold subst; rewrite traverse_bound.
  destruct (lt_eq_lt_dec n n) as [ [ ? | ? ] | ? ].
  - destruct (gt_irrefl n); auto.
  - reflexivity.
  - destruct (lt_irrefl n); auto.
Qed.

Lemma subst_bound_lt:
  forall e k n,
  n < k -> subst e k n = n.
Proof.
  intros.
  unfold subst; rewrite traverse_bound.
  destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
  - absurd (k <= n); auto with arith.
  - elim lt_irrefl with k; congruence.
  - reflexivity.
Qed.

Lemma lift_addition_distributes_over_subst:
  forall e y i p k,
  lift i (p + k) (subst y p e) = subst (lift i k y) p (lift i (S (p + k)) e).
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
  - destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct n; try lia.
      destruct (le_gt_dec (p + k) n).
      * rewrite lift_bound_ge; try lia.
        rewrite subst_bound_gt; try lia.
        rewrite lift_bound_ge; try lia.
        rewrite subst_bound_gt; try lia.
        f_equal; lia.
      * rewrite lift_bound_lt; auto with arith.
        rewrite subst_bound_gt; auto with arith.
        rewrite lift_bound_lt; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
    + destruct e.
      rewrite lift_bound_lt; try lia.
      rewrite subst_bound_eq; auto.
      rewrite subst_bound_eq; auto.
      apply lift_lift_permutation_inverse; lia.
    + rewrite lift_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; auto.
      rewrite lift_bound_lt; try lia.
      reflexivity.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    do 2 rewrite subst_distributes_over_negation.
    rewrite lift_distributes_over_negation.
    f_equal; list induction over H.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    do 2 rewrite subst_distributes_over_jump.
    rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    f_equal.
    + replace (S (p + k)) with (S p + k); try lia.
      apply IHe1.
    + list induction over H.
    + do 2 rewrite map_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (S (p + k) + length ts) with (S (p + length ts + k)); try lia.
      apply IHe2.
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
  forall e y i p k,
  p <= i + k ->
  k <= p -> subst y p (lift (S i) k e) = lift i k e.
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
  - destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      f_equal; lia.
    + rewrite lift_bound_lt; auto.
      rewrite lift_bound_lt; auto.
      rewrite subst_bound_lt; auto.
      lia.
  (* Case: negation. *)
  - do 2 rewrite lift_distributes_over_negation.
    rewrite subst_distributes_over_negation.
    f_equal; list induction over H.
  (* Case: jump. *)
  - do 2 rewrite lift_distributes_over_jump.
    rewrite subst_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 2 rewrite lift_distributes_over_bind.
    rewrite subst_distributes_over_bind.
    f_equal.
    + apply IHe1; lia.
    + list induction over H.
    + rewrite map_length.
      apply IHe2; lia.
Qed.

Lemma lift_and_subst_commute:
  forall e y i p k,
  k <= p ->
  lift i k (subst y p e) = subst y (i + p) (lift i k e).
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
  - destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ]; simpl.
    + rewrite lift_bound_ge; try lia.
      rewrite subst_bound_gt; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite subst_bound_gt; try lia.
      f_equal; lia.
    + rewrite lift_bound_ge; try lia.
      rewrite subst_bound_eq; try lia.
      rewrite subst_bound_eq; try lia.
      apply lift_lift_simplification; lia.
    + rewrite subst_bound_lt; auto.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge; auto.
        rewrite subst_bound_lt; try lia.
        reflexivity.
      * rewrite lift_bound_lt; auto.
        rewrite subst_bound_lt; auto.
        lia.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    do 2 rewrite subst_distributes_over_negation.
    rewrite lift_distributes_over_negation.
    f_equal; list induction over H.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    do 2 rewrite subst_distributes_over_jump.
    rewrite lift_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    f_equal.
    + replace (S (i + p)) with (i + S p); try lia.
      apply IHe1; lia.
    + list induction over H.
    + do 2 rewrite map_length.
      replace (i + p + length ts) with (i + (p + length ts)); try lia.
      apply IHe2; lia.
Qed.

Hint Resolve lift_and_subst_commute: cps.

Lemma subst_addition_distributes_over_itself:
  forall e y z p k,
  subst y (p + k) (subst z p e) = subst (subst y k z) p (subst y (S (p + k)) e).
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
  - destruct (lt_eq_lt_dec p n) as [ [ ? | ? ] | ? ].
    + destruct n; try lia.
      rewrite subst_bound_gt; try lia.
      destruct (lt_eq_lt_dec (p + k) n) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_gt; try lia.
        rewrite subst_bound_gt; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
      * rewrite subst_bound_eq; try lia.
        rewrite subst_bound_eq; try lia.
        rewrite subst_lift_simplification; try lia.
        reflexivity.
      * rewrite subst_bound_lt; try lia.
        rewrite subst_bound_lt; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
    + rewrite subst_bound_eq; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_eq; try lia.
      rewrite lift_and_subst_commute; try lia.
      f_equal; lia.
    + rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      reflexivity.
  (* Case: negation. *)
  - do 4 rewrite subst_distributes_over_negation.
    f_equal; list induction over H.
  (* Case: jump. *)
  - do 4 rewrite subst_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 4 rewrite subst_distributes_over_bind.
    f_equal.
    + replace (S (p + k)) with (S p + k); try lia.
      apply IHe1; lia.
    + list induction over H.
    + do 2 rewrite map_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (S (p + k) + length ts) with (S (p + length ts + k)); try lia.
      apply IHe2; lia.
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
  - rename n0 into m.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      constructor; lia.
    + rewrite lift_bound_lt; auto.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    constructor.
    dependent induction H.
    + simpl; constructor.
    + inversion_clear H1.
      inversion_clear H3.
      simpl; auto with cps.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    inversion_clear H0.
    constructor; auto.
    dependent induction H; auto.
    inversion_clear H3.
    simpl; auto.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    inversion_clear H0.
    constructor.
    + apply IHe1; auto with arith.
    + clear e1 e2 IHe1 IHe2 H2 H4.
      dependent induction H; auto.
      inversion_clear H3.
      simpl; constructor; auto.
    + rewrite map_length.
      apply IHe2; auto with arith.
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
  - rename n0 into m.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      constructor; lia.
    + rewrite lift_bound_lt; auto.
      constructor; lia.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    constructor.
    dependent induction H; simpl; auto.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    constructor; auto.
    dependent induction H; simpl; auto.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    constructor.
    + apply IHe1; lia.
    + dependent induction H; simpl; auto.
    + rewrite map_length.
      apply IHe2; lia.
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
  - rename n0 into m.
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_gt; auto.
      constructor; lia.
    + rewrite subst_bound_eq; auto.
      apply lifting_more_than_n_makes_not_free_in_n; lia.
    + rewrite subst_bound_lt; auto.
  (* Case: negation. *)
  - rewrite subst_distributes_over_negation.
    constructor; auto.
    dependent induction H; simpl.
    + constructor.
    + inversion_clear H1.
      inversion_clear H3.
      auto with cps.
  (* Case: jump. *)
  - rewrite subst_distributes_over_jump.
    inversion_clear H0.
    constructor; auto.
    dependent induction H; auto.
    inversion_clear H3.
    simpl; auto.
  (* Case: bind. *)
  - rewrite subst_distributes_over_bind.
    inversion_clear H0.
    constructor.
    + apply IHe1; auto with arith.
    + clear e1 e2 IHe1 IHe2 H2 H4.
      dependent induction H; auto.
      inversion_clear H3.
      simpl; constructor; auto.
    + rewrite map_length.
      apply IHe2; auto with arith.
Qed.

(******************************************************************************)
(* TODO: proofs are starting to get a bit more complicated after this point,  *)
(* so add a few comments and documentation before I forget what I'm doing.    *)
(******************************************************************************)

(** *)

Fixpoint apply_parameters (xs: list pseudoterm) (k: nat) (e: pseudoterm) :=
  match xs with
  | [] => e
  | x :: xs => apply_parameters xs k (subst x (k + length xs) e)
  end.

Hint Unfold apply_parameters: cps.

Definition switch_bindings (k: nat) (e: pseudoterm) :=
  subst 1 k (lift 1 (2 + k) e).

Hint Unfold switch_bindings: cps.

Fixpoint sequence (high: bool) (i: nat) :=
  match i with
  | 0 => []
  | S j => bound (if high then i else j) :: sequence high j
  end.

Hint Unfold sequence: cps.

Definition high_sequence: nat -> list pseudoterm :=
  sequence true.

Hint Unfold high_sequence: cps.

Definition low_sequence: nat -> list pseudoterm :=
  sequence false.

Hint Unfold low_sequence: cps.

Definition right_cycle (i: nat) (k: nat) e :=
  apply_parameters (bound 0 :: high_sequence i) k (lift (S i) (S i + k) e).

Hint Unfold right_cycle: cps.

(* TODO: add a depth parameter here... *)

Definition remove_closest_binding e :=
  subst 0 0 e.

(* TODO: rename "at_any_depth" to "addition", or the other way around *)

Lemma lift_distributes_over_apply_parameters_at_any_depth:
  forall xs i k p e,
  lift i (p + k) (apply_parameters xs p e) =
    apply_parameters (map (lift i k) xs) p (lift i (p + length xs + k) e).
Proof.
  induction xs; simpl; intros.
  (* Case: nil. *)
  - replace (p + 0) with p; auto.
  (* Case: cons. *)
  - rewrite IHxs.
    rewrite lift_addition_distributes_over_subst.
    rewrite map_length.
    do 3 f_equal; lia.
Qed.

Lemma lift_distributes_over_apply_parameters:
  forall i xs k e,
  lift i k (apply_parameters xs 0 e) =
    apply_parameters (map (lift i k) xs) 0 (lift i (length xs + k) e).
Proof.
  intros.
  apply lift_distributes_over_apply_parameters_at_any_depth with (p := 0).
Qed.

Lemma subst_distributes_over_apply_parameters_at_any_depth:
  forall xs x k p e,
  subst x (p + k) (apply_parameters xs p e) =
    apply_parameters (map (subst x k) xs) p (subst x (p + length xs + k) e).
Proof.
  induction xs; simpl; intros.
  (* Case: nil. *)
  - replace (p + 0) with p; auto.
  (* Case: cons. *)
  - rewrite IHxs.
    rewrite subst_addition_distributes_over_itself.
    rewrite map_length.
    do 3 f_equal; lia.
Qed.

Lemma subst_distributes_over_apply_parameters:
  forall xs x k e,
  subst x k (apply_parameters xs 0 e) =
    apply_parameters (map (subst x k) xs) 0 (subst x (length xs + k) e).
Proof.
  intros.
  apply subst_distributes_over_apply_parameters_at_any_depth with (p := 0).
Qed.

Lemma switch_bindings_behavior:
  forall e k,
  switch_bindings k e = right_cycle 1 k e.
Proof.
  unfold switch_bindings.
  unfold right_cycle; simpl.
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
  - destruct (le_gt_dec (S (S k)) n).
    + rewrite lift_bound_ge; auto.
      rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      rewrite subst_bound_gt; try lia.
      rewrite subst_bound_gt; try lia.
      reflexivity.
    + rewrite lift_bound_lt; auto.
      rewrite lift_bound_lt; auto.
      destruct (lt_eq_lt_dec n k) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_lt; auto.
        rewrite subst_bound_lt; try lia.
        rewrite subst_bound_lt; auto with arith.
      * rewrite subst_bound_eq; auto.
        rewrite subst_bound_lt; try lia.
        rewrite subst_bound_eq; eauto with arith.
        lia.
      * rewrite subst_bound_gt; auto.
        rewrite subst_bound_eq; try lia.
        rewrite lift_bound_ge; auto.
        rewrite subst_bound_gt; auto.
        lia.
  (* Case: negation. *)
  - do 2 rewrite lift_distributes_over_negation.
    do 3 rewrite subst_distributes_over_negation.
    f_equal.
    list induction over H.
  (* Case: jump. *)
  - do 2 rewrite lift_distributes_over_jump.
    do 3 rewrite subst_distributes_over_jump.
    f_equal; auto.
    list induction over H.
  (* Case: bind. *)
  - do 2 rewrite lift_distributes_over_bind.
    do 3 rewrite subst_distributes_over_bind.
    f_equal.
    + apply IHe1.
    + list induction over H.
    + do 3 rewrite map_length.
      replace (k + 0 + length ts) with (k + length ts + 0); try lia.
      replace (k + 1 + length ts) with (k + length ts + 1); try lia.
      apply IHe2.
Qed.

Lemma lift_preserved_by_useless_subst:
  forall e i k p x,
  not_free_in p e ->
  lift i (p + k) (subst x p e) = subst x p (lift i (p + S k) e).
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
  - destruct (lt_eq_lt_dec n p) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_lt; auto.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite subst_bound_lt; auto.
    + exfalso.
      inversion H.
      congruence.
    + rewrite subst_bound_gt; auto.
      destruct (le_gt_dec n (p + k)).
      * rewrite lift_bound_lt; try lia.
        rewrite lift_bound_lt; try lia.
        rewrite subst_bound_gt; auto.
      * rewrite lift_bound_ge; try lia.
        rewrite lift_bound_ge; try lia.
        rewrite subst_bound_gt; try lia.
        f_equal; lia.
  (* Case: negation. *)
  - rewrite lift_distributes_over_negation.
    do 2 rewrite subst_distributes_over_negation.
    rewrite lift_distributes_over_negation.
    inversion_clear H0.
    f_equal.
    dependent induction H; simpl.
    + reflexivity.
    + inversion_clear H1.
      f_equal; auto.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    do 2 rewrite subst_distributes_over_jump.
    rewrite lift_distributes_over_jump.
    inversion_clear H0.
    f_equal; auto.
    dependent induction H; simpl.
    + reflexivity.
    + inversion_clear H2.
      f_equal; auto.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    inversion_clear H0.
    simpl; f_equal.
    + replace (S (p + k)) with (S p + k); try lia.
      replace (S (p + S k)) with (S p + S k); try lia.
      apply IHe1; auto.
    + clear IHe1 IHe2 H1 H3.
      dependent induction H; simpl.
      * reflexivity.
      * inversion_clear H2.
        f_equal; auto.
    + do 2 rewrite map_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHe2; auto.
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
  - destruct (lt_eq_lt_dec n p) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_lt; auto.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; auto.
    + exfalso.
      inversion H; auto.
    + rewrite subst_bound_gt; auto.
      destruct (lt_eq_lt_dec n (p + S k)) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_lt; try lia.
        rewrite subst_bound_lt; try lia.
        rewrite subst_bound_gt; auto.
      * rewrite subst_bound_eq; try lia.
        rewrite subst_bound_eq; try lia.
        replace n with (S (p + k)) at 2; try lia.
        rewrite subst_lift_simplification; try lia.
        f_equal; lia.
      * rewrite subst_bound_gt; try lia.
        rewrite subst_bound_gt; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
  (* Case: negation. *)
  - do 4 rewrite subst_distributes_over_negation.
    inversion_clear H0.
    f_equal.
    dependent induction H; simpl.
    + reflexivity.
    + inversion_clear H1.
      f_equal; auto.
  (* Case: jump. *)
  - do 4 rewrite subst_distributes_over_jump.
    inversion_clear H0.
    f_equal; auto.
    dependent induction H; simpl.
    + reflexivity.
    + inversion_clear H2.
      f_equal; auto.
  (* Case: bind. *)
  - do 4 rewrite subst_distributes_over_bind.
    inversion_clear H0.
    simpl; f_equal.
    + replace (S (p + k)) with (S p + k); try lia.
      replace (S (p + S k)) with (S p + S k); try lia.
      apply IHe1; auto.
    + clear IHe1 IHe2 H1 H3.
      dependent induction H; simpl.
      * reflexivity.
      * inversion_clear H2.
        f_equal; auto.
    + do 2 rewrite map_length.
      replace (p + k + length ts) with (p + length ts + k); try lia.
      replace (p + S k + length ts) with (p + length ts + S k); try lia.
      apply IHe2; auto.
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
  forall n b,
  sequence b (S n) = bound (if b then S n else n) :: sequence b n.
Proof.
  auto.
Qed.

Lemma lifting_over_n_doesnt_change_sequence_n:
  forall n i k (b: bool),
  map (lift i ((if b then 1 else 0) + (n + k))) (sequence b n) = sequence b n.
Proof.
  induction n; intros.
  (* Case: zero. *)
  - reflexivity.
  (* Case: succ. *)
  - rewrite sequence_succ.
    rewrite map_cons.
    f_equal.
    + rewrite lift_bound_lt; auto.
      destruct b; lia.
    + replace (S n + k) with (n + S k); auto.
      lia.
Qed.

Lemma lifting_over_n_doesnt_change_high_sequence_n:
  forall n i k,
  map (lift i (S (n + k))) (high_sequence n) = high_sequence n.
Proof.
  intros.
  apply lifting_over_n_doesnt_change_sequence_n with (b := true).
Qed.

Lemma lifting_over_n_doesnt_change_low_sequence_n:
  forall n i k,
  map (lift i (n + k)) (low_sequence n) = low_sequence n.
Proof.
  intros.
  apply lifting_over_n_doesnt_change_sequence_n with (b := false).
Qed.

Lemma substing_over_n_doesnt_change_sequence_n:
  forall n x k (b: bool),
  map (subst x ((if b then 1 else 0) + (n + k))) (sequence b n) = sequence b n.
Proof.
  induction n; intros.
  (* Case: zero. *)
  - reflexivity.
  (* Case: succ. *)
  - rewrite sequence_succ.
    rewrite map_cons.
    f_equal.
    + rewrite subst_bound_lt; auto.
      destruct b; lia.
    + replace (S n + k) with (n + S k); auto.
      lia.
Qed.

Lemma substing_over_n_doesnt_change_high_sequence_n:
  forall n x k,
  map (subst x (S (n + k))) (high_sequence n) = high_sequence n.
Proof.
  intros.
  apply substing_over_n_doesnt_change_sequence_n with (b := true).
Qed.

Lemma substing_over_n_doesnt_change_low_sequence_n:
  forall n x k,
  map (subst x (n + k)) (low_sequence n) = low_sequence n.
Proof.
  intros.
  apply substing_over_n_doesnt_change_sequence_n with (b := false).
Qed.

Lemma length_sequence:
  forall n b,
  length (sequence b n) = n.
Proof.
  induction n; simpl; auto.
Qed.

(** ** Relations *)

Notation "'rt' ( R )" := (clos_refl_trans _ R)
  (format "'rt' ( R )"): type_scope.
Notation "'rst' ( R )" := (clos_refl_sym_trans _ R)
  (format "'rst' ( R )"): type_scope.

Hint Unfold transp: cps.
Hint Constructors clos_trans: cps.
Hint Constructors clos_refl_trans: cps.
Hint Constructors clos_refl_sym_trans: cps.

Definition confluent {T} R: Prop :=
  commut T R (transp T R).

Lemma strip_lemma:
  forall {T} R,
  forall confluency: confluent R,
  commut T (clos_trans T R) (transp T R).
Proof.
  compute.
  induction 2; intros.
  (* Case: step. *)
  - destruct confluency with y x z as (w, ?, ?); auto.
    exists w; auto.
    constructor; auto.
  (* Case: tran. *)
  - rename z0 into w.
    destruct IHclos_trans1 with w as (v, ?, ?); auto.
    destruct IHclos_trans2 with v as (u, ?, ?); auto.
    exists u; auto.
    apply t_trans with v; auto.
Qed.

Lemma transitive_closure_preserves_confluency:
  forall {T} R,
  forall confluency: confluent R,
  confluent (clos_trans T R).
Proof.
  compute.
  induction 2; intros.
  (* Case: step. *)
  - destruct @strip_lemma with T R z x y as (w, ?, ?); auto.
    exists w; auto.
    constructor; auto.
  (* Case: tran. *)
  - rename z0 into w.
    destruct IHclos_trans1 with w as (v, ?, ?); auto.
    destruct IHclos_trans2 with v as (u, ?, ?); auto.
    exists u; eauto with cps.
Qed.

Definition church_rosser {T} (R: relation T): Prop :=
  forall x y,
  rst(R) x y ->
  exists2 z,
  rt(R) x z & rt(R) y z.

Lemma confluency_implies_church_rosser:
  forall {T} R,
  forall confluency: @confluent T rt(R),
  church_rosser R.
Proof.
  compute; intros.
  induction H.
  (* Case: step. *)
  - exists y; auto with cps.
  (* Case: refl. *)
  - exists x; auto with cps.
  (* Case: symm. *)
  - destruct IHclos_refl_sym_trans as (z, ?, ?).
    exists z; auto.
  (* Case: tran. *)
  - destruct IHclos_refl_sym_trans1 as (w, ?, ?).
    destruct IHclos_refl_sym_trans2 as (v, ?, ?).
    destruct confluency with w y v as (u, ?, ?); auto with cps.
    exists u; eauto with cps.
Qed.

(** ** Axiomatic semantics *)

Definition JMP (R: relation pseudoterm): Prop :=
  forall xs ts c,
  length xs = length ts ->
  R (bind (jump 0 xs) ts c)
    (bind (apply_parameters xs 0 (lift 1 (length xs) c)) ts c).

Hint Unfold JMP: cps.

(* My first intuition was to make the redex as [jump (length ts + k) _], by
   using a bound var (that is not a parameter), but this is too restrictive for
   our "high-order" definition of pseudoterms; lifting k instead solves this,
   and it properly captures the notion of (ETA) for actual terms. *)

Definition ETA (R: relation pseudoterm): Prop :=
  forall b ts k,
  R (bind b ts (jump (lift (length ts) 0 k) (low_sequence (length ts))))
    (subst k 0 b).

Hint Unfold ETA: cps.

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

Definition DISTR (R: relation pseudoterm): Prop :=
  forall b ms m ns n,
  Forall (not_free_in 0) ms ->
  R (bind (bind b ms m) ns n)
    (bind (bind
      (switch_bindings 0 b)
      (map (lift 1 0) ns)
        (lift 1 (length ns) n))
      (map remove_closest_binding ms) (bind
        (right_cycle (length ms) 0 m)
        (map (lift (length ms) 0) ns)
          (lift (length ms) (length ns) n))).

Hint Unfold DISTR: cps.

Definition CONTR (R: relation pseudoterm): Prop :=
  forall b ts c,
  R (bind (bind b (map (lift 1 0) ts) (lift 1 (length ts) c)) ts c)
    (bind (remove_closest_binding b) ts c).

Hint Unfold CONTR: cps.

Definition GC (R: relation pseudoterm): Prop :=
  forall b ts c,
  not_free_in 0 b ->
  R (bind b ts c) (remove_closest_binding b).

Hint Unfold GC: cps.

Definition LEFT (R: relation pseudoterm): Prop :=
  forall b1 b2 ts c,
  R b1 b2 -> R (bind b1 ts c) (bind b2 ts c).

Hint Unfold LEFT: cps.

Definition RIGHT (R: relation pseudoterm): Prop :=
  forall b ts c1 c2,
  R c1 c2 -> R (bind b ts c1) (bind b ts c2).

Hint Unfold RIGHT: cps.

(* As of now, I'm still unsure whether we'll need a directed, one-step struct
   relation or just it's congruence version. Just to be sure, we'll define it
   anyway. *)

Inductive struct: relation pseudoterm :=
  | struct_jmp:
    JMP struct
  | struct_distr:
    DISTR struct
  | struct_contr:
    CONTR struct
  | struct_eta:
    ETA struct
  | struct_gc:
    GC struct
  | struct_bind_left:
    LEFT struct
  | struct_bind_right:
    RIGHT struct.

Hint Constructors struct: cps.

(* We'll just define our structural congruence as the smallest relation closed
   under the [struct] rules above. *)

Notation cong := rst(struct).
Notation "[ a == b ]" := (cong a b)
  (at level 0, a, b at level 200): type_scope.

Lemma cong_refl:
  forall e,
  [e == e].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_refl: cps.

Lemma cong_sym:
  forall a b,
  [a == b] -> [b == a].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_sym: cps.

Lemma cong_trans:
  forall a b c,
  [a == b] -> [b == c] -> [a == c].
Proof.
  eauto with cps.
Qed.

Hint Resolve cong_trans: cps.

Lemma cong_struct:
  forall a b,
  struct a b -> [a == b].
Proof.
  auto with cps.
Qed.

Hint Resolve cong_struct: cps.

Lemma cong_jmp:
  JMP cong.
Proof.
  auto with cps.
Qed.

Hint Resolve cong_jmp: cps.

Lemma cong_distr:
  DISTR cong.
Proof.
  auto with cps.
Qed.

Hint Resolve cong_distr: cps.

Lemma cong_contr:
  CONTR cong.
Proof.
  auto with cps.
Qed.

Hint Resolve cong_contr: cps.

Lemma cong_eta:
  ETA cong.
Proof.
  auto with cps.
Qed.

Lemma cong_gc:
  GC cong.
Proof.
  auto with cps.
Qed.

Hint Resolve cong_gc: cps.

Lemma cong_bind_left:
  LEFT cong.
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve cong_bind_left: cps.

Lemma cong_bind_right:
  RIGHT cong.
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve cong_bind_right: cps.

Instance cong_is_equiv: Equivalence cong.
Proof.
  split.
  - exact cong_refl.
  - exact cong_sym.
  - exact cong_trans.
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
  forall e n i k p,
  k > n ->
  lift i (p + k) (right_cycle n p e) = right_cycle n p (lift i (p + k) e).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_distributes_over_apply_parameters_at_any_depth.
  do 2 f_equal.
  - induction n.
    + reflexivity.
    + rewrite sequence_succ with (b := true); fold high_sequence.
      rewrite map_cons; f_equal.
      * apply lift_bound_lt; auto.
      * apply IHn; lia.
  - rewrite lift_addition_distributes_over_subst; f_equal.
    + rewrite lift_bound_lt; auto.
      lia.
    + rewrite length_sequence with (b := true).
      symmetry.
      rewrite lift_lift_permutation; try lia.
      f_equal; lia.
Qed.

Lemma lift_and_switch_bindings_commute:
  forall i k e,
  lift i (S (S k)) (switch_bindings 0 e) =
    switch_bindings 0 (lift i (S (S k)) e).
Proof.
  intros.
  do 2 rewrite switch_bindings_behavior.
  apply lift_and_right_cycle_commute with (p := 0) (n := 1); lia.
Qed.

Lemma subst_and_right_cycle_commute:
  forall e n x k p,
  k > n ->
  subst x (p + k) (right_cycle n p e) =
    right_cycle n p (subst x (p + k) e).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite subst_distributes_over_apply_parameters_at_any_depth.
  f_equal.
  - induction n.
    + reflexivity.
    + rewrite sequence_succ with (b := true); fold high_sequence.
      rewrite map_cons; f_equal.
      * apply subst_bound_lt; auto.
      * apply IHn; lia.
  - rewrite subst_addition_distributes_over_itself; f_equal.
    + rewrite subst_bound_lt; auto.
      lia.
    + rewrite length_sequence with (b := true).
      rewrite lift_and_subst_commute; try lia.
      f_equal; lia.
Qed.

Lemma subst_and_switch_bindings_commute:
  forall x k e,
  subst x (S (S k)) (switch_bindings 0 e) =
    switch_bindings 0 (subst x (S (S k)) e).
Proof.
  intros.
  do 2 rewrite switch_bindings_behavior.
  apply subst_and_right_cycle_commute with (p := 0) (n := 1); lia.
Qed.

Lemma struct_jmp_helper:
  forall xs ts c x1 x2 x3,
  x1 = apply_parameters xs 0 (lift 1 (length xs) c) ->
  x2 = ts ->
  x3 = c ->
  length xs = length ts ->
  struct (bind (jump 0 xs) ts c) (bind x1 x2 x3).
Proof.
  intros.
  rewrite H, H0, H1.
  apply struct_jmp; auto.
Qed.

Lemma struct_distr_helper:
  forall b ms m ns n x1 x2 x3 x4 x5 x6 x7,
  x1 = switch_bindings 0 b ->
  x2 = lift 1 (length ns) n ->
  x3 = right_cycle (length ms) 0 m ->
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

Lemma struct_eta_helper:
  forall b ts k x1 x2,
  x1 = jump (lift (length ts) 0 k) (low_sequence (length ts)) ->
  x2 = subst k 0 b ->
  struct (bind b ts x1) x2.
Proof.
  intros.
  rewrite H, H0.
  apply struct_eta.
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
  (* Case: struct_jmp. *)
  - do 2 rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump.
    apply struct_jmp_helper.
    + rewrite lift_distributes_over_apply_parameters.
      f_equal.
      rewrite map_length.
      symmetry.
      rewrite lift_lift_permutation; try lia.
      f_equal; lia.
    + reflexivity.
    + reflexivity.
    + do 2 rewrite map_length; auto.
  (* Case: struct_distr. *)
  - do 5 rewrite lift_distributes_over_bind.
    apply struct_distr_helper.
    + apply lift_and_switch_bindings_commute.
    + symmetry.
      do 2 rewrite map_length.
      rewrite lift_lift_permutation.
      * reflexivity.
      * lia.
    + do 2 rewrite map_length.
      apply lift_and_right_cycle_commute with (p := 0).
      lia.
    + do 4 rewrite map_length.
      symmetry.
      rewrite lift_lift_permutation.
      * f_equal; lia.
      * lia.
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
        f_equal; lia.
    + dependent induction H; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite remove_closest_binding_and_lift_commute; auto.
    + induction ms; simpl; auto.
      inversion_clear H.
      constructor; auto.
      apply lifting_over_n_preserves_not_free_in_n; auto with arith.
  (* Case: struct_contr. *)
  - do 3 rewrite lift_distributes_over_bind.
    apply struct_contr_helper.
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
  (* Case: struct_eta. *)
  - rename k into j, k0 into k.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump.
    eapply struct_eta_helper.
    + replace (k + length ts) with (length ts + k); auto with arith.
      rewrite map_length; f_equal.
      * symmetry.
        apply lift_lift_permutation; auto with arith.
      * apply lifting_over_n_doesnt_change_low_sequence_n.
    + apply lift_distributes_over_subst.
  (* Case: struct_gc. *)
  - rewrite lift_distributes_over_bind.
    rewrite remove_closest_binding_and_lift_commute; auto.
    apply struct_gc.
    apply lifting_over_n_preserves_not_free_in_n; auto with arith.
  (* Case: struct_bind_left. *)
  - do 2 rewrite lift_distributes_over_bind.
    auto with cps.
  (* Case: struct_bind_right. *)
  - do 2 rewrite lift_distributes_over_bind.
    auto with cps.
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
  (* Case: struct_jmp. *)
  - do 2 rewrite subst_distributes_over_bind.
    rewrite subst_distributes_over_jump.
    apply struct_jmp_helper.
    + rewrite subst_distributes_over_apply_parameters.
      f_equal.
      rewrite map_length.
      rewrite lift_and_subst_commute; try lia.
      f_equal; lia.
    + reflexivity.
    + reflexivity.
    + do 2 rewrite map_length; auto.
  (* Case: struct_distr. *)
  - do 5 rewrite subst_distributes_over_bind.
    apply struct_distr_helper.
    + apply subst_and_switch_bindings_commute.
    + do 2 rewrite map_length.
      rewrite lift_and_subst_commute.
      * reflexivity.
      * lia.
    + do 2 rewrite map_length.
      apply subst_and_right_cycle_commute with (p := 0).
      lia.
    + do 4 rewrite map_length.
      rewrite lift_and_subst_commute.
      * f_equal; lia.
      * lia.
    + induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite lift_and_subst_commute; auto with arith.
    + do 2 rewrite map_length.
      induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite lift_and_subst_commute; auto with arith.
        f_equal; lia.
    + dependent induction H; simpl.
      * reflexivity.
      * f_equal; auto.
        rewrite remove_closest_binding_and_subst_commute; auto.
    + induction ms; simpl; auto.
      inversion_clear H.
      constructor; auto.
      apply substing_over_n_preserves_not_free_in_n; auto with arith.
  (* Case: struct_contr. *)
  - do 3 rewrite subst_distributes_over_bind.
    apply struct_contr_helper.
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
  (* Case: struct_eta. *)
  - rename k into j, k0 into k.
    rewrite subst_distributes_over_bind.
    rewrite subst_distributes_over_jump.
    eapply struct_eta_helper.
    + replace (k + length ts) with (length ts + k); auto with arith.
      rewrite map_length; f_equal.
      * symmetry.
        apply lift_and_subst_commute; auto with arith.
      * apply substing_over_n_doesnt_change_low_sequence_n.
    + apply subst_distributes_over_itself.
  (* Case: struct_gc. *)
  - rewrite subst_distributes_over_bind.
    rewrite remove_closest_binding_and_subst_commute; auto.
    apply struct_gc.
    apply substing_over_n_preserves_not_free_in_n; auto with arith.
  (* Case: struct_bind_left. *)
  - do 2 rewrite subst_distributes_over_bind.
    auto with cps.
  (* Case: struct_bind_right. *)
  - do 2 rewrite subst_distributes_over_bind.
    auto with cps.
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
  forall xs k a b,
  [a == b] ->
  [apply_parameters xs k a == apply_parameters xs k b].
Proof.
  induction xs; eauto with cps.
Qed.

Hint Resolve cong_apply_parameters: cps.

Lemma cong_right_cycle:
  forall a b,
  [a == b] ->
  forall n k,
  [right_cycle n k a == right_cycle n k b].
Proof.
  unfold right_cycle; auto with cps.
Qed.

Hint Resolve cong_right_cycle: cps.

(******************************************************************************)

(* TODO: move the following lemmas to their correct places. *)

Arguments lift i k e: simpl nomatch.
Arguments subst y k e: simpl nomatch.

Inductive item {T} (e: T): list T -> nat -> Prop :=
  | item_car:
    forall cdr, item e (cons e cdr) 0
  | item_cdr:
    forall car cdr n, item e cdr n -> item e (cons car cdr) (S n).

Hint Constructors item: cps.

(* TODO: review names of the following lemmas. *)

Lemma item_insert_tail:
  forall {T} xs ys x k,
  @item T x xs k -> @item T x (xs ++ ys) k.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
Qed.

Lemma item_ignore_tail:
  forall {T} xs x ys k,
  length xs > k ->
  @item T x (xs ++ ys) k -> @item T x xs k.
Proof.
  induction xs; intros.
  - inversion H.
  - simpl in H, H0 |- *.
    destruct k.
    + inversion_clear H0; auto.
      constructor.
    + inversion_clear H0.
      constructor.
      eapply IHxs; eauto.
      lia.
Qed.

Lemma item_insert_head:
  forall {T} xs ys x k,
  k >= length xs ->
  @item T x ys (k - length xs) -> @item T x (xs ++ ys) k.
Proof.
  induction xs; intros.
  - simpl.
    replace (k - length []) with k in H0; auto.
    simpl; lia.
  - simpl in H, H0 |- *.
    destruct k.
    + inversion H.
    + constructor.
      apply IHxs; auto.
      lia.
Qed.

Lemma item_ignore_head:
  forall {T} xs x ys k,
  k >= length xs ->
  @item T x (xs ++ ys) k -> @item T x ys (k - length xs).
Proof.
  induction xs; intros.
  - simpl in H0 |- *.
    replace (k - 0) with k; auto with arith.
  - simpl in H, H0 |- *.
    destruct k.
    + inversion H.
    + inversion_clear H0.
      apply IHxs; auto.
      lia.
Qed.

Lemma apply_parameters_lift_e_equals_e:
  forall xs k e,
  apply_parameters xs k (lift (length xs) k e) = e.
Proof.
  induction xs; intros.
  - apply lift_zero_e_equals_e.
  - simpl.
    rewrite subst_lift_simplification; try lia.
    apply IHxs.
Qed.

Lemma apply_parameters_bound_lt:
  forall xs n,
  length xs > n ->
  forall x,
  item x (rev xs) n -> apply_parameters xs 0 (bound n) = x.
Proof.
  induction xs.
  - intros.
    inversion H0.
  - simpl; intros.
    destruct (le_gt_dec (length xs) n).
    + cut (n = length xs); try lia; intro.
      rewrite subst_bound_eq; auto.
      apply item_ignore_head in H0.
      * rewrite rev_length in H0.
        rewrite H1 in H0 |- *.
        replace (length xs - length xs) with 0 in H0; try lia.
        inversion_clear H0.
        apply apply_parameters_lift_e_equals_e.
      * rewrite rev_length; auto.
    + rewrite subst_bound_lt; auto.
      apply IHxs; auto.
      eapply item_ignore_tail; eauto.
      rewrite rev_length; auto.
Qed.

Lemma apply_parameters_bound_ge:
  forall xs n,
  length xs <= n -> apply_parameters xs 0 (bound n) = n - length xs.
Proof.
  induction xs; intros.
  - simpl; f_equal; lia.
  - simpl in H |- *.
    rewrite subst_bound_gt; auto.
    rewrite IHxs; try lia.
    f_equal; lia.
Qed.

Lemma high_sequence_rev_lifts_by_one:
  forall n k,
  n < k -> item (bound (S n)) (rev (high_sequence k)) n.
Proof.
  intros.
  induction k.
  - inversion H.
  - simpl.
    destruct (le_gt_dec k n).
    + apply item_insert_head.
      * rewrite rev_length.
        rewrite length_sequence with (b := true); auto.
      * rewrite rev_length.
        rewrite length_sequence with (b := true).
        replace n with k; try lia.
        replace (k - k) with 0; try lia.
        constructor.
    + apply item_insert_tail.
      apply IHk; lia.
Qed.

Lemma right_cycle_bound_lt:
  forall k n,
  n < k -> right_cycle k 0 (bound n) = S n.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_lt; try lia.
  rewrite length_sequence with (b := true).
  rewrite subst_bound_lt; auto.
  apply apply_parameters_bound_lt.
  - rewrite length_sequence with (b := true); auto.
  - apply high_sequence_rev_lifts_by_one; auto.
Qed.

Lemma right_cycle_bound_eq:
  forall k n,
  n = k -> right_cycle k 0 (bound n) = 0.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_lt; try lia.
  rewrite length_sequence with (b := true).
  rewrite subst_bound_eq; auto.
  rewrite lift_bound_ge; auto.
  rewrite apply_parameters_bound_ge.
  - rewrite length_sequence with (b := true).
    f_equal; lia.
  - rewrite length_sequence with (b := true).
    lia.
Qed.

Lemma right_cycle_bound_gt:
  forall k n,
  n > k -> right_cycle k 0 (bound n) = n.
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_bound_ge; try lia.
  rewrite length_sequence with (b := true).
  rewrite subst_bound_gt; try lia.
  rewrite apply_parameters_bound_ge; simpl.
  - rewrite length_sequence with (b := true).
    f_equal; lia.
  - rewrite length_sequence with (b := true).
    lia.
Qed.

(* Float left: L { M } { N } == L { N } { M } if n doesn't appear in M. *)

Definition FLOAT_LEFT (R: relation pseudoterm): Prop :=
  forall b ms m ns n,
  not_free_in (length ms) m ->
  Forall (not_free_in 0) ms ->
  R (bind (bind b ms m) ns n)
    (bind (bind
     (switch_bindings 0 b)
     (map (lift 1 0) ns) (lift 1 (length ns) n))
     (map (subst 0 0) ms) (subst 0 (length ms) m)).

Lemma cong_float_left:
  FLOAT_LEFT cong.
Proof.
  unfold FLOAT_LEFT; intros.
  eapply cong_trans.
  - apply cong_distr; auto.
  - apply cong_bind_right.
    apply cong_struct; apply struct_gc_helper.
    + admit.
    + admit.
Admitted.

(* Float right: L { M } { N } == L { M { N } } if n doesn't appear in L. *)

Definition FLOAT_RIGHT (R: relation pseudoterm): Prop :=
  forall b ms m ns n,
  not_free_in 1 b ->
  Forall (not_free_in 0) ms ->
  R (bind (bind b ms m) ns n)
    (bind
      (* TODO: we could use [remove_binding 1 b] or something like that here,
         though it of course will result in the same term. *)
      (remove_closest_binding (switch_bindings 0 b))
      (map remove_closest_binding ms) (bind
        (right_cycle (length ms) 0 m)
        (map (lift (length ms) 0) ns) (lift (length ms) (length ns) n))).

Lemma cong_float_right:
  FLOAT_RIGHT cong.
Proof.
  unfold FLOAT_RIGHT; intros.
  eapply cong_trans.
  - apply cong_distr; auto.
  - apply cong_bind_left.
    apply cong_gc.
    rewrite switch_bindings_behavior.
    admit.
Admitted.

(******************************************************************************)

(* TODO: move the following lemmas to the correct places! This is a mess! *)

Lemma apply_parameters_distributes_over_jump:
  forall xs k j ys,
  apply_parameters xs k (jump j ys) =
    jump (apply_parameters xs k j) (map (apply_parameters xs k) ys).
Proof.
  induction xs; intros.
  - simpl; f_equal.
    list induction over ys.
  - simpl.
    rewrite subst_distributes_over_jump.
    rewrite IHxs; f_equal.
    list induction over ys.
Qed.

Lemma right_cycle_distributes_over_jump:
  forall n p k xs,
  right_cycle n p (jump k xs) =
    jump (right_cycle n p k) (map (right_cycle n p) xs).
Proof.
  intros.
  unfold right_cycle; simpl.
  rewrite lift_distributes_over_jump.
  rewrite subst_distributes_over_jump.
  rewrite apply_parameters_distributes_over_jump; simpl.
  f_equal.
  list induction over xs.
Qed.

Lemma switch_bindings_is_involutive:
  forall e k,
  switch_bindings k (switch_bindings k e) = e.
Proof.
  unfold switch_bindings.
  induction e using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (le_gt_dec (2 + k) n); simpl.
    + rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      rewrite lift_bound_ge; auto.
      rewrite subst_bound_gt; try lia.
      f_equal; lia.
    + rewrite lift_bound_lt; try lia.
      destruct (lt_eq_lt_dec n k) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_lt; auto.
        rewrite lift_bound_lt; auto.
        rewrite subst_bound_lt; auto.
      * rewrite subst_bound_eq; auto.
        rewrite lift_bound_ge; auto.
        rewrite lift_bound_lt; try lia.
        rewrite subst_bound_gt; try lia.
        f_equal; lia.
      * rewrite subst_bound_gt; auto.
        rewrite lift_bound_lt; try lia.
        rewrite subst_bound_eq; try lia.
        rewrite lift_bound_ge; auto.
        f_equal; lia.
  - rewrite lift_distributes_over_negation.
    rewrite subst_distributes_over_negation.
    rewrite lift_distributes_over_negation.
    rewrite subst_distributes_over_negation.
    f_equal.
    list induction over H.
    apply H.
  - rewrite lift_distributes_over_jump.
    rewrite subst_distributes_over_jump.
    rewrite lift_distributes_over_jump.
    rewrite subst_distributes_over_jump.
    f_equal.
    + apply IHe.
    + list induction over H.
      apply H.
  - rewrite lift_distributes_over_bind.
    rewrite subst_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite subst_distributes_over_bind.
    f_equal.
    + apply IHe1.
    + list induction over H.
      apply H.
    + do 3 rewrite map_length.
      apply IHe2.
Qed.

Lemma cong_eq:
  forall a b,
  a = b -> [a == b].
Proof.
  intros.
  destruct H.
  apply cong_refl.
Qed.

Lemma right_cycle_low_sequence_n_equals_high_sequence_n:
  forall n m,
  m >= n -> map (right_cycle m 0) (low_sequence n) = high_sequence n.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl.
    rewrite IHn; auto with arith.
    rewrite sequence_succ with (b := true); f_equal.
    rewrite right_cycle_bound_lt; auto.
Qed.

Lemma apply_parameters_distributes_over_negation:
  forall xs k ts,
  apply_parameters xs k (negation ts) =
    negation (map (apply_parameters xs k) ts).
Proof.
  induction xs; intros.
  - simpl; f_equal.
    list induction over ts.
  - simpl.
    rewrite subst_distributes_over_negation.
    rewrite IHxs.
    f_equal.
    list induction over ts.
Qed.

Lemma apply_parameters_distributes_over_bind:
  forall xs k b ts c,
  apply_parameters xs k (bind b ts c) =
    bind (apply_parameters xs (S k) b)
      (map (apply_parameters xs k) ts)
        (apply_parameters xs (k + length ts) c).
Proof.
  induction xs; intros.
  - simpl; f_equal.
    list induction over ts.
  - simpl.
    rewrite subst_distributes_over_bind.
    rewrite IHxs.
    rewrite map_length.
    f_equal.
    + list induction over ts.
    + do 2 f_equal; lia.
Qed.

(* I have no idea what to call this one... *)

Lemma foo:
  forall e k n,
  apply_parameters (high_sequence n) k (lift (S n) (k + n) e) = lift 1 k e.
Proof.
  induction e using pseudoterm_deepind; intros.
  - simpl.
    induction n; auto.
  - simpl.
    induction n; auto.
  - simpl.
    induction n; auto.
  - simpl.
    induction n; auto.
  - rename n0 into m.
    destruct (le_gt_dec (k + m) n).
    + rewrite lift_bound_ge; auto.
      rewrite lift_bound_ge; try lia.
      admit.
    + rewrite lift_bound_lt; auto.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge; auto.
        admit.
      * rewrite lift_bound_lt; auto.
        admit.
  - do 2 rewrite lift_distributes_over_negation.
    rewrite apply_parameters_distributes_over_negation.
    f_equal.
    list induction over H.
  - do 2 rewrite lift_distributes_over_jump.
    rewrite apply_parameters_distributes_over_jump.
    f_equal.
    + apply IHe.
    + list induction over H.
  - do 2 rewrite lift_distributes_over_bind.
    rewrite apply_parameters_distributes_over_bind.
    f_equal.
    + apply IHe1.
    + list induction over H.
    + rewrite map_length.
      replace (k + n + length ts) with (k + length ts + n); try lia.
      apply IHe2.
Admitted.

(*
  Turns out the rule (CONTR) is derivable!
  To show that L { m<x> = M } { m'<x> = M } == L[m/m'] { m<x> = M }...

  In a named version of the calculus, start with symmetry... then:

    1)                           L[m/m'] { m<x> = M } ==      (by LEFT, ETA-1)
    2)                L { m'<y> = m<y> } { m<x> = M } ==      (by DISTR)
    3)   L { m<x> = M } { m'<y> = m<y> { m<x> = M } } ==      (by RIGHT, JMP)
    4) L { m<x> = M } { m'<y> = M[y/x] { m<x> = M } } ==      (by RIGHT, GC)
    5)              L { m<x> = M } { m'<y> = M[y/x] } ==      (by ALPHA)
    6)                   L { m<x> = M } { m'<x> = M }

  This is a bit bureaucratic when using de Bruijn indexes; we of course don't
  need an alpha conversion, but we'll need a (FLOAT-LEFT) in the end to fix the
  bindings' positions, "undoing" the (DISTR) we did, but it should still work.
*)

Lemma cong_contr_derivable:
  CONTR cong.
Proof.
  unfold CONTR; intros.
  apply cong_sym.
  (* Is there a more elegant way? *)
  eapply cong_trans;
    [| eapply cong_trans;
      [| eapply cong_trans;
        [| eapply cong_trans;
          [| eapply cong_trans ] ] ] ].
  - apply cong_bind_left.
    apply cong_sym.
    apply cong_eta with (ts := map (lift 1 0) ts).
  - apply cong_distr.
    induction ts; simpl.
    + constructor.
    + constructor; auto.
      apply lifting_more_than_n_makes_not_free_in_n; auto.
  - apply cong_bind_right.
    rewrite map_length.
    rewrite lift_bound_ge; auto.
    replace (length ts + 0) with (length ts); auto.
    rewrite right_cycle_distributes_over_jump.
    rewrite right_cycle_bound_eq; auto.
    apply cong_jmp.
    do 2 rewrite map_length.
    apply length_sequence.
  - apply cong_bind_right.
    apply cong_gc.
    rewrite right_cycle_low_sequence_n_equals_high_sequence_n; auto.
    rewrite length_sequence with (b := true).
    rewrite lift_lift_simplification; try lia.
    rewrite foo.
    apply lifting_more_than_n_makes_not_free_in_n; auto.
  - (* The term is in the form [(switch_bindings 0 b) { M } { N }] now, as we
       have changed [b] with the (DISTR) call above. Note that when applying
       (FLOAT-LEFT) here we will change the term into [b { M } { N }]: only [b]
       will actually change, as [M] is already equal to [lift 1 0 N] here (thus
       moving [N] left makes it equal to [M], and moving [M] right makes it
       equal to [N]). *)
    apply cong_float_left.
    + rewrite map_length.
      apply lifting_more_than_n_makes_not_free_in_n; lia.
    + induction ts; simpl.
      * constructor.
      * constructor; auto.
        apply lifting_more_than_n_makes_not_free_in_n; auto.
  - (* The term is finally in the form [b { M } { N }], which is what we want,
       but we still need to prove that as the term form is a bit different. *)
    apply cong_eq; f_equal.
    + f_equal.
      * apply switch_bindings_is_involutive.
      * list induction over ts.
        unfold remove_closest_binding.
        rewrite subst_lift_simplification; auto.
        rewrite lift_zero_e_equals_e; auto.
      * do 2 rewrite map_length; f_equal.
        rewrite right_cycle_low_sequence_n_equals_high_sequence_n; auto.
        rewrite length_sequence with (b := true).
        rewrite lift_lift_simplification; try lia.
        rewrite foo.
        unfold remove_closest_binding.
        rewrite subst_lift_simplification; auto.
        apply lift_zero_e_equals_e.
    + list induction over ts.
      rewrite subst_lift_simplification; auto.
      apply lift_zero_e_equals_e.
    + rewrite map_length.
      rewrite subst_lift_simplification; auto.
      apply lift_zero_e_equals_e.
Qed.

(** ** One-hole contexts. *)

Inductive context: Set :=
  | context_hole
  | context_left (b: context) (ts: list pseudoterm) (c: pseudoterm)
  | context_right (b: pseudoterm) (ts: list pseudoterm) (c: context).

Lemma context_eq_dec:
  forall h r: context,
  { h = r } + { h <> r }.
Proof.
  decide equality.
  - apply pseudoterm_eq_dec.
  - apply list_eq_dec.
    apply pseudoterm_eq_dec.
  - apply list_eq_dec.
    apply pseudoterm_eq_dec.
  - apply pseudoterm_eq_dec.
Qed.

Reserved Notation "# h" (at level 0, right associativity, format "# h").

Fixpoint context_depth (h: context): nat :=
  match h with
  | context_hole => 0
  | context_left b ts c => S #b
  | context_right b ts c => #c + length ts
  end

where "# h" := (context_depth h).

Fixpoint apply_context (h: context) (e: pseudoterm): pseudoterm :=
  match h with
  | context_hole => e
  | context_left b ts c => bind (apply_context b e) ts c
  | context_right b ts c => bind b ts (apply_context c e)
  end.

Coercion apply_context: context >-> Funclass.

Fixpoint compose_context (h: context) (r: context): context :=
  match h with
  | context_hole => r
  | context_left b ts c => context_left (compose_context b r) ts c
  | context_right b ts c => context_right b ts (compose_context c r)
  end.

Lemma compose_context_is_sound:
  forall h r e,
  compose_context h r e = h (r e).
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - rewrite IHh.
    reflexivity.
  - rewrite IHh.
    reflexivity.
Qed.

Lemma compose_context_depth:
  forall h r,
  #(compose_context h r) = #h + #r.
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite IHh; auto.
  - rewrite IHh; lia.
Qed.

Inductive static: context -> Prop :=
  | static_hole:
    static context_hole
  | static_left:
    forall h ts c,
    static h -> static (context_left h ts c).

Hint Constructors static: cps.

Lemma static_compose_context:
  forall h r,
  static h -> static r -> static (compose_context h r).
Proof.
  induction 1; simpl; intros.
  - assumption.
  - auto with cps.
Qed.

Definition nonstatic h: Prop :=
  ~static h.

Lemma context_static_nonstatic_dec:
  forall h,
  { static h } + { nonstatic h }.
Proof.
  induction h.
  (* Case: context_hole. *)
  - left; constructor.
  (* Case: context_left. *)
  - destruct IHh; simpl.
    + left; constructor.
      assumption.
    + right; intro.
      inversion_clear H.
      apply n; assumption.
  (* Case: context_right. *)
  - right; intro.
    inversion H.
Qed.

Lemma nonstatic_ind:
  forall P: context -> Prop,
  (* Recursion stops when a right context is found; we never reach a hole. *)
  forall f1: (forall b ts h, P (context_right b ts h)),
  forall f2: (forall h ts c, P h -> P (context_left h ts c)),
  forall h, nonstatic h -> P h.
Proof.
  induction h; intro.
  (* Case: context_hole. *)
  - exfalso; apply H.
    constructor.
  (* Case: context_left. *)
  - apply f2; apply IHh.
    intro; apply H.
    constructor.
    assumption.
  (* Case: context_right. *)
  - apply f1.
Qed.

Lemma context_is_injective:
  forall h r: context,
  h = r ->
  forall a b,
  h a = r b -> a = b.
Proof.
  induction h; destruct r; intros; try discriminate.
  - assumption.
  - dependent destruction H0.
    eauto.
  - dependent destruction H0.
    eauto.
Qed.

Inductive same_path: relation context :=
  | same_path_hole:
    same_path context_hole context_hole
  | same_path_left:
    forall h r ts c1 c2,
    same_path h r ->
    same_path (context_left h ts c1) (context_left r ts c2)
  | same_path_right:
    forall b1 b2 ts h r,
    same_path h r ->
    same_path (context_right b1 ts h) (context_right b2 ts r).

Hint Constructors same_path: cps.

Lemma same_path_refl:
  forall h,
  same_path h h.
Proof.
  induction h.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Hint Resolve same_path_refl: cps.

Lemma same_path_sym:
  forall h r,
  same_path h r -> same_path r h.
Proof.
  induction h; destruct r; inversion 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Hint Resolve same_path_sym: cps.

Lemma same_path_trans:
  forall h r s,
  same_path h r -> same_path r s -> same_path h s.
Proof.
  intros.
  generalize dependent s.
  induction H; intros.
  - assumption.
  - inversion_clear H0.
    constructor; auto.
  - inversion_clear H0.
    constructor; auto.
Qed.

Hint Resolve same_path_trans: cps.

Instance same_path_is_equiv: Equivalence same_path.
Proof.
  split.
  - exact same_path_refl.
  - exact same_path_sym.
  - exact same_path_trans.
Defined.

Lemma context_same_path_implies_same_depth:
  forall h r,
  same_path h r -> #h = #r.
Proof.
  induction 1.
  - reflexivity.
  - simpl; lia.
  - simpl; lia.
Qed.

Hint Resolve context_same_path_implies_same_depth: cps.
Hint Rewrite context_same_path_implies_same_depth: cps.

(*
  The intuition behind the following technical lemma is as follow:

  We have two contexts H and R there are different, but we do have jumps n<xs>
  and m<ys> such that H[n<xs>] = R[m<ys>]. This implies that m<ys> is a subterm
  of H, and n<xs> is a subterm of R, i.e., H and R "mark" two different jumps in
  the same term. We want to, given a term x, rebuild the context H, but we will
  exchange the m<ys> in it by the term x, thus making S[n<xs>] equal to R[x],
  and do the respective thing for R.

  This is useful for proving that redexes are non-overlapping.
*)
Lemma context_difference:
  forall h r: context,
  h <> r ->
  forall n m xs ys,
  h (jump n xs) = r (jump m ys) ->
  forall x,
  exists s: context,
       r x = s (jump n xs)
    /\ same_path h s
    /\ forall y,
       exists u: context,
            h y = u (jump m ys)
         /\ same_path r u
         /\ s y = u x.
Proof.
  induction h; destruct r; simpl; intros.
  (* Case: (context_hole, context_hole). *)
  - exfalso; auto.
  (* Case: (context_hole, context_left). *)
  - discriminate.
  (* Case: (context_hole, context_right). *)
  - discriminate.
  (* Case: (context_left, context_hole). *)
  - discriminate.
  (* Case: (context_left, context_left). *)
  - dependent destruction H0.
    edestruct IHh with (r := r) as (s, ?).
    + congruence.
    + eassumption.
    + exists (context_left s ts0 c0); simpl.
      intuition.
      * f_equal; eassumption.
      * edestruct H3 as (u, ?).
        exists (context_left u ts0 c0); simpl.
        intuition; f_equal; eauto.
  (* Case: (context_left, context_right). *)
  - clear IHh.
    dependent destruction H0.
    eexists (context_left h ts0 (r x)).
    intuition.
    eexists (context_right (h y) ts0 r); intuition.
  (* Case: (context_right, context_hole). *)
  - discriminate.
  (* Case: (context_right, context_left). *)
  - clear IHh.
    dependent destruction H0.
    eexists (context_right (r x) ts0 h).
    intuition.
    eexists (context_left r ts0 (h y)); intuition.
  (* Case: (context_right, context_right). *)
  - dependent destruction H0.
    edestruct IHh with (r := r) as (s, ?).
    + congruence.
    + eassumption.
    + exists (context_right b0 ts0 s); simpl.
      intuition.
      * f_equal; eassumption.
      * edestruct H3 as (u, ?).
        exists (context_right b0 ts0 u); simpl.
        intuition; f_equal; eauto.
Qed.

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

Reserved Notation "[ a => b ]" (at level 0, a, b at level 200).

Inductive step: relation pseudoterm :=
  | step_ctxjmp:
    forall (h: context),
    forall xs ts c,
    length xs = length ts ->
    [bind (h (jump #h xs)) ts c =>
      bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c]
  | step_bind_left:
    LEFT step
  | step_bind_right:
    (* TODO: we probably should require that the bound continuation appears free
       in the left side, so that (GC) won't mess things up. *)
    RIGHT step

where "[ a => b ]" := (step a b): type_scope.

Hint Constructors step: cps.

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
  apply step_ctxjmp with (h := context_left context_hole ?[ts] ?[c]); auto.
Qed.

Lemma step_jmp:
  JMP step.
Proof.
  unfold JMP; intros.
  replace c with (lift 0 (length ts) c) at 2.
  - rewrite lift_lift_simplification; try lia.
    apply step_ctxjmp with (h := context_hole); auto.
  - apply lift_zero_e_equals_e.
Qed.

Hint Resolve step_jmp: cps.

Lemma context_lift:
  forall (h: context) i k,
  exists2 r: context,
  #h = #r & forall e,
  lift i k (h e) = r (lift i (#h + k) e).
Proof.
  induction h; simpl; intros.
  - exists context_hole; auto.
  - destruct IHh with i (S k) as (r, ?H, ?H).
    eexists (compose_context (context_left context_hole _ _) r).
    + simpl; auto.
    + intros; rewrite lift_distributes_over_bind.
      simpl; f_equal.
      rewrite H0; f_equal.
      f_equal; lia.
  - destruct IHh with i (k + length ts) as (r, ?H, ?H).
    eexists (compose_context (context_right _ (map _ ts) context_hole) r).
    + simpl.
      rewrite H; f_equal.
      rewrite map_length; auto.
    + intros; rewrite lift_distributes_over_bind.
      simpl; f_equal.
      rewrite H0; f_equal.
      f_equal; lia.
Qed.

Lemma context_subst:
  forall (h: context) y k,
  exists2 r: context,
  #h = #r & forall e,
  subst y k (h e) = r (subst y (#h + k) e).
Proof.
  induction h; simpl; intros.
  - exists context_hole; auto.
  - destruct IHh with y (S k) as (r, ?H, ?H).
    eexists (compose_context (context_left context_hole _ _) r).
    + simpl; auto.
    + intros; rewrite subst_distributes_over_bind.
      simpl; f_equal.
      rewrite H0; f_equal.
      f_equal; lia.
  - destruct IHh with y (k + length ts) as (r, ?H, ?H).
    eexists (compose_context (context_right _ (map _ ts) context_hole) r).
    + simpl.
      rewrite H; f_equal.
      rewrite map_length; auto.
    + intros; rewrite subst_distributes_over_bind.
      simpl; f_equal.
      rewrite H0; f_equal.
      f_equal; lia.
Qed.

Lemma step_ctxjmp_helper:
  forall (h r: context),
  r = h ->
  forall xs ts c,
  length xs = length ts ->
  forall n,
  n = #h ->
  forall a,
  a = jump n xs ->
  forall b,
  b = apply_parameters xs 0 (lift (S n) (length ts) c) ->
  forall ts',
  ts' = ts ->
  forall c',
  c' = c ->
  [bind (h a) ts c =>
    bind (r b) ts' c'].
Proof.
  intros.
  rewrite H, H2, H3, H4, H5, H1.
  apply step_ctxjmp.
  assumption.
Qed.

Lemma step_lift:
  forall a b,
  [a => b] ->
  forall i k,
  [lift i k a => lift i k b].
Proof.
  induction 1; intros.
  - do 2 rewrite lift_distributes_over_bind.
    edestruct context_lift as (r, ?H, ?H).
    do 2 rewrite H1.
    rewrite lift_distributes_over_jump.
    rewrite lift_bound_lt; try lia.
    rewrite lift_distributes_over_apply_parameters.
    eapply step_ctxjmp_helper with (xs := map _ xs).
    + reflexivity.
    + do 2 rewrite map_length.
      assumption.
    + reflexivity.
    + f_equal; auto.
    + f_equal; symmetry.
      rewrite lift_lift_permutation.
      * f_equal; try lia.
        f_equal; auto.
        apply map_length.
      * rewrite map_length; lia.
    + reflexivity.
    + reflexivity.
  - do 2 rewrite lift_distributes_over_bind.
    apply step_bind_left.
    apply IHstep.
  - do 2 rewrite lift_distributes_over_bind.
    apply step_bind_right.
    apply IHstep.
Qed.

Lemma step_subst:
  forall a b,
  [a => b] ->
  forall y k,
  [subst y k a => subst y k b].
Proof.
  induction 1; intros.
  - do 2 rewrite subst_distributes_over_bind.
    edestruct context_subst as (r, ?H, ?H).
    do 2 rewrite H1.
    rewrite subst_distributes_over_jump.
    rewrite subst_bound_lt; try lia.
    rewrite subst_distributes_over_apply_parameters.
    eapply step_ctxjmp_helper with (xs := map _ xs).
    + reflexivity.
    + do 2 rewrite map_length.
      assumption.
    + reflexivity.
    + f_equal; auto.
    + f_equal; symmetry.
      rewrite lift_and_subst_commute.
      * f_equal; try lia.
        f_equal; auto.
        apply map_length.
      * rewrite map_length; lia.
    + reflexivity.
    + reflexivity.
  - do 2 rewrite subst_distributes_over_bind.
    apply step_bind_left.
    apply IHstep.
  - do 2 rewrite subst_distributes_over_bind.
    apply step_bind_right.
    apply IHstep.
Qed.

Lemma step_apply_parameters:
  forall xs k a b,
  [a => b] ->
  [apply_parameters xs k a => apply_parameters xs k b].
Proof.
  induction xs; intros.
  - simpl.
    assumption.
  - simpl.
    apply IHxs.
    apply step_subst.
    assumption.
Qed.

(*
  This lemma shows that "free jumps" are preserved in redexes. If we have a
  context H, and the term H[k<xs>] reduces to a term e, given that k is free in
  the hole of H, then e will keep the subterm k<xs>, i.e., there is a R such
  that e = R[k<xs>] and both R and H will bind the same variables in their
  respective holes.
*)
Lemma step_noninterference:
  forall h: context,
  forall n,
  n >= #h ->
  forall xs e,
  [h (jump n xs) => e] ->
  exists2 r: context,
  e = r (jump n xs) & same_path h r.
Proof.
  induction h; simpl; intros.
  (* Case: context_hole. *)
  - inversion H0.
  (* Case: context_left. *)
  - dependent destruction H0.
    + rename h0 into r.
      assert (h <> r).
      * destruct 1.
        apply context_is_injective in x; auto.
        inversion x; lia.
      * edestruct context_difference as (s, (?, ?)); eauto.
        eexists (context_left s ts c); intuition.
        simpl; f_equal; eassumption.
    + destruct IHh with n xs b2; eauto with arith.
      rewrite H1.
      eexists (context_left x ts c); auto with cps.
    + eexists (context_left h ts c2); auto with cps.
  (* Case: context_right. *)
  - dependent destruction H0.
    + rename h0 into r.
      eexists (context_right _ ts h).
      * simpl; f_equal.
      * auto with cps.
    + eexists (context_right b2 ts h); auto with cps.
    + destruct IHh with n xs c2; eauto with arith.
      rewrite H1.
      eexists (context_right b ts x); auto with cps.
Qed.

(*
Lemma step_redex_inv:
  forall P: pseudoterm -> Prop,
  forall (h: context) xs ts c e,
  forall f1: P (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c)))
                  ts c),
  forall f2: (forall r, #h = #r -> P (bind (r (jump #h xs)) ts c)),
  forall f3: (forall c2, [c => c2] -> P (bind (h (jump #h xs)) ts c2)),
  [bind (h (jump #h xs)) ts c => e] -> P e.
Proof.
  intros.
  dependent destruction H.
  - rename h0 into r.
    destruct context_eq_dec with h r.
    + destruct e.
      apply context_is_injective in x; auto.
      dependent destruction x.
      exact f1.
    + edestruct context_difference as (s, (?, (?, _))); eauto.
      erewrite H0.
      apply f2; auto.
  - destruct step_noninterference with h xs b2 as (r, ?, ?); auto.
    rewrite H0.
    apply f2; auto.
  - apply f3; auto.
Qed.
*)

(** ** Multi-step reduction *)

Notation star := rt(step).
Notation "[ a =>* b ]" := (star a b)
  (at level 0, a, b at level 200): type_scope.

Lemma star_step:
  forall a b,
  [a => b] -> [a =>* b].
Proof.
  auto with cps.
Qed.

Hint Resolve star_step: cps.

Lemma star_ctxjmp:
  forall h: context,
  forall xs ts c,
  length xs = length ts ->
  [bind (h (jump #h xs)) ts c =>*
    bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c].
Proof.
  auto with cps.
Qed.

Hint Resolve star_ctxjmp: cps.

Lemma star_refl:
  forall e,
  [e =>* e].
Proof.
  auto with cps.
Qed.

Hint Resolve star_refl: cps.

Lemma star_trans:
  forall a b c,
  [a =>* b] -> [b =>* c] -> [a =>* c].
Proof.
  eauto with cps.
Qed.

Hint Resolve star_trans: cps.

Lemma star_bind_left:
  LEFT star.
Proof.
  induction 1.
  - destruct H; auto with cps.
  - apply star_refl.
  - eapply star_trans; eauto.
Qed.

Hint Resolve star_bind_left: cps.

Lemma star_bind_right:
  RIGHT star.
Proof.
  induction 1.
  - destruct H; auto with cps.
  - apply star_refl.
  - eapply star_trans; eauto.
Qed.

Hint Resolve star_bind_right: cps.

(** ** Reduction convertibility *)

Notation conv := rst(step).
Notation "[ a <=> b ]" := (conv a b)
  (at level 0, a, b at level 200): type_scope.

Lemma conv_step:
  forall a b,
  [a => b] -> [a <=> b].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_step: cps.

Lemma conv_ctxjmp:
  forall h: context,
  forall xs ts c,
  length xs = length ts ->
  [bind (h (jump #h xs)) ts c <=>
    bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_ctxjmp: cps.

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

Lemma conv_sym:
  forall a b,
  [a <=> b] -> [b <=> a].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_sym: cps.

Lemma conv_trans:
  forall a b c,
  [a <=> b] -> [b <=> c] -> [a <=> c].
Proof.
  eauto with cps.
Qed.

Hint Resolve conv_trans: cps.

Lemma conv_bind_left:
  LEFT conv.
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve conv_bind_left: cps.

Lemma conv_bind_right:
  RIGHT conv.
Proof.
  induction 1; eauto with cps.
Qed.

Hint Resolve conv_bind_right: cps.

Instance conv_is_equiv: Equivalence conv.
Proof.
  split.
  - exact conv_refl.
  - exact conv_sym.
  - exact conv_trans.
Defined.

(** ** Beta reduction **)

Fixpoint beta ys k e: pseudoterm :=
  match e with
  | jump (bound n) xs =>
    (* If n >= k... *)
    match ge_dec n k with
    | left _ =>
      (* And n < k + |ys|... *)
      match lt_dec (n - k) (length ys) with
      | left _ =>
        (* Then there IS an y in ys for us. *)
        let y := nth (n - k) ys void in
        (* Almost sure we should lift by S n... *)
        apply_parameters xs 0 (lift (S n) (length xs) y)
      | right _ =>
        (* Out of range... *)
        jump n xs
      end
    | right _ =>
      (* Out of range... *)
      jump n xs
    end
  | bind b ts c =>
    bind (beta ys (S k) b) ts (beta ys (k + length ts) c)
  | _ =>
    e
  end.

Example ex4: pseudoterm :=
  (bind (bind
    (jump 0 [bound 2; bound 3])
    [base; base]
      (jump 6 [bound 3; bound 0]))
    [base; negation [base; base]; base]
      (jump 1 [bound 3; bound 0])).

Goal [ex3 => ex4].
Proof.
  apply step_ctxjmp with (h := context_right _ [_; _] context_hole); auto.
Qed.

Goal
  match ex1 with
  | bind b ts c =>
    bind (beta [c] 0 b) ts c = ex4
  | _ =>
    False
  end.
Proof.
  reflexivity.
Qed.

Lemma beta_distributes_over_bind:
  forall ys k b ts c,
  beta ys k (bind b ts c) =
    bind (beta ys (S k) b) ts (beta ys (k + length ts) c).
Proof.
  auto.
Qed.

Definition BETA (R: relation pseudoterm): Prop :=
  forall b ts c,
  R (bind b ts c) (bind (beta [c] 0 b) ts c).

Lemma star_beta:
  BETA star.
Proof.
  unfold BETA; intros.
  (* By induction on the number of free jumps to 0 in the original term,
     excluding any new introduced jumps, plus noninterference. *)
  admit.
Admitted.

Lemma conv_beta:
  BETA conv.
Proof.
  unfold BETA; intros.
  apply conv_star.
  apply star_beta.
Qed.

(** ** Parallel reduction *)

Inductive parallel: relation pseudoterm :=
  | parallel_refl:
    forall e,
    parallel e e
  | parallel_ctxjmp:
    forall h r xs ts c1 c2,
    same_path h r ->
    length xs = length ts ->
    (* Expect H and R to have the same hole to avoid reducing a copied jump. *)
    parallel (h (jump #h xs)) (r (jump #r xs)) ->
    parallel c1 c2 ->
    parallel (bind (h (jump #h xs)) ts c1)
      (bind (r (apply_parameters xs 0 (lift (S #r) (length ts) c2))) ts c2)
  | parallel_bind:
    forall b1 b2 ts c1 c2,
    parallel b1 b2 -> parallel c1 c2 ->
    parallel (bind b1 ts c1) (bind b2 ts c2).

Hint Constructors parallel: cps.

Lemma parallel_step:
  forall a b,
  [a => b] -> parallel a b.
Proof.
  induction 1.
  - eapply parallel_ctxjmp; auto.
    + apply same_path_refl.
    + apply parallel_refl.
    + apply parallel_refl.
  - apply parallel_bind; auto.
    apply parallel_refl.
  - apply parallel_bind; auto.
    apply parallel_refl.
Qed.

Hint Resolve parallel_step: cps.

Lemma star_parallel:
  forall a b,
  parallel a b -> [a =>* b].
Proof.
  induction 1.
  - apply star_refl.
  - eapply star_trans.
    + apply star_bind_left.
      eassumption.
    + eapply star_trans.
      * apply star_bind_right.
        eassumption.
      * apply star_ctxjmp.
        assumption.
  - eapply star_trans.
    + apply star_bind_left.
      eassumption.
    + apply star_bind_right.
      assumption.
Qed.

Hint Resolve star_parallel: cps.

Lemma parallel_lift:
  forall a b,
  parallel a b ->
  forall i k,
  parallel (lift i k a) (lift i k b).
Proof.
  induction 1; intros.
  - apply parallel_refl.
  - simpl.
    admit.
  - do 2 rewrite lift_distributes_over_bind.
    apply parallel_bind; auto.
Admitted.

Lemma parallel_subst:
  forall a b,
  parallel a b ->
  forall x k,
  parallel (subst x k a) (subst x k b).
Proof.
  induction 1; intros.
  - apply parallel_refl.
  - simpl.
    admit.
  - do 2 rewrite subst_distributes_over_bind.
    apply parallel_bind; auto.
Admitted.

Lemma parallel_apply_parameters:
  forall xs k a b,
  parallel a b ->
  parallel (apply_parameters xs k a) (apply_parameters xs k b).
Proof.
  induction xs; simpl; intros.
  - assumption.
  - apply IHxs.
    apply parallel_subst; auto.
Qed.

Lemma parallel_context:
  forall h: context,
  forall a b,
  parallel a b -> parallel (h a) (h b).
Proof.
  induction h; simpl; intros.
  - assumption.
  - apply parallel_bind; auto.
    apply parallel_refl.
  - apply parallel_bind; auto.
    apply parallel_refl.
Qed.

Lemma parallel_noninterference:
  forall h: context,
  forall n,
  n >= #h ->
  forall xs e,
  parallel (h (jump n xs)) e ->
  exists2 r: context,
  e = r (jump n xs) & same_path h r.
Proof.
  intros.
  apply star_parallel in H0.
  induction H0 using clos_refl_trans_ind_left.
  - exists h; auto with cps.
  - destruct IHclos_refl_trans.
    rewrite H2 in H1.
    destruct step_noninterference with x n xs z.
    + replace #x with #h; auto with cps.
    + assumption.
    + eauto with cps.
Qed.

(** ** Confluency *)

Lemma parallel_is_confluent:
  confluent parallel.
Proof.
  induction 1; unfold transp; intros.
  - exists z.
    + assumption.
    + apply parallel_refl.
  - dependent destruction H3.
    + eexists (bind (r _) ts c2).
      * apply parallel_refl.
      * apply parallel_ctxjmp; auto.
    + unfold transp in * |- *.
      admit.
    + unfold transp in *.
      admit.
  - dependent destruction H1.
    + exists (bind b2 ts c2).
      * apply parallel_refl.
      * apply parallel_bind; auto.
    + unfold transp in *.
      admit.
    + destruct IHparallel1 with b3 as (b4, ?, ?); auto.
      destruct IHparallel2 with c3 as (c4, ?, ?); auto.
      eexists (bind b4 ts c4); auto with cps.
Admitted.

Lemma transitive_parallel_is_confluent:
  confluent (clos_trans _ parallel).
Proof.
  apply transitive_closure_preserves_confluency.
  exact parallel_is_confluent.
Qed.

Lemma transitive_parallel_and_star_are_equivalent:
  forall a b,
  [a =>* b] <-> clos_trans _ parallel a b.
Proof.
  split; induction 1; eauto with cps.
Qed.

Theorem star_is_confluent:
  confluent star.
Proof.
  compute; intros.
  (* We apply a simple strip lemma here. *)
  destruct transitive_parallel_is_confluent with x y z as (w, ?, ?).
  - apply transitive_parallel_and_star_are_equivalent; auto.
  - apply transitive_parallel_and_star_are_equivalent; auto.
  - exists w.
    + apply transitive_parallel_and_star_are_equivalent; auto.
    + apply transitive_parallel_and_star_are_equivalent; auto.
Qed.

Corollary step_is_church_rosser:
  church_rosser step.
Proof.
  apply confluency_implies_church_rosser.
  exact star_is_confluent.
Qed.

(** ** Head Reduction *)

Definition env: Set :=
  list pseudoterm.

Inductive long: list env -> list pseudoterm -> relation pseudoterm :=
  | long_head:
    forall b,
    long [] [] b b
  | long_tail:
    forall tss ts cs c b e,
    long tss cs (bind b ts c) e ->
    long (ts :: tss) (c :: cs) b e.

Hint Constructors long: cps.

Lemma long_rev:
  forall tss ts cs c h b,
  long tss cs h b -> long (tss ++ [ts]) (cs ++ [c]) h (bind b ts c).
Proof.
  induction tss; intros.
  - dependent destruction H; simpl.
    auto with cps.
  - dependent destruction H; simpl.
    constructor.
    apply IHtss; auto.
Qed.

Lemma long_rev_inv:
  forall tss ts cs c h b,
  long (tss ++ [ts]) (cs ++ [c]) h (bind b ts c) -> long tss cs h b.
Proof.
  induction tss; intros.
  - destruct cs; simpl in H.
    + dependent destruction H.
      dependent destruction H.
      constructor.
    + exfalso.
      dependent destruction H.
      destruct cs; inversion H.
  - destruct cs.
    + simpl in H.
      dependent destruction H.
      destruct tss; inversion H.
    + constructor; simpl in H.
      dependent destruction H.
      eapply IHtss.
      eassumption.
Qed.

Lemma long_tail_inv:
  forall tss cs ts c b e,
  long (tss ++ [ts]) (cs ++ [c]) b e ->
  exists x, bind x ts c = e.
Proof.
  induction tss; intros.
  - destruct cs.
    + dependent destruction H.
      dependent destruction H.
      exists b; auto.
    + inversion H.
      destruct cs; inversion H6.
  - destruct cs.
    + dependent destruction H.
      destruct tss; inversion H.
    + dependent destruction H.
      edestruct IHtss; eauto.
Qed.

Lemma long_rev_ind:
  forall P: list env -> list pseudoterm -> relation pseudoterm,
  forall f1: (forall b, P [] [] b b),
  forall f2: (forall tss cs ts c h b, long tss cs h b ->
              P tss cs h b -> P (tss ++ [ts]) (cs ++ [c]) h (bind b ts c)),
  forall tss cs b e, long tss cs b e -> P tss cs b e.
Proof.
  induction tss using rev_ind; intros.
  - destruct cs.
    + dependent destruction H.
      apply f1.
    + inversion H.
  - destruct cs using rev_ind.
    + destruct tss; inversion H.
    + clear IHcs.
      rename x into ts, x0 into c.
      edestruct long_tail_inv; eauto.
      destruct H0.
      apply long_rev_inv in H.
      apply f2; auto.
Qed.

Lemma long_type_body_length:
  forall tss cs b e,
  long tss cs b e -> length tss = length cs.
Proof.
  induction 1; simpl; auto.
Qed.

Hint Resolve long_type_body_length: cps.

Lemma long_implies_context:
  forall tss cs,
  length tss = length cs ->
  exists h,
  #h = length tss /\ static h /\ forall b e,
  long tss cs b e -> e = h b.
Proof.
  induction tss; intros.
  - destruct cs; try discriminate.
    exists context_hole; intuition.
    inversion H0; auto.
  - destruct cs; try discriminate.
    destruct IHtss with cs as (h, (?, (?, ?))); auto.
    exists (compose_context h (context_left context_hole a p)).
    repeat split; simpl; intros.
    + rewrite compose_context_depth; simpl; lia.
    + apply static_compose_context; auto with cps.
    + rewrite compose_context_is_sound; simpl.
      dependent destruction H3.
      rewrite H2 with (bind b a p) e; auto.
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
    + simpl in H; lia.
    + eapply IHxs with (k := n).
      * simpl in H; lia.
      * eassumption.
Qed.

Lemma item_last_item:
  forall {T} xs k,
  length xs = k ->
  forall a b,
  @item T a (xs ++ [b]) k -> a = b.
Proof.
  intros.
  dependent induction H0.
  + destruct xs; try discriminate.
    dependent destruction x; auto.
  + destruct xs; try discriminate.
    dependent destruction x.
    eapply IHitem; eauto.
Qed.

Definition LONGJMP (R: relation pseudoterm): Prop :=
  forall tss cs k xs e1,
  long tss cs (jump (bound k) xs) e1 ->
  forall ts,
  length xs = length ts ->
  item ts tss k ->
  forall c,
  item c cs k ->
  forall e2,
  long tss cs (apply_parameters xs 0 (lift (S k) (length ts) c)) e2 ->
  R e1 e2.

Lemma step_longjmp:
  LONGJMP step.
Proof.
  unfold LONGJMP; intros until 1.
  dependent induction H using long_rev_ind; intros.
  - inversion H1.
  - edestruct long_tail_inv; eauto.
    destruct H4.
    destruct (lt_eq_lt_dec (length tss) k) as [ [ ? | ? ] | ? ].
    + exfalso.
      apply item_too_far with (tss ++ [ts]) ts0 k; auto.
      rewrite app_length; simpl; lia.
    + apply long_rev_inv in H3.
      destruct long_implies_context with tss cs; eauto with cps.
      destruct H4; destruct H5.
      erewrite H6 with _ b in H |- *; eauto.
      erewrite H6 with _ x in H3 |- *; eauto.
      apply long_type_body_length in H.
      apply item_last_item in H1; auto.
      apply item_last_item in H2; try congruence.
      destruct H1; destruct H2.
      replace k with #x0.
      * apply step_ctxjmp.
        assumption.
      * congruence.
    + apply step_bind_left.
      apply long_rev_inv in H3.
      eapply IHlong.
      * reflexivity.
      * eassumption.
      * eapply item_ignore_tail; eauto.
      * eapply item_ignore_tail; eauto.
        replace (length cs) with (length tss); eauto with cps.
      * assumption.
Qed.

(** ** Observational theory *)

Inductive converges: pseudoterm -> nat -> Prop :=
  | converges_jump:
    forall k xs,
    converges (jump (bound k) xs) k
  | converges_bind:
    forall b ts c k,
    converges b (S k) -> converges (bind b ts c) k.

Hint Constructors converges: cps.

Definition weakly_converges a n: Prop :=
  exists2 b,
  [a =>* b] & converges b n.

Hint Unfold weakly_converges: cps.

Lemma convergence_is_unique:
  forall e n,
  converges e n ->
  forall m,
  converges e m -> n = m.
Proof.
  induction 1; intros.
  (* Case: converges_jump. *)
  - inversion H; auto.
  (* Case: converges_bind. *)
  - dependent destruction H0.
    cut (S k = S k0); auto.
Qed.

(* Set theoretic definition of a barbed (bi)simulation... *)

Definition reduction_closed (R: relation pseudoterm): Prop :=
  forall a b,
  R a b ->
  forall c,
  [a => c] ->
  exists2 d,
  [b =>* d] & R c d.

Definition barb_preserving (R: relation pseudoterm): Prop :=
  forall a b,
  R a b ->
  forall n,
  converges a n -> weakly_converges b n.

Definition barbed_simulation (R: relation pseudoterm): Prop :=
  reduction_closed R /\ barb_preserving R.

Definition barbed_bisimulation (R: relation pseudoterm): Prop :=
  barbed_simulation R /\ barbed_simulation (transp _ R).

Definition bisi a b: Prop :=
  exists2 R, barbed_bisimulation R & R a b.

Lemma bisi_is_a_barbed_bisimulation_itself:
  barbed_bisimulation bisi.
Proof.
  split; split; do 5 intro.
  - destruct H as (R, ((C, P), X), I).
    destruct C with a b c as (d, ?, ?); auto.
    exists d; auto.
    exists R; auto.
    split; auto.
    split; auto.
  - destruct H as (R, ((C, P), X), I).
    eapply P; eauto.
  - destruct H as (R, (X, (C, P)), I).
    destruct C with a b c as (d, ?, ?); auto.
    exists d; auto.
    exists R; auto.
    split; auto.
    split; auto.
  - destruct H as (R, (X, (C, P)), I).
    eapply P; eauto.
Qed.

Lemma multistep_reduction_closed:
  forall R,
  reduction_closed R ->
  forall a b,
  R a b ->
  forall c,
  [a =>* c] ->
  exists2 d,
  [b =>* d] & R c d.
Proof.
  intros.
  generalize b H0; clear b H0.
  induction H1; simpl; intros.
  - eapply H; eauto.
  - exists b; auto with cps.
  - destruct IHclos_refl_trans1 with b as (w, ?, ?); auto.
    destruct IHclos_refl_trans2 with w as (v, ?, ?); auto.
    exists v; eauto with cps.
Qed.

(* I'd like to try a coinductive definition later on... but let's see... *)

Definition barb a b: Prop :=
  forall h: context,
  bisi (h a) (h b).

Notation "[ a ~~ b ]" := (barb a b)
  (at level 0, a, b at level 200): type_scope.

Lemma barb_refl:
  forall e,
  [e ~~ e].
Proof.
  intros.
  (* Consider, e.g., that our barbed relation is alpha equality. *)
  exists eq; auto.
  split; split; do 5 intro.
  - destruct H.
    exists c; auto with cps.
  - destruct H.
    split with a; auto with cps.
  - destruct H.
    exists c; auto with cps.
  - destruct H.
    split with b; auto with cps.
Qed.

Hint Resolve barb_refl: cps.

Lemma barb_sym:
  forall a b,
  [a ~~ b] -> [b ~~ a].
Proof.
  unfold barb; intros.
  destruct H with h as (R, (X, Y), I).
  exists (transp _ R); auto.
  split; auto.
Qed.

Hint Resolve barb_sym: cps.

Lemma barb_trans:
  forall a b c,
  [a ~~ b] -> [b ~~ c] -> [a ~~ c].
Proof.
  unfold barb at 3; intros.
  destruct H with h as (R, ?, ?).
  destruct H0 with h as (S, ?, ?).
  exists (fun a c =>
    exists2 b, R a b & S b c).
  - clear a b c H H0 h H2 H4.
    split; split; do 5 intro.
    + destruct H as (d, ?, ?).
      destruct H1 as ((?, _), _).
      destruct H3 as ((?, _), _).
      destruct H1 with a d c as (x, ?, ?); auto.
      destruct multistep_reduction_closed with S d b x as (y, ?, ?); auto.
      exists y; auto.
      exists x; auto.
    + destruct H as (d, ?, ?).
      destruct H1 as ((_, ?), _).
      destruct H3 as ((?, ?), _).
      destruct H1 with a d n as (x, ?, ?); auto.
      destruct multistep_reduction_closed with S d b x as (y, ?, ?); auto.
      destruct H4 with x y n as (z, ?, ?); auto.
      exists z; eauto with cps.
    + destruct H as (d, ?, ?).
      destruct H1 as (_, (?, _)).
      destruct H3 as (_, (?, _)).
      destruct H3 with a d c as (x, ?, ?); auto.
      destruct multistep_reduction_closed with (transp _ R) d b x as (y, ?, ?);
        auto.
      exists y; auto.
      exists x; auto.
    + destruct H as (d, ?, ?).
      destruct H1 as (_, (?, ?)).
      destruct H3 as (_, (_, ?)).
      destruct H3 with a d n as (x, ?, ?); auto.
      destruct multistep_reduction_closed with (transp _ R) d b x as (y, ?, ?);
        auto.
      destruct H4 with x y n as (z, ?, ?); auto.
      exists z; eauto with cps.
  - exists (h b); auto.
Qed.

Hint Resolve barb_trans: cps.

Instance barb_is_equiv: Equivalence barb.
Proof.
  split.
  - exact barb_refl.
  - exact barb_sym.
  - exact barb_trans.
Defined.

(** ** Type system *)

Definition item_lift (e: pseudoterm) (g: env) (n: nat): Prop :=
  exists2 x, e = lift (S n) 0 x & item x g n.

Fixpoint env_prepend ts g: env :=
  match ts with
  | [] => g
  | t :: ts => lift (length ts) 0 t :: env_prepend ts g
  end.

Inductive typing: env -> relation pseudoterm :=
  | typing_base:
    forall g,
    valid_env g -> typing g base prop
  | typing_negation:
    forall g ts,
    Forall (fun t => typing g t prop) ts -> valid_env g ->
    typing g (negation ts) prop
  | typing_bound:
    forall g n t,
    valid_env g -> item_lift t g n -> typing g n t
  | typing_jump:
    forall g k xs ts,
    typing g k (negation ts) -> Forall2 (typing g) xs ts ->
    typing g (jump k xs) void
  | typing_bind:
    forall g b ts c,
    typing (negation ts :: g) b void ->
    Forall (fun t => typing g t prop) ts ->
    typing (env_prepend ts g) c void ->
    typing g (bind b ts c) void

with valid_env: env -> Prop :=
  | valid_env_nil:
    valid_env []
  | valid_env_term_var:
    forall g t,
    typing g t prop -> valid_env (t :: g).

Hint Constructors typing: cps.
Hint Constructors valid_env: cps.

Lemma valid_env_typing:
  forall g e t,
  typing g e t -> valid_env g.
Proof.
  induction 1.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - dependent destruction IHtyping1.
    dependent destruction H2.
    assumption.
Qed.

Lemma valid_env_inv:
  forall x g,
  valid_env (x :: g) -> valid_env g.
Proof.
  intros.
  dependent destruction H.
  apply valid_env_typing with x prop; auto.
Qed.

Lemma typing_deepind:
  forall P: (forall g e t, Prop),
  forall f1: (forall g, P g base prop),
  forall f2: (forall g ts, Forall (fun t => P g t prop) ts ->
              P g (negation ts) prop),
  forall f3: (forall g n t, item_lift t g n -> P g n t),
  forall f4: (forall g k xs ts, P g k (negation ts) -> Forall2 (P g) xs ts ->
              P g (jump k xs) void),
  forall f5: (forall g b ts c, P (negation ts :: g) b void ->
              Forall (fun t => P g t prop) ts ->
              P (env_prepend ts g) c void -> P g (bind b ts c) void),
  forall g e t,
  typing g e t -> P g e t.
Proof.
  do 6 intro; fix H 4.
  destruct 1.
  - apply f1.
  - apply f2; auto.
    clear f1 f2 f3 f4 f5 H1.
    induction H0; auto.
  - apply f3; auto.
  - apply f4 with ts; auto.
    clear f1 f2 f3 f4 f5 H0.
    induction H1; auto.
  - apply f5; auto.
    clear f1 f2 f3 f4 f5 H0_ H0_0.
    induction H0; auto.
Qed.

Lemma typing_bound_cant_be_void:
  forall g n,
  ~typing g (bound n) void.
Proof.
  intros g n H.
  dependent destruction H.
  destruct H0.
  (* We should have added an inversion lemma, but oh well... *)
  replace x with void in *.
  - clear H0 x.
    induction H1.
    + dependent destruction H.
       inversion H.
    + dependent destruction H.
      apply IHitem.
      eapply valid_env_typing.
      eassumption.
  - destruct x; try discriminate.
    reflexivity.
Qed.

Inductive insert x: nat -> relation env :=
  | insert_head:
    forall tail,
    insert x 0 tail (x :: tail)
  | insert_tail:
    forall n head tail new_tail,
    insert x n tail new_tail ->
    insert x (S n) (head :: tail) (lift 1 n head :: new_tail).

Hint Constructors insert: cps.

Lemma item_lift_insert_ge:
  forall x n g h,
  insert x n g h ->
  forall m,
  n <= m ->
  forall y, item_lift y g m -> item_lift (lift 1 n y) h (S m).
Proof.
  induction 1; intros.
  - destruct H0 as (z, ?, ?).
    exists z; auto with cps.
    rewrite H0.
    rewrite lift_lift_simplification; auto with arith.
  - destruct H1 as (z, ?, ?).
    dependent destruction H2.
    + inversion H0.
    + rename n0 into m.
      destruct IHinsert with m (lift (S m) 0 z); try lia.
      * exists z; auto.
      * rewrite lift_lift_simplification in H3; try lia.
        exists x0; auto with cps.
        rewrite H1; rewrite lift_lift_simplification; try lia.
        admit.
Admitted.

Lemma item_lift_insert_lt:
  forall e n g h,
  insert e n g h ->
  forall m,
  n > m ->
  forall y, item_lift y g m -> item_lift (lift 1 n y) h m.
Proof.
  induction 1; intros.
  - inversion H.
  - destruct H1.
    dependent destruction H2.
    + clear IHinsert H0.
      exists (lift 1 n head); auto with cps.
      symmetry; rewrite lift_lift_permutation; auto with arith.
    + rename n0 into m.
      destruct IHinsert with m (lift (S m) 0 x) as (z, ?, ?); try lia.
      * exists x; auto.
      * exists z; auto with cps.
        admit.
Admitted.

Lemma env_prepend_rev:
  forall ts t g,
  env_prepend (ts ++ [t]) g = env_prepend (map (lift 1 0) ts) (t :: g).
Proof.
  induction ts; simpl; intros.
  - rewrite lift_zero_e_equals_e; auto.
  - rewrite app_length; simpl.
    rewrite map_length.
    rewrite lift_lift_simplification; try lia.
    rewrite IHts; f_equal.
Qed.

Lemma typing_weak_lift:
  forall g e t,
  typing g e t ->
  forall x n h,
  insert x n g h -> valid_env h -> typing h (lift 1 n e) (lift 1 n t).
Proof.
  induction 1 using typing_deepind; intros.
  (* Case: typing_base. *)
  - apply typing_base.
    assumption.
  (* Case: typing_negation. *)
  - rewrite lift_distributes_over_negation.
    apply typing_negation; auto.
    induction H; simpl.
    + constructor.
    + constructor; auto.
      apply H with x; auto.
  (* Case: typing_bound. *)
  - rename n0 into m.
    destruct (le_gt_dec m n).
    + rewrite lift_bound_ge; auto.
      apply typing_bound; auto.
      apply item_lift_insert_ge with x g; auto.
    + rewrite lift_bound_lt; auto.
      apply typing_bound; auto.
      apply item_lift_insert_lt with x g; auto.
  (* Case: typing_jump. *)
  - rewrite lift_distributes_over_jump.
    apply typing_jump with (map (lift 1 n) ts).
    + apply IHtyping with x; auto.
    + clear IHtyping.
      induction H; simpl.
      * constructor.
      * constructor; auto.
        apply H with x; auto.
  (* Case: typing_bind. *)
  - rewrite lift_distributes_over_bind.
    apply typing_bind.
    + apply IHtyping with x.
      * constructor; auto.
      * constructor; auto.
        clear IHtyping IHtyping0.
        constructor; auto.
        induction H; simpl; auto.
        constructor; auto.
        replace prop with (lift 1 n prop); auto.
        apply H with x; auto.
    + clear IHtyping IHtyping0.
      induction H; simpl; auto.
      constructor; auto.
      replace prop with (lift 1 n prop); auto.
      apply H with x; auto.
    + simpl in *.
      apply IHtyping0 with x.
      * clear IHtyping IHtyping0.
        rewrite Nat.add_comm.
        induction H; simpl; auto.
        rewrite map_length.
        rewrite lift_lift_permutation; try lia.
        constructor; auto.
      * admit.
Admitted.

Theorem weakening:
  forall g e t,
  typing g e t ->
  forall x,
  valid_env (x :: g) -> typing (x :: g) (lift 1 0 e) (lift 1 0 t).
Proof.
  intros.
  apply typing_weak_lift with g x; auto with cps.
Qed.

(** ** Normalization. *)

Notation flip f :=
  (fun a b => f b a).

Definition normal a: Prop :=
  forall b, ~[a => b].

Definition WN a: Prop :=
  exists2 b, [a =>* b] & normal b.

Notation SN :=
  (Acc (flip step)).

Lemma SN_preimage:
  forall f,
  (forall a b, [a => b] -> [f a => f b]) ->
  forall e,
  SN (f e) -> SN e.
Proof.
  intros.
  dependent induction H0.
  constructor; intros.
  eapply H0.
  - eauto.
  - eassumption.
  - reflexivity.
Qed.

Lemma SN_unlift:
  forall i k e,
  SN (lift i k e) -> SN e.
Proof.
  intros.
  apply SN_preimage with (lift i k); intros.
  - apply step_lift; auto.
  - assumption.
Qed.

Lemma SN_unsubst:
  forall y k e,
  SN (subst y k e) -> SN e.
Proof.
  intros.
  apply SN_preimage with (subst y k); intros.
  - apply step_subst; auto.
  - assumption.
Qed.

Lemma SN_bind_left:
  forall b ts c,
  SN (bind b ts c) -> SN b.
Proof.
  intros.
  apply SN_preimage with (fun b => bind b ts c); auto with cps.
Qed.

Lemma SN_bind_right:
  forall b ts c,
  SN (bind b ts c) -> SN c.
Proof.
  intros.
  apply SN_preimage with (fun c => bind b ts c); auto with cps.
Qed.

Inductive step_in_env: relation env :=
  | step_in_env_car:
    forall g t u,
    step t u -> step_in_env (t :: g) (u :: g)
  | step_in_env_cdr:
    forall g h t,
    step_in_env g h -> step_in_env (t :: g) (t :: h).

Lemma step_in_env_is_well_founded:
  forall xs: env,
  Forall SN xs ->
  Acc (flip step_in_env) xs.
Proof.
  induction xs; intros.
  - constructor; intros.
    inversion H0.
  - dependent destruction H.
    apply IHxs in H0; clear IHxs.
    induction H; clear H.
    induction H0.
    constructor; intros.
    dependent destruction H2.
    + intuition.
    + apply H0; intros.
      * assumption.
      * eapply H1; eauto.
        constructor.
        assumption.
Qed.

Definition sumup {T} (f: T -> nat) (ts: list T): nat :=
  fold_right Nat.add 0 (map f ts).

Lemma sumup_app:
  forall {T} f a b,
  @sumup T f (a ++ b) = sumup f a + sumup f b.
Proof.
  induction a; simpl; intros.
  - reflexivity.
  - unfold sumup; simpl.
    rewrite plus_assoc_reverse; f_equal.
    apply IHa.
Defined.

Fixpoint count (t: pseudoterm): nat :=
  match t with
  | base =>
    1
  | negation ts =>
    1 + sumup count ts
  | _ =>
    0
  end.

Lemma count_is_well_founded:
  well_founded (ltof _ count).
Proof.
  apply well_founded_ltof.
Defined.

Lemma count_arg:
  forall {t ts g},
  t = negation (negation ts :: g) ->
  count (negation ts) < count t.
Proof.
  intros.
  rewrite H; simpl.
  replace (negation ts :: g) with ([negation ts] ++ g); auto.
  rewrite sumup_app; simpl; auto with arith.
Qed.

Lemma count_ret:
  forall {t ts g},
  t = negation (negation ts :: g) ->
  count (negation g) < count t.
Proof.
  intros.
  rewrite H; simpl.
  replace (negation ts :: g) with ([negation ts] ++ g); auto.
  rewrite sumup_app; simpl; auto with arith.
Qed.

Definition ARR ts (U V: pseudoterm -> Prop): pseudoterm -> Prop :=
  fun b =>
    forall c: pseudoterm,
    U c -> V (bind b ts c).

(* TODO: interpret ~(G, b)... by subst? *)
Definition L: pseudoterm -> pseudoterm -> Prop :=
  Fix count_is_well_founded (fun _ => pseudoterm -> Prop) (fun t f =>
    match t as x return (t = x -> pseudoterm -> Prop) with
    (* Given ~(G, ~T)... *)
    | negation (negation ts :: g) =>
      fun H =>
        ARR ts (f _ (count_arg H)) (f _ (count_ret H))
    (* By default... *)
    | _ =>
      fun _ => SN
    end eq_refl).

Lemma L_composition:
  forall ts g,
  L (negation (negation ts :: g)) =
    ARR ts (L (negation ts)) (L (negation g)).
Proof.
  intros.
  unfold L.
  rewrite Fix_eq.
  - fold L.
    reflexivity.
  - intros.
    destruct x; simpl; auto.
    destruct ts0; simpl; auto.
    destruct p; simpl; auto.
    do 2 rewrite H; auto.
Defined.

Definition candidate: Type :=
  pseudoterm -> Prop.

(* A neutral term should no trigger a reduction interacting with its context.
   I.e., in the lambda calculus, they are neither abstractions, which would
   trigger a reduction with ([] x), nor <a, b>, which would trigger a reduction
   with (pi1 []) or (pi2 []). Since the CPS calculus "works at a distance", we
   would probably need something that DOESN'T jump to bound variables. So I'll
   probably need to index this by the (size of the) environment. *)
Axiom neutral: pseudoterm -> Prop.

Record reducible (P: candidate): Prop := {
  cr1:
    forall e,
    P e -> SN e;
  cr2:
    forall a b,
    P a -> [a => b] -> P b;
  cr3:
    forall a,
    (* Since the CPS calculus is non-erasing, do we really need to restrict
       ourselves to neutral terms here...? *)
    neutral a -> (forall b, [a => b] -> P b) -> P a
}.

Lemma cr2_star:
  forall P,
  reducible P ->
  forall a b,
  P a -> [a =>* b] -> P b.
Proof.
  induction 3.
  - apply cr2 with x; auto.
  - assumption.
  - auto.
Qed.

Lemma reducible_SN:
  reducible SN.
Proof.
  constructor; intros.
  - assumption.
  - apply H.
    assumption.
  - constructor.
    assumption.
Qed.

(* Should probably modularize the following lemma. *)

Lemma reducible_ARR:
  forall g ts,
  reducible (L (negation g)) ->
  reducible (L (negation ts)) ->
  reducible (L (negation (negation ts :: g))).
Proof.
  constructor; intros.
  - rewrite L_composition in H1.
    unfold ARR in H1.
    cut (exists c, L (negation ts) c).
    + destruct 1 as (c, ?H).
      apply SN_bind_left with ts c.
      apply cr1 with (L (negation g)); auto.
    + (* We should add a free jump here, right...? *)
      admit.
  - rewrite L_composition in H1 |- *.
    unfold ARR in H1 |- *; intros.
    apply cr2 with (bind a ts c); auto.
    apply step_bind_left; auto.
  - rewrite L_composition in H2 |- *.
    unfold ARR in H2 |- *; intros.
    assert (SN c).
    + eapply cr1 with (L (negation ts)); auto.
    + induction H4; clear H4.
      apply cr3; intros.
      * assumption.
      * (* Oh no! Are we really neutral here?

           We'll probably have to change candidates from sets of terms to
           relations between environments and terms. Could we derive then that x
           is neutral based on that, e.g., such that a { k<xs: ts> = x } is
           neutral in G? *)
        admit.
      * dependent destruction H4.
        -- (* It is neutral, so we CAN'T have a redex here! *)
           admit.
        -- apply H2; auto.
        -- apply H5; auto.
           apply cr2 with x; auto.
Admitted.

Lemma reducible_L:
  forall t,
  reducible (L t).
Proof.
  intros.
  induction count_is_well_founded with t.
  clear H; rename H0 into H; unfold ltof in H.
  (* Ok, start wordering about the type... *)
  destruct x; try exact reducible_SN.
  destruct ts; try exact reducible_SN.
  destruct p; try exact reducible_SN.
  (* "Arrow types", in a way... *)
  rename ts0 into ts, ts into g.
  apply reducible_ARR.
  - apply H.
    eapply count_ret; eauto.
  - apply H.
    eapply count_arg; eauto.
Qed.

Lemma SN_L:
  forall t e,
  L t e -> SN e.
Proof.
  intros.
  apply cr1 with (L t); auto.
  apply reducible_L.
Qed.

Lemma fundamental:
  forall e g,
  typing g e void ->
  forall cs,
  Forall2 L g cs ->
  SN (beta cs 0 e).
Proof.
  induction e; inversion_clear 1.
  (* Case: bound. *)
  - exfalso.
    (* Commands don't have types, but variables do. *)
    apply typing_bound_cant_be_void with g n; auto with cps.
  (* Case: jump. *)
  - clear IHe.
    admit.
  (* Case: bind. *)
  - admit.
Admitted.

End STCC.
