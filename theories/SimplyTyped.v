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

Fixpoint sequence (high: bool) n :=
  match n with
  | 0 => nil
  | S m => cons (bound (if high then n else m)) (sequence high m)
  end.

Hint Unfold sequence: cps.

Definition high_sequence: nat -> list pseudoterm :=
  sequence true.

Hint Unfold high_sequence: cps.

Definition low_sequence: nat -> list pseudoterm :=
  sequence false.

Hint Unfold low_sequence: cps.

Definition right_cycle (n: nat) e :=
  apply_parameters (cons (bound 0) (high_sequence n)) 0 (lift n (S n) e).

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

Lemma apply_parameters_high_sequence_equals_nat_fold:
  forall e n m,
  apply_parameters (high_sequence n) (S m) (lift (m + n) (S m + n) e) =
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
  apply apply_parameters_high_sequence_equals_nat_fold.
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

Lemma high_sequence_succ:
  forall n,
  high_sequence (S n) = bound (S n) :: high_sequence n.
Proof.
  reflexivity.
Qed.

Lemma lifting_over_n_doesnt_change_high_sequence_n:
  forall n i k,
  map (lift i (S (n + k))) (high_sequence n) = high_sequence n.
Proof.
  induction n; intros.
  (* Case: zero. *)
  - reflexivity.
  (* Case: succ. *)
  - rewrite high_sequence_succ.
    rewrite map_cons.
    f_equal.
    + rewrite lift_bound_lt; auto.
      omega.
    + replace (S n + k) with (n + S k); auto.
      omega.
Qed.

Lemma substing_over_n_doesnt_change_high_sequence_n:
  forall n x k,
  map (subst x (S (n + k))) (high_sequence n) = high_sequence n.
Proof.
  induction n; intros.
  (* Case: zero. *)
  - reflexivity.
  (* Case: succ. *)
  - rewrite high_sequence_succ.
    rewrite map_cons.
    f_equal.
    + rewrite subst_bound_lt; auto.
      omega.
    + replace (S n + k) with (n + S k); auto.
      omega.
Qed.

Lemma length_high_sequence:
  forall n,
  length (high_sequence n) = n.
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
   anyway. TODO: should we consider (JMP) here as well? What about (ETA)? *)

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

Notation "[ a == b ]" := (rst(struct) a b)
  (at level 0, a, b at level 200): type_scope.

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

Instance cong_is_equiv: Equivalence rst(struct).
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
  - apply lifting_over_n_doesnt_change_high_sequence_n.
  - rewrite length_high_sequence.
    simpl; symmetry.
    rewrite lift_lift_permutation; try omega.
    f_equal; omega.
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
  - apply substing_over_n_doesnt_change_high_sequence_n.
  - rewrite length_high_sequence; simpl.
    rewrite lift_and_subst_commute; try omega.
    f_equal; omega.
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

Inductive context: nat -> Set :=
  | context_hole:
    context 0
  | context_left {n} (b: context n) (ts: list pseudoterm) (c: pseudoterm):
    context (S n)
  | context_right {n} (b: pseudoterm) (ts: list pseudoterm) (c: context n):
    context (n + length ts).

Fixpoint apply_context {n} (h: context n) (e: pseudoterm): pseudoterm :=
  match h with
  | context_hole => e
  | context_left b ts c => bind (apply_context b e) ts c
  | context_right b ts c => bind b ts (apply_context c e)
  end.

Coercion apply_context: context >-> Funclass.

Reserved Notation "[ a => b ]" (at level 0, a, b at level 200).

(* Should (ETA) be in [step], or just in [cong]? *)

Inductive step: relation pseudoterm :=
  | step_ctxjmp:
    forall {k} (h: context k),
    forall xs ts c,
    length xs = length ts ->
    [bind (h (jump k xs)) ts c =>
      bind (h (apply_parameters xs 0 (lift k (length ts) c))) ts c]
  | step_eta:
    forall b ts j,
    [bind b ts (jump (bound (length ts + j)) (low_sequence (length ts))) =>
      subst j 0 b]
  | step_bind_left:
    forall b1 b2 ts c,
    [b1 => b2] -> [bind b1 ts c => bind b2 ts c]
  | step_bind_right:
    forall b ts c1 c2,
    [c1 => c2] -> [bind b ts c1 => bind b ts c2]

where "[ a => b ]" := (step a b): type_scope.

Hint Constructors step: cps.

Lemma step_jmp:
  forall xs ts c,
  length xs = length ts ->
  [bind (jump 0 xs) ts c => bind (apply_parameters xs 0 c) ts c].
Proof.
  intros.
  replace c with (lift 0 (length ts) c) at 2.
  - apply step_ctxjmp with (h := context_hole); auto.
  - apply lift_zero_e_equals_e.
Qed.

Hint Resolve step_jmp: cps.

(******************************************************************************)

(*
  \j.\x.\y.\z.
    k@0<z@1, y@2, x@3>            =>     \j.\x.\y.\z.
    { k<a, b, c> =                         j@3<z@0, y@1, x@2>
        j@6<a@2, b@1, c@0> }

  Hm, unfortunately the parameters won't match [sequence] as it is defined...
*)

Example foo: pseudoterm :=
  (bind
    (jump 0 [bound 1; bound 2; bound 3])
    [base; base; base]
      (jump 6 [bound 2; bound 1; bound 0])).

Example bar: pseudoterm :=
  (jump 3 [bound 0; bound 1; bound 2]).

Lemma step_eta_helper:
  forall b ts k xs j e,
  k = length ts + j ->
  xs = low_sequence (length ts) ->
  e = subst j 0 b ->
  [bind b ts (jump k xs) => e].
Proof.
  intros.
  rewrite H, H0, H1.
  apply step_eta.
Qed.

Goal [foo => bar].
Proof.
  compute.
  eapply step_eta_helper.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(******************************************************************************)

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

(** ** Multi-step reduction *)

Notation "[ a =>* b ]" := (rt(step) a b)
  (at level 0, a, b at level 200): type_scope.

Lemma star_step:
  forall a b,
  [a => b] -> [a =>* b].
Proof.
  auto with cps.
Qed.

Hint Resolve star_step: cps.

Lemma star_ctxjmp:
  forall {k} (h: context k),
  forall xs ts c,
  length xs = length ts ->
  [bind (h (jump k xs)) ts c =>*
    bind (h (apply_parameters xs 0 (lift k (length ts) c))) ts c].
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

(** ** Reduction convertibility *)

Notation "[ a <=> b ]" := (rst(step) a b)
  (at level 0, a, b at level 200): type_scope.

Lemma conv_step:
  forall a b,
  [a => b] -> [a <=> b].
Proof.
  auto with cps.
Qed.

Hint Resolve conv_step: cps.

Lemma conv_ctxjmp:
  forall {k} (h: context k),
  forall xs ts c,
  length xs = length ts ->
  [bind (h (jump k xs)) ts c <=>
    bind (h (apply_parameters xs 0 (lift k (length ts) c))) ts c].
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

Instance conv_is_equiv: Equivalence rst(step).
Proof.
  split.
  - exact conv_refl.
  - exact conv_symm.
  - exact conv_tran.
Defined.

(** ** Parallel reduction *)

Inductive parallel: relation pseudoterm :=
  | parallel_refl:
    forall e,
    parallel e e
  | parallel_ctxjmp:
    forall {k} (h: context k),
    forall xs ts b c1 c2,
    length xs = length ts ->
    parallel b (h (jump k xs)) ->
    parallel c1 c2 ->
    parallel (bind b ts c1)
      (bind (h (apply_parameters xs 0 (lift k (length ts) c2))) ts c2)
  | parallel_eta:
    forall b1 b2 ts j,
    parallel b1 b2 ->
    parallel (bind b1 ts (jump (length ts + j) (low_sequence (length ts))))
      (subst j 0 b2)
  | parallel_bind:
    forall b1 b2 ts c1 c2,
    parallel b1 b2 -> parallel c1 c2 ->
    parallel (bind b1 ts c1) (bind b2 ts c2).

Lemma parallel_step:
  forall a b,
  [a => b] -> parallel a b.
Proof.
  induction 1.
  - eapply parallel_ctxjmp; auto.
    + apply parallel_refl.
    + apply parallel_refl.
  - apply parallel_eta.
    apply parallel_refl.
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
  - eapply star_tran.
    + apply star_bind_left; eauto.
    + eapply star_tran.
      * apply star_bind_right; eauto.
      * apply star_ctxjmp; auto.
  - eapply star_tran.
    + apply star_bind_left; eauto.
    + (* TODO: use [star_eta] instead! *)
      apply star_step.
      apply step_eta.
  - eauto with cps.
Qed.

Hint Resolve star_parallel: cps.

Lemma context_lift:
  forall {n} (h: context n),
  forall i k,
  exists r: context n,
  forall e, lift i k (h e) = r (lift i (n + k) e).
Proof.
  induction h; simpl; intros.
  - exists context_hole; auto.
  - edestruct IHh with i (S k) as (r, ?).
    exists (context_left r (map (lift i k) ts) (lift i (k + length ts) c)).
    intro; simpl; f_equal.
    replace (S (n + k)) with (n + S k); try omega.
    apply H.
  - edestruct IHh with i (k + length ts) as (r, ?).
    replace (length ts) with (length (map (lift i k) ts)).
    + exists (context_right (lift i (S k) b) (map (lift i k) ts) r).
      intro; simpl; f_equal.
      rewrite map_length.
      replace (n + length ts + k) with (n + (k + length ts)); try omega.
      apply H.
    + apply map_length.
Qed.

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
  - simpl.
    admit.
  - apply parallel_bind; auto.
Admitted.

Lemma context_subst:
  forall {n} (h: context n),
  forall x k,
  exists r: context n,
  forall e, subst x k (h e) = r (subst x (n + k) e).
Proof.
  induction h; simpl; intros.
  - exists context_hole; auto.
  - edestruct IHh with x (S k) as (r, ?).
    exists (context_left r (map (subst x k) ts) (subst x (k + length ts) c)).
    intro; simpl; f_equal.
    replace (S (n + k)) with (n + S k); try omega.
    apply H.
  - edestruct IHh with x (k + length ts) as (r, ?).
    replace (length ts) with (length (map (subst x k) ts)).
    + exists (context_right (subst x (S k) b) (map (subst x k) ts) r).
      intro; simpl; f_equal.
      rewrite map_length.
      replace (n + length ts + k) with (n + (k + length ts)); try omega.
      apply H.
    + apply map_length.
Qed.

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
  - simpl.
    admit.
  - apply parallel_bind; auto.
Admitted.

Lemma parallel_apply_parameters:
  forall a b,
  parallel a b ->
  forall xs k,
  parallel (apply_parameters xs k a) (apply_parameters xs k b).
Proof.
  induction xs; simpl; intros.
  - apply parallel_lift; auto.
  - apply parallel_subst; auto.
Qed.

Lemma parallel_context:
  forall n (h: context n),
  forall a b,
  parallel a b -> parallel (h a) (h b).
Proof.
  induction h; simpl; intros.
  - auto.
  - apply parallel_bind; auto.
    apply parallel_refl.
  - apply parallel_bind; auto.
    apply parallel_refl.
Qed.

Lemma parallel_is_confluent:
  confluent parallel.
Proof.
  admit.
Admitted.

End STCC.
