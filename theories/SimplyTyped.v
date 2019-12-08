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
  forall f5: (forall n: nat, P (bound n)),
  forall f6: (forall ts, List.Forall P ts -> P (negation ts)),
  forall f7: (forall f xs, P f -> List.Forall P xs -> P (jump f xs)),
  forall f8: (forall b ts c, P b -> List.Forall P ts -> P c -> P (bind b ts c)),
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
    [List.Forall P] proposition over them, so we'll add a tactic for that. *)

Tactic Notation "list" "induction" "over" hyp(H) :=
  induction H; simpl;
  [ (* Case: nil. *)
    reflexivity
  | (* Case: cons. *)
    f_equal; auto ].

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
    List.Forall type_class ts -> type_class (negation ts).

Inductive value_class: pseudoterm -> Prop :=
  | bound_is_a_value:
    forall n: nat,
    value_class n.

Inductive command_class: pseudoterm -> Prop :=
  | jump_is_a_command:
    forall k xs,
    value_class k -> List.Forall value_class xs ->
    command_class (jump k xs)
  | bind_is_a_command:
    forall b ts c,
    command_class b -> List.Forall type_class ts -> command_class c ->
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
    negation (List.map (lift i k) ts)
  | jump f xs =>
    jump (lift i k f) (List.map (lift i k) xs)
  | bind b ts c =>
    bind (lift i (S k) b) (List.map (lift i k) ts) (lift i (k + length ts) c)
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
    + rewrite List.map_length; apply IHe2.
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
    + rewrite List.map_length.
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
    + do 2 rewrite List.map_length.
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
    negation (List.map (subst p k) ts)
  | jump f xs =>
    jump (subst p k f) (List.map (subst p k) xs)
  | bind b ts c =>
    bind (subst p (S k) b) (List.map (subst p k) ts) (subst p (k + length ts) c)
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
    + do 2 rewrite List.map_length.
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
    + rewrite List.map_length.
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
    + do 2 rewrite List.map_length.
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
    + do 2 rewrite List.map_length.
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
    not_free_in n (negation ts)
  | not_free_jump:
    forall n x,
    not_free_in n x ->
    forall ts,
    List.Forall (not_free_in n) ts -> not_free_in n (jump x ts)
  | not_free_bind:
    forall n b,
    not_free_in (S n) b ->
    forall ts c,
    not_free_in (n + length ts) c ->
    not_free_in n (bind b ts c).

Definition free_in n e := ~not_free_in n e.

(** ** Structural congruence *)

Definition switch_bindings e: pseudoterm :=
  subst 1 0 (lift 1 2 e).

Hint Unfold switch_bindings: cps.

Example simple_switch:
  switch_bindings (jump 0 [bound 1; bound 3; bound 0; bound 1; bound 2]) =
    jump 1 [bound 0; bound 3; bound 1; bound 0; bound 2].
Proof.
  reflexivity.
Qed.

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

Inductive struct: relation pseudoterm :=
(*  | struct_distr:
    forall b ms m ns n,
    struct
      (bind
      (bind
        b
        ms m)
        ns n)

      (bind
      (bind
        (switch_bindings b)
        ns (lift 1 (length ns) n))
        ms (bind
              ???
              ns ???)) *).

Hint Constructors struct: cps.

Definition cong: relation pseudoterm :=
  clos_refl_sym_trans _ struct.

Hint Unfold cong: cps.
Hint Constructors clos_refl_sym_trans: cps.
Notation "[ a ~=~ b ]" := (cong a b)
  (at level 0, a, b at level 200): type_scope.

Instance cong_is_an_equivalence: Equivalence cong.
Proof.
  split; eauto with cps.
Defined.

(** ** One-step reduction. *)

Fixpoint apply_parameters (xs: list pseudoterm) (k: nat) (c: pseudoterm) :=
  match xs with
  | nil => lift 1 k c
  | cons x xs => subst (lift k 0 x) 0 (apply_parameters xs (S k) c)
  end.

Hint Unfold apply_parameters: cps.








Fixpoint sequence n :=
  match n with
  | 0 => nil
  | S m => cons (bound n) (sequence m)
  end.

Definition right_cycle (n: nat) e :=
  apply_parameters (cons (bound 0) (sequence n)) 0 (lift n (S n) e).

Fixpoint nat_fold {T} n (f: T -> T) e :=
  match n with
  | 0 => e
  | S m => f (nat_fold m f e)
  end.













Lemma lift_distributes_over_apply_parameters_at_any_depth:
  forall i xs k c n,
  lift i (n + S k) (apply_parameters xs n c) =
    apply_parameters (List.map (lift i (S k)) xs) n
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




















Lemma aaaaa:
  forall e n m,
  apply_parameters (sequence n) (S m) (lift (m + n) (S m + n) e) =
    nat_fold n (subst (S m + n) 0) (lift (S m + n) (S m + n) e).
Proof.
  induction n; intros.
  - unfold sequence.
    unfold apply_parameters.
    unfold nat_fold.
    replace (m + 0) with m; auto.
    replace (S m + 0) with (S m); auto.
    rewrite lift_lift_simplification; auto with arith.
  - unfold sequence; fold sequence.
    unfold apply_parameters; fold apply_parameters.
    unfold nat_fold; fold (@nat_fold pseudoterm).
    simpl; f_equal.
    replace (S m + S n) with (S (S m) + n).
    + replace (m + S n) with (S m + n).
      * apply IHn.
      * omega.
    + omega.
Qed.

Lemma right_cycle_behavior n (e: nat):
  right_cycle n e =
    subst 0 0 (nat_fold n (subst (S n) 0) (lift (S n) (S n) e)).
Proof.
  unfold right_cycle.
  unfold apply_parameters; fold apply_parameters.
  rewrite lift_zero_e_equals_e.
  f_equal.
  apply aaaaa.
Qed.

Theorem hmm:
  right_cycle 3 (jump 0 [bound 1; bound 2; bound 3; bound 4; bound 5]) =
                (jump 1 [bound 2; bound 3; bound 0; bound 4; bound 5]).
Proof.
  unfold right_cycle.
  unfold sequence.
  unfold apply_parameters.
  rewrite lift_zero_e_equals_e.
  do 3 unfold lift at 1.
  unfold le_gt_dec.
  unfold le_lt_dec.
  unfold nat_rec.
  unfold nat_rect.
  unfold "+".
  rewrite lift_lift_simplification.
  - unfold "+".
    reflexivity.
  - omega.
  - omega.
Qed.






















Lemma lift_distributes_over_apply_parameters:
  forall i xs k c,
  lift i (S k) (apply_parameters xs 0 c) =
    apply_parameters (List.map (lift i (S k)) xs) 0 (lift i (k + length xs) c).
Proof.
  intros.
  apply lift_distributes_over_apply_parameters_at_any_depth with (n := 0).
Qed.

Lemma subst_distributes_over_apply_parameters_at_any_depth:
  forall i xs k c n,
  subst i (n + S k) (apply_parameters xs n c) =
    apply_parameters (List.map (subst i (S k)) xs) n
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
    apply_parameters (List.map (subst i (S k)) xs) 0
      (subst i (k + length xs) c).
Proof.
  intros.
  apply subst_distributes_over_apply_parameters_at_any_depth with (n := 0).
Qed.

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
    parallel (bind b1 ts c1) (bind b2 ts c2).

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
  induction 1; auto with cps.
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
    + do 2 rewrite List.map_length.
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

Hint Resolve parallel_lift: cps.

(* We would usually like to have two different substition values (c and d), that
   should be parallel, but we don't do that as reductions never happen inside of
   parameter packs. *)
Lemma parallel_subst:
  forall a b,
  parallel a b ->
  forall c k,
  parallel (subst c k a) (subst c k b).
Proof.
  induction 1; intros.
  - simpl.
    rewrite subst_distributes_over_apply_parameters.
    rewrite H; apply parallel_beta.
    + do 2 rewrite List.map_length.
      assumption.
    + apply IHparallel.
  - apply parallel_type.
  - apply parallel_prop.
  - apply parallel_base.
  - apply parallel_void.
  - apply parallel_refl.
  - apply parallel_negation.
  - apply parallel_jump.
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
  - eapply star_tran.
    + apply star_bind_right.
      eassumption.
    + apply star_beta.
      assumption.
  - apply star_refl.
  - apply star_refl.
  - apply star_refl.
  - apply star_refl.
  - apply star_refl.
  - apply star_refl.
  - apply star_refl.
  - eapply star_tran.
    + apply star_bind_left.
      eassumption.
    + apply star_bind_right.
      assumption.
Qed.

Hint Resolve star_parallel: cps.

End STCC.
