(** * The Simply Typed CPS Calculus *)

Require Import Arith.
Require Import Omega.

(** ** Syntax

    We split our syntax into three classes: [sort], [value] and [command]. *)

Inductive level: Prop :=
  | sort
  | value
  | command.

(** We unify the syntax into the same type in order to make a few proofs easier,
    though still respecting the above syntactic classes.

    Inspired by the lambda cube, we use [type] and [prop] as our universes, and
    we keep [base] as our only base type. We also use [void] as the type of
    commands, though it won't appear on any actual terms. As standard, we use de
    Bruijn indexes on the [bound] constructor for variables. Types are simple;
    our only type constructor is [negation], a polyadic type which represents
    the negation of an N-tuple of types.

    The commands in our language are either a [jump], written as [k<x, ...>], or
    a [bind], written as [b { k<x: t, ...> = c }]. *)

Inductive pseudoterm: level -> Set :=
  | type:
    pseudoterm sort
  | prop:
    pseudoterm sort
  | base:
    pseudoterm sort
  | void:
    pseudoterm sort
  | bound:
    forall n: nat,
    pseudoterm value
  | negation:
    forall ts: list (pseudoterm sort),
    pseudoterm sort
  | jump:
    forall f: pseudoterm value,
    forall xs: list (pseudoterm value),
    pseudoterm command
  | bind:
    forall b: pseudoterm command,
    forall ts: list (pseudoterm sort),
    forall c: pseudoterm command,
    pseudoterm command.

Coercion bound: nat >-> pseudoterm.
Coercion pseudoterm: level >-> Sortclass.

(** As we have lists inside our pseudoterms, we'll need a stronger induction
    principle for it, stating that propositions are kept inside the lists. *)

Definition pseudoterm_deepind:
  forall P: (forall {l: level}, l -> Prop),
  forall f1: P type,
  forall f2: P prop,
  forall f3: P base,
  forall f4: P void,
  forall f5: (forall n: nat, P n),
  forall f6: (forall ts, List.Forall P ts -> P (negation ts)),
  forall f7: (forall f xs, P f -> List.Forall P xs -> P (jump f xs)),
  forall f8: (forall b ts c, P b -> List.Forall P ts -> P c -> P (bind b ts c)),
  forall {l: level} (e: l), P e.
Proof.
  do 9 intro; fix H 2.
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

(** *)

Inductive subterm: forall {l1 l2: level}, l1 -> l2 -> Prop :=
  | subterm_negation:
    forall t ts,
    List.In t ts -> subterm t (negation ts)
  | subterm_jump_left:
    forall f xs,
    subterm f (jump f xs)
  | subterm_jump_right:
    forall f x xs,
    List.In x xs -> subterm x (jump f xs)
  | subterm_bind_left:
    forall b ts c,
    subterm b (bind b ts c)
  | subterm_bind_middle:
    forall b t ts c,
    List.In t ts -> subterm t (bind b ts c)
  | subterm_bind_right:
    forall b ts c,
    subterm c (bind b ts c).

(** ** Lifting

    As we're dealing with de Bruijn indexes, we need a notion of lifting in our
    calculus. On the simply typed CPS calculus, most lifing is standard and
    straightforward, with the notable exception of the binding operation. On a
    term of the form [b { k<x: t, ...> = c }], we need to bind the continuation
    [k] on the [b] term, and we need to bind [N] variables on the [c] term. *)

Fixpoint lift (i: nat) (k: nat) {l: level} (e: l): l :=
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
  forall {l: level} (e: l) k,
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
  forall {l: level} (e: l) i j k,
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
  forall n k {l: level} (e: l),
  lift (S n) k e = lift 1 k (lift n k e).
Proof.
  intros.
  replace (S n) with (1 + n); auto.
  rewrite lift_i_lift_j_equals_lift_i_plus_j; auto.
Qed.

Hint Resolve lift_succ_n_equals_lift_1_lift_n: cps.

Lemma lift_lift_simplification:
  forall {l: level} (e: l) i j k l,
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
  forall {l: level} (e: l) i j k l,
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

Fixpoint subst (p: value) (k: nat) {l: level} (q: l): l :=
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
  forall {l: level} (a: l) b i p k,
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
  forall {l: level} (a: l) b i k,
  lift i k (subst b 0 a) = subst (lift i k b) 0 (lift i (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply lift_addition_distributes_over_subst.
Qed.

Lemma subst_lift_simplification:
   forall {l: level} (a: l) b i p k,
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
  forall {l: level} (a: l) b i p k,
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
  forall {l: level} (a: l) b c p k,
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
  forall {l: level} (a: l) b c k,
  subst c k (subst b 0 a) = subst (subst c k b) 0 (subst c (S k) a).
Proof.
  intros.
  replace k with (0 + k); auto.
  apply subst_addition_distributes_over_itself.
Qed.

(** ** One-step reduction. *)

Fixpoint apply_parameters (xs: list value) (k: nat) (c: command) :=
  match xs with
  | nil => lift 1 k c
  | cons x xs => subst (lift k 1 x) 0 (apply_parameters xs (S k) c)
  end.

(*
  We have four assumptions: j, x, y, z.

  \j.\x.\y.\z.                       \j.\x.\y.\z.
  k@0<x@3, y@2>                      j@4<x@3, y@2, z@1>
  { k<a, b> =                 =>     { k<a, b> =
      j@5<a@1, b@0, z@2> }               j@5<a@1, b@0, z@2> }

  Does it make sense to keep the continuation binding there on a simply typed
  environment? I.e., does k<..., k, ...> ever make sense? I don't think there
  can be a (simple) type for that... oh, now I get it!
*)

Inductive step: forall {l: level}, l -> l -> Prop :=
  | step_jmp:
    forall xs ts c,
    length xs = length ts ->
    step
      (bind (jump 0 xs) ts c)
      (bind (apply_parameters xs 0 c) ts c)
  (* TODO *).
