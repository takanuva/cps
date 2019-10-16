(** * The Simply Typed CPS Calculus *)

Require Import Arith.
Require Import Omega.

(** ** Syntax

    We split our syntax into three classes: [sort], [value] and [command]. *)

Inductive level: Prop :=
  | sort
  | value
  | command.

(** We use [type] and [prop] as our universes, [void] and [base] represent the
    bottom and base types respectively. We use de Bruijn indexes on the [bound]
    constructor. The only type constructor is [negation], a polyadic type which
    represents the negation of an N-tuple. Our commands are either a [jump],
    written as [k<x, ...>], or a [bind], written as [b { k<x: t, ...> = c }]. *)

Inductive pseudoterm: level -> Set :=
  | type:
    pseudoterm sort
  | prop:
    pseudoterm sort
  | void:
    pseudoterm sort
  | base:
    pseudoterm sort
  | bound:
    forall n: nat,
    pseudoterm value
  | negation:
    forall xs: list (pseudoterm sort),
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
  forall f3: P void,
  forall f4: P base,
  forall f5: (forall n: nat, P n),
  forall f6: (forall xs, List.Forall P xs -> P (negation xs)),
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
  (* Case: void. *)
  - apply f3.
  (* Case: base. *)
  - apply f4.
  (* Case: bound. *)
  - apply f5.
  (* Case: negation. *)
  - apply f6.
    induction xs; auto.
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
    f_equal; auto].

(** ** Lifting *)

Fixpoint lift (i: nat) (k: nat) {l: level} (e: l): l :=
  match e with
  | type =>
    type
  | prop =>
    prop
  | void =>
    void
  | base =>
    base
  | bound n =>
    if le_gt_dec k n then
      bound (i + n)
    else
      bound n
  | negation xs =>
    negation (List.map (lift i k) xs)
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
  (* Case: void.*)
  - reflexivity.
  (* Case: base.*)
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
  (* Case: void. *)
  - reflexivity.
  (* Case: base. *)
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
  (* Case: void. *)
  - reflexivity.
  (* Case: base. *)
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
  (* Case: void. *)
  - reflexivity.
  (* Case: base. *)
  - reflexivity.
  (* Case: bound. *)
  - simpl.
    destruct (le_gt_dec l n); destruct (le_gt_dec k n); intros.
    + rewrite lift_bound_ge.
      * rewrite lift_bound_ge; auto with arith.
        do 2 elim plus_assoc_reverse; auto with arith.
      * eapply le_trans; eauto with arith.
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
