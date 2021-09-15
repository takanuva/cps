(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Export List.
Require Import Arith.
Require Import Local.Prelude.
Export ListNotations.

(** ** Syntax

    Inspired by the lambda cube, we use [type] and [prop] as our universes, and
    we keep [base] as our only base type. We also use [void] as the type of
    commands, though it won't appear on any actual terms. As standard, we use de
    Bruijn indexes on the [bound] constructor for variables. Types are simple;
    our only type constructor is [negation], a polyadic type which represents
    the negation of an N-tuple of types.

    The commands in our language are either a [jump], written as k<x, ...>, or a
    [bind], written as b { k<x: t, ...> = c }. *)

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

(** A simple example. We use a lambda syntax to bind the name of free variables
    for illustration purposes. Notice that, in the list notation used by Coq,
    the head of the list appears at the leftmost position, while in the CPS term
    syntax, the most recent binding will appear at the rightmost position.

    As such, [ex1] is equivalent to the following term:

    \j.\x.\y.\z.
      h@1<y@3, k@0, x@4>
      { k<a, b> =
          h@2<b@0, j@6, a@1> }
      { h<c, d, e> =
          d@1<e@0, z@3> }
*)

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

(** Equality on pseudoterms is decidable. *)

Lemma pseudoterm_eq_dec:
  forall a b: pseudoterm,
  { a = b } + { a <> b }.
Proof.
  fix H 1.
  destruct a; destruct b; try (right; intro; discriminate).
  (* Case: type. *)
  - left; reflexivity.
  (* Case: prop. *)
  - left; reflexivity.
  (* Case: base. *)
  - left; reflexivity.
  (* Case: void. *)
  - left; reflexivity.
  (* Case: bound. *)
  - destruct Nat.eq_dec with n n0.
    + left; congruence.
    + right; congruence.
  (* Case negation. *)
  - destruct list_eq_dec with pseudoterm ts ts0.
    + exact H.
    + left; congruence.
    + right; congruence.
  (* Case: jump. *)
  - destruct list_eq_dec with pseudoterm xs xs0.
    + exact H.
    + destruct H with a b; try (right; congruence).
      left; congruence.
    + right; congruence.
  (* Case: bind. *)
  - destruct list_eq_dec with pseudoterm ts ts0.
    + exact H.
    + destruct H with a1 b1; try (right; congruence).
      destruct H with a2 b2; try (right; congruence).
      left; congruence.
    + right; congruence.
Qed.

Definition traverse_list f k: list pseudoterm -> list pseudoterm :=
  fold_right (fun t ts =>
    f (length ts + k) t :: ts) [].

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
    negation (traverse_list (traverse f) k ts)
  | jump x xs =>
    jump (traverse f k x) (map (traverse f k) xs)
  | bind b ts c =>
    bind (traverse f (S k) b) (traverse_list (traverse f) k ts)
      (traverse f (k + length ts) c)
  end.

Definition lift i: nat -> pseudoterm -> pseudoterm :=
  traverse (fun k n =>
    if le_gt_dec k n then
      bound (i + n)
    else
      bound n).

Definition subst y: nat -> pseudoterm -> pseudoterm :=
  traverse (fun k n =>
    match lt_eq_lt_dec k n with
    | inleft (left _) => bound (pred n)
    | inleft (right _) => lift k 0 y
    | inright _ => bound n
    end).

Inductive not_free: nat -> pseudoterm -> Prop :=
  | not_free_type:
    forall n,
    not_free n type
  | not_free_prop:
    forall n,
    not_free n prop
  | not_free_base:
    forall n,
    not_free n base
  | not_free_void:
    forall n,
    not_free n void
  | not_free_bound:
    forall n m,
    n <> m -> not_free n m
  | not_free_negation:
    forall n ts,
    not_free_list n ts ->
    not_free n (negation ts)
  | not_free_jump:
    forall n x ts,
    not_free n x ->
    Forall (not_free n) ts -> not_free n (jump x ts)
  | not_free_bind:
    forall n b ts c,
    not_free (S n) b ->
    not_free_list n ts ->
    not_free (length ts + n) c ->
    not_free n (bind b ts c)

with not_free_list: nat -> list pseudoterm -> Prop :=
  | not_free_list_nil:
    forall n,
    not_free_list n []
  | not_free_list_cons:
    forall n t ts,
    not_free (length ts + n) t ->
    not_free_list n ts ->
    not_free_list n (t :: ts).

Global Hint Constructors not_free: cps.
Global Hint Constructors not_free_list: cps.

Definition free n e: Prop :=
  ~not_free n e.

Global Hint Unfold free: cps.
