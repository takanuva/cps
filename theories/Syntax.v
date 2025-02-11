(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Arith.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.

Import ListNotations.

(** ** Syntax

    In the original formulation for this code, such as presented in the ICFP 24
    paper, we had types directly encoded in the syntax for terms. In order to
    properly reuse the proofs for different type systems (such as simple types
    and dependent types), we now use a distinct definition. *)

Inductive pseudotype: Set :=
  | base
  | negation (ts: list pseudotype)

(** We give a higher order definition for the syntax of the CPS-calculus, in a
    way inspired by how dependent type theories are usually given. This was
    originally done so because we wanted to simplify the de Bruijn arithmetic
    stuff. However, now that we got the sigma library doing most of the work,
    there's no reason for this anymore and this code can shift to a first order
    presentation. TODO: define atomics and do it. *)

with pseudoterm: Set :=
  | bound (n: nat)
  | jump (f: pseudoterm) (xs: list pseudoterm)
  | bind (b: pseudoterm) (ts: list pseudotype) (c: pseudoterm).

Coercion bound: nat >-> pseudoterm.

(** A simple example.

    We use a lambda syntax to bind the name of free variables for illustration
    purposes. Notice that in the written syntax, the most recent term (index 0)
    is at the rightmost position, while in the abstract syntax we use here it's
    the leftmost one, so we always write lists (of types or terms) inverted. As
    such, [ex1] is equivalent to the following term:

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

(** We define a predicate stating that a pseudoterm appears inside a pseudotype,
    as in the dependent cases, to simplify the inductive hypotheses. *)

Inductive dependent: pseudoterm -> pseudotype -> Prop :=
  (* For now, we don't define any dependent types, so this is empty. *).

Definition Dep (P: pseudoterm -> Prop) (t: pseudotype): Prop :=
  forall b, dependent b t -> P b.

(** As we have lists inside our pseudoterms, we'll need a stronger induction
    principle for it, stating that propositions are kept inside those lists. *)

Definition pseudoterm_deepind:
  forall P: pseudoterm -> Prop,
  forall f1:
    (forall n, P (bound n)),
  forall f2:
    (forall k xs, P k -> Forall P xs -> P (jump k xs)),
  forall f3:
    (forall b ts c, P b -> Forall (Dep P) ts -> P c -> P (bind b ts c)),
  forall e,
  P e.
Proof.
  do 4 intro; fix H 1.
  destruct e.
  (* Case: bound. *)
  - apply f1.
  (* Case: jump. *)
  - apply f2; auto.
    induction xs; auto.
  (* Case: bind. *)
  - apply f3; auto.
    induction ts.
    + constructor.
    + constructor; auto.
      unfold Dep; intros.
      inversion H0.
Defined.

(** Equality on pseudoterms (and pseudotypes) is decidable. *)

Lemma pseudoterm_eq_dec:
  forall b c: pseudoterm,
  { b = c } + { b <> c }
with pseudotype_eq_dec:
  forall t u: pseudotype,
  { t = u } + { t <> u }.
Proof with try now (right; congruence).
  - destruct b; destruct c...
    (* Case: bound. *)
    + rename n into n1, n0 into n2.
      destruct Nat.eq_dec with n1 n2...
      left; congruence.
    (* Case: jump. *)
    + rename xs into xs1, xs0 into xs2.
      destruct list_eq_dec with pseudoterm xs1 xs2...
      * exact pseudoterm_eq_dec.
      * destruct pseudoterm_eq_dec with b c...
        left; congruence.
    (* Case: bind. *)
    + rename ts into ts1, ts0 into ts2.
      destruct list_eq_dec with pseudotype ts1 ts2...
      * exact pseudotype_eq_dec.
      * destruct pseudoterm_eq_dec with b1 c1...
        destruct pseudoterm_eq_dec with b2 c2...
        left; congruence.
  - destruct t; destruct u...
    (* Case: base. *)
    + now left.
    (* Case: negation. *)
    + rename ts into ts1, ts0 into ts2.
      destruct list_eq_dec with pseudotype ts1 ts2...
      * exact pseudotype_eq_dec.
      * left; congruence.
Qed.

(* TODO: is this definition still needed...? *)

Definition traverse_list f k: list pseudoterm -> list pseudoterm :=
  fold_right (fun t ts =>
    f (length ts + k) t :: ts) [].

Fixpoint traverse f k e: pseudoterm :=
  match e with
  | bound n =>
    f k n
  | jump x xs =>
    jump (traverse f k x) (map (traverse f k) xs)
  | bind b ts c =>
    (* TODO: for now, types don't contain variables... *)
    bind (traverse f (S k) b) ((* traverse_list (traverse f) k *) ts)
      (traverse f (k + length ts) c)
  end.

Global Instance pseudoterm_dbVar: dbVar pseudoterm :=
  bound.

Global Instance pseudoterm_dbTraverse: dbTraverse pseudoterm pseudoterm :=
  traverse.

(* -------------------------------------------------------------------------- *)

Lemma bound_var_equality_stuff:
  forall n,
  bound n = var n.
Proof.
  auto.
Qed.

Lemma inst_distributes_over_jump:
  forall s x xs,
  inst s (jump x xs) = jump (s 0 x) (smap s 0 xs).
Proof.
  auto.
Qed.

Lemma inst_distributes_over_bind:
  forall s b ts c,
  inst s (bind b ts c) = bind (s 1 b) ts (s (length ts) c).
Proof.
  auto.
Qed.

Global Hint Rewrite bound_var_equality_stuff using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_jump using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_bind using sigma_solver: sigma.

(* -------------------------------------------------------------------------- *)

Definition apply_parameters (ys: list pseudoterm): substitution :=
  subst_app ys subst_ids.

Definition switch_bindings: substitution :=
  subst_app [bound 1; bound 0] (subst_lift 2).

Fixpoint sequence (i: nat) (n: nat): list pseudoterm :=
  match n with
  | 0 => []
  | S m => bound i :: sequence (1 + i) m
  end.

Global Hint Unfold sequence: cps.

Notation high_sequence := (sequence 1).
Notation low_sequence := (sequence 0).

Definition right_cycle (i: nat): substitution :=
  subst_app (high_sequence i ++ [bound 0]) (subst_lift (S i)).

Global Hint Unfold right_cycle: cps.

Definition left_cycle i k e :=
  subst (bound i) k (lift 1 (1 + i + k) e).

Global Hint Unfold left_cycle: cps.

Definition remove_binding k e: pseudoterm :=
  subst (bound 0) k e.

Inductive not_free: nat -> pseudoterm -> Prop :=
  | not_free_bound:
    forall n m,
    n <> m -> not_free n m
  | not_free_jump:
    forall n x ts,
    not_free n x ->
    Forall (not_free n) ts -> not_free n (jump x ts)
  | not_free_bind:
    forall n b ts c,
    not_free (S n) b ->
    (* TODO: types don't have variables... yet. *)
    (* not_free_list n ts -> *)
    not_free (length ts + n) c ->
    not_free n (bind b ts c)

(* Checks a list in a telescope-like fashion. *)
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

Inductive subterm: relation pseudoterm :=
  | subterm_bind_left:
    forall b ts c,
    subterm b (bind b ts c)
  | subterm_bind_right:
    forall b ts c,
    subterm c (bind b ts c).

Fixpoint size (c: pseudoterm): nat :=
  match c with
  | bind b ts c =>
    1 + size b + size c
  | _ =>
    0
  end.
