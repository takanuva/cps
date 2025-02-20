(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.

Import ListNotations.

(** ** Syntax

    In the original formulation for this code, such as presented in the ICFP 24
    paper [...], we had types directly encoded in the syntax for terms. [...] *)

Variant type_tag: Set :=
  | VOID
  | BASE
  | NEGATION.

(** [...]. *)

Inductive pseudoterm: Set :=
  | bound (n: nat)
  | type (x: type_tag) (xs: list pseudoterm)
  | jump (f: pseudoterm) (xs: list pseudoterm)
  | bind (b: pseudoterm) (ts: list pseudoterm) (c: pseudoterm).

Coercion bound: nat >-> pseudoterm.

Global Notation void :=
  (type VOID []).

Global Notation base :=
  (type BASE []).

Global Notation negation ts :=
  (type NEGATION ts).

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

(** ... *)

Lemma pseudoterm_deepind:
  forall P: pseudoterm -> Prop,
  forall f1: (forall n, P (bound n)),
  forall f2: (forall x ts, Forall P ts -> P (type x ts)),
  forall f3: (forall k xs, P k -> Forall P xs -> P (jump k xs)),
  forall f4: (forall b ts c, P b -> Forall P ts -> P c -> P (bind b ts c)),
  forall e,
  P e.
Proof.
  do 5 intro.
  fix IH 1; destruct e.
  (* Case: bound. *)
  - apply f1.
  (* Case: type. *)
  - apply f2.
    induction xs.
    + constructor.
    + constructor; auto.
  (* Case: jump. *)
  - apply f3; auto.
    induction xs.
    + constructor.
    + constructor; auto.
  (* Case: bind. *)
  - apply f4; auto.
    induction ts.
    + constructor.
    + constructor; auto.
Qed.

(** Equality on pseudoterms (and pseudotypes) is decidable. *)

Lemma pseudoterm_eq_dec:
  forall b c: pseudoterm,
  { b = c } + { b <> c }.
Proof with try now (right; congruence).
  fix IH 1; intros.
  destruct b; destruct c...
  (* Case: bound. *)
  - destruct Nat.eq_dec with n n0...
    subst; now left.
  (* Case: type. *)
  - assert ({ x = x0 } + { x <> x0 }) as [ ? | ? ]...
    + decide equality.
    + assert ({ xs = xs0 } + { xs <> xs0 }) as [ ? | ? ]...
      * now apply list_eq_dec.
      * subst; now left.
  (* Case: jump. *)
  - destruct IH with b c...
    assert ({ xs = xs0 } + { xs <> xs0 }) as [ ? | ? ]...
    + now apply list_eq_dec.
    + subst; now left.
  (* Case: bind. *)
  - destruct IH with b1 c1...
    destruct IH with b2 c2...
    assert ({ ts = ts0 } + { ts <> ts0 }) as [ ? | ? ]...
    + now apply list_eq_dec.
    + subst; now left.
Qed.

(* TODO: do we actually need this anymore...? Try removing this definition! *)

Definition traverse_list {T} f k: list T -> list T :=
  fold_right (fun t ts => f (length ts + k) t :: ts) [].

Definition type_binder x i :=
  match x, i with
  | VOID, _ => 0
  | BASE, _ => 0
  | NEGATION, _ => i
  end.

Definition traverse_type {T} x f k: list T -> list T :=
  fold_right (fun t ts => f (type_binder x (length ts) + k) t :: ts) [].

Local Goal
  forall {T} f k ts,
  @map T T (f k) ts = @traverse_type T BASE f k ts.
Proof.
  auto.
Qed.

Local Goal
  forall {T} f k ts,
  @traverse_list T f k ts = @traverse_type T NEGATION f k ts.
Proof.
  auto.
Qed.

Fixpoint traverse f k e: pseudoterm :=
  match e with
  | bound n =>
    f k n
  | type x ts =>
    type x (traverse_type x (traverse f) k ts)
  | jump x xs =>
    jump (traverse f k x) (map (traverse f k) xs)
  | bind b ts c =>
    bind (traverse f (S k) b) (traverse_list (traverse f) k ts)
      (traverse f (k + length ts) c)
  end.

Global Instance pseudoterm_dbVar: dbVar pseudoterm :=
  bound.

Global Instance pseudoterm_dbTraverse: dbTraverse pseudoterm pseudoterm :=
  traverse.

(* -------------------------------------------------------------------------- *)

(* TODO: rename... or, appropriately, find a way for sigma to derive this. *)

Lemma bound_var_equality_stuff:
  forall n,
  bound n = var n.
Proof.
  auto.
Qed.

Lemma inst_distributes_over_type:
  forall s x ts,
  inst s (type x ts) = type x (traverse_type x s 0 ts).
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
  inst s (bind b ts c) = bind (s 1 b) (bsmap s 0 ts) (s (length ts) c).
Proof.
  auto.
Qed.

Global Hint Rewrite bound_var_equality_stuff using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_type using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_jump using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_bind using sigma_solver: sigma.

(* -------------------------------------------------------------------------- *)

Definition apply_parameters (ys: list pseudoterm): substitution :=
  subst_app ys subst_ids.

Definition switch_bindings: substitution :=
  subst_app [bound 1; bound 0] (subst_lift 2).

(* TODO: there's a "seq" fixpoint on Coq's List module. We should use it! *)

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
  | not_free_type:
    forall x n ts,
    not_free_list x n ts ->
    not_free n (type x ts)
  | not_free_jump:
    forall n x ts,
    not_free n x ->
    Forall (not_free n) ts ->
    not_free n (jump x ts)
  | not_free_bind:
    forall n b ts c,
    not_free (S n) b ->
    not_free_list NEGATION n ts ->
    not_free (length ts + n) c ->
    not_free n (bind b ts c)

(* Checks a list following a type binder descriptor. *)
with not_free_list: type_tag -> nat -> list pseudoterm -> Prop :=
  | not_free_list_nil:
    forall x n,
    not_free_list x n []
  | not_free_list_cons:
    forall x n t ts,
    not_free (type_binder x (length ts) + n) t ->
    not_free_list x n ts ->
    not_free_list x n (t :: ts).

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
