(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.

Export ListNotations.

Variant mode: Set :=
  | mode_input
  | mode_output.

Notation I := mode_input.
Notation O := mode_output.

Inductive type: Set :=
  | channel (m: mode) (ts: list type).

Inductive term: Set :=
  | inactive
  | restriction (t: type) (p: term)
  | parallel (p: term) (q: term)
  | output (k: nat) (ns: list nat)
  | input (k: nat) (ts: list type) (p: term)
  | replicated_input (k: nat) (ts: list type) (p: term).

Notation poly_restriction :=
  (fold_left (fun e t => restriction t e)).

Fixpoint sequence i n :=
  match n with
  | 0 => []
  | S m => i :: sequence (1 + i) m
  end.

Definition bound_output (n: nat) (ts: list type) (p: term) :=
  (* TODO: reuse this from the CPS-calculus? *)
  poly_restriction ts (parallel (output (length ts + n)
                                (sequence 0 (length ts))) p).

Fixpoint traverse (f: nat -> nat -> nat) (k: nat) (e: term): term :=
  match e with
  | inactive =>
    inactive
  | restriction t p =>
    restriction t (traverse f (S k) p)
  | parallel p q =>
    parallel (traverse f k p) (traverse f k q)
  | output n ns =>
    output (f k n) (map (f k) ns)
  | input n ts p =>
    input (f k n) ts (traverse f (length ts + k) p)
  | replicated_input n ts p =>
    replicated_input (f k n) ts (traverse f (length ts + k) p)
  end.

Global Instance pi_dbTraverse: dbTraverse term nat :=
  traverse.

Global Instance pi_dbTraverseLaws: dbTraverseLaws term nat.
Proof.
  split; unfold Substitution.traverse; intros.
  - generalize dependent k.
    induction x; intros; simpl; auto;
    f_equal; eauto.
    induction ns; auto; simpl;
    f_equal; eauto.
  - specialize (H k (output n [])).
    dependent destruction H.
    assumption.
  - generalize dependent j.
    generalize dependent k.
    induction x; intros; simpl; auto;
    f_equal; auto.
    + apply IHx; intros.
      replace (l + S k) with (S l + k) by lia.
      replace (l + S j) with (S l + j) by lia.
      apply H.
    + apply H with (l := 0).
    + induction ns; auto; simpl; f_equal; auto.
      apply H with (l := 0).
    + apply H with (l := 0).
    + apply IHx; intros.
      do 2 rewrite Nat.add_assoc.
      apply H.
    + apply H with (l := 0).
    + apply IHx; intros.
      do 2 rewrite Nat.add_assoc.
      apply H.
  - generalize dependent k.
    induction x; intros; simpl; auto;
    f_equal; auto.
    now rewrite map_map.
Qed.

Definition inverse (m: mode): mode :=
  match m with
  | I => O
  | O => I
  end.

Fixpoint dual (t: type): type :=
  match t with
  | channel m ts =>
    channel (inverse m) (map dual ts)
  end.

Lemma dual_is_involutive:
  forall t,
  dual (dual t) = t.
Proof.
  fix H 1; destruct t.
  destruct m; simpl.
  - rewrite map_map; f_equal.
    induction ts; simpl.
    + reflexivity.
    + f_equal; auto.
  - rewrite map_map; f_equal.
    induction ts; simpl.
    + reflexivity.
    + f_equal; auto.
Qed.

Inductive alternating: mode -> type -> Prop :=
  | alternating_input:
    forall ts,
    Forall (alternating O) ts ->
    alternating I (channel I ts)
  | alternating_output:
    forall ts,
    Forall (alternating I) ts ->
    alternating O (channel O ts).

Lemma alternating_inverse_dual:
  forall m t,
  alternating m t ->
  alternating (inverse m) (dual t).
Proof.
  fix H 3; destruct 1; simpl.
  - constructor.
    induction H0; simpl.
    + constructor.
    + constructor; auto.
      now apply H in H0.
  - constructor.
    induction H0; simpl.
    + constructor.
    + constructor; auto.
      now apply H in H0.
Qed.

Definition get_mode (t: type): mode :=
  match t with
  | channel m ts => m
  end.

(* TODO: define size? *)

(* TODO: define subterm? *)

(* TODO: define context. *)

Inductive not_free: nat -> term -> Prop :=
  | not_free_inactive:
    forall n,
    not_free n inactive
  | not_free_restriction:
    forall n t p,
    not_free (S n) p ->
    not_free n (restriction t p)
  | not_free_parallel:
    forall n p q,
    not_free n p ->
    not_free n q ->
    not_free n (parallel p q)
  | not_free_output:
    forall n k ns,
    n <> k ->
    Forall (fun m => n <> m) ns ->
    not_free n (output k ns)
  | not_free_input:
    forall n k ts p,
    n <> k ->
    not_free (length ts + n) p ->
    not_free n (input k ts p)
  | not_free_replicated_input:
    forall n k ts p,
    n <> k ->
    not_free (length ts + n) p ->
    not_free n (replicated_input k ts p).

Definition free (n: nat) (e: term): Prop :=
  ~not_free n e.

Definition closed (e: term): Prop :=
  forall n, not_free n e.

(* ... *)

Inductive structural: relation term := .

(* TODO: define canonical forms. *)

Inductive step: relation term :=
  | step_linear:
    (* x<y> | x(z).p -> p[y/z] *)
    forall x ys ts p,
    length ys = length ts ->
    step (parallel (output x ys) (input x ts p))
         (inst (subst_app ys subst_ids) p)
  | step_replicated:
    (* x<y> | !x(z).p -> p[y/z] | !x(z).p *)
    forall x ys ts p,
    length ys = length ts ->
    step (parallel (output x ys) (replicated_input x ts p))
         (parallel (inst (subst_app ys subst_ids) p) (replicated_input x ts p))
  | step_restriction:
    forall t p q,
    step p q ->
    step (restriction t p) (restriction t q)
  | step_parallel:
    forall p q r,
    step p q ->
    step (parallel p r) (parallel q r)
  | step_structural:
    forall p1 p2 q1 q2,
    rst(structural) p1 p2 ->
    step p2 q1 ->
    rst(structural) q1 q2 ->
    step p1 p2.

Goal
  (* Let's check that the bound output version, [y] p | x(y).q -> (\y)(p | q),
     as described in Honda's paper, is derivable with the above definitions. *)
  forall ts x p q,
  step (parallel (bound_output x ts p) (input x ts p))
       (poly_restriction ts (parallel p q)).
Proof.
  induction ts using rev_ind; intros.
  - admit.
  - admit.
Admitted.

(* TODO: define barbed congruence. *)

(* TODO: define and try to prove equational theory...? *)
