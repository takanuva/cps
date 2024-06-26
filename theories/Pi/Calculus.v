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
  | input (k: nat) (ts: list type) (p: term)
  | output (k: nat) (ns: list nat)
  | replication (p: term).

Definition bound_output (n: nat) (ts: list type) (p: term) :=
  let fix sequence i n :=
    match n with
    | 0 => []
    | S m => i :: sequence (1 + i) m
    end
  in fold_left (fun e t => restriction t e) ts
    (parallel (output (length ts + n) (sequence 0 (length ts))) p).

Fixpoint lift (i: nat) (k: nat) (e: term): term :=
  let conv n :=
    if le_gt_dec k n then
      i + n
    else
      n
  in match e with
  | inactive =>
    inactive
  | restriction t p =>
    restriction t (lift i (S k) p)
  | parallel p q =>
    parallel (lift i k p) (lift i k q)
  | input k ts p =>
    input (conv k) ts (lift i (length ts + k) p)
  | output k ns =>
    output (conv k) (map conv ns)
  | replication p =>
    replication (lift i k p)
  end.

Fixpoint subst (y: nat) (k: nat) (e: term): term :=
  let conv n :=
    match lt_eq_lt_dec k n with
    | inleft (left _) => pred n
    | inleft (right _) => k + y
    | inright _ => n
    end
  in match e with
  | inactive =>
    inactive
  | restriction t p =>
    restriction t (subst y (S k) p)
  | parallel p q =>
    parallel (subst y k p) (subst y k q)
  | input k ts p =>
    input (conv k) ts (subst y (length ts + k) p)
  | output k ns =>
    output (conv k) (map conv ns)
  | replication p =>
    replication (subst y k p)
  end.

(* Lemma type_eq_dec:
  forall t1 t2: type,
  { t1 = t2 } + { t1 <> t2 }.
Proof.
  fix H 1.
  destruct t1, t2.
  destruct m, m0.
  - destruct list_eq_dec with type ts ts0.
    + exact H.
    + left; now subst.
    + right; intro.
      dependent destruction H0.
      contradiction.
  - right; intro.
    dependent destruction H0.
  - right; intro.
    dependent destruction H0.
  - destruct list_eq_dec with type ts ts0.
    + exact H.
    + left; now subst.
    + right; intro.
      dependent destruction H0.
      contradiction.
Qed. *)

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
  | not_free_input:
    forall n k ts p,
    n <> k ->
    not_free (length ts + n) p ->
    not_free n (input k ts p)
  | not_free_output:
    forall n k ns,
    n <> k ->
    Forall (fun m => n <> m) ns ->
    not_free n (output k ns)
  | not_free_replication:
    forall n p,
    not_free n (replication p).

Definition free (n: nat) (e: term): Prop :=
  ~not_free n e.

Definition closed (e: term): Prop :=
  forall n, not_free n e.
