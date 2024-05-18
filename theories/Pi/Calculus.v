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
  | input (ts: list type) (p: term)
  | output (ns: list nat)
  | replication (p: term).

Fixpoint lift (i: nat) (k: nat) (e: term): term :=
  match e with
  | inactive =>
    inactive
  | restriction t p =>
    restriction t (lift i (S k) p)
  | parallel p q =>
    parallel (lift i k p) (lift i k q)
  | input ts p =>
    input ts (lift i (length ts + k) p)
  | output ns =>
    let conv n :=
      if le_gt_dec k n then
        i + n
      else
        n
    in output (map conv ns)
  | replication p =>
    replication (lift i k p)
  end.

Fixpoint subst (y: nat) (k: nat) (e: term): term :=
  match e with
  | inactive =>
    inactive
  | restriction t p =>
    restriction t (subst y (S k) p)
  | parallel p q =>
    parallel (subst y k p) (subst y k q)
  | input ts p =>
    input ts (subst y (length ts + k) p)
  | output ns =>
    let conv n :=
      match lt_eq_lt_dec k n with
      | inleft (left _) => pred n
      | inleft (right _) => k + y
      | inright _ => n
      end
    in output (map conv ns)
  | replication p =>
    replication (subst y k p)
  end.
