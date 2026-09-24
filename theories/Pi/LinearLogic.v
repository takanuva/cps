(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Setoid.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Pi.Graph.
Require Import Local.Pi.Calculus.

Variant polarity: Set :=
  | positive
  | negative.

Inductive formula: Set :=
  (* Base formulas... *)
  | base (p: polarity)
  (* Units... *)
  | one
  | bot
  (* Multiplicatives... *)
  | tensor (t: formula) (u: formula)
  | par (t: formula) (u: formula)
  (* Exponentials... *)
  | ofcourse (t: formula)
  | whynot (t: formula).

Fixpoint negate (t: formula): formula :=
  match t with
  | base positive => base negative
  | base negative => base positive
  | one => bot
  | bot => one
  | tensor t u => par (negate t) (negate u)
  | par t u => tensor (negate t) (negate u)
  | ofcourse t => whynot (negate t)
  | whynot t => ofcourse (negate t)
  end.

Lemma negate_is_involutive:
  forall t,
  negate (negate t) = t.
Proof.
  induction t; simpl.
  - now destruct p.
  - reflexivity.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt.
Qed.
