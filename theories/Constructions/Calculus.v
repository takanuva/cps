(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.

Variant universe: Set :=
  | prop
  | type (n: nat).

Inductive term: Set :=
  (* Sorts. *)
  | sort (u: universe)
  (* Variables. *)
  | bound (n: nat)
  (* Products. *)
  | pi (t: term) (e: term)
  | abstraction (t: term) (e: term)
  | application (f: term) (e: term)
  | definition (e: term) (t: term) (f: term).

Fixpoint traverse g k e: term :=
  match e with
  | sort u =>
    sort u
  | bound n =>
    g k n 
  | pi t e =>
    pi (traverse g k t) (traverse g (S k) e)
  | abstraction t e =>
    abstraction (traverse g k t) (traverse g (S k) e)
  | application f e =>
    application (traverse g k f) (traverse g k e)
  | definition e t f =>
    definition (traverse g k e) (traverse g k t) (traverse g (S k) f)
  end.

Global Instance cc_dbVar: dbVar term :=
  bound.

Global Instance cc_dbTraverse: dbTraverse term term :=
  traverse.

Global Instance cc_dbVarLaws: dbVarLaws term.
Proof.
  split; auto.
Qed.

Global Instance cc_dbTraverseLaws: dbTraverseLaws term term.
Proof.
  split; unfold Substitution.traverse; intros.
  - generalize dependent k.
    induction x; simpl; auto; intros;
    f_equal; auto.
  - apply (H k (bound n)).
  - generalize dependent j.
    generalize dependent k.
    induction x; simpl; auto; intros;
    try now (f_equal; auto).
    + apply (H 0).
    + f_equal.
      * apply IHx1; intros.
        apply H.
      * apply IHx2; intros.
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H.
    + f_equal.
      * apply IHx1; intros.
        apply H.
      * apply IHx2; intros.
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H.
    + f_equal.
      * apply IHx1; intros.
        apply H.
      * apply IHx2; intros.
        apply H.
      * apply IHx3; intros.
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H.
  - generalize dependent k.
    induction x; simpl; intros; auto;
    f_equal; auto.
Qed.
