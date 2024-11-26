(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Local.Prelude.
Require Import Local.Substitution.

Variant universe: Set :=
  | prop
  | type.

Inductive term: Set :=
  (* Sorts. *)
  | sort (s: universe)
  (* Variables. *)
  | bound (n: nat)
  (* Products. *)
  | pi (t: term) (u: term)
  | abstraction (t: term) (e: term)
  | application (e: term) (f: term)
  | definition (e: term) (t: term) (f: term).

Global Coercion sort: universe >-> term.

Fixpoint traverse g k e: term :=
  match e with
  | sort u =>
    sort u
  | bound n =>
    g k n 
  | pi t u =>
    pi (traverse g k t) (traverse g (S k) u)
  | abstraction t e =>
    abstraction (traverse g k t) (traverse g (S k) e)
  | application e f =>
    application (traverse g k e) (traverse g k f)
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

Inductive context: Set :=
  | context_hole
  | context_pi_type (t: context) (u: term)
  | context_pi_body (t: term) (u: context)
  | context_abs_type (t: context) (e: term)
  | context_abs_body (t: term) (e: context)
  | context_app_left (f: context) (e: term)
  | context_app_right (f: term) (e: context)
  | context_def_val (e: context) (t: term) (f: term)
  | context_def_type (e: term) (t: context) (f: term)
  | context_def_body (e: term) (t: term) (f: context).

Fixpoint apply_context (h: context) (x: term): term :=
  match h with
  | context_hole =>
    x
  | context_pi_type t u =>
    pi (apply_context t x) u
  | context_pi_body t u =>
    pi t (apply_context u x)
  | context_abs_type t e =>
    abstraction (apply_context t x) e
  | context_abs_body t e =>
    abstraction t (apply_context e x)
  | context_app_left f e =>
    application (apply_context f x) e
  | context_app_right f e =>
    application f (apply_context e x)
  | context_def_val e t f =>
    definition (apply_context e x) t f
  | context_def_type e t f =>
    definition e (apply_context t x) f
  | context_def_body e t f =>
    definition e t (apply_context f x)
  end.

Coercion apply_context: context >-> Funclass.

Definition decl: Set :=
  option term * term.

Definition decl_var (t: term): decl :=
  (None, t).

Definition decl_def (e: term) (t: term): decl :=
  (Some e, t).

Definition env: Set :=
  list decl.
