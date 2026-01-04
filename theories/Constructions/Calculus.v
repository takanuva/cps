(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Local.Prelude.
Require Import Local.Substitution.

(* Slightly unusual type system: we don't have an universe of propositions yet,
   but we do have impredicative (computationally relevant) sets and an infinite
   hierarchy of predicative types. *)

Variant universe: Set :=
  | iset
  | type (n: nat).

Definition top (s1: universe) (s2: universe) :=
  match s1, s2 with
  | _, iset => s1
  | iset, _ => s2
  | type n, type m => type (max n m)
  end.

Definition sort_of_product (s1: universe) (s2: universe) :=
  if s2 (* is iset *) then
    iset
  else
    top s1 s2.

Inductive term: Set :=
  (* Sorts. *)
  | sort (s: universe)
  (* Variables. *)
  | bound (n: nat)
  (* Products. *)
  | pi (t: term) (u: term)
  | abstraction (t: term) (e: term)
  | application (e: term) (f: term)
  (* | definition (e: term) (t: term) (f: term)
  (* Pairs. *)
  | sigma (t: term) (u: term)
  | pair (e: term) (f: term) (t: term)
  | proj1 (e: term)
  | proj2 (e: term)
  (* Booleans. *)
  | boolean
  | bool_tt
  | bool_ff
  | bool_if (e: term) (t: term) (f1: term) (f2: term)
  (* Thunks. *)
  | thunk (t: term)
  | delay (e: term)
  | force (e: term) *).

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
  (* | definition e t f =>
    definition (traverse g k e) (traverse g k t) (traverse g (S k) f)
  | sigma t u =>
    sigma (traverse g k t) (traverse g (S k) u)
  | pair e f t =>
    pair (traverse g k e) (traverse g k f) (traverse g k t)
  | proj1 e =>
    proj1 (traverse g k e)
  | proj2 e =>
    proj2 (traverse g k e)
  | boolean =>
    boolean
  | bool_tt =>
    bool_tt
  | bool_ff =>
    bool_ff
  | bool_if e t f1 f2 =>
    let rec := traverse in
    bool_if (rec g k e) (rec g (S k) t) (rec g k f1) (rec g k f2)
  | thunk t =>
    thunk (traverse g k t)
  | delay e =>
    delay (traverse g k e)
  | force e =>
    force (traverse g k e) *)
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
    (* + f_equal.
      * apply IHx1; intros.
        apply H.
      * apply IHx2; intros.
        apply H.
      * apply IHx3; intros.
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
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H.
      * apply IHx3; intros.
        apply H.
      * apply IHx4; intros.
        apply H. *)
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
  (* | context_def_val (e: context) (t: term) (f: term)
  | context_def_type (e: term) (t: context) (f: term)
  | context_def_body (e: term) (t: term) (f: context)
  | context_sigma_type (t: context) (u: term)
  | context_sigma_body (t: term) (u: context)
  | context_pair_left (e: context) (f: term) (t: term)
  | context_pair_right (e: term) (f: context) (t: term)
  | context_pair_type (e: term) (f: term) (t: context)
  | context_proj1 (e: context)
  | context_proj2 (e: context)
  | context_if_term (e: context) (t: term) (f1: term) (f2: term)
  | context_if_type (e: term) (t: context) (f1: term) (f2: term)
  | context_if_then (e: term) (t: term) (f1: context) (f2: term)
  | context_if_else (e: term) (t: term) (f1: term) (f2: context)
  | context_thunk (t: context)
  | context_delay (e: context)
  | context_force (e: context) *).

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
  (* | context_def_val e t f =>
    definition (apply_context e x) t f
  | context_def_type e t f =>
    definition e (apply_context t x) f
  | context_def_body e t f =>
    definition e t (apply_context f x)
  | context_sigma_type t u =>
    sigma (apply_context t x) u
  | context_sigma_body t u =>
    sigma t (apply_context u x)
  | context_pair_left e f t =>
    pair (apply_context e x) f t
  | context_pair_right e f t =>
    pair e (apply_context f x) t
  | context_pair_type e f t =>
    pair e f (apply_context t x)
  | context_proj1 e =>
    proj1 (apply_context e x)
  | context_proj2 e =>
    proj2 (apply_context e x)
  | context_if_term e t f1 f2 =>
    bool_if (apply_context e x) t f1 f2
  | context_if_type e t f1 f2 =>
    bool_if e (apply_context t x) f1 f2
  | context_if_then e t f1 f2 =>
    bool_if e t (apply_context f1 x) f2
  | context_if_else e t f1 f2 =>
    bool_if e t f1 (apply_context f2 x)
  | context_thunk t =>
    thunk (apply_context t x)
  | context_delay e =>
    delay (apply_context e x)
  | context_force e =>
    force (apply_context e x) *)
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

Inductive value: term -> Prop :=
  | value_sort:
    forall s,
    value (sort s)
  | value_bound:
    forall n,
    value (bound n)
  | value_pi:
    forall t u,
    value (pi t u)
  | value_abstraction:
    forall t e,
    value (abstraction t e)
  (* | value_sigma:
    forall t u,
    value (sigma t u)
  | value_pair:
    forall e f t,
    value e ->
    value f ->
    value (pair e f t)
  | value_true:
    value bool_tt
  | value_false:
    value bool_ff
  (* TODO: thunks... *) *).

Global Hint Constructors value: cps.
