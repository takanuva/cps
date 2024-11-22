(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
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
  | application (e: term) (f: term)
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
  | context_pi_type (t: context) (e: term)
  | context_pi_body (t: term) (e: context)
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
  | context_pi_type t e =>
    pi (apply_context t x) e
  | context_pi_body t e =>
    pi t (apply_context e x)
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

Inductive decl: Set :=
  | decl_var (t: term)
  | decl_def (e: term) (t: term).

Definition env: Set :=
  list decl.

Inductive step (g: env): relation term :=
  | step_beta:
    forall t e f,
    step g (application (abstraction t e) f) (subst f 0 e)
  | step_zeta:
    forall e t f,
    step g (definition e t f) (subst e 0 f)
  | step_delta:
    forall t e n,
    item (decl_def e t) g n ->
    step g (bound n) (lift (S n) 0 e)
  | step_pi_type:
    forall t1 t2 e,
    step g t1 t2 ->
    step g (pi t1 e) (pi t2 e)
  | step_pi_body:
    forall t e1 e2,
    step g e1 e2 ->
    step g (pi t e1) (pi t e2)
  | step_abs_type:
    forall t1 t2 e,
    step g t1 t2 ->
    step g (abstraction t1 e) (abstraction t2 e)
  | step_abs_body:
    forall t e1 e2,
    step g e1 e2 ->
    step g (abstraction t e1) (abstraction t e2)
  | step_app_left:
    forall e1 e2 f,
    step g e1 e2 ->
    step g (application e1 f) (application e2 f)
  | step_app_right:
    forall e f1 f2,
    step g f1 f2 ->
    step g (application e f1) (application e f2)
  | step_def_val:
    forall e1 e2 t f,
    step g e1 e2 ->
    step g (definition e1 t f) (definition e2 t f)
  | step_def_type:
    forall e t1 t2 f,
    step g t1 t2 ->
    step g (definition e t1 f) (definition e t2 f)
  | step_def_body:
    forall e t f1 f2,
    step g f1 f2 ->
    step g (definition e t f1) (definition e t f2).

Lemma step_context:
  forall g e1 e2,
  step g e1 e2 ->
  forall h: context,
  step g (h e1) (h e2).
Proof.
  induction h; simpl; intros.
  - assumption.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
  - now constructor.
Qed.

Conjecture step_is_confluent: forall g, confluent (step g).

Inductive conv: env -> relation term :=
  | conv_join:
    forall g e1 e2 f,
    rt(step g) e1 f ->
    rt(step g) e2 f ->
    conv g e1 e2
  | conv_eta_left:
    forall g e1 e2 t f1 f2,
    rt(step g) e1 (abstraction t f1) ->
    rt(step g) e2 f2 ->
    conv (decl_var t :: g) f1 (application f2 (bound 0)) ->
    conv g e1 e2
  | conv_eta_right:
    forall g e1 e2 t f1 f2,
    rt(step g) e1 f1 ->
    rt(step g) e2 (abstraction t f2) ->
    conv (decl_var t :: g) (application f1 (bound 0)) f2 ->
    conv g e1 e2.

Lemma conv_refl:
  forall g,
  reflexive (conv g).
Proof.
  repeat intro.
  apply conv_join with x.
  - apply rt_refl.
  - apply rt_refl.
Qed.

Lemma conv_sym:
  forall g,
  symmetric (conv g).
Proof.
  induction 1.
  - now apply conv_join with f.
  - eapply conv_eta_right; eauto with cps.
  - eapply conv_eta_left; eauto with cps.
Qed.

Lemma conv_trans:
  forall g,
  transitive (conv g).
Proof.
  admit.
Admitted.
