(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Arith.
Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.

Inductive CL: Set :=
  | bound (n: nat)
  | S: CL
  | K: CL
  | app: CL -> CL -> CL.

Coercion bound: nat >-> CL.
Coercion app: CL >-> Funclass.

Definition I: CL :=
  S K K.

Definition B: CL :=
  S (K S) K.

Definition C: CL :=
  S (S (K (S (K S) K)) S) (K K).

Definition F: CL :=
  S K.

Definition P: CL :=
  C (B B (B C (B (C I) I))) I.

Inductive step: relation CL :=
  | step_S:
    forall x y z,
    step (S x y z) (x z (y z))
  | step_K:
    forall x y,
    step (K x y) x
  | step_app_left:
    forall x1 x2 y,
    step x1 x2 ->
    step (app x1 y) (app x2 y)
  | step_app_right:
    forall x y1 y2,
    step y1 y2 ->
    step (app x y1) (app x y2).

Definition conv: relation CL :=
  rst(step).

Definition conv_S:
  forall x y z,
  conv (S x y z) (x z (y z)).
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply step_S.
Qed.

Definition conv_K:
  forall x y,
  conv (K x y) x.
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply step_K.
Qed.

Instance conv_equiv:
  Equivalence conv.
Proof.
  split; repeat intro.
  - apply rst_refl.
  - now apply rst_sym.
  - now apply rst_trans with y.
Qed.

Instance conv_app_proper:
  Proper (conv ==> conv ==> conv) app.
Proof.
  repeat intro.
  transitivity (y x0).
  - clear H0 y0.
    induction H.
    + apply rst_step.
      now apply step_app_left.
    + reflexivity.
    + now symmetry.
    + now transitivity (y x0).
  - clear H x.
    induction H0.
    + apply rst_step.
      now apply step_app_right.
    + reflexivity.
    + now symmetry.
    + now transitivity (y y0).
Qed.

Definition conv_I:
  forall x,
  conv (I x) x.
Proof.
  intros.
  unfold I.
  rewrite conv_S.
  rewrite conv_K.
  reflexivity.
Qed.

Definition conv_B:
  forall x y z,
  conv (B x y z) (x (y z)).
Proof.
  intros.
  unfold B.
  rewrite conv_S.
  rewrite conv_K.
  rewrite conv_S.
  rewrite conv_K.
  reflexivity.
Qed.

Definition conv_C:
  forall x y z,
  conv (C x y z) (x z y).
Proof.
  intros.
  unfold C.
  rewrite conv_S.
  rewrite conv_S.
  rewrite conv_K.
  rewrite conv_S.
  rewrite conv_K.
  rewrite conv_S.
  rewrite conv_K.
  rewrite conv_S.
  rewrite conv_K.
  rewrite conv_K.
  reflexivity.
Qed.

Definition conv_F:
  forall x y,
  conv (F x y) y.
Proof.
  intros.
  unfold F.
  rewrite conv_S.
  rewrite conv_K.
  reflexivity.
Qed.

Definition conv_P:
  forall x y f,
  conv (P x y f) (f x y).
Proof.
  intros.
  unfold P.
  rewrite conv_C.
  rewrite conv_B.
  rewrite conv_B.
  rewrite conv_B.
  rewrite conv_C.
  rewrite conv_B.
  rewrite conv_C.
  rewrite conv_I.
  rewrite conv_I.
  rewrite conv_I.
  reflexivity.
Qed.

Fixpoint cl_traverse (f: nat -> nat -> CL) (k: nat) (e: CL): CL :=
  match e with
  | bound n =>
    f k n
  | S =>
    S
  | K =>
    K
  | app e1 e2 =>
    app (cl_traverse f k e1) (cl_traverse f k e2)
  end.

Global Instance cl_dbVar: dbVar CL :=
  bound.

Global Instance cl_dbTraverse: dbTraverse CL CL :=
  cl_traverse.

Global Instance cl_dbVarLaws: dbVarLaws CL.
Proof.
  split; intros.
  reflexivity.
Qed.

Global Instance cl_dbTraverseLaws: dbTraverseLaws CL CL.
Proof.
  split; intros.
  - unfold traverse, cl_dbTraverse.
    induction x; simpl; eauto.
    congruence.
  - apply (H k (bound n)).
  - unfold traverse, cl_dbTraverse.
    induction x; simpl; eauto.
    + apply (H 0 n).
    + congruence.
  - unfold traverse, cl_dbTraverse.
    induction x; simpl; eauto.
    congruence.
Qed.

Inductive not_free: nat -> CL -> Prop :=
  | not_free_bound:
    forall n m,
    n <> m -> not_free n m
  | not_free_S:
    forall n,
    not_free n S
  | not_free_K:
    forall n,
    not_free n K
  | not_free_app:
    forall n e f,
    not_free n e ->
    not_free n f ->
    not_free n (e f).

Definition free n e: Prop :=
  ~not_free n e.

(* TODO: check if this name is consistent with the remaining of the codebase,
   cause I don't remember it now. *)

Program Fixpoint free_not_free_dec n e: { free n e } + { not_free n e } :=
  match e with
  | bound m =>
    if Nat.eq_dec n m then
      left _
    else
      right _
  | S =>
    right _
  | K =>
    right _
  | app f g =>
    if free_not_free_dec n f then
      left _
    else
      if free_not_free_dec n g then
        left _
      else
        right _
  end.

Next Obligation of free_not_free_dec.
  inversion 1; subst.
  contradiction.
Qed.

Next Obligation of free_not_free_dec.
  now constructor.
Qed.

Next Obligation of free_not_free_dec.
  constructor.
Qed.

Next Obligation of free_not_free_dec.
  constructor.
Qed.

Next Obligation of free_not_free_dec.
  intro.
  inversion H; subst.
  now apply f0.
Qed.

Next Obligation of free_not_free_dec.
  intro.
  inversion H; subst.
  now apply f0.
Qed.

Next Obligation of free_not_free_dec.
  now constructor.
Qed.

(* TODO: bracket abstraction, just for fun, then define P and F with it. *)
