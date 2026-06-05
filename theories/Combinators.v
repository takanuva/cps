(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Arith.
Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Setoid.
Require Import Local.Universe.
Require Import Local.Sets.

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

Definition CL_equiv: relation CL :=
  rst(step).

Lemma CL_equiv_refl:
  forall x,
  CL_equiv x x.
Proof.
  intros.
  apply rst_refl.
Qed.

Lemma CL_equiv_sym:
  forall x y,
  CL_equiv x y -> CL_equiv y x.
Proof.
  intros.
  now apply rst_sym.
Qed.

Lemma CL_equiv_trans:
  forall x y z,
  CL_equiv x y -> CL_equiv y z -> CL_equiv x z.
Proof.
  intros.
  now apply rst_trans with y.
Qed.

Definition CL_setoid: Setoid := {|
  setoid_carrier := CL;
  setoid_equiv := CL_equiv;
  setoid_refl := CL_equiv_refl;
  setoid_sym := CL_equiv_sym;
  setoid_trans := CL_equiv_trans
|}.

Global Canonical Structure CL_setoid.

Definition CL_equiv_S:
  forall x y z,
  CL_equiv (S x y z) (x z (y z)).
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply step_S.
Qed.

Definition CL_equiv_K:
  forall x y,
  CL_equiv (K x y) x.
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply step_K.
Qed.

Global Instance CL_equiv_app_proper:
  Proper (CL_equiv ==> CL_equiv ==> CL_equiv) app.
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

Global Instance setoid_equiv_app_proper:
  Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) app.
Proof.
  apply CL_equiv_app_proper.
Qed.

Definition CL_equiv_I:
  forall x,
  CL_equiv (I x) x.
Proof.
  intros.
  unfold I.
  rewrite CL_equiv_S.
  rewrite CL_equiv_K.
  reflexivity.
Qed.

Definition CL_equiv_B:
  forall x y z,
  CL_equiv (B x y z) (x (y z)).
Proof.
  intros.
  unfold B.
  rewrite CL_equiv_S.
  rewrite CL_equiv_K.
  rewrite CL_equiv_S.
  rewrite CL_equiv_K.
  reflexivity.
Qed.

Definition CL_equiv_C:
  forall x y z,
  CL_equiv (C x y z) (x z y).
Proof.
  intros.
  unfold C.
  rewrite CL_equiv_S.
  rewrite CL_equiv_S.
  rewrite CL_equiv_K.
  rewrite CL_equiv_S.
  rewrite CL_equiv_K.
  rewrite CL_equiv_S.
  rewrite CL_equiv_K.
  rewrite CL_equiv_S.
  rewrite CL_equiv_K.
  rewrite CL_equiv_K.
  reflexivity.
Qed.

Definition CL_equiv_F:
  forall x y,
  CL_equiv (F x y) y.
Proof.
  intros.
  unfold F.
  rewrite CL_equiv_S.
  rewrite CL_equiv_K.
  reflexivity.
Qed.

Definition CL_equiv_P:
  forall x y f,
  CL_equiv (P x y f) (f x y).
Proof.
  intros.
  unfold P.
  rewrite CL_equiv_C.
  rewrite CL_equiv_B.
  rewrite CL_equiv_B.
  rewrite CL_equiv_B.
  rewrite CL_equiv_C.
  rewrite CL_equiv_B.
  rewrite CL_equiv_C.
  rewrite CL_equiv_I.
  rewrite CL_equiv_I.
  rewrite CL_equiv_I.
  reflexivity.
Qed.

Fixpoint CL_traverse (f: nat -> nat -> CL) (k: nat) (e: CL): CL :=
  match e with
  | bound n =>
    f k n
  | S =>
    S
  | K =>
    K
  | app e1 e2 =>
    app (CL_traverse f k e1) (CL_traverse f k e2)
  end.

Global Instance CL_dbVar: dbVar CL :=
  bound.

Global Instance CL_dbTraverse: dbTraverse CL CL :=
  CL_traverse.

Global Instance CL_dbVarLaws: dbVarLaws CL.
Proof.
  split; intros.
  reflexivity.
Qed.

Global Instance CL_dbTraverseLaws: dbTraverseLaws CL CL.
Proof.
  split; intros.
  - unfold traverse, CL_dbTraverse.
    induction x; simpl; eauto.
    congruence.
  - apply (H k (bound n)).
  - unfold traverse, CL_dbTraverse.
    induction x; simpl; eauto.
    + apply (H 0 n).
    + congruence.
  - unfold traverse, CL_dbTraverse.
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
