(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.

Inductive CL: Set :=
  | K: CL
  | S: CL
  | app: CL -> CL -> CL.

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

Inductive CLstep: relation CL :=
  | CLstep_K:
    forall x y,
    CLstep (K x y) x
  | CLstep_S:
    forall x y z,
    CLstep (S x y z) (x z (y z))
  | CLstep_app_left:
    forall x1 x2 y,
    CLstep x1 x2 ->
    CLstep (app x1 y) (app x2 y)
  | CLstep_app_right:
    forall x y1 y2,
    CLstep y1 y2 ->
    CLstep (app x y1) (app x y2).

Definition CLeq: relation CL :=
  rst(CLstep).

Definition CLeq_K:
  forall x y,
  CLeq (K x y) x.
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply CLstep_K.
Qed.

Definition CLeq_S:
  forall x y z,
  CLeq (S x y z) (x z (y z)).
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply CLstep_S.
Qed.

Instance CLeq_equiv: Equivalence CLeq.
Proof.
  split; repeat intro.
  - apply rst_refl.
  - now apply rst_sym.
  - now apply rst_trans with y.
Qed.

Instance CLeq_app_proper:
  Proper (CLeq ==> CLeq ==> CLeq) app.
Proof.
  repeat intro.
  transitivity (y x0).
  - clear H0 y0.
    induction H.
    + apply rst_step.
      now apply CLstep_app_left.
    + reflexivity.
    + now symmetry.
    + now transitivity (y x0).
  - clear H x.
    induction H0.
    + apply rst_step.
      now apply CLstep_app_right.
    + reflexivity.
    + now symmetry.
    + now transitivity (y y0).
Qed.

Definition CLeq_I:
  forall x,
  CLeq (I x) x.
Proof.
  intros.
  unfold I.
  rewrite CLeq_S.
  rewrite CLeq_K.
  reflexivity.
Qed.

Definition CLeq_B:
  forall x y z,
  CLeq (B x y z) (x (y z)).
Proof.
  intros.
  unfold B.
  rewrite CLeq_S.
  rewrite CLeq_K.
  rewrite CLeq_S.
  rewrite CLeq_K.
  reflexivity.
Qed.

Definition CLeq_C:
  forall x y z,
  CLeq (C x y z) (x z y).
Proof.
  intros.
  unfold C.
  rewrite CLeq_S.
  rewrite CLeq_S.
  rewrite CLeq_K.
  rewrite CLeq_S.
  rewrite CLeq_K.
  rewrite CLeq_S.
  rewrite CLeq_K.
  rewrite CLeq_S.
  rewrite CLeq_K.
  rewrite CLeq_K.
  reflexivity.
Qed.

Definition CLeq_F:
  forall x y,
  CLeq (F x y) y.
Proof.
  intros.
  unfold F.
  rewrite CLeq_S.
  rewrite CLeq_K.
  reflexivity.
Qed.

Definition CLeq_P:
  forall x y f,
  CLeq (P x y f) (f x y).
Proof.
  intros.
  unfold P.
  rewrite CLeq_C.
  rewrite CLeq_B.
  rewrite CLeq_B.
  rewrite CLeq_B.
  rewrite CLeq_C.
  rewrite CLeq_B.
  rewrite CLeq_C.
  rewrite CLeq_I.
  rewrite CLeq_I.
  rewrite CLeq_I.
  reflexivity.
Qed.
