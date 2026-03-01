(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

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

Inductive step: relation CL :=
  | step_K:
    forall x y,
    step (K x y) x
  | step_S:
    forall x y z,
    step (S x y z) (x z (y z))
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

Definition conv_K:
  forall x y,
  conv (K x y) x.
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply step_K.
Qed.

Definition conv_S:
  forall x y z,
  conv (S x y z) (x z (y z)).
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply step_S.
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
