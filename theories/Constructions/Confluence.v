(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Equality.
Require Import Morphisms.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.

(* I can, of course, prove that this reduction relation is confluent. However,
   that will require a lot of code and a lot of time that I don't have at the
   moment. I might be tempted to come back here at some point and follow the
   procedure in the "Coq Coq Correct!" paper to actually prove this. *)

Conjecture step_is_confluent:
  forall g, confluent (step g).

Corollary step_is_church_rosser:
  forall g,
  church_rosser (step g).
Proof.
  intros.
  apply confluence_implies_church_rosser.
  apply step_is_confluent.
Qed.

Inductive step_env: relation env :=
  | step_env_head:
    forall g e1 e2,
    step g e1 e2 ->
    step_env (decl_var e1 :: g) (decl_var e2 :: g)
  | step_env_tail:
    forall g1 g2 e,
    step_env g1 g2 ->
    step_env (e :: g1) (e :: g2).

Lemma step_step_env:
  forall g1 e1 e2,
  step g1 e1 e2 ->
  forall g2,
  step_env g1 g2 ->
  step g2 e1 e2.
Proof.
  induction 1; intros.
  - constructor.
  - constructor.
  - apply step_delta with t.
    generalize dependent n.
    induction H0; intros.
    + inversion_clear H0.
      now constructor.
    + dependent destruction H.
      * constructor.
      * constructor.
        now apply IHstep_env.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  (* TODO: congruence rules... *)
Qed.

Lemma rt_step_rt_step_env:
  forall g1 e1 e2,
  rt(step g1) e1 e2 ->
  forall g2,
  rt(step_env) g1 g2 ->
  rt(step g2) e1 e2.
Proof.
  intros.
  generalize dependent e2.
  induction H0; intros.
  - induction H0.
    + apply rt_step.
      now apply step_step_env with x.
    + apply rt_refl.
    + eauto with cps.
  - assumption.
  - firstorder.
Qed.

Lemma rt_step_env_head:
  forall g e1 e2,
  rt(step g) e1 e2 ->
  rt(step_env) (decl_var e1 :: g) (decl_var e2 :: g).
Proof.
  induction 1.
  - apply rt_step.
    now constructor.
  - apply rt_refl.
  - eauto with cps.
Qed.

Lemma conv_trans:
  forall g,
  transitive (conv g).
Proof.
  (* TODO: Bowman's paper says this is transitive, and, intuitively, I agree.
     I'm not really sure yet how to prove this, tho. I'll come back here later.
     More recent note: I hate my past self. *)
  repeat intro.
  generalize dependent z.
  induction H; intros.
  - assert (rst(step g) e1 e2) by eauto with cps.
    clear H H0 f.
    generalize dependent e1.
    induction H1; intros.
    + admit.
    + assert (rst(step g) e0 (abstraction t f1)) by eauto with cps.
      apply step_is_church_rosser in H3.
      destruct H3 as (z, ?H, ?H).
      assert (exists t1 f3,
        z = abstraction t1 f3 /\
          rt(step g) t t1 /\
          rt(step (decl_var t :: g)) f1 f3) by admit.
      destruct H5 as (t1, (f3, ?H)).
      destruct H5.
      destruct H6.
      subst.
      eapply conv_eta_left.
      eassumption.
      eassumption.
      specialize (IHconv f3).
      apply clos_rt_clos_rst in H7.
      apply rst_sym in H7.
      specialize (IHconv H7).
      (* There we go... *)
      admit.
Admitted.

Global Hint Resolve conv_trans: cps.

Global Instance conv_equivalence:
  forall g,
  Equivalence (conv g).
Proof.
  split.
  - apply conv_refl.
  - apply conv_sym.
  - apply conv_trans.
Qed.
