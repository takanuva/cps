(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Constructions.Calculus.

Inductive step: env -> relation term :=
  (* Beta reduction. *)
  | step_beta:
    forall g t e f,
    step g (application (abstraction t e) f) (subst f 0 e)
  (* Zeta reduction. *)
  | step_zeta:
    forall g e t f,
    step g (definition e t f) (subst e 0 f)
  (* Delta reduction. *)
  | step_delta:
    forall g t e n,
    item (decl_def e t) g n ->
    step g (bound n) (lift (1 + n) 0 e)
  (* Congruence closure. *)
  | step_pi_type:
    forall g t1 t2 u,
    step g t1 t2 ->
    step g (pi t1 u) (pi t2 u)
  | step_pi_body:
    forall g t u1 u2,
    step (decl_var t :: g) u1 u2 ->
    step g (pi t u1) (pi t u2)
  | step_abs_type:
    forall g t1 t2 e,
    step g t1 t2 ->
    step g (abstraction t1 e) (abstraction t2 e)
  | step_abs_body:
    forall g t e1 e2,
    step (decl_var t :: g) e1 e2 ->
    step g (abstraction t e1) (abstraction t e2)
  | step_app_left:
    forall g e1 e2 f,
    step g e1 e2 ->
    step g (application e1 f) (application e2 f)
  | step_app_right:
    forall g e f1 f2,
    step g f1 f2 ->
    step g (application e f1) (application e f2)
  | step_def_val:
    forall g e1 e2 t f,
    step g e1 e2 ->
    step g (definition e1 t f) (definition e2 t f)
  | step_def_type:
    forall g e t1 t2 f,
    step g t1 t2 ->
    step g (definition e t1 f) (definition e t2 f)
  | step_def_body:
    forall g e t f1 f2,
    step (decl_def e t :: g) f1 f2 ->
    step g (definition e t f1) (definition e t f2).

Lemma declaration_existance_is_decidable:
  forall g n,
  { exists e t, item (decl_def e t) g n } +
    { ~exists e t, item (decl_def e t) g n }.
Proof.
  induction g; intros.
  - right; intros (e, (t, ?)).
    inversion H.
  - destruct n.
    + clear IHg.
      destruct a.
      destruct o.
      * rename t0 into e.
        left.
        do 2 eexists.
        constructor.
      * right; intros (e, (u, ?)).
        inversion H.
    + destruct IHg with n.
      * left.
        destruct e as (e, (t, ?)).
        do 2 eexists.
        constructor.
        eassumption.
      * right; intros (e, (t, ?)).
        dependent destruction H.
        firstorder.
Qed.

Lemma abstraction_is_decidable:
  forall e,
  { exists t f, e = abstraction t f } + { ~exists t f, e = abstraction t f }.
Proof.
  destruct e.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - left; eauto with cps.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
Qed.

Lemma step_is_decidable:
  forall e g,
  { exists f, step g e f } + { ~exists f, step g e f }.
Proof.
  induction e; intros.
  - right; intros (f, ?).
    inversion H.
  - destruct declaration_existance_is_decidable with g n.
    + left.
      destruct e as (e, (t, ?)).
      eexists.
      eapply step_delta.
      eassumption.
    + right; intros (f, ?).
      dependent destruction H.
      firstorder.
  - destruct IHe1 with g.
    + left.
      destruct e as (f, ?).
      eexists.
      apply step_pi_type.
      eassumption.
    + destruct IHe2 with (decl_var e1 :: g).
      * left.
        destruct e as (f, ?).
        eexists.
        apply step_pi_body.
        eassumption.
      * right; intros (f, ?).
        dependent destruction H; firstorder.
  - destruct IHe1 with g.
    + left.
      destruct e as (f, ?).
      eexists.
      apply step_abs_type.
      eassumption.
    + destruct IHe2 with (decl_var e1 :: g).
      * left.
        destruct e as (f, ?).
        eexists.
        apply step_abs_body.
        eassumption.
      * right; intros (f, ?).
        dependent destruction H; firstorder.
  - destruct IHe1 with g.
    + (* There's a redex on the left, so this can't be itself a redex. *)
      left.
      destruct e as (f, ?).
      eexists.
      apply step_app_left.
      eassumption.
    + (* Before reducing on the right, is this a beta-redex? *)
      destruct abstraction_is_decidable with e1.
      * (* It is... *)
        left.
        destruct e as (t, (e, ?)); subst.
        eexists.
        apply step_beta.
      * (* Is there a redex on the right...? *)
        destruct IHe2 with g.
        (* TODO: refactor me, at some point... *)
        --- left.
            destruct e as (f, ?).
            eexists.
            apply step_app_right.
            eassumption.
        --- (* I really wish Coq had FOUR proof levels... *)
            right; intros (f, ?).
            dependent destruction H; eauto with cps.
  - (* There's always a zeta-redex in here! *)
    left; eexists.
    apply step_zeta.
Qed.

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
    conv (decl_var t :: g) f1 (application (lift 1 0 f2) (bound 0)) ->
    conv g e1 e2
  | conv_eta_right:
    forall g e1 e2 t f1 f2,
    rt(step g) e1 f1 ->
    rt(step g) e2 (abstraction t f2) ->
    conv (decl_var t :: g) (application (lift 1 0 f1) (bound 0)) f2 ->
    conv g e1 e2.

(* Lemma step_abs_inversion:
  forall g t1 e1 f,
  step g (abstraction t1 e1) f ->
  exists t2 e2,
  f = abstraction t2 e2.
Proof.
  intros.
  dependent destruction H.
  - do 2 eexists.
    reflexivity.
  - do 2 eexists.
    reflexivity.
Qed.

Lemma rt_step_abs_inversion:
  forall g t1 e1 f,
  rt(step g) (abstraction t1 e1) f ->
  exists t2 e2,
  f = abstraction t2 e2.
Proof.
  intros.
  dependent induction H.
  - now apply step_abs_inversion with g t1 e1.
  - now exists t1, e1.
  - edestruct IHclos_refl_trans1 as (t2, (e2, ?)).
    + reflexivity.
    + subst.
      now apply IHclos_refl_trans2 with t2 e2.
Qed. *)

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
  (* Bowman's paper says this is transitive, and, intuitively, I agree. I'm not
     really sure yet how to prove this, tho. I'll come back here later. *)
  admit.
Admitted.
