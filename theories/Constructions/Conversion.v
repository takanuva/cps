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
  (* Pi reductions. *)
  | step_pi1:
    forall g e f t,
    step g (proj1 (pair e f t)) e
  | step_pi2:
    forall g e f t,
    step g (proj2 (pair e f t)) f
  (* Iota reductions. *)
  | step_tt:
    forall g t f1 f2,
    step g (bool_if bool_tt t f1 f2) f1
  | step_ff:
    forall g t f1 f2,
    step g (bool_if bool_ff t f1 f2) f2
  (* Congruence closure... many rules! *)
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
    step g (definition e t f1) (definition e t f2)
  | step_sigma_type:
    forall g t1 t2 u,
    step g t1 t2 ->
    step g (sigma t1 u) (sigma t2 u)
  | step_sigma_body:
    forall g t u1 u2,
    step (decl_var t :: g) u1 u2 ->
    step g (sigma t u1) (sigma t u2)
  | step_pair_left:
    forall g e1 e2 f t,
    step g e1 e2 ->
    step g (pair e1 f t) (pair e2 f t)
  | step_pair_right:
    forall g e f1 f2 t,
    step g f1 f2 ->
    step g (pair e f1 t) (pair e f2 t)
  | step_pair_type:
    forall g e f t1 t2,
    step g t1 t2 ->
    step g (pair e f t1) (pair e f t2)
  | step_proj1:
    forall g e1 e2,
    step g e1 e2 ->
    step g (proj1 e1) (proj1 e2)
  | step_proj2:
    forall g e1 e2,
    step g e1 e2 ->
    step g (proj2 e1) (proj2 e2)
  | step_if_term:
    forall g e1 e2 t f1 f2,
    step g e1 e2 ->
    step g (bool_if e1 t f1 f2) (bool_if e2 t f1 f2)
  | step_if_type:
    forall g e t1 t2 f1 f2,
    step g t1 t2 ->
    step g (bool_if e t1 f1 f2) (bool_if e t2 f1 f2)
  | step_if_then:
    forall g e t f11 f12 f2,
    step g f11 f12 ->
    step g (bool_if e t f11 f2) (bool_if e t f12 f2)
  | step_if_else:
    forall g e t f1 f21 f22,
    step g f21 f22 ->
    step g (bool_if e t f1 f21) (bool_if e t f1 f22).

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
  forall x,
  { exists t e, x = abstraction t e } + { ~exists t e, x = abstraction t e }.
Proof.
  destruct x.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - left; eauto with cps.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
  - right; intros (t, (f, ?)); easy.
Qed.

Lemma pair_is_decidable:
  forall x,
  { exists e f t, x = pair e f t } + { ~exists e f t, x = pair e f t }.
Proof.
  destruct x.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - left; eauto with cps.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
  - right; intros (e, (f, (t, ?))); easy.
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
  - destruct IHe1 with g.
    + left.
      destruct e as (f, ?).
      eexists.
      apply step_sigma_type.
      eassumption.
    + destruct IHe2 with (decl_var e1 :: g).
      * left.
        destruct e as (f, ?).
        eexists.
        apply step_sigma_body.
        eassumption.
      * right; intros (f, ?).
        dependent destruction H; firstorder.
  - (* We go in lexicographic order, as the term is written in full. *)
    destruct IHe1 with g.
    + left.
      destruct e as (f, ?).
      eexists.
      apply step_pair_left.
      eassumption.
    + destruct IHe2 with g.
      * left.
        destruct e as (f, ?).
        eexists.
        apply step_pair_right.
        eassumption.
      * (* TODO: please, refactor me... *)
        destruct IHe3 with g.
        --- left.
            destruct e as (f, ?).
            eexists.
            apply step_pair_type.
            eassumption.
        --- right.
            intros (f, ?).
            dependent destruction H; firstorder.
  - destruct IHe with g.
    + left.
      destruct e0 as (f, ?).
      eexists.
      apply step_proj1.
      eassumption.
    + (* Do we have a projection? *)
      destruct pair_is_decidable with e.
      * (* We do! *)
        left.
        destruct e0 as (e2, (f, (t, ?))); subst.
        eexists.
        apply step_pi1.
      * (* No reduction. *)
        right; intros (f, ?).
        dependent destruction H.
        (* TODO: refactor me... not sure why firstorder doesn't work. *)
        --- apply n0; now do 3 eexists.
        --- apply n; now exists e2.
  - destruct IHe with g.
    + left.
      destruct e0 as (f, ?).
      eexists.
      apply step_proj2.
      eassumption.
    + (* Do we have a projection? *)
      destruct pair_is_decidable with e.
      * (* We do! *)
        left.
        destruct e0 as (e2, (f, (t, ?))); subst.
        eexists.
        apply step_pi2.
      * (* No reduction. *)
        right; intros (f, ?).
        dependent destruction H.
        (* TODO: refactor me... not sure why firstorder doesn't work. *)
        --- apply n0; now do 3 eexists.
        --- apply n; now exists e2.
  - right; intros (f, ?).
    inversion H.
  - right; intros (f, ?).
    inversion H.
  - right; intros (f, ?).
    inversion H.
  - (* TODO: do we have an iota reduction here...? *)
    admit.
Admitted.

(* This relation is mentioned in Coq's documentation and in Bowman's papers.

   The documentation doesn't seem to suggest this is a congruence relation, but,
   according to Coq's [kernel/conversion.ml], it should be. In their conversion
   procedure they convert arrays of terms (representing n-ary applications) to
   their weak-head normal form and then compare the leftmost item; if it's a pi
   or a lambda or a constructor, in both sides, they keep going and do this for
   the arguments. At this point, if only one side is a lambda, or only one side
   is a primitive record, they try to eta expand as described. I believe that
   simply turning this relation into a congruence is enough to characterize this
   behavior, having the algorithm as a decision procedure, but then again we'd
   have to prove this. As we do not have arbitrary record types, we "specialize"
   the rules for the case of surjective pairing of sigma types. Remember that
   terms that are checked for convertibility by the typechecking algorithm are
   already expected to have the same type. *)

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
    conv g e1 e2
  | conv_sur_left:
    forall g e1 p q t e2 f,
    rt(step g) e1 (pair p q t) ->
    rt(step g) e2 f ->
    conv g p (proj1 f) ->
    conv g q (proj2 f) ->
    conv g e1 e2
  | conv_sur_right:
    forall g e1 p q t e2 f,
    rt(step g) e1 f ->
    rt(step g) e2 (pair p q t) ->
    conv g (proj1 f) p ->
    conv g (proj2 f) q ->
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
  - eapply conv_sur_right; eauto with cps.
  - eapply conv_sur_left; eauto with cps.
Qed.

Lemma conv_trans:
  forall g,
  transitive (conv g).
Proof.
  (* TODO: Bowman's paper says this is transitive, and, intuitively, I agree.
     I'm not really sure yet how to prove this, tho. I'll come back here later.
  *)
  admit.
Admitted.

Lemma surjective_pairing:
  forall g e t,
  conv g (pair (proj1 e) (proj2 e) t) e.
Proof.
  intros.
  eapply conv_sur_left.
  - apply rt_refl.
  - apply rt_refl.
  - apply conv_refl.
  - apply conv_refl.
Qed.

Definition typed_conv (g: env) (t: term): relation term :=
  (* Simply ignore the type. *)
  conv g.
