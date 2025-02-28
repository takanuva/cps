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
  | step_def_term:
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
    step (decl_var boolean :: g) t1 t2 ->
    step g (bool_if e t1 f1 f2) (bool_if e t2 f1 f2)
  | step_if_then:
    forall g e t f11 f12 f2,
    step g f11 f12 ->
    step g (bool_if e t f11 f2) (bool_if e t f12 f2)
  | step_if_else:
    forall g e t f1 f21 f22,
    step g f21 f22 ->
    step g (bool_if e t f1 f21) (bool_if e t f1 f22).

Global Hint Constructors step: cps.

Lemma declaration_existance_is_decidable:
  forall g n,
  { e | exists t, item (decl_def e t) g n } +
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
        exists e, t.
        constructor.
      * right; intros (e, (u, ?)).
        inversion H.
    + destruct IHg with n.
      * left.
        destruct s as (e, ?H).
        exists e.
        destruct H as (t, ?H).
        exists t.
        constructor.
        assumption.
      * right; intros (e, (t, ?)).
        dependent destruction H.
        firstorder.
Qed.

Local Hint Extern 4 (~(_ = _)) => discriminate: cps.

Lemma abstraction_is_decidable:
  forall P: term -> Type,
  forall f1: (forall t e, P (abstraction t e)),
  forall f2: (forall x, (forall t e, x <> abstraction t e) -> P x),
  forall x,
  P x.
Proof.
  induction x; auto with cps.
Qed.

Lemma pair_is_decidable:
  forall P: term -> Type,
  forall f1: (forall t e f, P (pair t e f)),
  forall f2: (forall x, (forall t e f, x <> pair t e f) -> P x),
  forall x,
  P x.
Proof.
  induction x; auto with cps.
Qed.

Lemma bool_value_is_decidable:
  forall P: term -> Type,
  forall f1: P bool_tt,
  forall f2: P bool_ff,
  forall f3: (forall x, x <> bool_tt -> x <> bool_ff -> P x),
  forall x,
  P x.
Proof.
  induction x; auto with cps.
Qed.

(* Pick a reduct for a term, arbitrarily defined in a call-by-name order in a
   computationally relevant way, or return a proof that there is none. *)

Lemma step_is_decidable:
  forall g e,
  { f | step g e f } + { normal (step g) e }.
Proof with eauto with cps.
  intros.
  generalize dependent g.
  induction e; intros.
  (* Case: sort. *)
  - (* Sorts are atomics, of course. *)
    right; easy.
  (* Case: bound. *)
  - (* A variable can reduce if and only if the environment defines it. *)
    destruct declaration_existance_is_decidable with g n as [ (e, ?H) | ?H ].
    + (* It does, so we have a delta reduction. *)
      left; eexists.
      destruct H as (t, ?H)...
    + (* There's no definition, so no reduction either. *)
      right; intros x ?.
      inversion H0; firstorder.
  (* Case: pi. *)
  - (* Check subterms, left to right. *)
    destruct IHe1 with g as [ (x, ?H) | ?H ]...
    destruct IHe2 with (decl_var e1 :: g) as [ (x, ?H) | ?H ]...
    (* We're in normal form. *)
    right; intros x ?.
    inversion H1; firstorder.
  (* Case: abstraction. *)
  - (* Check subterms, left to right. *)
    destruct IHe1 with g as [ (x, ?H) | ?H ]...
    destruct IHe2 with (decl_var e1 :: g) as [ (x, ?H) | ?H ]...
    (* We're in normal form. *)
    right; intros x ?.
    inversion H1; firstorder.
  (* Case: application. *)
  - (* In the standard reduction sequence, we reduce a redex as soon as it
       appears. So we'll check if we have a beta-redex right away. *)
    destruct e1 using abstraction_is_decidable...
    (* There's no beta-redex, check subterms. *)
    destruct IHe1 with g as [ (x, ?H) | ?H ]...
    destruct IHe2 with g as [ (x, ?H) | ?H ]...
    (* We're in normal form. *)
    right; intros x ?.
    inversion H2.
    + subst; now apply H with t e.
    + firstorder.
    + firstorder.
  (* Case: definition. *)
  - (* Easy. This is always a zeta-redex! *)
    left...
  (* Case: sigma. *)
  - (* Check subterms, left to right. *)
    destruct IHe1 with g as [ (x, ?H) | ?H ]...
    destruct IHe2 with (decl_var e1 :: g) as [ (x, ?H) | ?H ]...
    (* We're in normal form. *)
    right; intros x ?.
    inversion H1; firstorder.
  (* Case: pair. *)
  - (* Check subterms, left to right. *)
    destruct IHe1 with g as [ (x, ?H) | ?H ]...
    destruct IHe2 with g as [ (x, ?H) | ?H ]...
    destruct IHe3 with g as [ (x, ?H) | ?H ]...
    (* We're in normal form. *)
    right; intros x ?.
    inversion H2; firstorder.
  (* Case: proj1. *)
  - (* Do we have a pi-redex? *)
    destruct e using pair_is_decidable...
    (* Either our subterm has a redex, or we're in normal form. *)
    destruct IHe with g as [ (x, ?H) | ?H ]...
    right; intros x ?.
    inversion H1.
    + subst; now apply H with x f t.
    + firstorder.
  (* Case: proj2. *)
  - (* Exact same thing as the case for proj1 above. *)
    destruct e using pair_is_decidable...
    destruct IHe with g as [ (x, ?H) | ?H ]...
    right; intros x ?.
    inversion H1.
    + subst; rename e0 into e.
      now apply H with e x t.
    + firstorder.
  (* Case: boolean. *)
  - (* This is a const, so it's already in normal form. *)
    right; easy.
  (* Case: bool_tt. *)
  - (* Same as above. *)
    right; easy.
  (* Case: bool_ff. *)
  - (* Same as above too. *)
    right; easy.
  (* Case: bool_if. *)
  - (* We first check for the existence of an iota-redex in here... *)
    destruct e1 using bool_value_is_decidable...
    (* Check now for subterms... *)
    destruct IHe1 with g as [ (x, ?H) | ?H ]...
    destruct IHe2 with (decl_var boolean :: g) as [ (x, ?H) | ?H ]...
    destruct IHe3 with g as [ (x, ?H) | ?H ]...
    destruct IHe4 with g as [ (x, ?H) | ?H ]...
    (* The term is in normal form. *)
    right; intros x ?.
    inversion H5.
    + subst; contradiction.
    + subst; contradiction.
    + firstorder.
    + firstorder.
    + firstorder.
    + firstorder.
Qed.

(* This relation is mentioned in Coq's documentation and in Bowman's papers.

   The documentation doesn't seem to suggest this is a congruence relation, but,
   according to Coq's [kernel/conversion.ml], it should be. In their conversion
   procedure they convert arrays of terms to their weak-head normal form and
   then compare the leftmost item; if it's a pi, a lambda, a constructor or etc,
   equal in both sides, they keep going (e.g., in an application). So, at this
   point, if only one side is a lambda, or only one side is a primitive record,
   they try to eta expand as described (symmetrically, indeed). I believe that
   simply turning this relation into a congruence is enough to characterize this
   behavior, having the algorithm as a decision procedure, but then again we'd
   have to prove this. As we do not have arbitrary record types, we "specialize"
   the rules for the case of surjective pairing of sigma types. Remember that
   terms that are checked for convertibility by the typechecking algorithm are
   already expected to have the same type. *)

Inductive conv: env -> relation term :=
  (* Common reduct. *)
  | conv_join:
    forall g e1 e2 f,
    rt(step g) e1 f ->
    rt(step g) e2 f ->
    conv g e1 e2
  (* Eta-expansion for lambda, abstraction on the left. *)
  | conv_eta_left:
    forall g e1 e2 t f1 f2,
    rt(step g) e1 (abstraction t f1) ->
    rt(step g) e2 f2 ->
    conv (decl_var t :: g) f1 (application (lift 1 0 f2) (bound 0)) ->
    conv g e1 e2
  (* Eta-expansion for lambda, abstraction on the right. *)
  | conv_eta_right:
    forall g e1 e2 t f1 f2,
    rt(step g) e1 f1 ->
    rt(step g) e2 (abstraction t f2) ->
    conv (decl_var t :: g) (application (lift 1 0 f1) (bound 0)) f2 ->
    conv g e1 e2
  (* Surjective pairing, pair on the left. *)
  | conv_sur_left:
    forall g e1 p q t e2 f,
    rt(step g) e1 (pair p q t) ->
    rt(step g) e2 f ->
    conv g p (proj1 f) ->
    conv g q (proj2 f) ->
    conv g e1 e2
  (* Surjective pairing, pair on the right. *)
  | conv_sur_right:
    forall g e1 p q t e2 f,
    rt(step g) e1 f ->
    rt(step g) e2 (pair p q t) ->
    conv g (proj1 f) p ->
    conv g (proj2 f) q ->
    conv g e1 e2
  (* TODO: add congruence rules. *).

Global Hint Constructors conv: cps.

Lemma conv_refl:
  forall g,
  reflexive (conv g).
Proof.
  repeat intro.
  apply conv_join with x.
  - apply rt_refl.
  - apply rt_refl.
Qed.

Global Hint Resolve conv_refl: cps.

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

Global Hint Resolve conv_sym: cps.

Lemma conv_trans:
  forall g,
  transitive (conv g).
Proof.
  (* TODO: Bowman's paper says this is transitive, and, intuitively, I agree.
     I'm not really sure yet how to prove this, tho. I'll come back here later.
  *)
Admitted.

Global Hint Resolve conv_trans: cps.

Lemma conv_context:
  forall (h: context) g e f,
  conv g e f ->
  conv g (h e) (h f).
Proof.
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
