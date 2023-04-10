(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
(* TODO: remove this one. *)
Require Import Local.Axiomatic.
Require Import Local.Reduction.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Observational.
Require Import Local.Lambda.Calculus.

(* TODO: move this comment somewhere else.

   The definitions of call by name and call by value reductions are standard;
   as of this development, they were taken from Plotkin's paper.

   Note: if the CPS-calculus properly simulates CBN/CBV reduction, then, by the
   factorization lemma, it's possible to show that we'll reach the desired value
   only by using head redutions! They are enough to simulate the results.

   The CPS translations are given in Thielecke's dissertation, and are based on
   those of Plotkin's paper as well. We note that both translations receive the
   returning continuation as a parameter, but the translation will always set
   this to be the most recently bound continuation, i.e., the de Bruijn index 0,
   so this parameter is taken implictly in our setting. *)

Inductive lambda_cbn: relation lambda_term :=
  | lambda_cbn_beta:
    forall t b x,
    lambda_cbn
      (lambda_application (lambda_abstraction t b) x)
      (lambda_subst x 0 b)
  | lambda_cbn_app1:
    forall f1 f2 x,
    lambda_cbn f1 f2 ->
    lambda_cbn (lambda_application f1 x) (lambda_application f2 x)
  | lambda_cbn_app2:
    forall (f: nat) x1 x2,
    lambda_cbn x1 x2 ->
    lambda_cbn (lambda_application f x1) (lambda_application f x2).

Lemma lambda_full_cbn:
  inclusion lambda_cbn lambda_full.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma lambda_cbn_implies_nonvalue:
  forall a b,
  lambda_cbn a b -> ~lambda_value a.
Proof.
  induction 1; inversion 1.
Qed.

Lemma lambda_cbn_is_a_function:
  forall a b1,
  lambda_cbn a b1 ->
  forall b2,
  lambda_cbn a b2 -> b1 = b2.
Proof.
  induction 1; intros.
  - dependent destruction H.
    + reflexivity.
    + exfalso.
      inversion H.
  - dependent destruction H0.
    + exfalso.
      inversion H.
    + f_equal; auto.
    + exfalso.
      inversion H.
  - dependent destruction H0.
    + exfalso.
      inversion H0.
    + f_equal; auto.
Qed.

(* TODO: fix typing on the following! *)

Inductive cbn_cps: lambda_term -> pseudoterm -> Prop :=
  | cbn_cps_bound:
    (* [x](k) = x<k> *)
    forall n: nat,
    (* TODO: assume k is fresh! *)
    cbn_cps n (jump n [bound 0])
  | cbn_cps_abstraction:
    (* [\x.M](k) = k<f> { f<x, h> = [M](h) } *)
    forall t b b',
    cbn_cps (lambda_lift 1 0 b) b' ->
    cbn_cps
      (lambda_abstraction t b)
      (bind
        (jump 1 [bound 0])
        [void; void]
        b')
  | cbn_cps_application:
    (* [M N](k) = [M](m) { m<f> = f<n, k> { n<h> = [N](h) } } *)
    forall f x f' x',
    cbn_cps (lambda_lift 1 0 f) f' ->
    cbn_cps (lambda_lift 2 0 x) x' ->
    cbn_cps
      (lambda_application f x)
      (bind
        f'
        [void]
        (bind
          (jump 1 [bound 0; bound 2])
          [void]
          x')).

Lemma cbn_cps_is_a_function:
  forall e c1,
  cbn_cps e c1 ->
  forall c2,
  cbn_cps e c2 -> c1 = c2.
Proof.
  induction 1; intros.
  - dependent destruction H; auto.
  - dependent destruction H0.
    f_equal; auto.
  - dependent destruction H1.
    f_equal; auto.
    f_equal; auto.
Qed.

Local Hint Resolve cbn_cps_is_a_function: cps.

Lemma cbn_cps_lift:
  forall e c,
  cbn_cps e c ->
  forall i k,
  k > 0 ->
  cbn_cps (lambda_lift i k e) (lift i k c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k n).
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_lt; try lia.
      constructor.
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      constructor.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    rewrite lambda_lift_lift_permutation; try lia.
    replace (k + 2) with (2 + k); simpl; try lia.
    apply IHcbn_cps; lia.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    + rewrite lambda_lift_lift_permutation; try lia.
      apply IHcbn_cps1; lia.
    + rewrite lambda_lift_lift_permutation; try lia.
      replace (k + 1 + 1) with (2 + k); try lia.
      apply IHcbn_cps2; lia.
Qed.

Lemma cbn_cps_is_compositional:
  forall c1 c2,
  [c1 ~~ c2] ->
  forall e1 e2,
  lambda_not_free 0 e1 ->
  lambda_not_free 0 e2 ->
  cbn_cps e1 c1 ->
  cbn_cps e2 c2 ->
  forall (h: lambda_context) c3 c4,
  cbn_cps (h e1) c3 ->
  cbn_cps (h e2) c4 ->
  [c3 ~~ c4].
Proof.
  intros until h.
  (* Do some reordering to help with unification... *)
  move H0 after H2.
  move H1 after H3.
  generalize dependent e2.
  generalize dependent e1.
  generalize dependent c2.
  generalize dependent c1.
  (* We'll do induction on the depth of h, not on h itself. *)
  remember (lambda_context_depth h) as k.
  generalize dependent h.
  induction k using lt_wf_ind; intros.
  dependent destruction Heqk.
  (* There we go. *)
  destruct h; simpl in H.
  (* Case: lambda_context_hole. *)
  - assert (c1 = c3); eauto with cps.
    destruct H7.
    assert (c2 = c4); eauto with cps.
    destruct H7.
    assumption.
  (* Case: lambda_context_abstraction. *)
  - dependent destruction H5.
    dependent destruction H6.
    rewrite lambda_context_lift_is_sound in H5.
    rewrite lambda_context_lift_is_sound in H6.
    rewrite Nat.add_0_r in H5, H6.
    apply barb_bind_right.
    (* We notice that 0 can't be free in e1 or e2, so, if h happens to bind no
       var, so that we have lambda_lift 1 0 e1 in H3 (and ... e2 in H4), those
       may be freely replaced with lambda_lift 1 1, thus fixing what we need. *)
    destruct (lambda_context_bvars h).
    + admit.
    + eapply H with (m := lambda_context_depth (lambda_context_lift 1 0 h)).
      * (* Clearly. *)
        admit.
      * reflexivity.
      * apply barb_lift with (k := S n).
        exact H0.
      * apply cbn_cps_lift; try lia.
        exact H2.
      * (* Clearly. *)
        admit.
      * apply cbn_cps_lift; try lia.
        exact H3.
      * (* Clearly. *)
        admit.
      * exact H5.
      * exact H6.
  (* Case: lambda_context_abstraction_left. *)
  - dependent destruction H5.
    dependent destruction H6.
    assert (x' = x'0); eauto with cps.
    dependent destruction H5.
    apply barb_bind_left.
    rewrite lambda_context_lift_is_sound in H5_, H6_.
    rewrite Nat.add_comm in H5_, H6_; simpl in H5_, H6_.
    eapply H with (m := lambda_context_depth (lambda_context_lift 1 0 h)).
    + rewrite lambda_context_lift_depth; auto.
    + reflexivity.
    + (* We lifted e1 and e2 by 1... can we derive ?c1 and ?c2 in here? *)
      admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + exact H5_.
    + exact H6_.
  (* Case: lambda_context_abstraction_right. *)
  - dependent destruction H5.
    dependent destruction H6.
    assert (f' = f'0); eauto with cps.
    dependent destruction H5.
    apply barb_bind_right.
    apply barb_bind_right.
    admit.
Admitted.

(* -------------------------------------------------------------------------- *)

(* Ideally, given a lambda term e which is in normal form, and a variable k
   which is fresh, the CPS translation [e]k should not have administrative
   redexes which can't be fixed by applying only tyding reductions. *)

Inductive no_administrative_jumps e: Prop :=
  | no_administrative_jumps_ctor
    (b: pseudoterm)
    (H1: cbn_cps e b)
    (c: pseudoterm)
    (* Actually, b should reduce to c through tidying reductions! TODO: fix
       this, please. *)
    (H2: [b == c])
    (H3: normal beta c).

Lemma lambda_abstraction_normal:
  forall t e,
  normal lambda_full (lambda_abstraction t e) ->
  normal lambda_full e.
Proof.
  intros; do 2 intro.
  eapply H; clear H.
  apply lambda_full_abs.
  eassumption.
Qed.

Goal
  forall e,
  normal lambda_full e ->
  (* We need to be sure that k is free in e! *)
  no_administrative_jumps (lambda_lift 1 0 e).
Proof.
  induction e; intros.
  (* Case: [x]k. *)
  - (* This case is pretty much straightforward. *)
    econstructor.
    + simpl.
      constructor.
    + apply sema_refl.
    + inversion 1.
  (* Case: [\x.e]k. *)
  - (* This simply follows by induction. *)
    simpl.
    apply lambda_abstraction_normal in H.
    specialize (IHe H); clear H.
    dependent destruction IHe.
    econstructor.
    + constructor.
      rewrite lambda_lift_lift_permutation; simpl; try lia.
      apply cbn_cps_lift; try lia.
      eassumption.
    + apply sema_bind_right.
      apply sema_lift.
      eassumption.
    + do 2 intro.
      dependent destruction H.
      * destruct h; discriminate.
      * inversion H.
      * edestruct beta_lift_inversion; eauto.
        dependent destruction H0.
        apply beta_unlift in H.
        eapply H3.
        eassumption.
  (* Case: [f e]k. *)
  - (* We should remember that:

         [f e]k = [f]k { k<f> = f<v, k> { v<k> = [e]k } }

       The only way there can be any jumps in here, since [f]k and [e]k are in
       jump normal form, is if [f]k has a jump to k anywhere. This will only
       happen if f is a lambda abstraction, which we know it can't be! We note
       this is slightly different from the CBV version, in here [f]k will have
       a jump to k iff f is a value. In the CBN version, we won't have a jump
       to k if f is just a variable. So no administrative redexes at all! *)
    admit.
Admitted.
