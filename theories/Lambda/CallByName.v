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
Require Export Local.Lambda.Calculus.

Include Lambda.Calculus.
Module CPS := Local.Syntax.

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

Inductive cbn: relation term :=
  | cbn_beta:
    forall t b x,
    cbn
      (application (abstraction t b) x)
      (subst x 0 b)
  | cbn_app1:
    forall f1 f2 x,
    cbn f1 f2 ->
    cbn (application f1 x) (application f2 x)
  | cbn_app2:
    forall (f: nat) x1 x2,
    cbn x1 x2 ->
    cbn (application f x1) (application f x2).

Lemma full_cbn:
  inclusion cbn full.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma cbn_implies_nonvalue:
  forall a b,
  cbn a b -> ~value a.
Proof.
  induction 1; inversion 1.
Qed.

Lemma cbn_is_a_function:
  forall a b1,
  cbn a b1 ->
  forall b2,
  cbn a b2 -> b1 = b2.
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

Inductive cbn_cps: term -> pseudoterm -> Prop :=
  | cbn_cps_bound:
    (* [x](k) = x<k> *)
    forall n: nat,
    cbn_cps (S n) (jump (S n) [CPS.bound 0])
  | cbn_cps_abstraction:
    (* [\x.M](k) = k<f> { f<x, h> = [M](h) } *)
    forall t b b',
    cbn_cps (lift 1 0 b) b' ->
    cbn_cps
      (abstraction t b)
      (bind
        (jump 1 [CPS.bound 0])
        [void; void]
        b')
  | cbn_cps_application:
    (* [M N](k) = [M](m) { m<f> = f<n, k> { n<h> = [N](h) } } *)
    forall f x f' x',
    cbn_cps (lift 1 0 f) f' ->
    cbn_cps (lift 2 0 x) x' ->
    cbn_cps
      (application f x)
      (bind
        f'
        [void]
        (bind
          (jump 1 [CPS.bound 0; CPS.bound 2])
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
  cbn_cps (lift i k e) (CPS.lift i k c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k (S n)).
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_lt; try lia.
      replace (i + S n) with (S (i + n)); try lia.
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
    rewrite lift_lift_permutation; try lia.
    replace (k + 2) with (2 + k); simpl; try lia.
    apply IHcbn_cps; lia.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    + rewrite lift_lift_permutation; try lia.
      apply IHcbn_cps1; lia.
    + rewrite lift_lift_permutation; try lia.
      replace (k + 1 + 1) with (2 + k); try lia.
      apply IHcbn_cps2; lia.
Qed.

Lemma cbn_cps_is_compositional:
  forall c1 c2,
  [c1 ~~ c2] ->
  forall e1 e2,
  not_free 0 e1 ->
  not_free 0 e2 ->
  cbn_cps e1 c1 ->
  cbn_cps e2 c2 ->
  forall (h: context) c3 c4,
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
  remember (context_depth h) as k.
  generalize dependent h.
  induction k using lt_wf_ind; intros.
  dependent destruction Heqk.
  (* There we go. *)
  destruct h; simpl in H.
  (* Case: context_hole. *)
  - assert (c1 = c3); eauto with cps.
    destruct H7.
    assert (c2 = c4); eauto with cps.
    destruct H7.
    assumption.
  (* Case: context_abstraction. *)
  - dependent destruction H5.
    dependent destruction H6.
    rewrite context_lift_is_sound in H5.
    rewrite context_lift_is_sound in H6.
    rewrite Nat.add_0_r in H5, H6.
    apply barb_bind_right.
    (* We notice that 0 can't be free in e1 or e2, so, if h happens to bind no
       var, so that we have lift 1 0 e1 in H3 (and ... e2 in H4), those
       may be freely replaced with lift 1 1, thus fixing what we need. *)
    destruct (context_bvars h).
    + admit.
    + eapply H with (m := context_depth (context_lift 1 0 h)).
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
  (* Case: context_abstraction_left. *)
  - dependent destruction H5.
    dependent destruction H6.
    assert (x' = x'0); eauto with cps.
    dependent destruction H5.
    apply barb_bind_left.
    rewrite context_lift_is_sound in H5_, H6_.
    rewrite Nat.add_comm in H5_, H6_; simpl in H5_, H6_.
    eapply H with (m := context_depth (context_lift 1 0 h)).
    + rewrite context_lift_depth; auto.
    + reflexivity.
    + (* We lifted e1 and e2 by 1... can we derive ?c1 and ?c2 in here? *)
      admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + exact H5_.
    + exact H6_.
  (* Case: context_abstraction_right. *)
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

Lemma abstraction_normal:
  forall t e,
  normal full (abstraction t e) ->
  normal full e.
Proof.
  intros; do 2 intro.
  eapply H; clear H.
  apply full_abs.
  eassumption.
Qed.

Goal
  forall e,
  normal full e ->
  (* We need to be sure that k is free in e! *)
  no_administrative_jumps (lift 1 0 e).
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
    apply abstraction_normal in H.
    specialize (IHe H); clear H.
    dependent destruction IHe.
    econstructor.
    + constructor.
      rewrite lift_lift_permutation; simpl; try lia.
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

Goal
  forall e c,
  cbn_cps e c ->
  forall n,
  n > 0 ->
  not_free n e -> CPS.not_free n c.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    rename n0 into m.
    constructor.
    + constructor; lia.
    + do 2 constructor; lia.
  - constructor; simpl.
    + constructor.
      * constructor; lia.
      * do 2 constructor; lia.
    + do 3 constructor.
    + dependent destruction H1.
      apply IHcbn_cps; try lia.
      apply not_free_lift_zero with (k := 1) in H1.
      assumption.
  - dependent destruction H2.
    constructor; simpl.
    + apply IHcbn_cps1; auto.
      apply not_free_lift_zero with (k := 1) in H2_.
      assumption.
    + do 2 constructor.
    + repeat (try constructor; try lia).
      simpl; eapply IHcbn_cps2; auto.
      apply not_free_lift_zero with (k := 2) in H2_0.
      assumption.
Qed.

(* -------------------------------------------------------------------------- *)

(*
  From Amadio's class notes, we know that head reduction can't directly simulate
  beta reduction, though it's still computationally adequate. It should be the
  case that extended reduction will be able to properly simulate beta reduction
  on both CPS translations. For the call-by-name translation:

    1) [x]    = x<k>
    2) [\x.M] = k<f> { f<x, k> = [M] }
    3) [M N]  = [M] { k<f> = f<v, k> { v<k> = [N] } }

  For a lambda term of the form [(\x.a) b], we will have:

    k<f>
    { f<x, k> =
        [a] }
    { k<f> =
        f<v, k>
        { v<k> =
            [b] } }

  We immediately can apply a two linear head redexes:

    [a]
    { x<k> =
        [b] }

  Though the exact indution statement may be awkward, as we have to apply these
  simplifications first and keep building the way, we will proceed by induction
  now on the number of free occurrences of x in a:

    Base: if we don't have x free in a, we don't have x free in [a]. Thus, we
    can apply a garbage collection step and get [a] alone, as expected.

    Step: if there's a x in a, then a can be rewritten as C[x]. Then, due to the
    composability of the translation, we will have:

      D[x<k>]
      { x<k> =
        [b] }

    We would want to show that we can mimick a single substitution, thus, we
    will compare (\x.C[x]) b to (\x.C[b]) b. Thus, we want the above to reduce
    to:

      D[[b]]
      { x<k> =
        [b] }

    Which we can do in one (CTXJMP) step. Qed.

  We note that eta reduction is not sound in here, because this translation is
  tailored for the weak beta reduction used in programming languages. We know
  that eta is not sound in it, because \x.O x has a weak head normal form while
  O does not in the empty context (where O is the omega combinator). Similarly,
  for a variable y, \x.y x and y can be taken apart in the context C = (\y.[]) O
  if y is free (or similar context if it is bound). The remaining case is that
  when we have an abstraction, but then a beta step can be applied and eta is
  not really necessary anymore. We can prove that the translation also doesn't
  validate eta, same as the source language doesn't.

*)
