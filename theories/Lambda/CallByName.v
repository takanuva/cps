(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.Reduction.
Require Import Local.Factorization.
Require Import Local.Observational.
Require Import Local.Conservation.
Require Import Local.Shrinking.
Require Export Local.Lambda.Calculus.

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
    (* This rule is hardly ever considered, probably because it's only necessary
       for open terms, but it was used in Plotkin's paper, so we'll add it here
       as well. *)
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

Lemma cbn_whr:
  inclusion whr cbn.
Proof.
  induction 1.
  - constructor.
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

Lemma cbn_is_decidable:
  forall e,
  { normal cbn e } + { exists f, cbn e f }.
Proof.
  induction e; simpl.
  - left.
    inversion 1.
  - left.
    inversion 1.
  - destruct e1.
    + clear IHe1.
      destruct IHe2.
      * left.
        inversion_clear 1.
        (* TODO: refactor me... *)
        inversion H0.
        firstorder.
      * right.
        destruct e as (x, ?).
        eexists.
        constructor 3.
        eassumption.
    + right; eexists.
      constructor.
    + destruct IHe1.
      * left; intros x ?.
        dependent destruction H.
        firstorder.
      * right.
        destruct e as (x, ?).
        eexists.
        constructor.
        eassumption.
Qed.

Lemma cbn_whr_iff:
  forall e,
  closed e ->
  forall f,
  cbn e f <-> whr e f.
Proof.
  split; induction 1.
  - constructor.
  - constructor.
    apply IHcbn.
    apply closed_application_left with x.
    assumption.
  - exfalso.
    specialize (H f).
    dependent destruction H.
    dependent destruction H.
    contradiction.
  - constructor.
  - constructor.
    apply IHwhr.
    apply closed_application_left with x.
    assumption.
Qed.

Lemma closed_normal_cbn_implies_value:
  forall e,
  closed e ->
  normal cbn e ->
  value e.
Proof.
  intros.
  destruct value_dec with e.
  - assumption.
  - exfalso.
    induction e.
    + apply n.
      constructor.
    + apply n.
      constructor.
    + clear IHe2 n.
      destruct e1.
      * specialize (H n).
        dependent destruction H.
        dependent destruction H.
        contradiction.
      * eapply H0.
        constructor.
      * apply IHe1.
        (* TODO: refactor me, please... *)
        intro.
        specialize (H n).
        dependent destruction H.
        assumption.
        intros x ?.
        eapply H0.
        constructor.
        eassumption.
        inversion 1.
Qed.

(* TODO: fix typing on the following! *)

Local Notation VAR n :=
  (* [x] = x<k> *)
  (jump (S n) [CPS.bound 0]).

Local Notation ABS b :=
  (* [\x.e] = k<f> { f<x, k> = [e] } *)
  (bind (jump 1 [CPS.bound 0]) [void; void] b).

Local Notation APP b c :=
  (* [e f] = [e] { k<f> = f<v, k> { v<k> = [f] } } *)
  (bind b [void] (bind (jump 1 [CPS.bound 2; CPS.bound 0]) [void] c)).

(* TODO: these lifts could be moved from source to target! *)

Inductive cbn_cps: term -> pseudoterm -> Prop :=
  | cbn_cps_bound:
    forall n: nat,
    cbn_cps n (VAR n)
  | cbn_cps_abstraction:
    forall t e b,
    cbn_cps (lift 1 1 e) b ->
    cbn_cps (abstraction t e) (ABS b)
  | cbn_cps_application:
    forall f x b c,
    cbn_cps (lift 1 0 f) b ->
    cbn_cps (lift 2 0 x) c ->
    cbn_cps (application f x) (APP b c).

Local Hint Constructors cbn_cps: cps.

Lemma cbn_cps_is_a_function:
  forall e c1,
  cbn_cps e c1 ->
  forall c2,
  cbn_cps e c2 -> c1 = c2.
Proof.
  induction 1; intros.
  - dependent destruction H.
    reflexivity.
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
  cbn_cps (lift i k e) (CPS.lift i (S k) c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k n).
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

Local Hint Resolve cbn_cps_lift: cps.

Lemma cbn_cps_is_total:
  forall e,
  exists c,
  cbn_cps e c.
Proof.
  induction e.
  - eauto with cps.
  - destruct IHe as (c, ?).
    eauto with cps.
  - destruct IHe1 as (b, ?).
    destruct IHe2 as (c, ?).
    eauto with cps.
Qed.

Local Hint Resolve cbn_cps_is_total: cps.

Lemma cbn_cps_lift_inversion:
  forall i k e b,
  cbn_cps (lift i k e) b ->
  exists2 c,
  cbn_cps e c & b = CPS.lift i (S k) c.
Proof.
  intros.
  assert (exists c, cbn_cps e c) as (c, ?).
  - eauto with cps.
  - eauto with cps.
Qed.

Local Hint Resolve cbn_cps_lift_inversion: cps.

Lemma cbn_cps_not_free:
  forall e c,
  cbn_cps e c ->
  forall n,
  not_free n e <-> CPS.not_free (S n) c.
Proof.
  induction 1; split; intros.
  - dependent destruction H.
    rename n0 into m.
    constructor.
    + constructor; lia.
    + do 2 constructor; lia.
  - dependent destruction H.
    dependent destruction H.
    rename n0 into m.
    constructor; lia.
  - constructor; simpl.
    + constructor.
      * constructor; lia.
      * do 2 constructor; lia.
    + do 3 constructor.
    + dependent destruction H0.
      apply IHcbn_cps; try lia.
      replace (S n) with (n + 1) in H0; try lia.
      apply not_free_lift with (k := 1) in H0.
      replace (n + 1 + 1) with (2 + n) in H0; try lia.
      assumption.
  - constructor.
    dependent destruction H0.
    simpl in H0_0.
    apply IHcbn_cps in H0_0; auto.
    replace (S (S n)) with (n + 1 + 1) in H0_0; try lia.
    apply not_free_lift in H0_0.
    replace (n + 1) with (1 + n) in H0_0; try lia.
    assumption.
  - dependent destruction H1.
    constructor; simpl.
    + apply IHcbn_cps1; auto.
      replace (S n) with (n + 1 + 0); try lia.
      apply not_free_lift.
      rewrite Nat.add_comm.
      assumption.
    + do 2 constructor.
    + repeat (try constructor; try lia).
      simpl; eapply IHcbn_cps2; auto.
      replace (S (S n)) with (n + 2 + 0); try lia.
      apply not_free_lift.
      rewrite Nat.add_comm.
      assumption.
  - dependent destruction H1.
    dependent destruction H1_0.
    simpl in H2, H1_0_2.
    constructor.
    + apply IHcbn_cps1 in H1_; auto.
      replace (S n) with (n + 1 + 0) in H1_; try lia.
      apply not_free_lift in H1_.
      rewrite Nat.add_comm in H1_.
      assumption.
    + apply IHcbn_cps2 in H1_0_2; auto.
      replace (S (S n)) with (n + 2 + 0) in H1_0_2; try lia.
      apply not_free_lift in H1_0_2.
      rewrite Nat.add_comm in H1_0_2.
      assumption.
Qed.

(*
  From Amadio's class notes, we know that head reduction can't directly simulate
  beta reduction, though it's still computationally adequate. It should be the
  case that extended reduction will be able to properly simulate beta reduction.

  For the call-by-name translation:

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

  Though the exact induction statement may be awkward, as we have to apply these
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

Lemma cbn_simulates_beta:
  forall t e x b c,
  cbn_cps (application (abstraction t e) x) b ->
  cbn_cps (subst x 0 e) c ->
  [b =>* c].
Proof.
  intros.
  do 2 dependent destruction H.
  rewrite lift_lift_simplification in H; auto.
  apply cbn_cps_lift_inversion in H.
  destruct H as (b1, ?, ?).
  apply cbn_cps_lift_inversion in H0.
  destruct H0 as (b2, ?, ?).
  subst; simpl.
  (* As above. TODO: probably should move the comments in here. *)
  admit.
Admitted.

Lemma cbn_simulation:
  forall e f,
  full e f ->
  forall b c,
  cbn_cps e b ->
  cbn_cps f c ->
  [b =>* c].
Proof.
  induction 1; intros.
  (* Case: full_beta. *)
  - eapply cbn_simulates_beta.
    + eassumption.
    + assumption.
  (* Case: full_abs. *)
  - dependent destruction H0.
    dependent destruction H1.
    apply cbn_cps_lift_inversion in H0.
    destruct H0 as (c1, ?, ?).
    apply cbn_cps_lift_inversion in H1.
    destruct H1 as (c2, ?, ?).
    specialize IHfull with c1 c2; subst.
    apply star_bind_right.
    apply star_lift.
    firstorder.
  (* Case: full_app1. *)
  - dependent destruction H0.
    dependent destruction H1.
    assert (c0 = c); eauto 2 with cps.
    clear H0_0 H1_0; subst.
    apply cbn_cps_lift_inversion in H0_.
    destruct H0_ as (c1, ?, ?).
    apply cbn_cps_lift_inversion in H1_.
    destruct H1_ as (c2, ?, ?).
    specialize IHfull with c1 c2; subst.
    apply star_bind_left.
    apply star_lift.
    firstorder.
  (* Case: full_app2. *)
  - dependent destruction H0.
    dependent destruction H1.
    assert (b0 = b); eauto 2 with cps.
    clear H0_ H1_; subst.
    apply cbn_cps_lift_inversion in H0_0.
    destruct H0_0 as (b1, ?, ?).
    apply cbn_cps_lift_inversion in H1_0.
    destruct H1_0 as (b2, ?, ?).
    specialize IHfull with b1 b2; subst.
    apply star_bind_right.
    apply star_bind_right.
    apply star_lift.
    firstorder.
Qed.

Lemma termination_nonvalue:
  forall e,
  ~value e ->
  whnf e ->
  forall c,
  cbn_cps e c ->
  exists2 k,
  converges c (1 + k) & free k e.
Proof.
  induction e; intros.
  - exfalso.
    apply H.
    constructor.
  - exfalso.
    apply H.
    constructor.
  - destruct e1.
    + exists n.
      * dependent destruction H1.
        dependent destruction H1_.
        do 2 constructor.
      * intro.
        dependent destruction H2.
        dependent destruction H2_.
        contradiction.
    + exfalso.
      eapply H0.
      constructor.
    + clear IHe2.
      dependent destruction H1.
      edestruct cbn_cps_lift_inversion with (b := b); eauto.
      subst; rename x into b.
      edestruct IHe1.
      * inversion 1.
      * eapply whnf_application_left.
        eassumption.
      * eassumption.
      * (* TODO: please refactor me. *)
        rename x into k; exists k.
        constructor.
        eapply converges_lift.
        eassumption.
        rewrite lift_bound_ge; try lia.
        constructor; lia.
        intro; apply H3.
        dependent destruction H4.
        assumption.
Qed.

Lemma termination:
  forall e,
  normal cbn e ->
  forall c,
  cbn_cps e c ->
  exists k,
  converges c k.
Proof.
  intros.
  destruct value_dec with e.
  (* Case: e is a value. *)
  - destruct v.
    + (* If this is a free variable, we converge to it. *)
      dependent destruction H0.
      exists (S n).
      constructor.
    + (* If this is an abstraction, we converge to the fresh k. *)
      dependent destruction H0.
      eexists 0.
      do 2 constructor.
  (* Case: e is not a value. *)
  - edestruct termination_nonvalue.
    + eassumption.
    + intros f ?.
      apply H with f.
      apply cbn_whr.
      assumption.
    + eassumption.
    + exists (1 + x).
      assumption.
Qed.

Lemma normal_form_preservation:
  forall e,
  normal full e ->
  forall c,
  cbn_cps e c ->
  normal step c.
Proof.
  admit.
Admitted.

(* -------------------------------------------------------------------------- *)

(* TODO: move this! *)

Notation cps_terminates c :=
  (exists k, weakly_converges c k).

Lemma cps_terminates_implies_sn_head:
  forall b,
  cps_terminates b -> SN head b.
Proof.
  intros.
  destruct H as (k, ?).
  apply weak_convergence_characterization in H.
  destruct H as (c, ?, ?).
  apply clos_rt_rt1n_iff in H.
  induction H.
  - constructor; intros.
    exfalso.
    apply convergence_implies_head_normal_form in H0.
    firstorder.
  - constructor; intros w ?.
    assert (w = y).
    + eapply head_is_a_function; eauto.
    + subst.
      apply IHclos_refl_trans_1n.
      assumption.
Qed.

Lemma cps_terminates_barb:
  forall b,
  cps_terminates b ->
  forall c,
  [b ~~ c] ->
  cps_terminates c.
Proof.
  intros.
  destruct H as (k, (b', ?, ?)).
  assert [b' ~~ c].
  - eapply barb_trans.
    + apply barb_sym.
      apply barb_conv.
      apply conv_star.
      eassumption.
    + assumption.
  - destruct barb_weak_convergence with b' c k; auto.
    destruct H3; eauto with cps.
Qed.

(* --------------------------- *)

Definition cbn_terminates (e: term): Prop :=
  exists2 v,
  value v & rt(cbn) e v.

Lemma sn_cbn_terminates:
  forall e,
  cbn_terminates e -> SN cbn e.
Proof.
  intros.
  destruct H as (v, ?, ?).
  apply clos_rt_rt1n in H0.
  induction H0.
  - rename x into e.
    constructor; intros f ?.
    exfalso.
    eapply cbn_implies_nonvalue with e f; auto.
  - clear H1.
    constructor; intros w ?.
    assert (y = w).
    + apply cbn_is_a_function with x; auto.
    + subst; firstorder.
Qed.

Lemma adequacy_only_if:
  forall e,
  closed e ->
  forall c,
  cbn_cps e c ->
  cbn_terminates e ->
  cps_terminates c.
Proof.
  intros.
  generalize dependent c.
  apply sn_cbn_terminates in H1.
  induction H1 using SN_ind.
  destruct cbn_is_decidable with x; intros.
  - rename x into e; clear H1 H2.
    destruct termination with e c as (k, ?).
    + assumption.
    + assumption.
    + exists k, c; auto with cps.
  - rename c into b.
    destruct e as (y, ?).
    assert (exists c, cbn_cps y c) as (c, ?); eauto with cps.
    assert [b =>* c].
    + apply cbn_simulation with x y; auto.
      apply full_cbn; auto.
    + destruct H2 with y c as (k, ?).
      * apply t_step.
        assumption.
      * (* Reduction can't introduce free variables! *)
        admit.
      * assumption.
      * destruct H6 as (d, ?, ?).
        exists k, d; eauto with cps.
Admitted.

Lemma adequacy_if:
  forall e,
  closed e ->
  forall b,
  cbn_cps e b ->
  cps_terminates b ->
  cbn_terminates e.
Proof.
  intros.
  admit.
Admitted.

Theorem adequacy:
  forall e,
  closed e ->
  forall c,
  cbn_cps e c ->
  cbn_terminates e <-> cps_terminates c.
Proof.
  split; intros.
  - apply adequacy_only_if with e; auto.
  - apply adequacy_if with c; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma cbn_cps_is_compositional:
  forall b1 b2 e1 e2,
  cbn_cps e1 b1 ->
  cbn_cps e2 b2 ->
  [b1 ~~ b2] ->
  forall (h: context) c1 c2,
  cbn_cps (h e1) c1 ->
  cbn_cps (h e2) c2 ->
  [c1 ~~ c2].
Proof.
  induction h; simpl; intros.
  - assert (b1 = c1); eauto 2 with cps.
    assert (b2 = c2); eauto 2 with cps.
    subst; assumption.
  - dependent destruction H2.
    dependent destruction H3.
    apply cbn_cps_lift_inversion in H2.
    apply cbn_cps_lift_inversion in H3.
    destruct H2 as (d1, ?, ?).
    destruct H3 as (d2, ?, ?).
    subst.
    apply barb_bind_right.
    apply barb_lift.
    apply IHh; auto.
  - dependent destruction H2.
    dependent destruction H3.
    assert (c0 = c); eauto 2 with cps.
    subst; clear H2_0 H3_0.
    apply cbn_cps_lift_inversion in H2_.
    apply cbn_cps_lift_inversion in H3_.
    destruct H2_ as (d1, ?, ?).
    destruct H3_ as (d2, ?, ?).
    subst.
    apply barb_bind_left.
    apply barb_lift.
    apply IHh; auto.
  - dependent destruction H2.
    dependent destruction H3.
    assert (b0 = b); eauto 2 with cps.
    subst; clear H2_ H3_.
    apply cbn_cps_lift_inversion in H2_0.
    apply cbn_cps_lift_inversion in H3_0.
    destruct H2_0 as (d1, ?, ?).
    destruct H3_0 as (d2, ?, ?).
    subst.
    apply barb_bind_right.
    apply barb_bind_right.
    apply barb_lift.
    apply IHh; auto.
Qed.

Local Hint Resolve cbn_cps_is_compositional: cps.

Definition cbn_equivalent e f: Prop :=
  forall h: context,
  closed (h e) ->
  closed (h f) ->
  cbn_terminates (h e) <-> cbn_terminates (h f).

Corollary denotational_soundness:
  forall e b,
  cbn_cps e b ->
  forall f c,
  cbn_cps f c ->
  [b ~~ c] -> cbn_equivalent e f.
Proof.
  split; intros.
  - assert (exists b', cbn_cps (h e) b') as (b', ?); auto with cps.
    assert (exists c', cbn_cps (h f) c') as (c', ?); auto with cps.
    apply adequacy with c'.
    + assumption.
    + assumption.
    + apply adequacy with (h e) b' in H4.
      * assert [b' ~~ c']; eauto 2 with cps.
        apply cps_terminates_barb with b'; auto.
      * assumption.
      * assumption.
  - assert (exists b', cbn_cps (h e) b') as (b', ?); auto with cps.
    assert (exists c', cbn_cps (h f) c') as (c', ?); auto with cps.
    apply adequacy with b'.
    + assumption.
    + assumption.
    + apply adequacy with (h f) c' in H4.
      * assert [b' ~~ c']; eauto 2 with cps.
        apply cps_terminates_barb with c'; auto with cps.
      * assumption.
      * assumption.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma cbn_cps_subterm_wn:
  forall e b,
  cbn_cps e b ->
  forall f,
  subterm f e ->
  forall c,
  cbn_cps f c ->
  WN beta b -> WN beta c.
Proof.
  intros.
  (* This is perhaps not the best approach, computationally speaking, as we rely
     a lot on uniform normalization, and there are certainly more efficient ways
     to compute this, but still... it's a somewhat simple way to prove it. *)
  apply uniform_normalization in H2.
  destruct H0.
  (* Case: inside abstraction. *)
  - dependent destruction H.
    apply cbn_cps_lift_inversion in H.
    destruct H; subst; rename b0 into e.
    assert (x = c); eauto with cps; subst.
    apply uniform_normalization.
    eapply SN_preimage with (f := fun c =>
      bind _ _ (CPS.lift 1 2 c));
    eauto; intros.
    apply beta_bind_right.
    apply beta_lift.
    assumption.
  (* Case: inside left hand side of application. *)
  - dependent destruction H.
    apply cbn_cps_lift_inversion in H.
    destruct H; subst; rename x0 into b.
    assert (c0 = b); eauto with cps; subst.
    apply uniform_normalization.
    eapply SN_preimage with (f := fun b =>
      bind (CPS.lift 1 1 b) _ _);
    eauto; intros.
    apply beta_bind_left.
    apply beta_lift.
    assumption.
  (* Case: inside right hand side of application. *)
  - dependent destruction H.
    apply cbn_cps_lift_inversion in H0.
    destruct H0; subst; rename x0 into c.
    assert (c0 = c); eauto with cps; subst.
    apply uniform_normalization.
    eapply SN_preimage with (f := fun c =>
      bind _ _ (bind _ _ (CPS.lift 2 1 c)));
    eauto; intros.
    apply beta_bind_right.
    apply beta_bind_right.
    apply beta_lift.
    assumption.
Qed.

Lemma foo:
  forall y x,
  t(subterm) y x ->
  forall z,
  t(full) y z ->
  exists2 w, t(full) x w & t(subterm) z w.
Proof.
  intros.
  eapply transitive_closure_preserves_diagram; eauto with cps.
  destruct 1; eauto with cps.
Qed.

Lemma bar:
  forall e,
  SN full e ->
  SN (union full (transp subterm)) e.
Proof.
  induction 1 using SN_ind.
  induction subterm_is_well_founded with x.
  clear H0.
  assert (forall y : term,
     subterm y x ->
     SN full y ->
     SN (union full (transp subterm)) y).
  - intros.
    apply H1; clear H1; auto; intros.
    rename y0 into z.
    assert (exists2 w, t(full) x w & subterm z w) as (w, ?, ?).
    + edestruct foo; eauto with cps.
      admit.
    + specialize (H2 w H4).
      destruct H2.
      apply H2; right.
      assumption.
  - clear H1.
    constructor; destruct 1.
    + apply H2; auto with cps.
    + apply H0; auto with cps.
      admit.
Admitted.

Lemma lambda_sn_implies_beta_normal_form:
  forall e,
  SN full e ->
  forall b,
  cbn_cps e b -> WN beta b.
Proof.
  induction 1 using SN_ind; intros.
  destruct x.
  - clear H2.
    dependent destruction H0.
    eexists.
    + eauto with cps.
    + inversion 1.
  - dependent destruction H0.
    apply cbn_cps_lift_inversion in H0.
    destruct H0; subst; rename x0 into b.
    admit.
Admitted.

Theorem preservation_of_strong_normalization:
  forall e,
  SN full e ->
  forall b,
  cbn_cps e b -> SN step b.
Proof.
  intros.
  apply SN_subset with (union beta smol).
  - apply step_characterization.
  - apply shrinking_preserves_strong_normalization.
    + apply smol_is_shrinking.
    + apply uniform_normalization.
      apply lambda_sn_implies_beta_normal_form with e; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Fixpoint cbn_type (t: type): pseudoterm :=
  match t with
  | base =>
    negation [CPS.base]
  | arrow t s =>
    negation [negation [cbn_type s; negation [cbn_type t]]]
  end.

Definition cbn_env (g: env): list pseudoterm :=
  map (fun t => CPS.negation [cbn_type t]) g.

Fixpoint cbn_type_alt (t: type): pseudoterm :=
  match t with
  | base =>
    CPS.base
  | arrow t s =>
    negation [negation [cbn_type_alt s]; negation [negation [cbn_type_alt t]]]
  end.

Definition cbn_env_alt (g: env): list pseudoterm :=
  map (fun t => CPS.negation [CPS.negation [cbn_type_alt t]]) g.

Goal
  forall g,
  cbn_env g = cbn_env_alt g.
Proof.
  induction g; simpl.
  - reflexivity.
  - f_equal.
    + clear IHg g; do 2 f_equal.
      induction a; simpl.
      * reflexivity.
      * rewrite IHa1, IHa2.
        reflexivity.
    + assumption.
Qed.
