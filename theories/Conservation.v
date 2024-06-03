(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Residuals.
Require Import Local.Confluence.

(* Anything that is a bisimulation on parallel reduction should preserve jump
   reduction. *)

(* TODO: move this definition to [Prelude.v]! *)

Notation const T x :=
  (fun _: T => x).

Definition equi: relation pseudoterm :=
  strong_bisimilarity (const unit parallel).

Global Hint Unfold equi: cps.

Lemma beta_and_parallel_SN_coincide:
  forall c,
  SN beta c <-> SN parallel c.
Proof.
  (* TODO: rewrite this proof by using a proper morphism! *)
  split; intros.
  - apply SN_R_t_R in H.
    apply SN_R_t_R.
    induction H; constructor; intros.
    apply H0.
    apply t_beta_and_t_parallel_coincide.
    assumption.
  - apply SN_R_t_R in H.
    apply SN_R_t_R.
    induction H; constructor; intros.
    apply H0.
    apply t_beta_and_t_parallel_coincide.
    assumption.
Qed.

Section Technique.

  Local Notation R := parallel.

  Variable S: relation pseudoterm.

  Hypothesis R_diagram1:
    diagram R S rt(S) R.

  Hypothesis R_diagram2:
    diagram R (transp S) rt(transp S) R.

  Local Lemma rst_S_is_bisimulation:
    strong_bisimulation (const unit R) rst(S).
  Proof.
    (* TODO: this lemma could use auxiliary stuff: symmetric simulation is a
       bisimulation, something about rt(transp R), etc... *)
    split;
    intros x y ?;
    [ apply clos_rst_rst1n_iff in H
    | apply clos_rst_rstn1_iff in H ];
    induction H;
    intros w _ ?.
    - exists w; auto with cps.
    - destruct H.
      + destruct R_diagram1 with x w y as (p, ?, ?); auto.
        destruct IHclos_refl_sym_trans_1n with p as (q, ?, ?); try easy.
        exists q; eauto with cps.
        (* I'm not sure why eauto can't solve this one. *)
        eapply rst_trans; eauto.
        apply clos_rt_clos_rst; auto.
      + destruct R_diagram2 with x w y as (p, ?, ?); auto.
        destruct IHclos_refl_sym_trans_1n with p as (q, ?, ?); try easy.
        exists q; eauto with cps.
        eapply rst_trans; eauto.
        apply rst_sym, clos_rt_clos_rst.
        clear H1 H3 H4 H5; induction H2; eauto with cps.
    - exists w; auto with cps.
    - rename y0 into x.
      destruct H.
      + destruct R_diagram2 with z w x as (p, ?, ?); auto.
        destruct IHclos_refl_sym_trans_n1 with p as (q, ?, ?); try easy.
        exists q; eauto with cps.
        eapply rst_trans; eauto.
        (* TODO: again, make some lemmas... *)
        clear H1 H3 H4 H5.
        induction H2; eauto with cps.
      + destruct R_diagram1 with z w x as (p, ?, ?); auto.
        destruct IHclos_refl_sym_trans_n1 with p as (q, ?, ?); try easy.
        exists q; eauto with cps.
        eapply rst_trans; eauto.
        apply rst_sym, clos_rt_clos_rst.
        clear H1 H3 H4 H5; induction H2; eauto with cps.
  Qed.

  Local Lemma strong_normalization_module_equi:
    forall c,
    SN R c ->
    SN (modulo R equi) c.
  Proof.
    apply modulo_bisimulation_strong_normalization; try split.
    - apply strong_bisimilarity_refl.
    - apply strong_bisimilarity_trans.
    - apply strong_bisimilarity_sym.
    - destruct 1 as (X, (?, ?), ?); intros.
      destruct H with a b c; auto.
      exists x.
      + assumption.
      + exists X; auto.
        split; auto.
    - destruct 1 as (X, (?, ?), ?); intros.
      destruct H0 with a b c; auto.
      exists x.
      + assumption.
      + exists X; auto.
        split; auto.
  Qed.

  Local Lemma strong_normalization_module_relation:
    forall T,
    inclusion T equi ->
    forall c,
    SN R c ->
    SN (modulo R T) c.
  Proof.
    intros.
    apply SN_subset with (modulo R equi).
    - intros x w (y, (z, (?, (?, ?)))).
      exists y, z; repeat split.
      + apply H; auto.
      + assumption.
      + apply H; auto.
    - apply strong_normalization_module_equi.
      assumption.
  Qed.

  Lemma preservation_technique:
    forall b,
    SN beta b ->
    forall c,
    rst(S) b c -> SN beta c.
  Proof.
    intros.
    apply beta_and_parallel_SN_coincide in H.
    apply strong_normalization_module_relation with (T := rst(S)) in H.
    - eapply SN_subset with (R := modulo R rst(S)).
      + clear H H0 b c.
        intros b c ?.
        exists b, c; eauto with cps.
      + constructor; intros d (e, (f, (?, (?, ?)))).
        apply H.
        exists e, f; eauto with cps.
    - clear H H0 b c.
      intros b c ?.
      exists rst(S).
      + exact rst_S_is_bisimulation.
      + assumption.
  Qed.

End Technique.

(* Is jump reduction modulo strong parallel bisimilarity really valid? TODO: add
   some comments in here, of course. This seems a bit odd, as it should include
   the (DISTR) law, which can duplicate redexes...

   Edit: it IS valid, and it does NOT include the (DISTR) law. The issue is that
   using (DISTR) doesn't require us to join/split a reference. I gotta write
   some explanation about this. *)

Goal
  forall c,
  SN beta c ->
  SN (modulo beta equi) c.
Proof.
  intros.
  apply beta_and_parallel_SN_coincide in H.
  apply strong_normalization_module_equi in H.
  apply SN_subset with (R := modulo parallel equi).
  - clear H c; intros b e (c, (d, (?, (?, ?)))).
    exists c, d; eauto with cps.
  - assumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* This property is mentioned in Yoshida's paper for the pi-calculus, using the
   same reduction relation as we are. The proof dates back to Church, who first
   showed it, but she (on lemma B.3) refers to Barendregt's textbook (page 293,
   lemma 11.3.1), which contains his own version of the proof. We follow it in
   spirit. *)

Lemma backwards_parallel_preservation:
  forall c,
  SN parallel c ->
  forall b,
  parallel b c -> SN parallel b.
Proof.
  (* We follow by induction both on the maximal reduction length for c, as well
     as the maximal length for development in b. *)
  induction 1 using SN_ind; intros.
  rename x into c.
  destruct H0 as (r, ?, ?).
  remember (redexes_weight [] r) as n.
  generalize dependent r.
  generalize dependent b.
  induction n using lt_wf_ind; intros.
  dependent destruction Heqn.
  (* Now we can check the next move! *)
  constructor; intros d (p, ?, ?).
  fold (SN parallel).
  (* So, since parallel reduction is defined in terms of residuals, we can use
     the paving lemma to join back the reductions that lead to c and d. *)
  destruct paving with (mark b) r (mark c) p (mark d); eauto.
  (* As c has no marks (or d, of course), so the result shouldn't as well. *)
  assert (exists e, d0 = mark e) as (e, ?) by eauto with cps; subst.
  (* We proceed by case analysis on the number of marks in rp and pr. *)
  destruct (le_gt_dec (redexes_count rp) 0) as [ ?H | ?H ];
  destruct (le_gt_dec (redexes_count pr) 0) as [ ?H | ?H ].
  (* Case: r and p are the same. *)
  - (* We have reached a point where the terms were joined back, thus all the
       missing redexes were contracted. Since neither path requires any work,
       we conclude that c = d and we are done by our inductive hypothesis. *)
    assert (c = e) by eauto with arith cps; subst.
    assert (d = e) by eauto with arith cps; subst.
    assumption.
  (* Case: r is a strict subset of p. *)
  - (* Here c can move to d. So we performed all the missing redexes and a few
       more! As our hypothesis says that c is SN, we can finish already by doing
       the additional redexes alone. *)
    assert (d = e) by eauto with arith cps; subst.
    apply H; unfold transp.
    eauto with cps.
  (* Case: p is a strict subset of r. *)
  - (* Here we are performing some, but not all, of the missing redexes, and
       nothing more. We proceed by our second inductive hypothesis, as we will
       now need less work to develop all the missing redexes. We have enough
       information to state that p is a subset of r. *)
    assert (c = e) by eauto with arith cps; subst.
    apply H0 with (redexes_weight [] rp) rp; auto.
    (* Naturally, any partial development reduces the maximum number of steps
       required to develop the term. *)
    apply development_reduces_weight with p [].
    + (* Clearly, from H6 and H11. *)
      eapply subset_residuals_zero_marks; eauto with arith.
    + eauto with cps.
    + assumption.
    + constructor.
  (* Case: r and p are unrelated. *)
  - (* We need to move in both directions. So we follow by our first inductive
       hypothesis, as we're decreasing the maximum reduction length. *)
    apply H2 with e; eauto with cps.
Qed.

Lemma sn_beta_backwards_step:
  forall b c,
  beta b c ->
  SN beta c -> SN beta b.
Proof.
  intros.
  apply beta_and_parallel_SN_coincide in H0.
  apply beta_and_parallel_SN_coincide.
  apply backwards_parallel_preservation with c.
  - assumption.
  - auto with cps.
Qed.

Theorem uniform_normalization:
  forall b,
  WN beta b <-> SN beta b.
Proof.
  split; intros.
  (* Case: WN implies SN. *)
  - destruct H as (c, ?, ?).
    apply clos_rt_rt1n_iff in H.
    induction H.
    + constructor; intros.
      exfalso.
      now apply H0 with y.
    + apply sn_beta_backwards_step with y; auto.
  (* Case: WN implies SN. *)
  - apply sn_implies_wn; auto.
    apply beta_is_decidable.
Qed.

Corollary conservation:
  forall a,
  ~SN beta a ->
  forall b,
  beta a b -> ~SN beta b.
Proof.
  intros a ? b ? ?.
  eapply H; clear H.
  apply uniform_normalization in H1.
  destruct H1 as (c, ?, ?).
  apply uniform_normalization.
  exists c; eauto with cps.
Qed.
