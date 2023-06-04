(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Axiomatic.
Require Import Local.Reduction.
Require Import Local.Residuals.
Require Import Local.Confluence.

(* Anything that is a bisimulation on parallel reduction should preserve jump
   reduction. *)

(* TODO: move this definition to [Prelude.v]! *)

Notation const T x :=
  (fun _: T => x).

Definition equi: relation pseudoterm :=
  (* TODO: we need the definition of strong bisimilarity! *)
  fun b c =>
    exists2 S,
    strong_bisimulation (const unit parallel) S & S b c.

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
    apply modulo_bisimulation_strong_normalization.
    - split; admit.
    - admit.
  Admitted.

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
   the (DISTR) law, which can duplicate redexes... *)

Goal
  forall c,
  SN beta c ->
  SN (modulo beta equi) c.
Proof.
  intros.
  apply beta_and_parallel_SN_coincide in H.
  apply strong_normalization_module_equi with (S := equi) in H.
  - apply SN_subset with (R := modulo parallel equi).
    + clear H c; intros b e (c, (d, (?, (?, ?)))).
      exists c, d; eauto with cps.
    + assumption.
  - (* Why is Coq asking for the diagrams from us if we didn't use them? *)
    clear H c.
    intros x y ? z ?.
    destruct H0 as (S, (?, ?), ?).
    destruct H0 with x z y as (w, ?, ?); try easy.
    exists w.
    + apply rt_step.
      exists S; try split; auto.
    + assumption.
  - (* That's strange... *)
    clear H c.
    intros x y ? z ?.
    destruct H0 as (S, (?, ?), ?).
    destruct H1 with x z y as (w, ?, ?); try easy.
    exists w.
    + apply rt_step.
      exists S; try split; auto.
    + assumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* This property is mentioned in Yoshida's paper for the pi-calculus, using the
   same reduction relation as we are. The proof dates back to Church, who first
   showed it, but she (on lemma B.3) refers to Barendregt's textbook (page 293,
   lemma 11.3.1), which contains his own version of the proof. *)

Lemma backwards_parallel_preservation:
  forall c,
  SN parallel c ->
  forall b,
  parallel b c -> SN parallel b.
Proof.
  (* We follow by induction both on the maximal reduction length for c, as well
     as the maximal length for development in b. *)
  induction 1; intros.
  (* Some housekeeping... TODO: we should have SN_ind, right? *)
  rename x into c.
  fold (SN parallel) in H.
  unfold transp in H, H0.
  destruct H1 as (r, ?, ?).
  (* TODO: We should have the maximum development length in here! *)
  remember (redexes_count r) as n.
  generalize dependent r.
  generalize dependent b.
  induction n using lt_wf_ind; intros.
  dependent destruction Heqn.
  (* Now we can check the next move! *)
  constructor; intros d (s, ?, ?).
  fold (SN parallel).
  (* So, since parallel reduction has the weak diamond property... *)
  destruct parallel_is_joinable with b c d as (e, ?, ?); eauto with cps.
  destruct H6; destruct H7.
  (* Case: r and s are unrelated. *)
  - (* We need to "move" in both directions. We follow by our first inductive
       hypothesis. *)
    rename y into e.
    apply H0 with e; auto.
  (* Case: r is a strict subset of s. *)
  - (* Here c can move to d. So we performed all the missing redexes and a few
       more! As our hypothesis says that c is SN, we can finish already. *)
    apply H; auto.
  (* Case: s is a strict subset of r. *)
  - (* Here we are performing some, but not all, of the missing redexes. We
       proceed by our second inductive hypothesis, as it will now need less work
       to develop all the missing redexes. *)
    rename y into e.
    destruct H6 as (t, ?, ?).
    apply H1 with (redexes_count t) t; auto.
    (* TODO: As stated above, we gotta fix the right number in here. Well, if we
       had started with a single jump, we could argue that this is indeed true
       if we kept the invariant that r can only mark jumps to the same variable,
       but as we'll probably need to reason about development length in order to
       prove finite development (in any order), this also works. *)
    admit.
  (* Case: r and s are the same. *)
  - (* Now we have reached a point where the terms were joined back, all the
       missing redexes were contracted, and we proceed with our induction
       hypothesis alone. *)
    constructor.
    exact H.
Admitted.

Theorem uniform_normalization:
  forall b,
  WN beta b <-> SN beta b.
Proof.
  admit.
Admitted.

Corollary conservation:
  forall a,
  ~SN beta a ->
  forall b,
  beta a b -> ~SN beta b.
Proof.
  intros a ? b ? ?.
  eapply H; clear H.
  (* TODO: review this. *)
  apply uniform_normalization in H1.
  apply uniform_normalization.
  destruct H1 as (c, ?, ?).
  exists c; eauto with cps.
Qed.
