(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
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

Goal
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
