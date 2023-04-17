(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Reduction.

(* This property is mentioned in Yoshida's paper for the pi-calculus, using the
   same reduction relation as we are. The proof dates back to Church, who first
   showed it, but she (on lemma B.3) refers to Barendregt's textbook (page 293,
   lemma 11.3.1), which contains his own version of the proof. So this property
   is true, but might be somewhat awkward to prove in Coq. I wonder if I'll need
   the context difference lemma. *)

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
  apply uniform_normalization in H1.
  apply uniform_normalization.
  destruct H1 as (c, ?, ?).
  exists c; eauto with cps.
Qed.
