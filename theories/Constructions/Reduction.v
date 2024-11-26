(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Normalization.

(* For typeable terms, the normal form is computable. *)
Lemma normal_form_is_decidable:
  forall g e t,
  typing g e t ->
  exists2 f,
  rt(step g) e f & normal (step g) f.
Proof.
  intros.
  apply strong_normalization in H.
  induction H using SN_ind.
  destruct step_is_decidable with x g as [ (y, ?) | ? ].
  - destruct H2 with y as (z, ?, ?).
    + now apply t_step.
    + exists z; eauto with cps.
  - exists x.
    + apply rt_refl.
    + intros y ?.
      apply n.
      now exists y.
Qed.
