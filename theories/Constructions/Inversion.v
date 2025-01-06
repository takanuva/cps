(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Confluence.
Require Import Local.Constructions.Normalization.

Local Notation R := typed_conv.

Lemma typing_type_inv:
  forall g n t,
  ~typing g (type n) t R.
Proof.
  repeat intro.
  dependent induction H.
  specialize (IHinfer1 _ _ _ eq_refl JMeq_refl).
  assumption.
Qed.

Lemma typing_prop_inv:
  forall g t,
  typing g prop t R ->
  conv g t (type 0).
Proof.
  intros.
  dependent induction H.
  - apply conv_refl.
  - rename t0 into u.
    apply conv_trans with u.
    + now apply conv_sym.
    + now apply IHinfer1.
Qed.
