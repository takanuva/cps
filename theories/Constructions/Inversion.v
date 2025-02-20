(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
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

Lemma typing_iset_inv:
  forall g t,
  typing g iset t R ->
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

Lemma typing_bound_inv:
  forall g n t,
  typing g (bound n) t R ->
  exists2 x,
  item x g n & conv g t (lift (1 + n) 0 (snd x)).
Proof.
  intros.
  dependent induction H.
  - clear IHinfer; destruct d.
    + eexists.
      * eassumption.
      * simpl.
        apply conv_refl.
    + eexists.
      * eassumption.
      * simpl.
        apply conv_refl.
  - clear IHinfer2.
    specialize (IHinfer1 _ _ _ eq_refl JMeq_refl) as (x, ?, ?).
    exists x.
    + assumption.
    + rename t0 into u.
      apply conv_trans with u.
      * now apply conv_sym.
      * assumption.
Qed.

Lemma typing_unique:
  forall g e t1,
  typing g e t1 R ->
  forall t2,
  typing g e t2 R ->
  conv g t1 t2.
Proof.
  intros until 1.
  dependent induction H; intros.
  - clear IHinfer.
    apply typing_iset_inv in H0.
    now apply conv_sym.
  - clear IHinfer.
    destruct typing_bound_inv with g n t2.
    + assumption.
    + assert (x = (d, t)) by now apply item_unique with g n.
      dependent destruction H4.
      simpl in H3.
      now apply conv_sym.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - specialize (IHinfer1 _ _ _ eq_refl JMeq_refl _ H2).
    apply conv_trans with t.
    + now apply conv_sym.
    + assumption.
Admitted.
