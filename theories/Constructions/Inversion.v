(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.Cumulativity.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Confluence.
(* Require Import Local.Constructions.Normalization. *)

Section Inversion.

  Variable R: typing_equivalence.

  Variable R_refl: forall g t, R g t t.
  Variable R_trans: forall g t1 t2 t3, R g t1 t2 -> R g t2 t3 -> R g t1 t3.

  Lemma typing_bound_inv:
    forall g n t,
    typing g (bound n) t R ->
    exists2 x,
    item x g n & R g (lift (1 + n) 0 (snd x)) t.
  Proof.
    intros.
    dependent induction H.
    - clear IHinfer.
      eexists.
      + eassumption.
      + simpl.
        apply R_refl.
    - clear IHinfer.
      eexists.
      + eassumption.
      + simpl.
        apply R_refl.
    - clear IHinfer2.
      specialize (IHinfer1 R_refl R_trans _ _ _ eq_refl) as (d, ?H, ?H).
      exists d.
      + assumption.
      + rename t0 into t, t into u.
        now apply R_trans with t.
  Qed.

  Lemma typing_implies_sort:
    forall g e t,
    typing g e t R ->
    exists s,
    typing g t (sort_term s) R.
  Proof.
    intros.
    dependent induction H.
    - exists (type 1).
      now constructor.
    - exists (type (2 + n)).
      now constructor.
    - clear IHinfer.
      admit.
    - clear IHinfer.
      admit.
    - apply valid_env_typing in H.
      clear - H.
      destruct s.
      + exists (type 0).
        now constructor.
      + exists (type (1 + n)).
        now constructor.
    - apply valid_env_typing in H.
      clear - H.
      exists (type 0).
      now constructor.
    - admit.
    - admit.
    - admit.
    - apply valid_env_typing in H.
      clear - H.
      destruct s.
      + exists (type 0).
        now constructor.
      + exists (type (1 + n)).
        now constructor.
    - admit.
    - admit.
    - admit.
    - clear - H.
      exists (type 0).
      now constructor.
    - clear - H.
      exists iset.
      now constructor.
    - clear - H.
      exists iset.
      now constructor.
    - admit.
    - now exists s.
  Admitted.

End Inversion.

(*

Lemma typing_type_inv:
  forall g n t,
  typing g (type n) t conv ->
  conv g t (type (1 + n)).
Proof.
  repeat intro.
  dependent induction H.
  - apply conv_refl.
  - rename t0 into u.
    apply conv_trans with u.
    + now apply conv_sym.
    + now apply IHinfer1.
  - rename t0 into u.
    apply cumul_trans with u.
Qed.

Lemma typing_iset_inv:
  forall g t,
  typing g iset t conv ->
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
  typing g (bound n) t conv ->
  exists2 x,
  item x g n & conv g t (lift (1 + n) 0 (snd x)).
Proof.
  intros.
  dependent induction H.
  (* Case: var. *)
  - clear IHinfer.
    eexists.
    + eassumption.
    + apply conv_refl.
  (* Case: ref. *)
  - clear IHinfer.
    eexists.
    + eassumption.
    + apply conv_refl.
  (* Case: conv. *)
  - clear IHinfer2.
    specialize (IHinfer1 _ _ _ eq_refl eq_refl) as (x, ?, ?).
    exists x.
    + assumption.
    + rename t0 into u.
      apply conv_trans with u.
      * now apply conv_sym.
      * assumption.
Qed.

Lemma typing_unique:
  forall g e t1,
  typing g e t1 conv ->
  forall t2,
  typing g e t2 conv ->
  (* TODO: use the subtyping relation on conv. *)
  conv g t1 t2.
Proof.
  intros until 1.
  dependent induction H; intros.
  - clear IHinfer.
    apply typing_iset_inv in H0.
    now apply conv_sym.
  - clear IHinfer.
    apply typing_type_inv in H0.
    now apply conv_sym.
  - clear IHinfer.
    destruct typing_bound_inv with g n t2.
    + assumption.
    + assert (x = (None, t)) by now apply item_unique with g n.
      dependent destruction H4; simpl in H3.
      now apply conv_sym.
  - clear IHinfer.
    destruct typing_bound_inv with g n t2.
    + assumption.
    + rename e0 into e.
      assert (x = (Some e, t)) by now apply item_unique with g n.
      dependent destruction H4; simpl in H3.
      now apply conv_sym.
  - specialize (IHinfer1 _ _ _ eq_refl eq_refl).
    specialize (IHinfer2 _ _ _ eq_refl eq_refl).
    generalize dependent s2.
    generalize dependent s1.
    dependent induction H1; intros.
    + clear IHinfer1 IHinfer2.
      specialize (IHinfer0 _ H1_).
      specialize (IHinfer3 _ H1_0).
      admit.
    + clear IHinfer2.
      specialize (IHinfer1 _ _ _ _ eq_refl eq_refl).
      eapply conv_trans with t0; auto.
  (* - admit.
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
  - admit. *)
  - admit.
  - admit.
  - specialize (IHinfer1 _ _ _ eq_refl eq_refl _ H2).
    apply conv_trans with t.
    + now apply conv_sym.
    + assumption.
Admitted.
*)
