(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Equality.
Require Export Relations.
Require Import Local.Prelude.

(** ** Relations *)

Notation "'t(' R )" := (clos_trans _ R)
  (format "'t(' R )"): type_scope.

Notation "'rt(' R )" := (clos_refl_trans _ R)
  (format "'rt(' R )"): type_scope.

Notation "'rst(' R )" := (clos_refl_sym_trans _ R)
  (format "'rst(' R )"): type_scope.

Global Hint Constructors clos_trans: cps.
Global Hint Constructors clos_refl_trans: cps.
Global Hint Constructors clos_refl_sym_trans: cps.

Arguments transp {A}.

Global Hint Unfold transp: cps.

Arguments commut {A}.

Global Hint Unfold commut: cps.

Arguments same_relation {A}.

Global Hint Unfold same_relation: cps.

Definition confluent {T} (R: relation T): Prop :=
  commut R (transp R).

Global Hint Unfold confluent: cps.

Definition comp {A} {B} {C} R S: A -> C -> Prop :=
  fun a c =>
    exists2 b: B,
    R a b & S b c.

Section Confluency.

  Set Implicit Arguments.

  Variable T: Type.
  Variable R: relation T.

  Definition church_rosser: Prop :=
    forall x y,
    rst(R) x y ->
    exists2 z,
    rt(R) x z & rt(R) y z.

  Lemma strip_lemma:
    forall confluency: confluent R,
    commut t(R) (transp R).
  Proof.
    induction 2; intros.
    (* Case: step. *)
    - destruct confluency with y x z as (w, ?, ?); auto.
      exists w; auto.
      apply t_step; auto.
    (* Case: trans. *)
    - rename z0 into w.
      destruct IHclos_trans1 with w as (v, ?, ?); auto.
      destruct IHclos_trans2 with v as (u, ?, ?); auto.
      exists u; auto.
      apply t_trans with v; auto.
  Qed.

  Lemma transitive_closure_preserves_confluency:
    forall confluency: confluent R,
    confluent t(R).
  Proof.
    induction 2; intros.
    (* Case: step. *)
    - destruct strip_lemma with z x y as (w, ?, ?); auto.
      exists w; auto.
      apply t_step; auto.
    (* Case: tran. *)
    - rename z0 into w.
      destruct IHclos_trans1 with w as (v, ?, ?); auto.
      destruct IHclos_trans2 with v as (u, ?, ?); auto.
      exists u; eauto with cps.
  Qed.

  Lemma confluency_implies_church_rosser:
    confluent rt(R) -> church_rosser.
  Proof.
    induction 2.
    (* Case: step. *)
    - exists y; auto with cps.
    (* Case: refl. *)
    - exists x; auto with cps.
    (* Case: symm. *)
    - destruct IHclos_refl_sym_trans as (z, ?, ?).
      exists z; auto.
    (* Case: tran. *)
    - destruct IHclos_refl_sym_trans1 as (w, ?, ?).
      destruct IHclos_refl_sym_trans2 as (v, ?, ?).
      destruct H with w y v as (u, ?, ?); auto with cps.
      exists u; eauto with cps.
  Qed.

End Confluency.

Section Normalization.

  Variable T: Type.
  Variable R: relation T.

  Definition normal a: Prop :=
    forall b, ~R a b.

  Definition WN a: Prop :=
    exists2 b, rt(R) a b & normal b.

  Definition SN :=
    (Acc (transp R)).

  Lemma SN_preimage:
    forall f,
    (forall a b, R a b -> R (f a) (f b)) ->
    forall e,
    Acc R (f e) -> Acc R e.
  Proof.
    intros.
    (* There seems to be a bug in the dependent induction tactic... *)
    remember (f e) as x.
    generalize dependent e.
    induction H0; intros.
    constructor; intros.
    eapply H1; eauto.
    rewrite Heqx.
    apply H.
    assumption.
  Qed.

End Normalization.

Section ListNormalization.

  Variable T: Type.
  Variable R: relation T.

  Inductive step_in_list: relation (list T) :=
    | step_in_env_car:
      forall g t u,
      R t u -> step_in_list (t :: g) (u :: g)
    | step_in_env_cdr:
      forall g h t,
      step_in_list g h -> step_in_list (t :: g) (t :: h).

  (* Still not sure we'll be needing this, but just in case... *)

  Lemma step_in_list_is_well_founded:
    forall xs,
    Forall (SN R) xs ->
    SN step_in_list xs.
  Proof.
    induction xs; intros.
    - constructor; intros.
      exfalso.
      inversion H0.
    - dependent destruction H.
      apply IHxs in H0; clear IHxs.
      induction H; clear H.
      induction H0.
      constructor; intros.
      unfold transp in H2.
      dependent destruction H2.
      + apply H1.
        assumption.
      + apply H0; intros.
        * assumption.
        * eapply H1; eauto.
          constructor.
          assumption.
  Qed.

End ListNormalization.
