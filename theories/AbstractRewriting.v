(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

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

Notation flip f := (fun a b => f b a).

Arguments commut {A} R1.

Global Hint Unfold commut: cps.

Definition confluent {T} (R: relation T): Prop :=
  commut R (flip R).

Global Hint Unfold confluent: cps.

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
    commut t(R) (flip R).
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
