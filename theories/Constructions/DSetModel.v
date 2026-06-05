(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Program.
Require Import Equality.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Setoid.
Require Import Local.Category.
Require Import Local.Combinators.
Require Import Local.DSet.
Require Import Local.Universe.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.

Set Primitive Projections.

Definition dset_omega: Type :=
  dset (U uw) T.

(* TODO: might want to move this... *)

Import EqNotations.

Arguments finite_O {n}.
Arguments finite_S {n}.

Definition tt1 {l}: T (FINITE 1) :=
  rew <- [fun T => T] T_FINITE l 1 in finite_O.

Lemma tt1_unique:
  forall l: level,
  forall u: T (@FINITE l 1),
  u = @tt1 l.
Proof.
  intro; unfold tt1.
  rewrite T_FINITE.
  compute; intros.
  dependent destruction u.
  - reflexivity.
  - exfalso.
    inversion u.
Qed.

Program Definition nabla_unit: dset_omega := {|
  dset_code := FINITE 1;
  dset_equiv := eq;
  dset_realization x y := True
|}.

Next Obligation of nabla_unit.
  now exists I.
Defined.

Program Definition dset_terminal: Terminal (dset_category (U uw) T) := {|
  terminal := nabla_unit;
  terminal_hom X := {|
    dmap_fun x := tt1;
    dmap_wit := I
  |}
|}.

Next Obligation of dset_terminal.
  repeat intro; simpl in *.
  apply (tt1_unique uw).
Qed.

Program Definition dset_model: CwF := {|
  cwf_cat := dset_category (U uw) T;
  cwf_empty := dset_terminal
|}.

Admit Obligations.

(*

Section DSetModel.

  Import EqNotations.

  (* These will be the telescopes! *)
  Variable C: SmallCategory.

  Program Definition dset_model: CwF := {|
    cwf_cat := dset_category C;
    cwf_empty := {|
      terminal := delta_unit C;
      terminal_hom X := {|
        dmap_fun x := ();
        dmap_wit := I
      |}
    |};
    cwf_ty := dset_family C;
    cwf_tsub (G D: dset C) :=
      map (S: dmap C D (const G)) (T: dset_family C G) =>
        fun (d: D) => T (S d);
    cwf_el (G: dset C) := {|
      setoid_family (T: dset_family C G) :=
        dmap_setoid C G T;
      setoid_family_prf := {|
        setoid_transport T U H := {|
          setoid_map E := {|
            dmap_fun (X: G) :=
              rew [dset_carrier C] H X in E X;
            dmap_wit := dmap_wit C E
          |}
        |}
      |}
    |};
    cwf_esub (G D: dset C) (T: dset_family C G) (S: dmap C D (const G)) :=
      map (E: dmap C G T) => {|
        dmap_fun (d: D) := E (S d);
        dmap_wit := B (dmap_wit C E) (dmap_wit C S)
      |};
    cwf_u (G: dset C) (n: nat) (g: G) :=
      delta_dset C;
    cwf_t (G: dset C) (n: nat) U :=
      dmap_fun C U;
    cwf_lift (G: dset C) n l (H: n < l) U :=
      U
  |}.

  Next Obligation of dset_model.
    repeat intro; simpl.
    now destruct (f x).
  Qed.

  Next Obligation of dset_model.
    repeat intro.
    now rewrite H.
  Qed.

  Next Obligation of dset_model.
    repeat intro.
    now rewrite H.
  Qed.

  Next Obligation of dset_model.
    destruct (H g); simpl.
    now apply dmap_preserves.
  Qed.

  Next Obligation of dset_model.
    repeat intro; simpl.
    destruct (H x0); simpl.
    apply H0.
  Qed.

  Next Obligation of dset_model.
    repeat intro; simpl.
    generalize (H2 x1) as Y.
    generalize (H1 x1) as X.
    clear H1 H2; intros.
    dependent destruction X; simpl.
    dependent destruction Y; simpl.
    reflexivity.
  Qed.

  Next Obligation of dset_model.
    repeat intro; simpl.
    generalize (H x1) as X; intros.
    dependent destruction X; simpl.
    reflexivity.
  Qed.

  Next Obligation of dset_model.
    repeat intro; simpl.
    generalize (H3 x1) as Z.
    generalize (H2 x1) as Y.
    generalize (H1 x1) as X.
    intros.
    dependent destruction X; simpl.
    dependent destruction Y; simpl.
    dependent destruction Z; simpl.
    reflexivity.
  Qed.

  Next Obligation of dset_model.
    apply dset_respectful with (dmap_wit C E (dmap_wit C S y)).
    - apply conv_B.
    - apply dmap_preserves.
      now apply (dmap_preserves C D (const G)).
  Qed.

  Next Obligation of dset_model.
    repeat intro; simpl.
    now rewrite H.
  Qed.

  Next Obligation of dset_model.
    repeat intro.
    reflexivity.
  Qed.

End DSetModel.

*)
