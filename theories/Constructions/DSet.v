(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Setoid.
Require Import Local.Category.
Require Import Local.Universe.
Require Import Local.Combinators.

Set Universe Polymorphism.
Set Primitive Projections.

(* TODO: we're axiomatizing D-sets as an inductive-recursive type for now, but
   we'll later properly encode it once we're satisfied with the formulation. *)

Section DSet.

  Variable C: SmallCategory.

  Inductive dset: Set :=
    (* | dset_mk:
      forall T: Set,
      forall R: CL -> T -> Prop,
      (forall x1 x2 y, x1 == x2 -> R x2 y -> R x1 y) ->
      (forall y, exists x, R x y) ->
      dset *)
    | delta_unit: dset
    | delta_dset: dset
    | delta_hom: C -> C -> dset.

  Definition dset_carrier (G: dset): Type :=
    match G with
    (* | dset_mk T R _ _ => T *)
    | delta_unit => unit
    | delta_dset => dset
    | delta_hom X Y => C X Y
    end.

  Global Coercion dset_carrier: dset >-> Sortclass.

  Definition dset_realization (G: dset): CL -> G -> Prop :=
    match G with
    (* | dset_mk T R _ _ => R *)
    (* For the following, return the universal relation. *)
    | delta_unit => fun _ _ => True
    | delta_dset => fun _ _ => True
    | delta_hom X Y => fun _ _ => True
    end.

  Global Coercion dset_realization: dset >-> Funclass.

  Lemma dset_respectful:
    forall x1 x2,
    x1 == x2 ->
    forall (G: dset) y,
    G x2 y -> G x1 y.
  Proof.
    simpl; intros.
    destruct G.
    (* + now apply r with x2. *)
    + trivial.
    + trivial.
    + trivial.
  Qed.

  Lemma dset_surjective (G: dset) (y: G): exists x, G x y.
  Proof.
    destruct G.
    (* - apply e. *)
    - exists I; simpl.
      trivial.
    - exists I; simpl.
      trivial.
    - exists I; simpl.
      trivial.
  Qed.

  Structure dmap (G: dset) (D: G -> dset): Type := {
    dmap_fun: forall g: G, D g;
    dmap_wit: CL;
    dmap_preserves:
      forall y g,
      G y g -> D g (app dmap_wit y) (dmap_fun g)
  }.

  Global Arguments dmap_fun {G} {D}.
  Global Arguments dmap_wit {G} {D}.

  Global Coercion dmap_fun: dmap >-> Funclass.

  (* TODO: should dmaps carry setoids...? We'll find out later! *)

  Definition dmap_equiv {G D}: dmap G D -> dmap G D -> Prop :=
    funext_equiv.

  Program Definition dmap_setoid G D: SmallSetoid := {|
    setoid_carrier := dmap G D;
    setoid_equiv := dmap_equiv
  |}.

  Next Obligation of dmap_setoid.
    repeat intro.
    reflexivity.
  Qed.

  Next Obligation of dmap_setoid.
    repeat intro.
    now rewrite H.
  Qed.

  Next Obligation of dmap_setoid.
    repeat intro.
    now rewrite H, H0.
  Qed.

  Global Canonical Structure dmap_setoid.

  Program Definition dset_category: SmallCategory := {|
    obj := dset;
    hom G D := dmap G (fun _ => D);
    id G := {|
      dmap_fun x := x;
      dmap_wit := I
    |};
    post G D E := map f g => {|
      dmap_fun x := g (f x);
      dmap_wit := B (dmap_wit g) (dmap_wit f)
    |}
  |}.

  Next Obligation of dset_category.
    apply dset_respectful with y.
    - apply conv_I.
    - assumption.
  Qed.

  Next Obligation of dset_category.
    rename g0 into x.
    apply dset_respectful with (dmap_wit g (dmap_wit f y)).
    - apply conv_B.
    - now apply g, f.
  Qed.

  Next Obligation of dset_category.
    repeat intro; simpl.
    now rewrite H.
  Qed.

  Next Obligation of dset_category.
    repeat intro; simpl.
    now rewrite H.
  Qed.

  Next Obligation of dset_category.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of dset_category.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of dset_category.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Definition dset_family_equiv (G: dset): (G -> dset) -> (G -> dset) -> Prop :=
    funext_equiv.

  Program Definition dset_family (G: dset): SmallSetoid := {|
    setoid_carrier := G -> dset;
    setoid_equiv := dset_family_equiv G
  |}.

  Next Obligation of dset_family.
    reflexivity.
  Qed.

  Next Obligation of dset_family.
    now symmetry.
  Qed.

  Next Obligation of dset_family.
    now transitivity y.
  Qed.

End DSet.
