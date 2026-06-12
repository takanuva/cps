(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Setoid.
Require Import Local.Category.
Require Import Local.Combinators.

Import ListNotations.
Set Primitive Projections.

(*
  Modeling a D-set hierarchy in Coq is seemingly not a trivial task... but lets
  give it a shot. Out of spite, of course.

  Namely, a D-set, also called an assembly (actually this name seems preferred),
  is just a carrier set S along with a relation between some combinatory algebra
  D (which we fix as CL here!) and S, that specifies that a combinator realizes
  S. We can think of these as "machine implementations" for such a carrier, as
  noted by van Evert ("Realizability semantics for type theory").

  This would usually be simple to code, but in order to construct universes in
  the categorical model for some type theory, we'll need to build a D-set such
  that the carrier set is the set of D-sets itself. Of course then there will be
  size issues: we need to define D-set up to some size. While we can define the
  D-set type as a polymorphic structure, such that we can always take D-sets
  from a smaller universe as carrier sets, these universes are not internally
  indexable in Coq's type theory, so we can't really make an initial model (out
  of the syntax objects). In Agda we would simply eliminate from nat into Level
  and call it a day... sigh.

  So, in order to model this, we rely on the encoding for induction-recursion
  using impredicative Set, in order to make internal Tarski universes. We start
  with some basic universe U 0: Set (defined in [Univese/Hierarchy.v]). We then
  build a small generalization of D-sets over some family of types, dset A B,
  which allows most of the constructions needed when A = U 0 and B = T 0. For
  the following universes in the hierarchy, we need then a code for dset itself,
  which we can take as a type constructor. So, by now using dset (U 1) (T 1), we
  can embed everything from dset (U 0) (T 0) due to cumulativity, plus we will
  have a code for dset (U 0) (T 0) itself too, leading to the desired notion of
  hierarchy. This will, of course, also happen for all U n in the hierarchy. So
  finally, we can work using the transfinite universe, by defining our category
  using dset (U uw) (T uw).
*)

Section DSet.

  Variable U: Type.
  Variable T: U -> Type.

  Structure dset: Type := {
    dset_code: U;
    dset_carrier := T dset_code;
    dset_equiv: dset_carrier -> dset_carrier -> Prop;
    dset_realization: CL -> dset_carrier -> Prop;
    dset_refl:
      forall x,
      dset_equiv x x;
    dset_sym:
      forall x y,
      dset_equiv x y ->
      dset_equiv y x;
    dset_trans:
      forall x y z,
      dset_equiv x y ->
      dset_equiv y z ->
      dset_equiv x z;
    dset_respectful:
      forall x1 x2,
      CL_equiv x1 x2 ->
      forall y1 y2,
      dset_equiv y1 y2 ->
      dset_realization x2 y2 ->
      dset_realization x1 y1;
    dset_surjective:
      forall y: dset_carrier,
      { x: CL | dset_realization x y }
  }.

  Global Coercion dset_realization: dset >-> Funclass.

  Global Instance dset_equiv_is_equivalence:
    forall G,
    Equivalence (dset_equiv G).
  Proof.
    split; repeat intro.
    - apply dset_refl.
    - now apply dset_sym.
    - now apply dset_trans with y.
  Qed.

  Definition dset_carrier_setoid (s: dset): Setoid := {|
    setoid_carrier := dset_carrier s;
    setoid_equiv := dset_equiv s;
    setoid_refl := dset_refl s;
    setoid_sym := dset_sym s;
    setoid_trans := dset_trans s
  |}.

  Global Canonical Structure dset_carrier_setoid.

  Global Coercion dset_carrier_setoid: dset >-> Setoid.

  Global Instance dset_realization_proper:
    forall {G: dset},
    Proper (setoid_equiv ==>
            (@setoid_equiv (dset_carrier_setoid G)) ==>
            iff) (dset_realization G).
  Proof.
    split; intro.
    - now apply dset_respectful with x x0.
    - now apply dset_respectful with y y0.
  Qed.

  Definition tracks {G: dset} {D: G -> dset} (d: CL) (f: forall x: G, D x) :=
    forall x: G,
    forall e: CL,
    G e x -> D x (d e) (f x).

  Structure dmap (G: dset) (D: dset): Type := {
    dmap_fun: SetoidMap G D;
    dmap_machine: CL;
    dmap_tracks: tracks dmap_machine dmap_fun
  }.

  Global Coercion dmap_fun: dmap >-> SetoidMap.

  Global Arguments dmap_fun {G} {D}.
  Global Arguments dmap_machine {G} {D}.

  Definition dmap_equiv {G D} (f: dmap G D) (g: dmap G D): Prop :=
    dmap_fun f == dmap_fun g.

  Program Definition dmap_setoid (G: dset) (D: dset): Setoid := {|
    setoid_carrier := dmap G D;
    setoid_equiv := dmap_equiv
  |}.

  Next Obligation of dmap_setoid.
    repeat intro.
    reflexivity.
  Qed.

  Next Obligation of dmap_setoid.
    repeat intro.
    now symmetry.
  Qed.

  Next Obligation of dmap_setoid.
    repeat intro.
    rename x0 into w.
    now transitivity (y w).
  Qed.

  Global Canonical Structure dmap_setoid.

  Program Definition dmap_id {G}: dmap G G := {|
    dmap_fun := map x => x;
    dmap_machine := I
  |}.

  Next Obligation of dmap_id.
    repeat intro.
    now rewrite CL_equiv_I.
  Qed.

  Program Definition dmap_post {G D E} (f: dmap G D) (g: dmap D E) := {|
    dmap_fun := map x => g (f x);
    dmap_machine := B (dmap_machine g) (dmap_machine f)
  |}.

  Next Obligation of dmap_post.
    now rewrite H.
  Qed.

  Next Obligation of dmap_post.
    repeat intro.
    rewrite CL_equiv_B.
    apply dmap_tracks.
    apply dmap_tracks.
    assumption.
  Qed.

  Global Instance dmap_post_proper:
    forall G D E,
    Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) (@dmap_post G D E).
  Proof.
    repeat intro.
    unfold dmap_post; simpl.
    setoidify.
    transitivity (y0 (x x1)).
    - apply H0.
    - apply cong.
      apply H.
  Qed.

  Program Definition dset_category: Category := {|
    obj := dset;
    hom := dmap_setoid;
    id G := dmap_id;
    post G D E :=
      map f g => dmap_post f g
  |}.

  Next Obligation of dset_category.
    now rewrite H.
  Qed.

  Next Obligation of dset_category.
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

  Definition dset_family (G: dset): Type :=
    { f: G -> dset & is_family G f }.

  (* TODO: we need to define the notion of equality on families... *)

  Axiom dset_family_equiv:
    forall G: dset,
    dset_family G ->
    dset_family G ->
    Prop.

  Program Definition dset_family_setoid (G: dset): Setoid := {|
    setoid_carrier := dset_family G;
    setoid_equiv := dset_family_equiv G
  |}.

  Next Obligation of dset_family_setoid.
    admit.
  Admitted.

  Next Obligation of dset_family_setoid.
    admit.
  Admitted.

  Next Obligation of dset_family_setoid.
    admit.
  Admitted.

  (* There's some coercions involved, but... *)

  Definition dset_setoid_family G (D: dset_family G): SetoidFamily G := {|
    setoid_family := projT1 D;
    setoid_family_prf := projT2 D
  |}.

  Global Coercion dset_setoid_family: dset_family >-> SetoidFamily.

End DSet.
