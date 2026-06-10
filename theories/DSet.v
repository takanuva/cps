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
      forall x: dset_carrier,
      dset_equiv x x;
    dset_sym:
      forall x y: dset_carrier,
      dset_equiv x y ->
      dset_equiv y x;
    dset_trans:
      forall x y z: dset_carrier,
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

  Definition dset_setoid (s: dset): Setoid := {|
    setoid_carrier := dset_carrier s;
    setoid_equiv := dset_equiv s;
    setoid_refl := dset_refl s;
    setoid_sym := dset_sym s;
    setoid_trans := dset_trans s
  |}.

  Global Canonical Structure dset_setoid.

  Global Coercion dset_setoid: dset >-> Setoid.

  Global Instance dset_realization_proper:
    forall {G: dset},
    Proper (setoid_equiv ==>
            (@setoid_equiv (dset_setoid G)) ==>
            iff) (dset_realization G).
  Proof.
    split; intro.
    - now apply dset_respectful with x x0.
    - now apply dset_respectful with y y0.
  Qed.

  Structure dmap (G: dset) (D: dset): Type := {
    dmap_fun: G -> D;
    dmap_wit: CL;
    dmap_respectful:
      forall y1 y2,
      y1 == y2 ->
      dmap_fun y1 == dmap_fun y2;
    dmap_preserves:
      forall y g,
      G y g ->
      D (app dmap_wit y) (dmap_fun g)
  }.

  Global Coercion dmap_fun: dmap >-> Funclass.

  Definition dmap_equiv {G D} (f: dmap G D) (g: dmap G D): Prop :=
    forall x, f x == g x.

  Program Definition dmap_setoid G D: Setoid := {|
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

  Global Instance dmap_proper:
    forall G D f,
    Proper (setoid_equiv ==> setoid_equiv) (@dmap_fun G D f).
  Proof.
    repeat intro.
    now apply dmap_respectful.
  Qed.

  Program Definition dmap_id {G}: dmap G G := {|
    dmap_fun x := x;
    dmap_wit := I
  |}.

  Next Obligation of dmap_id.
    now rewrite CL_equiv_I.
  Qed.

  Program Definition dmap_post {G D E} (f: dmap G D) (g: dmap D E) := {|
    dmap_fun x := g (f x);
    dmap_wit := B (dmap_wit _ _ g) (dmap_wit _ _ f)
  |}.

  Next Obligation of dmap_post.
    now rewrite H.
  Qed.

  Next Obligation of dmap_post.
    rewrite CL_equiv_B.
    apply dmap_preserves.
    apply dmap_preserves.
    assumption.
  Qed.

  Global Instance dmap_post_proper:
    forall G D E,
    Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) (@dmap_post G D E).
  Proof.
    repeat intro.
    unfold dmap_post; simpl.
    transitivity (y0 (x x1)).
    - apply H0.
    - apply dmap_respectful.
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

End DSet.

(*
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
*)
