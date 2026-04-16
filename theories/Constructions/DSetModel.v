(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Category.
Require Import Local.Substitution.
Require Import Local.Combinators.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.

Import EqNotations.

Set Universe Polymorphism.
Set Primitive Projections.

(* TODO: these will be the telescopes! *)
Axiom C: SmallCategory.

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
  now rewrite H.
Qed.

Next Obligation of dmap_setoid.
  repeat intro.
  now rewrite H, H0.
Qed.

Global Canonical Structure dmap_setoid.

Program Definition dset_category: Category := {|
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

Program Definition dset_family (G: dset): Setoid := {|
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

Program Definition dset_model: CwF := {|
  cwf_cat := dset_category;
  cwf_empty := {|
    terminal := delta_unit;
    terminal_hom X := {|
      dmap_fun x := ();
      dmap_wit := I
    |}
  |};
  cwf_ty := dset_family;
  cwf_tsub (G D: dset) :=
    map (S: dmap D (const G)) (T: dset_family G) =>
      fun (d: D) => T (S d);
  cwf_el (G: dset) := {|
    setoid_family (T: dset_family G) :=
      dmap_setoid G T;
    setoid_transport T U H := {|
      setoid_map E := {|
        dmap_fun (X: G) :=
          rew [dset_carrier] H X in E X;
        dmap_wit := dmap_wit E
      |}
    |}
  |};
  cwf_esub (G D: dset) (T: dset_family G) (S: dmap D (const G)) :=
    map (E: dmap G T) => {|
      dmap_fun (d: D) := E (S d);
      dmap_wit := B (dmap_wit E) (dmap_wit S)
    |};
  cwf_u (G: dset) (n: nat) (g: G) :=
    delta_dset;
  cwf_t (G: dset) (n: nat) U :=
    dmap_fun U;
  cwf_lift (G: dset) n l (H: n < l) U :=
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
  apply dset_respectful with (dmap_wit E (dmap_wit S y)).
  - apply conv_B.
  - apply dmap_preserves.
    now apply (dmap_preserves D (const G)).
Qed.

Next Obligation of dset_model.
  repeat intro; simpl.
  now rewrite H.
Qed.

Next Obligation of dset_model.
  repeat intro.
  reflexivity.
Qed.
