(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
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
Require Import Local.Constructions.Inversion.

Set Primitive Projections.

(* Given some partial combinatory algebra D, which in here we specialize for the
   plain SK combinatory logic, a D-set is a pair (G, R) such that:
   - G is a type that represents a context (the carrier type);
   - R is a relation between D and G that specifies whether an element x of D
     realizes the context g in G;
   - R is respectful of D's inner structure, so x R g <-> y R g when x == y;
   - R is surjective, such that for every g in G, there is at least one x in D
     such that x R g. *)

Polymorphic Record Dset: Type := {
  Dset_carrier :> Type;
  Dset_realization:
    CL -> Dset_carrier -> Prop;
  Dset_respectful:
    forall x1 x2,
    Combinators.conv x1 x2 ->
    forall y, (* Note that conv is symmetric! *)
    Dset_realization x2 y -> Dset_realization x1 y;
  Dset_surjective:
    forall y: Dset_carrier,
    exists x: CL,
    Dset_realization x y
}.

(* We associate the Dset object to the realization relation for convenience. *)

Local Coercion Dset_realization: Dset >-> Funclass.

(* We define an operation to lift an arbitrary type into a D-set by taking the
   full relation as it's realization (thus we don't care about the computational
   content); i.e., any element x realizes contexts. *)

Polymorphic Program Definition Delta (A: Type): Dset := {|
  Dset_carrier := A;
  Dset_realization x y := True
|}.

Next Obligation of Delta.
  (* Any combinator is ok; we merely need to show that some exist. We pick I. *)
  exists I; trivial.
Qed.

(* A mapping between D-set D and D-indexed family of D-sets G, called D-map, is
   a function f between their carrier types such that there is some combinator x
   where, for any element d of D, and for any realizer y such y realizes d in D,
   then x y realizes f d in G d. We call those D-maps here; Streicher calls them
   D-functions or realizable morphisms. *)

Polymorphic Record Dmap (D: Dset) (G: D -> Dset): Type := {
  Dmap_fun: forall d: D, G d;
  (* TODO: does the element x have to be relevant...? *)
  Dmap_preserve: exists x, forall y d, D y d -> G d (app x y) (Dmap_fun d)
}.

Local Coercion Dmap_fun: Dmap >-> Funclass.

(* Two Dmaps are the same iff their inner mappings are extensionally equal. *)

Definition Dmap_eq: forall {X Y}, relation (Dmap X Y) :=
  fun X Y M N => forall x, M x = N x.

(* This, of course, forms a setoid. *)

Polymorphic Program Definition DmapSetoid {X Y}: Setoid := {|
  carrier := Dmap X Y;
  equiv := Dmap_eq
|}.

Obligation 1 of DmapSetoid.
  split; repeat intro.
  - reflexivity.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Global Canonical Structure DmapSetoid.

(* We will often want maps from D-sets into simple D-sets rather than into D-set
   families, so we add an abbreviation for these. *)

Polymorphic Definition Dmap' (D: Dset) (G: Dset) := Dmap D (const G).

(* We may consider the identity Dmap on Dsets, using the identity function. *)

Polymorphic Program Definition Dmap'_id (X: Dset): Dmap' X X := {|
  Dmap_fun x := x
|}.

Obligation 1 of Dmap'_id.
  exists I; intros.
  apply Dset_respectful with y.
  - apply conv_I.
  - assumption.
Qed.

(* Of course, we may compose D-maps using composition of their functions, which
   respects the proper conditions. *)

Polymorphic Program Definition Dmap'_post X Y Z (M: Dmap' X Y) (N: Dmap' Y Z):
  Dmap' X Z :=
{|
  Dmap_fun x := N (M x)
|}.

Obligation 1 of Dmap'_post.
  destruct M as (g, (y, ?H)).
  destruct N as (f, (x, ?H)).
  exists (B x y); intros; simpl.
  rename y0 into z.
  apply Dset_respectful with (x (y z)).
  - apply conv_B.
  - now apply H0, H.
Qed.

(* As required, D-sets and D-maps form a category. *)

Polymorphic Program Definition DsetCategory: Category := {|
  obj := Dset;
  hom := Dmap';
  id := Dmap'_id;
  post := Dmap'_post
|}.

Obligation 1 of DsetCategory.
  repeat intro; simpl.
  now rewrite H, H0.
Qed.

Obligation 2 of DsetCategory.
  repeat intro; simpl.
  reflexivity.
Qed.

Obligation 3 of DsetCategory.
  repeat intro; simpl.
  reflexivity.
Qed.

Obligation 4 of DsetCategory.
  repeat intro; simpl.
  reflexivity.
Qed.

Local Canonical Structure DsetCategory.

(* -------------------------------------------------------------------------- *)

Section DsetModel.

  Program Definition DsetModel: CwF := {|
    cwf_cat := Dset;
    cwf_empty := {|
      terminal := Delta ();
      terminal_hom (X: Dset) := {|
        Dmap_fun (g: X) := ();
      |}
    |};
    cwf_ty G := G -> Dset;
    cwf_tsub G D (s: Dmap' D G) (A: G -> Dset) (d: D) :=
      A (s d);
    cwf_el G := {|
      setoid_fun (A: G -> Dset) := Dmap G A;
    |};
    cwf_esub G D (A: G -> Dset) (s: Dmap' D G) (e: Dmap G A) := {|
      Dmap_fun d := e (s d)
    |};
    (* TODO: make a general definition for Dset pairs! *)
    cwf_snoc G D (s: Dmap' D G) (A: G -> Dset) e := {|
      Dmap_fun d := existT _ (s d) (e d)
    |};
    cwf_ext G (A: G -> Dset) := {|
      Dset_carrier := { g: G & A g };
      Dset_realization (x: CL) p :=
        let (g, e) := p in G (x K) g /\ A g (x F) e
    |};
    (* TODO: define snoc... *)
    (* First projection. *)
    cwf_proj G (A: G -> Dset) := {|
      Dmap_fun p := let (g, e) := p in g
    |};
    (* Second projection. *)
    cwf_zero G (A: G -> Dset) := {|
      (* The program mode will make the conversion for us! *)
      Dmap_fun p := let (g, e) := p in _ e
    |}
  |}.

  Next Obligation of DsetModel.
    exists I; intros.
    trivial.
  Qed.

  Next Obligation of DsetModel.
    repeat intro; simpl.
    remember (f x) as u.
    now destruct u.
  Qed.

  Next Obligation of DsetModel.
    repeat intro.
    unfold funext_eq in H.
    admit.
  Admitted.

  Next Obligation of DsetModel.
    destruct e as (e, (x, ?H)); simpl in *.
    destruct s as (s, (y, ?H)); simpl in *.
    exists (B x y); intros.
    rename y0 into z.
    (* TODO: may we merge this with the postcomposition definition for DMap? *)
    apply Dset_respectful with (x (y z)).
    - apply conv_B.
    - apply H, H0.
      assumption.
  Qed.

  Next Obligation of DsetModel.
    split.
    - apply Dset_respectful with (x2 K).
      + now rewrite H.
      + assumption.
    - apply Dset_respectful with (x2 F).
      + now rewrite H.
      + assumption.
  Qed.

  Next Obligation of DsetModel.
    rename y into g, X into e.
    destruct Dset_surjective with G g as (x, ?H).
    destruct Dset_surjective with (A g) e as (y, ?H).
    exists (P x y); split.
    - apply Dset_respectful with x.
      + rewrite conv_P.
        rewrite conv_K.
        reflexivity.
      + assumption.
    - apply Dset_respectful with y.
      + rewrite conv_P.
        rewrite conv_F.
        reflexivity.
      + assumption.
  Qed.

  Next Obligation of DsetModel.
    destruct (Dmap_preserve _ _ s) as (x, ?).
    destruct (Dmap_preserve _ _ e) as (y, ?).
    (* Careful inspection: this term is enough! *)
    exists (C (P x y)); intros z ? ?; split.
    - specialize (H _ _ H1).
      unfold const in H.
      apply Dset_respectful with (x z).
      + rewrite conv_C.
        rewrite conv_P.
        rewrite conv_K.
        reflexivity.
      + assumption.
    - specialize (H0 _ _ H1).
      apply Dset_respectful with (y z).
      + rewrite conv_C.
        rewrite conv_P.
        rewrite conv_F.
        reflexivity.
      + assumption.
  Qed.

  Next Obligation of DsetModel.
    exists (C I K); intros.
    destruct d as (g, e).
    unfold const.
    apply Dset_respectful with (y K).
    - rewrite conv_C.
      rewrite conv_I.
      reflexivity.
    - destruct H.
      assumption.
  Qed.

  Next Obligation of DsetModel.
    exists (C I F); intros.
    destruct d as (g, e); simpl.
    apply Dset_respectful with (y F).
    - rewrite conv_C.
      rewrite conv_I.
      reflexivity.
    - destruct H.
      assumption.
  Qed.

  Next Obligation of DsetModel.
    repeat intro.
    now rewrite H, H0.
  Qed.

  Next Obligation of DsetModel.
    repeat intro.
    reflexivity.
  Qed.

  Next Obligation of DsetModel.
    repeat intro.
    reflexivity.
  Qed.

End DsetModel.

Section DPresheaf.

  (* TODO: make C polymorphic, turn this into an actual presheaf... *)

  Variable C: Category.

  Local Definition Dpresheaf: Type := Functor (opposite C) Dset.

  (* We'll define this as in the thesis for now; some definitions look like they
     may be simplified later. *)

  Program Definition DpresheafModel: CwF := {|
    cwf_cat := Dpresheaf;
    cwf_empty := {|
      terminal := {|
        mapping (X: opposite C) := terminal _ (cwf_empty DsetModel);
        fmap (X: opposite C) (Y: opposite C) := {|
          setoid_fun (f: opposite C X Y) := {|
            Dmap_fun (Z: Delta ()) := Z
          |}
        |}
      |};
      terminal_hom (X: Dpresheaf) := {|
        transformation (Y: opposite C) :=
          terminal_hom Dset (cwf_empty DsetModel) (X Y)
      |}
    |};
    cwf_ty (G: Dpresheaf) := _;
    cwf_tsub (G: Dpresheaf) (D: Dpresheaf) (s: NaturalTransformation D G)
      (A: _) := _;
  |}.

  Next Obligation of DpresheafModel.
    exists I; intros.
    assumption.
  Qed.

  Next Obligation of DpresheafModel.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    intro; simpl.
    rename X0 into Y.
    remember (f Y x) as u.
    now destruct u.
  Qed.

  Admit Obligations.

End DPresheaf.

(* TODO: move these definitions to the [Category.v] file. *)

Section Elements.

  Variable C: Category.

  (* TODO: use any kind of presheaf! *)

  Variable G: Dpresheaf C.

  (* The category of elements of G, a presheaf over C, has, as objects, pairs
     of an object X of C and an element r of the set G(X). Then, for every
     morphism f in C from Y to X, and for every element r of G(X), it has a
     morphism from (X, r) to (Y, G(f)(r)); i.e., the morphisms are technically
     pairs of an inner morphism in C^op and a proof about the relation between
     the respective sets (in the second projection). *)

  Record elem: Type := elem_mk {
    elem_obj: opposite C;
    elem_set: G elem_obj
  }.

  Record elem_hom (x: elem) (y: elem): Type := elem_hom_mk {
    elem_hom_morphism: opposite C (elem_obj x) (elem_obj y);
    elem_hom_coherence: elem_set y = fmap G elem_hom_morphism (elem_set x)
  }.

  Local Coercion elem_hom_morphism: elem_hom >-> carrier.

  Program Definition ElemHomSetoid e f: Setoid := {|
    carrier := elem_hom e f;
    (* We use the D-set morphism definition of equality for the inner map. *)
    equiv := equiv
  |}.

  Next Obligation.
    split; repeat intro.
    - reflexivity.
    - now symmetry.
    - now transitivity (elem_hom_morphism e f y).
  Qed.

  Local Canonical Structure ElemHomSetoid.

  Program Definition ElementsCategory: Category := {|
    obj := elem;
    hom e f := elem_hom e f;
    id x := elem_hom_mk x x id _;
    post x y z f g := elem_hom_mk x z (post f g) _
  |}.

  Next Obligation.
    rewrite (fmap_id _ _ G); simpl.
    reflexivity.
  Qed.

  Next Obligation.
    destruct x as (x, r).
    destruct y as (y, s).
    destruct z as (z, t).
    destruct f as (f, ?H); simpl in *.
    destruct g as (g, ?H); simpl in *.
    change (post g f) with (post (c := opposite C) f g).
    rewrite (fmap_comp _ _ G); simpl.
    subst; reflexivity.
  Qed.

  Next Obligation.
    repeat intro; simpl.
    now rewrite H, H0.
  Qed.

  Next Obligation.
    now rewrite post_id_right.
  Qed.

  Next Obligation.
    now rewrite post_id_left.
  Qed.

  Next Obligation.
    now rewrite post_assoc.
  Qed.

End Elements.
