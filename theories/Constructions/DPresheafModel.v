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
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Inversion.

Set Primitive Projections.

Inductive D: Set :=
  | K: D
  | S: D
  | app: D -> D -> D.

Local Coercion app: D >-> Funclass.

Local Definition I: D :=
  S K K.

Local Definition B: D :=
  S (K S) K.

Local Definition C: D :=
  S (S (K (S (K S) K)) S) (K K).

Local Definition F: D :=
  S K.

Local Definition P: D :=
  (* Perhaps shockingly, (fun x y f => f x y) becomes this. *)
  C (B B (B C (B (C I) I))) I.

Inductive Dstep: relation D :=
  | Dstep_K:
    forall x y,
    Dstep (K x y) x
  | Dstep_S:
    forall x y z,
    Dstep (S x y z) (x z (y z))
  | Dstep_app_left:
    forall x1 x2 y,
    Dstep x1 x2 ->
    Dstep (x1 y) (x2 y)
  | Dstep_app_right:
    forall (x: D) y1 y2,
    Dstep y1 y2 ->
    Dstep (x y1) (x y2).

Definition Deq: relation D :=
  rst(Dstep).

Definition Deq_K:
  forall x y,
  Deq (K x y) x.
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply Dstep_K.
Qed.

Definition Deq_S:
  forall x y z,
  Deq (S x y z) (x z (y z)).
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_step.
  apply Dstep_S.
Qed.

Local Instance Deq_equiv: Equivalence Deq.
Proof.
  split; repeat intro.
  - apply rst_refl.
  - now apply rst_sym.
  - now apply rst_trans with y.
Qed.

Local Instance Deq_app_proper:
  Proper (Deq ==> Deq ==> Deq) app.
Proof.
  repeat intro.
  transitivity (y x0).
  - clear H0 y0.
    induction H.
    + apply rst_step.
      now apply Dstep_app_left.
    + reflexivity.
    + now symmetry.
    + now transitivity (y x0).
  - clear H x.
    induction H0.
    + apply rst_step.
      now apply Dstep_app_right.
    + reflexivity.
    + now symmetry.
    + now transitivity (y y0).
Qed.

Definition Deq_I:
  forall x,
  Deq (I x) x.
Proof.
  intros.
  unfold I.
  rewrite Deq_S.
  rewrite Deq_K.
  reflexivity.
Qed.

Definition Deq_B:
  forall x y z,
  Deq (B x y z) (x (y z)).
Proof.
  intros.
  unfold B.
  rewrite Deq_S.
  rewrite Deq_K.
  rewrite Deq_S.
  rewrite Deq_K.
  reflexivity.
Qed.

Definition Deq_C:
  forall x y z,
  Deq (C x y z) (x z y).
Proof.
  intros.
  unfold C.
  rewrite Deq_S.
  rewrite Deq_S.
  rewrite Deq_K.
  rewrite Deq_S.
  rewrite Deq_K.
  rewrite Deq_S.
  rewrite Deq_K.
  rewrite Deq_S.
  rewrite Deq_K.
  rewrite Deq_K.
  reflexivity.
Qed.

Definition Deq_F:
  forall x y,
  Deq (F x y) y.
Proof.
  intros.
  unfold F.
  rewrite Deq_S.
  rewrite Deq_K.
  reflexivity.
Qed.

Definition Deq_P:
  forall x y f,
  Deq (P x y f) (f x y).
Proof.
  intros.
  unfold P.
  rewrite Deq_C.
  rewrite Deq_B.
  rewrite Deq_B.
  rewrite Deq_B.
  rewrite Deq_C.
  rewrite Deq_B.
  rewrite Deq_C.
  rewrite Deq_I.
  rewrite Deq_I.
  rewrite Deq_I.
  reflexivity.
Qed.

(* A D-set is a pair (G, R) such that:
   - G is a type that represents a context (the carrier type);
   - R is a relation between D and G that specifies that an element x of D
     realizes the context g in G;
   - R is respectful of D's inner structure, so x R g <-> y R g when x == y;
   - R is surjective, such that for every g in G, there is at least one x in D
     such that x R g. *)

Polymorphic Record Dset: Type := {
  Dset_carrier :> Type;
  Dset_realization:
    D -> Dset_carrier -> Prop;
  Dset_respectful:
    forall d1 d2,
    Deq d1 d2 ->
    forall x, (* Note that Deq is symmetric! *)
    Dset_realization d2 x -> Dset_realization d1 x;
  Dset_surjective:
    forall y: Dset_carrier,
    exists x: D,
    Dset_realization x y
}.

Local Coercion Dset_realization: Dset >-> Funclass.

(* We define an operation to lift an arbitrary type into a Dset by taking the
   full relation as it's relation; i.e., any element x realizes contexts. *)

Polymorphic Program Definition Delta (A: Type): Dset := {|
  Dset_carrier := A;
  Dset_realization x y := True
|}.

Next Obligation of Delta.
  (* Any combinator is ok; we merely need to show that some exist. We pick I. *)
  exists I; trivial.
Qed.

(* A mapping between Dset D and D-indexed family of Dsets G is a function f
   between their carrier types such that there is some combinator x where, for
   any element d of D, and for any realizer y such y realizes d in D, then (x y)
   realizes (f d) in G d. *)

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

(* We will often want maps from Dsets into simple Dsets rather than into Dset
   families, so we add an abbreviation for these. *)

Polymorphic Definition Dmap' (D: Dset) (G: Dset) := Dmap D (const G).

(* We may consider the identity Dmap on Dsets, using the identity function. *)

Polymorphic Program Definition Dmap'_id (X: Dset): Dmap' X X := {|
  Dmap_fun x := x
|}.

Obligation 1 of Dmap'_id.
  exists I; intros.
  apply Dset_respectful with y.
  - apply Deq_I.
  - assumption.
Qed.

(* Of course, we may compose Dmaps using composition of their functions, which
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
  - apply Deq_B.
  - now apply H0, H.
Qed.

(* Dsets and Dmaps form a category. *)

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
    cwf_el G (A: G -> Dset) := Dmap G A;
    cwf_esub G D (A: G -> Dset) (s: Dmap' D G) (e: Dmap G A) := {|
      Dmap_fun d := e (s d)
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
    destruct e as (e, (x, ?H)); simpl in *.
    destruct s as (s, (y, ?H)); simpl in *.
    exists (B x y); intros.
    rename y0 into z.
    (* TODO: may we merge this with the postcomposition definition for DMap? *)
    apply Dset_respectful with (x (y z)).
    - apply Deq_B.
    - apply H, H0.
      assumption.
  Qed.

  Next Obligation of DsetModel.
    compute.
    admit.
  Admitted.

  Next Obligation of DsetModel.
    compute.
    admit.
  Admitted.

  Next Obligation of DsetModel.
    compute; intros.
    now rewrite H, H0.
  Qed.

  Next Obligation of DsetModel.
    compute; intros.
    reflexivity.
  Qed.

  Next Obligation of DsetModel.
    compute; intros.
    reflexivity.
  Qed.

End DsetModel.

Section DPresheaf.

  (* TODO: make C polymorphic, turn this into an actual presheaf... *)

  Variable C: Category.

  Local Definition DPresheaf: Type := Functor (opposite C) Dset.

  (* TODO: move these definitions to the [Category.v] file. *)

  Section Elements.

    Variable G: DPresheaf.

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
      (* We use the Dset morphism definition of equality for the inner map. *)
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

End DPresheaf.
