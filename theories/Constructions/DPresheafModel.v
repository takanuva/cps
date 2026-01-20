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

Definition rt_Dstep_I:
  forall x,
  rt(Dstep) (I x) x.
Proof.
  intros.
  unfold I.
  eapply rt_trans.
  - apply rt_step.
    apply Dstep_S.
  - apply rt_step.
    apply Dstep_K.
Qed.

Definition rt_Dstep_B:
  forall x y z,
  rt(Dstep) (B x y z) (x (y z)).
Proof.
  intros.
  unfold B.
  eapply rt_trans.
  - apply rt_step.
    do 2 apply Dstep_app_left.
    apply Dstep_S.
  - eapply rt_trans.
    + apply rt_step.
      do 3 apply Dstep_app_left.
      apply Dstep_K.
    + eapply rt_trans.
      * apply rt_step.
        apply Dstep_S.
      * apply rt_step.
        apply Dstep_app_left.
        apply Dstep_K.
Qed.

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

Definition Deq_I:
  forall x,
  Deq (I x) x.
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_Dstep_I.
Qed.

Definition Deq_B:
  forall x y z,
  Deq (B x y z) (x (y z)).
Proof.
  intros.
  apply clos_rt_clos_rst.
  apply rt_Dstep_B.
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

(* A D-set is a pair (C, R) such that:
   - G is a type that represents a context (the carrier type);
   - R is a relation between D and C that specifies that an element x of D
     realizes the context g in C;
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
    { x: D | Dset_realization x y }
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

(* A mapping between Dsets D and G is a function f between their carrier types
   such that there is some combinator x where, for any element d of D, and for
   any realizer y such y realizes d in D, then (x y) realizes (f d) in G. *)

Polymorphic Record Dmap (D: Dset) (G: Dset): Type := {
  Dmap_fun: D -> G;
  (* TODO: does the element x have to be relevant...? *)
  Dmap_preserve: exists x, forall y d, D y d -> G (app x y) (Dmap_fun d)
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

(* We may consider the identity Dmap on Dsets, using the identity function. *)

Polymorphic Program Definition Dmap_id (X: Dset): Dmap X X := {|
  Dmap_fun x := x
|}.

Obligation 1 of Dmap_id.
  exists I; intros.
  apply Dset_respectful with y.
  - apply Deq_I.
  - assumption.
Qed.

(* Of course, we may compose Dmaps using composition of their functions, which
   respects the proper conditions. *)

Polymorphic Program Definition Dmap_post X Y Z (M: Dmap X Y) (N: Dmap Y Z):
  Dmap X Z :=
{|
  Dmap_fun x := N (M x)
|}.

Obligation 1 of Dmap_post.
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
  hom := Dmap;
  id := Dmap_id;
  post := Dmap_post
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

Section DPresheaf.

  Variable C: SmallCategory.

  Local Definition DPresheaf: Type := Functor (opposite C) Dset.

  (* We build a model using the functor category [C^op, Dset] as the category of
     contexts and morphisms. Types... *)

  Definition Con: Type := Dset.
  Definition Sub: Con -> Con -> Setoid := Dmap.
  Definition Ty (G: Con): Setoid := G -> Dset.
  (* Definition El (G: Con) (A: Ty G): Setoid :=
    Dmap G A. *)

  Program Definition DPresheafModel: CwF := {|
    cwf_cat := DPresheaf;
    cwf_empty := {|
      terminal := {|
        mapping (X: C) := Delta ();
        fmap (X: C) (Y: C) (f: C Y X) := Dmap_id (Delta ())
      |};
      terminal_hom (F: DPresheaf) := {|
        transformation (X: C) := {|
          Dmap_fun (A: F X) := tt
        |}
      |}
    |}
  |}.

  Next Obligation.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation.
    exists I; easy.
  Qed.

  Next Obligation.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation.
    repeat intro; simpl.
    enough (forall v: unit, v = ()); intros.
    - apply H.
    - now destruct v.
  Qed.

  Next Obligation.
    admit.
  Admitted.

  Next Obligation.
    admit.
  Admitted.

  Next Obligation.
    admit.
  Admitted.

  Next Obligation.
    admit.
  Admitted.

  Next Obligation.
    admit.
  Admitted.

  Next Obligation.
    admit.
  Admitted.

End DPresheaf.
