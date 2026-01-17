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

Import ListNotations.

(* We build here the initial model (also called the term model) for our type
   theory. It is a category with family such that contexts (i.e., environments),
   substitutions, types and elements are well-typed syntactic objects modulo the
   equational reasoning. To build this model, we will consider our canonical
   reduction relation.

   Let us be honest, I don't really care about proving that this model is indeed
   initial, so please bear with me. I'm very tired. :( *)

Definition welltyped_env: Set :=
  { g: env | valid_env g conv }.

(* TODO: we need to make a type system for substitutions! *)

(* -------------------------------------------------------------------------- *)
(* TODO: move me, please? For now, let's play with the D-presheaf model! *)

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

Definition Dstep_I:
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

Definition Dstep_B:
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
  apply Dstep_I.
Qed.

Definition Deq_B:
  forall x y z,
  Deq (B x y z) (x (y z)).
  intros.
  apply clos_rt_clos_rst.
  apply Dstep_B.
Qed.

Lemma Deq_equiv: Equivalence Deq.
Proof.
  split; repeat intro.
  - apply rst_refl.
  - now apply rst_sym.
  - now apply rst_trans with y.
Qed.

Local Existing Instance Deq_equiv.

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

Polymorphic Record Dset: Type := {
  Dset_carrier :> Type;
  Dset_realization:
    D -> Dset_carrier -> Prop;
  Dset_respectful:
    forall d1 d2,
    Deq d1 d2 ->
    forall x,
    Dset_realization d2 x -> Dset_realization d1 x;
  Dset_surjective:
    forall y: Dset_carrier,
    { x: D | Dset_realization x y }
}.

Local Coercion Dset_realization: Dset >-> Funclass.

Polymorphic Program Definition Delta (A: Type): Dset := {|
  Dset_carrier := A;
  Dset_realization x y := True
|}.

Next Obligation of Delta.
  (* Any combinator is ok; we merely need to show that some exist. Pick I. *)
  exists I; trivial.
Qed.

Polymorphic Record Dmap (X: Dset) (Y: Dset): Type := {
  Dmap_fun: X -> Y;
  (* TODO: do we want this element to be irrelevant...? *)
  Dmap_preserve: exists x, forall y z, X y z -> Y (app x y) (Dmap_fun z)
}.

Local Coercion Dmap_fun: Dmap >-> Funclass.

Definition Dmap_eq: forall {X Y}, relation (Dmap X Y) :=
  fun X Y M N => forall x, M x = N x.

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

Polymorphic Program Definition Dmap_id (X: Dset): Dmap X X := {|
  Dmap_fun x := x
|}.

Obligation 1 of Dmap_id.
  exists I; intros.
  apply Dset_respectful with y.
  - apply Deq_I.
  - assumption.
Qed.

Polymorphic Program Definition Dmap_post X Y Z (M: Dmap X Y) (N: Dmap Y Z):
  Dmap X Z :=
{|
  Dmap_fun x := N (M x)
|}.

Obligation 1 of Dmap_post.
  destruct M as (g, (y, ?H)).
  destruct N as (f, (x, ?H)).
  simpl.
  exists (B x y); intros.
  rename y0 into z, z into w.
  apply Dset_respectful with (x (y z)).
  - apply Deq_B.
  - apply H0.
    apply H.
    assumption.
Qed.

Program Definition DsetCategory: Category := {|
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
