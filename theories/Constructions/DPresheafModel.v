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
  (* Shockingly, (fun x y f => f x y) becomes this. *)
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

Section DPresheaf.

  Variable C: Category.

  Local Definition DPresheaf: Type := Functor (opposite C) Dset.

  (* We build a model using the functor category [C^op, Dset] as the category of
     contexts and morphisms. Types... *)

  (* Temprary definitions for the Dset model (not used); TODO: remove it! *)

  Definition Env: Type := Dset.
  Definition Sub: Env -> Env -> Setoid := Dmap'.
  Definition Ty (G: Env): Setoid := G -> Dset.
  Definition El (G: Env) (A: Ty G): Setoid := Dmap G A.

  Program Definition ext (G: Env) (A: Ty G): Env := {|
    Dset_carrier := { g: G & A g };
    Dset_realization (x: D) p :=
      let (g, a) := p in
      G (x K) g /\ A g (x F) a
  |}.

  Next Obligation.
    split.
    - apply Dset_respectful with (d2 K).
      + now rewrite H.
      + assumption.
    - apply Dset_respectful with (d2 F).
      + now rewrite H.
      + assumption.
  Qed.

  Next Obligation.
    rename y into x, X into y.
    destruct Dset_surjective with G x as (a, ?H).
    destruct Dset_surjective with (A x) y as (b, ?H).
    exists (P a b); split.
    - apply Dset_respectful with a.
      + rewrite Deq_P.
        rewrite Deq_K.
        reflexivity.
      + assumption.
    - apply Dset_respectful with b.
      + rewrite Deq_P.
        rewrite Deq_F.
        reflexivity.
      + assumption.
  Qed.

  (* Program Definition DPresheafModel: CwF := {|
    cwf_cat := DPresheaf;
    cwf_empty := {|
      terminal := {|
        mapping (X: C) := Delta ();
        fmap (X: C) (Y: C) (f: C Y X) := Dmap'_id (Delta ())
      |};
      terminal_hom (F: DPresheaf) := {|
        transformation (X: C) := {|
          Dmap_fun (A: F X) := tt
        |}
      |}
    |};
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

  Admit Obligations. *)

End DPresheaf.
