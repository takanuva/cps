(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Morphisms.
Require Import Local.Setoid.
Require Import Local.Universe.

Set Universe Polymorphism.

Section IZF.

  Context `{Universe}.

  Inductive V: Set :=
    | setof (A: U) (f: T A -> V): V.

  Definition V_class: Type :=
    V -> Prop.

  Fixpoint V_equiv (x: V) (y: V): Prop :=
    match x, y with
    | setof A f, setof B g =>
      (forall a: T A, exists b: T B, V_equiv (f a) (g b)) /\
        (forall b: T B, exists a: T A, V_equiv (f a) (g b))
    end.

  Lemma V_equiv_refl:
    forall x,
    V_equiv x x.
  Proof.
    induction x; split; intros.
    - now exists a.
    - now exists b.
  Qed.

  Lemma V_equiv_sym:
    forall x y,
    V_equiv x y -> V_equiv y x.
  Proof.
    induction x; destruct y; split; intros.
    - destruct H1 as (_, ?H).
      destruct (H1 a) as (b, ?H).
      exists b.
      now apply H0.
    - destruct H1 as (?H, _).
      destruct (H1 b) as (a, ?H).
      exists a.
      now apply H0.
  Qed.

  Lemma V_equiv_trans:
    forall x y z,
    V_equiv x y -> V_equiv y z -> V_equiv x z.
  Proof.
    induction x; destruct y, z; split; intros.
    - destruct H1 as (?H, _).
      destruct H2 as (?H, _).
      destruct (H1 a) as (b, ?H).
      destruct (H2 b) as (c, ?H).
      exists c.
      now apply H0 with (f0 b).
    - destruct H1 as (_, ?H).
      destruct H2 as (_, ?H).
      destruct (H2 b) as (a, ?H).
      destruct (H1 a) as (c, ?H).
      exists c.
      now apply H0 with (f0 a).
  Qed.

  Definition V_in (x: V) (y: V): Prop :=
    match y with
    | setof A f => exists a: T A, V_equiv x (f a)
    end.

  Definition V_setoid: SmallSetoid := {|
    setoid_carrier := V;
    setoid_equiv := V_equiv;
    setoid_refl := V_equiv_refl;
    setoid_sym := V_equiv_sym;
    setoid_trans := V_equiv_trans
  |}.

  Global Canonical Structure V_setoid.

  Global Instance V_in_proper:
    Proper (setoid_equiv ==> setoid_equiv ==> iff) V_in.
  Proof.
    split; intros.
    - destruct x0 as (A, f), y0 as (B, g); simpl in H2 |- *.
      destruct H2 as (a, ?H).
      destruct H1 as (?H, _).
      destruct (H1 a) as (b, ?H).
      exists b.
      rewrite <- H0, H2.
      assumption.
    - destruct x0 as (A, f), y0 as (B, g); simpl in H2 |- *.
      destruct H2 as (b, ?H).
      destruct H1 as (_, ?H).
      destruct (H1 b) as (a, ?H).
      exists a.
      rewrite H0, H3.
      assumption.
  Qed.

End IZF.
