(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Program.
Require Import Equality.
Require Import Morphisms.
Require Import Local.Setoid.
Require Import Local.Universe.

(* I would like to set those types at level 2 and 1, respectively, but... *)

Inductive V: Type :=
  | setof (A: Set) (B: A -> V): V.

Definition idx (x: V): Set :=
  match x with
  | setof A f => A
  end.

Definition elts (x: V): idx x -> V :=
  match x return idx x -> V with
  | setof A f => f
  end.

Fixpoint V_equiv (x: V) (y: V): Prop :=
  match x, y with
  | setof A f, setof B g =>
    (forall a: A, exists b: B, V_equiv (f a) (g b)) /\
      (forall b: B, exists a: A, V_equiv (f a) (g b))
  end.

Lemma V_equiv_refl:
  forall x,
  V_equiv x x.
Proof.
  induction x as [A f]; split; intros.
  - now exists a.
  - now exists b.
Qed.

Lemma V_equiv_sym:
  forall x y,
  V_equiv x y -> V_equiv y x.
Proof.
  induction x as [A f]; destruct y as (B, g); split; intros.
  - destruct H0 as (_, ?H).
    destruct (H0 a) as (b, ?H).
    exists b.
    now apply H.
  - destruct H0 as (?H, _).
    destruct (H0 b) as (a, ?H).
    exists a.
    now apply H.
Qed.

Lemma V_equiv_trans:
  forall x y z,
  V_equiv x y -> V_equiv y z -> V_equiv x z.
Proof.
  induction x as [A f]; destruct y as (B, g), z as (C, h); split; intros.
  - destruct H0 as (?H, _).
    destruct H1 as (?H, _).
    destruct (H0 a) as (b, ?H).
    destruct (H1 b) as (c, ?H).
    exists c.
    now apply H with (g b).
  - destruct H0 as (_, ?H).
    destruct H1 as (_, ?H).
    destruct (H1 b) as (a, ?H).
    destruct (H0 a) as (c, ?H).
    exists c.
    now apply H with (g a).
Qed.

Definition V_in (x: V) (y: V): Prop :=
  match y with
  | setof A f => exists a: A, V_equiv x (f a)
  end.

Definition V_setoid: Setoid := {|
  setoid_carrier := V;
  setoid_equiv := V_equiv;
  setoid_refl := V_equiv_refl;
  setoid_sym := V_equiv_sym;
  setoid_trans := V_equiv_trans
|}.

Global Canonical Structure V_setoid.

Global Instance V_in_is_proper:
  Proper (setoid_equiv ==> setoid_equiv ==> iff) V_in.
Proof.
  split; intros.
  - destruct x0 as (A, f), y0 as (B, g); simpl in H1 |- *.
    destruct H1 as (a, ?H).
    destruct H0 as (?H, _).
    destruct (H0 a) as (b, ?H).
    exists b.
    rewrite <- H, H1.
    assumption.
  - destruct x0 as (A, f), y0 as (B, g); simpl in H1 |- *.
    destruct H1 as (b, ?H).
    destruct H0 as (_, ?H).
    destruct (H0 b) as (a, ?H).
    exists a.
    rewrite H, H2.
    assumption.
Qed.

Theorem V_extensionality_ax:
  forall x y,
  (forall z, V_in z x <-> V_in z y) ->
  x == y.
Proof.
  intros.
  destruct x as (A, f), y as (B, g); split; intros.
  - simpl in H.
    destruct (H (f a)) as (?H, _).
    apply H0.
    now exists a.
  - simpl in H.
    destruct (H (g b)) as (_, ?H).
    destruct H0 as (a, ?H).
    + now exists b.
    + now exists a.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive logic: Type :=
  | EQUIV (x: V) (y: V)
  | IN (x: V) (y: V)
  | FALSE
  | IMPL (p: logic) (q: logic)
  | CONJ (p: logic) (q: logic)
  | DISJ (p: logic) (q: logic)
  | FORALL (p: V -> logic)
  | EXISTS (p: V -> logic).

Fixpoint interpret (formula: logic): Prop :=
  match formula with
  | EQUIV x y =>
    V_equiv x y
  | IN x y =>
    V_in x y
  | FALSE =>
    False
  | IMPL p q =>
    interpret p -> interpret q
  | CONJ p q =>
    interpret p /\ interpret q
  | DISJ p q =>
    interpret p \/ interpret q
  | FORALL p =>
    forall x: V, interpret (p x)
  | EXISTS p =>
    exists x: V, interpret (p x)
  end.

Definition V_class (x: V): Type :=
  { p: V -> logic | interpret (p x) }.

(* -------------------------------------------------------------------------- *)

Section CZF.

End CZF.

(* -------------------------------------------------------------------------- *)

Definition sV (u: universe): Set :=
  w (U u) T.

Fixpoint emb {u: universe} (x: sV u): V :=
  match x with
  | sup _ _ a f => setof (T a) (fun y: T a => emb (f y))
  end.

Definition uV (u: universe): V :=
  setof (sV u) emb.
