(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Setoid.
Require Import Local.Category.
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

  Definition V_in (x: V) (y: V): Prop :=
    match y with
    | setof A f => exists a: T A, V_equiv x (f a)
    end.

End IZF.
