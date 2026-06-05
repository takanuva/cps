(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Local.Category.
Require Import Local.DSet.
Require Import Local.Universe.Construction.

Import ListNotations.
Set Primitive Projections.

Section Preliminaries.

  Inductive finite: nat -> Set :=
    | finite_O:
      forall n,
      finite (S n)
    | finite_S:
      forall n,
      finite n ->
      finite (S n).

  Polymorphic Definition pi (A: Type) (B: A -> Type): Type :=
    forall x: A, B x.

  Polymorphic Definition sigma (A: Type) (B: A -> Type): Type :=
    @sigT A B.

End Preliminaries.

Structure universe: Type := {
  U: Set;
  T: U -> Type
}.

Local Definition ctors :=
  [pi; sigma; dset].

Definition next_universe (u: universe): universe := {|
  U := CODE (U u) (@T u) ctors;
  T := @TYPE _ _ _
|}.

Fixpoint un (i: nat): universe :=
  match i with
  | 0 =>
    {|
      U := CODE nat finite ctors;
      T := @TYPE _ _ _
    |}
  | S j => 
    next_universe (un j)
  end.

Definition uw: universe := {|
  U := CODE { i: nat & U (un i) } (fun p => T _ (projT2 p)) ctors;
  T := @TYPE _ _ _
|}.
