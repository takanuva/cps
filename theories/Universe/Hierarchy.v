(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
(* Require Import Local.Category. *)
Require Import Local.DSet.
Require Import Local.Universe.Construction.

Import ListNotations.
Set Primitive Projections.

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

Structure tarski: Type := {
  U: Set;
  T: U -> Type
}.

Local Definition ctors :=
  [pi; sigma; dset].

Definition small_universe: tarski := {|
  U := CODE nat finite ctors;
  T := @TYPE _ _ _
|}.

Definition next_universe (u: tarski): tarski := {|
  U := CODE (U u) (@T u) ctors;
  T := @TYPE _ _ _
|}.

Variant level: Set :=
  | un (i: nat)
  | uw.

Global Coercion un: nat >-> level.

Fixpoint universe_finite (i: nat): tarski :=
  match i with
  | 0 =>
    small_universe
  | S j => 
    next_universe (universe_finite j)
  end.

Definition universe_transfinite: tarski := {|
  U := CODE { i: nat & U (universe_finite i) } (fun p => T _ (projT2 p)) ctors;
  T := @TYPE _ _ _
|}.

Definition universe (l: level): tarski :=
  match l with
  | un i => universe_finite i
  | uw => universe_transfinite
  end.

Global Coercion universe: level >-> tarski.

Local Definition NAT' (l: level):
  { c: U l | T _ c = nat }.
Proof.
  destruct l.
  - induction i; simpl.
    + exists IDX.
      apply TYPE_IDX.
    + destruct IHi as (c, ?H).
      exists (LIFT c).
      now rewrite TYPE_LIFT.
  - unshelve eexists.
    + apply LIFT.
      exists 0.
      exact IDX.
    + simpl.
      rewrite TYPE_LIFT; simpl.
      apply TYPE_IDX.
Defined.

Definition NAT {l: level}: U l :=
  proj1_sig (NAT' l).

Lemma T_NAT:
  forall l,
  T _ (@NAT l) = nat.
Proof.
  intros; simpl.
  unfold NAT.
  now destruct (NAT' l).
Qed.

Local Definition FINITE' (l: level) (n: nat):
  { c: U l | T _ c = finite n }.
Proof.
  destruct l.
  - induction i; simpl.
    + exists (LIFT n).
      apply TYPE_LIFT.
    + destruct IHi as (c, ?H).
      exists (LIFT c).
      now rewrite TYPE_LIFT.
  - unshelve eexists.
    + apply LIFT.
      exists 0.
      exact (LIFT n).
    + simpl.
      rewrite TYPE_LIFT; simpl.
      now rewrite TYPE_LIFT.
Defined.

Definition FINITE {l: level} (n: nat): U l :=
  proj1_sig (FINITE' l n).

Lemma T_FINITE:
  forall l n,
  T _ (@FINITE l n) = finite n.
Proof.
  intros; simpl.
  unfold FINITE.
  now destruct (FINITE' l n).
Qed.

Global Arguments U: simpl never.
Global Arguments T {t}: simpl never.
