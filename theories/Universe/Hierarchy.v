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

Local Definition universe_fam (l: level): { X: Set & X -> Type } :=
  let fix fin i :=
    match i with
    | 0 =>
      existT nat finite
    | S k =>
      let A := projT1 (fin k) in
      let B := projT2 (fin k) in
      existT (CODE A B ctors) TYPE
    end
  in match l with
     | un i =>
       fin i
     | uw =>
       let A := { i: nat & projT1 (fin (1 + i)) } in
       let B (p: A) := TYPE (projT2 p) in
       existT A B
     end.

Definition universe (l: level): tarski := {|
  U := CODE (projT1 (universe_fam l)) (projT2 (universe_fam l)) ctors;
  T := TYPE
|}.

Global Arguments universe: simpl never.

Global Coercion universe: level >-> tarski.

Local Definition NAT' (l: level):
  { c: U l | T l c = nat }.
Proof.
  destruct l.
  - induction i; simpl.
    + exists IDX.
      apply TYPE_IDX.
    + destruct IHi as (c, ?H).
      exists (LIFT c).
      now rewrite TYPE_LIFT.
  - unshelve eexists.
    + change (U uw) with
        (CODE { i: nat & U i } (fun p => TYPE (projT2 p)) ctors).
      apply LIFT.
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
  { c: U l | T l c = finite n }.
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
      exists 0; simpl.
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

Local Definition PI' (l: level) (a: U l) (b: T l a -> U l):
  { c: U l | T l c = (forall x: T l a, T l (b x)) }.
Proof.
  unshelve eexists.
  - unshelve eapply CTOR.
    + exact a.
    + exists 0.
      eauto with arith.
    + exact b.
  - simpl.
    rewrite TYPE_CTOR.
    unfold GET_CTOR; simpl.
    reflexivity.
Defined.

Definition PI {l: level} (a: U l) (b: T l a -> U l): U l :=
  proj1_sig (PI' l a b).

Lemma T_PI:
  forall l a b,
  T _ (@PI l a b) = (forall x: T _ a, T _ (b x)).
Proof.
  intros; simpl.
  unfold PI.
  now destruct (PI' l a b).
Qed.

Global Arguments U: simpl never.
Global Arguments T {t}: simpl never.
