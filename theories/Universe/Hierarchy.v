(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Local.Universe.Construction.

Import ListNotations.
Set Primitive Projections.

Section Preliminaries.

  Local Set Universe Polymorphism.

  Definition finite (n: nat): Set :=
    { m: nat | m < n }.

  Definition pi (A: Type) (B: A -> Type): Type :=
    forall x: A, B x.

  Definition sigma (A: Type) (B: A -> Type): Type :=
    @sigT A B.

  Cumulative Inductive w (A: Type) (B: A -> Type): Type :=
    | sup (a: A) (f: B a -> w A B): w A B.

  Cumulative CoInductive m (A: Type) (B: A -> Type): Type := inf {
    seed: A;
    step: B seed -> m A B
  }.

End Preliminaries.

Structure universe: Type := {
  U: Set;
  T: U -> Set;
  NAT: U;
  T_NAT: T NAT = nat;
  FIN: nat -> U;
  T_FIN: forall n, T (FIN n) = finite n;
  PI: forall a: U, (T a -> U) -> U;
  T_PI: forall a b, T (PI a b) = (forall x: T a, T (b x));
  SIGMA: forall a: U, (T a -> U) -> U;
  T_SIGMA: forall a b, T (SIGMA a b) = { x: T a & T (b x) };
  W: forall a: U, (T a -> U) -> U;
  T_W: forall a b, T (W a b) = w (T a) (fun x => T (b x));
  M: forall a: U, (T a -> U) -> U;
  T_M: forall a b, T (M a b) = m (T a) (fun x => T (b x))
}.

Arguments T {u}.
Arguments T_FIN {u}.
Arguments T_PI {u}.
Arguments T_SIGMA {u}.
Arguments T_W {u}.
Arguments T_M {u}.

Local Notation ctors :=
  [pi; sigma; w; m].

Program Definition u0: universe := {|
  U := CODE nat finite ctors;
  T := TYPE;
  NAT := IDX;
  FIN := LIFT;
  PI := CTOR 0;
  SIGMA := CTOR 1;
  W := CTOR 2;
  M := CTOR 3
|}.

Next Obligation of u0.
  apply TYPE_IDX.
Qed.

Next Obligation of u0.
  apply TYPE_LIFT.
Qed.

Next Obligation of u0.
  apply TYPE_CTOR.
Qed.

Next Obligation of u0.
  apply TYPE_CTOR.
Qed.

Next Obligation of u0.
  apply TYPE_CTOR.
Qed.

Next Obligation of u0.
  apply TYPE_CTOR.
Qed.

Program Definition next_universe (u: universe): universe := {|
  U := CODE (U u) (@T u) ctors;
  T := TYPE;
  NAT := LIFT (NAT u);
  FIN n := LIFT (FIN u n);
  PI := CTOR 0;
  SIGMA := CTOR 1;
  W := CTOR 2;
  M := CTOR 3
|}.

Next Obligation of next_universe.
  rewrite TYPE_LIFT.
  apply T_NAT.
Qed.

Next Obligation of next_universe.
  rewrite TYPE_LIFT.
  apply T_FIN.
Qed.

Next Obligation of next_universe.
  apply TYPE_CTOR.
Qed.

Next Obligation of next_universe.
  apply TYPE_CTOR.
Qed.

Next Obligation of next_universe.
  apply TYPE_CTOR.
Qed.

Next Obligation of next_universe.
  apply TYPE_CTOR.
Qed.

Fixpoint un (i: nat): universe :=
  match i with
  | 0 => u0
  | S j => next_universe (un j)
  end.

Program Definition uw: universe := {|
  U := CODE { i: nat & U (un i) } (fun p => T (projT2 p)) ctors;
  T := TYPE;
  NAT := LIFT (existT 0 (NAT u0));
  FIN n := LIFT (existT 0 (FIN u0 n));
  PI := CTOR 0;
  SIGMA := CTOR 1;
  W := CTOR 2;
  M := CTOR 3
|}.

Next Obligation of uw.
  rewrite TYPE_LIFT; simpl.
  apply TYPE_IDX.
Qed.

Next Obligation of uw.
  rewrite TYPE_LIFT; simpl.
  apply TYPE_LIFT.
Qed.

Next Obligation of uw.
  apply TYPE_CTOR.
Qed.

Next Obligation of uw.
  apply TYPE_CTOR.
Qed.

Next Obligation of uw.
  apply TYPE_CTOR.
Qed.

Next Obligation of uw.
  apply TYPE_CTOR.
Qed.
