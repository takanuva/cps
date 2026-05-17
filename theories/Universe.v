(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Program.
Require Import Equality.
Require Import Local.Category.
Require Import Local.InductionRecursion.

Import ListNotations.
Set Universe Polymorphism.
Set Primitive Projections.

(* This file will have a version of my technique for encoding Tarski universes
   in Coq, as shown in https://github.com/takanuva/tarski-rocq, but this time
   using setoids to avoid the need for functional extensionality. Of course I
   would prefer to avoid uniqueness of identity proofs as well, but most of my
   codebase in this repository uses it already... so why bother? Sorry.

   We also construct an enhanced version; instead of abstracting the universes
   over some family of types, we also abstract them over types constructors, so
   that we may also build Palmgren's notion of a superuniverse and we may have
   codes for D-sets within the universes (for the proof of strong normalization
   for the dependent type theory). *)

Section Family.

  Variable A: SmallSetoid.
  Variable B: A -> Setoid.
  Variable C: list (forall (X: Setoid), (X -> Setoid) -> Setoid).

  Variant branch: Set :=
    | U_idx
    | U_lift
    | U_ctor.

  Local Notation ctor_index :=
    ({ n: nat | n < length C }).

  Local Program Definition GET_CTOR (n: ctor_index) :=
    match nth_error C n with
    | Some ctor => ctor
    | None => False_rect _ _
    end.

  Next Obligation.
    eapply nth_error_Some.
    - eassumption.
    - auto.
  Qed.

  Definition TARSKI: @Sig Setoid :=
    sigma branch (fun b: branch =>
      match b with
      | U_idx =>
        iota (A: Setoid)
      | U_lift =>
        sigma A (fun a: A =>
          iota (B a))
      | U_ctor =>
        sigma ctor_index (fun n =>
          delta unit (fun Ta: unit -> Setoid =>
            delta (Ta tt) (fun Tb: Ta tt -> Setoid =>
              iota (GET_CTOR n (Ta tt) Tb))))
      end).

  Arguments projT1 {A} {P}.
  Arguments projT2 {A} {P}.
  Arguments exist {A} {P}.
  Arguments existT {A} {P}.

  Local Definition IND: Type :=
    E TARSKI (total (muE TARSKI)) projT1.

  Local Definition REC: IND -> Setoid :=
    F TARSKI (total (muE TARSKI)) projT1.

  Local Definition embed (x: IND): total (muE TARSKI) :=
    existT (REC x) (inE TARSKI (exist x eq_refl)).

  Definition IDX': IND :=
    existT U_idx tt.

  Definition LIFT' (a: A): IND :=
    existT U_lift
      (existT a tt).

  Definition CTOR' (n: ctor_index) (a: IND) (b: REC a -> IND): IND :=
    existT U_ctor
      (existT n
        (existT (fun _ => embed a)
          (existT (fun x => embed (b x))
            tt))).

  Inductive canonical: IND -> Type :=
    | canonical_idx:
      canonical IDX'
    | canonical_lift:
      forall a: A,
      canonical (LIFT' a)
    | canonical_ctor:
      forall n: ctor_index,
      forall a: IND,
      forall b: REC a -> IND,
      forall ok_a: canonical a,
      forall ok_b: (forall x, canonical (b x)),
      canonical (CTOR' n a b).

  Unset Elimination Schemes.

  Inductive CODE: Set :=
    | shrink (x: IND) (ok: canonical x).

  Set Elimination Schemes.

  Definition get_branch (c: CODE): branch :=
    let (x, ok) := c in projT1 x.

  Definition left_child:
    forall c: CODE,
    U_ctor = get_branch c ->
    CODE.
  Proof.
    intros.
    destruct c.
    destruct ok.
    - exfalso.
      simpl in H.
      inversion H.
    - exfalso.
      simpl in H.
      inversion H.
    - exact (shrink a ok).
  Defined.

End Family.
