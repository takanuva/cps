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
    | U_lft
    | U_ctor.

  Local Program Definition GET_CTOR (n: nat | n < length C) :=
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
      | U_lft =>
        sigma A (fun a: A =>
          iota (B a))
      | U_ctor =>
        sigma { n: nat | n < length C } (fun n =>
          delta unit (fun Ta: unit -> Setoid =>
            delta (Ta tt) (fun Tb: Ta tt -> Setoid =>
              iota (GET_CTOR n (Ta tt) Tb))))
      end).

End Family.
