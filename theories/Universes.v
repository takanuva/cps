(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Equality.
Require Import Local.Category.
Require Import Local.InductionRecursion.

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

  (* ... *)

End Family.
