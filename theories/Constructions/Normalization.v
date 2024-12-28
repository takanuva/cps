(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.

(* We're dealing with a subset of Coq's theory inside of Coq. Although it might
   be possible that strong normalization for this is actually provable, at some
   point it would become hopeless because of the incompleteness theorem. So, we
   will merely conjecture that this system is strongly normalizing and go on,
   just like the people in the "Coq Coq Correct!" paper did. *)

Conjecture strong_normalization:
  forall g e t,
  typing g e t typed_conv -> SN (step g) e.
