(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.

(* I can, of course, prove that this reduction relation is confluent. However,
   that will require a lot of code and a lot of time that I don't have at the
   moment. I might be tempted to come back here at some point and follow the
   procedure in the "Coq Coq Correct!" paper to actually prove this. *)

Conjecture step_is_confluent:
  forall g, confluent (step g).
