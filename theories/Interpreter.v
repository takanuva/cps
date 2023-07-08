(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Program.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.
Require Import Local.Machine.

(* Since Kennedy's machine semantics is sound and complete, we should write a
   version of Appel's interpreter, which is the denotational semantics of his IR
   into ML, by using the partiality monad and prove it correct with regard to
   the machine semantics as well. This would allow us to extract an executable
   interpreter for the CPS-calculus which is verified to be correct. *)
