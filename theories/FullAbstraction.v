(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Simulation.

(* It is most probably not possible to achieve full abstraction as terms in the
   CPS-calculus are allowed to discard and duplicate continuations; a simple
   example using call/cc might be enough (there's something similar in one of
   Ahmed's papers). We might try to prove that 1) it's really not possible, and
   2) that it is indeed possible if we restrict ourselves to the subset of terms
   that are free of control effects (which is actually a subcategory, as it is
   described by Thielecke). This restriction may be done syntactically. *)
