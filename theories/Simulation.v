(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
(* TODO: remove this one. *)
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Observational.
Require Local.Lambda.CallByName.
Require Local.Lambda.CallByValue.

(* I should probably move the CPS translations and simulation results here. For
   now, they reside in the [CallByName.v] and [CallByValue.v] files. TODO: do
   this or delete this file. *)
