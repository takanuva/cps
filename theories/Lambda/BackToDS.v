(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Lambda.Calculus.
Require Import Local.Lambda.PlotkinCBN.
Require Import Local.Lambda.PlotkinCBV.
Require Local.Syntax.
Require Local.Intuitionistic.

Import ListNotations.

Module CPS.
  Include Local.Syntax.
  Include Local.Intuitionistic.
End CPS.

Notation polarity := CPS.polarity.
Notation consume := CPS.consume.
Notation lift_var := CPS.lift_var.

