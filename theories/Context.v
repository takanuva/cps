(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Export Setoid.
Require Export Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.

Definition LEFT (R: relation pseudoterm): Prop :=
  forall b1 b2 ts c,
  R b1 b2 -> R (bind b1 ts c) (bind b2 ts c).

Global Hint Unfold LEFT: cps.

Definition RIGHT (R: relation pseudoterm): Prop :=
  forall b ts c1 c2,
  R c1 c2 -> R (bind b ts c1) (bind b ts c2).

Global Hint Unfold RIGHT: cps.

Class Congruence (R: relation pseudoterm) := {
  (* A congruence is an equivalence relation. *)
  Congruence_Equivalence :> Equivalence R;
  (* It also is preserved by any contexts. *)
  Congruence_Left: LEFT R;
  Congruence_Right: RIGHT R
}.
