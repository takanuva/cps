(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.
(* TODO: I've defined not_free_context in the wrong file so fix this, please? *)
Require Import Local.Reduction.

(*
  The contification transformation, as presented by Kennedy:

    C[D[f x1 j, ..., f xn j]] { f<x, k> = c }

                       ->s                      (CONTI)

    C[D[f x1, ..., f xn] { f<x> = c[j/k] }]

  In the above, D is a multi-hole context, it is minimal (or, alternatively, C
  is maximal in the left-hand side), and f is not free in C nor D.
*)

Definition CONTI (R: relation pseudoterm): Prop :=
  forall h n (ts us: list pseudoterm) (b c: pseudoterm),
  not_free_context 0 h ->
  drop n ts us ->
  False.
