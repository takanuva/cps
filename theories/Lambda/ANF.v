(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Export Local.Lambda.Calculus.
Require Export Local.Lambda.CallByValue.

(* From Sabry and Felleisen's "Reasoning About Programs in CPS"... this is the
   set of A-reductions, which extend Plotkin's CBV calculus. We expect a few
   things from here: (1) the simulation should extend to A, I hope, (2) there
   should be a Gallois connection between the CPS-calculus and the ANF calculus,
   so that we can reuse our operational semantics in there.

   Additionaly, we could prove the results from the above paper, as a treat. *)

Inductive A: relation term :=
  (* Eta-v: (\x.V x) -> V, given x not free in V. *)
  (* Beta-lift: E[((\x.M) N)] -> ((\x.E[M]) N), if x not free in E. *)
  (* Beta-flat: E[((M N) L)] -> ((\x.E[(x L)]) (M N)), if x not free in E, L. *)
  (* Beta-id: ((\x.x) M) -> M. *)
  (* Beta-omega: ((\x.E[(y x)]) M) -> E[(y M)], if x not free in E[y]. *)
  .
