(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.

Inductive lambda_type: Set :=
  | lambda_base
  | lambda_arrow (a: lambda_type) (b: lambda_type).

Inductive lambda_term: Set :=
  | lambda_bound (n: nat)
  | lambda_application (f: lambda_term) (x: lambda_term)
  | lambda_abstraction (t: lambda_type) (b: lambda_term).
