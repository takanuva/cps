(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Confluence.
Require Import Local.Conservation.

Inductive struct: relation pseudoterm :=
  | struct_float_left:
    FLOAT_LEFT struct
  | struct_float_right:
    FLOAT_RIGHT struct
  | struct_bind_left:
    LEFT struct
  | struct_bind_right:
    RIGHT struct.
