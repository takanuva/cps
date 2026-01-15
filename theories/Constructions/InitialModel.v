(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Local.Prelude.
Require Import Local.Category.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Inversion.

Import ListNotations.

(* We build here the initial model (also called the term model) for our type
   theory. It is a category with family such that contexts (i.e., environments),
   substitutions, types and elements are well-typed syntactic objects modulo the
   equational reasoning. To build this model, we will consider our canonical
   reduction relation.

   Let us be honest, I don't really care about proving that this model is indeed
   initial, so please bear with me. I'm very tired. :( *)

Definition welltyped_env: Set :=
  { g: env | valid_env g conv }.

(* TODO: we need to make a type system for substitutions! *)
