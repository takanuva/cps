(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Category.
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

Definition welltyped_sub (d: welltyped_env) (g: welltyped_env): Set :=
  { s: @substitution term | valid_subst s (`d) (`g) conv }.

Definition welltyped_sub_eq {d g}: relation (welltyped_sub d g) :=
  fun s t => subst_equiv (`s) (`t).

Program Definition WelltypedSubstSetoid d g: Setoid := {|
  carrier := @welltyped_sub d g;
  equiv := @welltyped_sub_eq d g
|}.

(* TODO: This is DEFINITELY wrong! *)
Obligation 1 of WelltypedSubstSetoid.
  split; repeat intro; simpl.
  - reflexivity.
  - symmetry.
    now apply H.
  - transitivity ((`y) k x0).
    + now apply H.
    + now apply H0.
Qed.

Global Canonical Structure WelltypedSubstSetoid.

Program Definition TermCategory: Category := {|
  obj := welltyped_env;
  hom := welltyped_sub;
  id X := subst_ids;
  post X Y Z f g := subst_comp g f
|}.

Obligation 1 of TermCategory.
  destruct X as (g, ?H); simpl.
  now constructor.
Qed.

Obligation 2 of TermCategory.
  destruct f as (s, ?H).
  destruct g as (t, ?H).
  simpl.
  apply valid_subst_comp with (`Y).
  - assumption.
  - assumption.
Qed.

Obligation 3 of TermCategory.
  repeat intro; simpl.
  (* Oh boy, no way this is correct... *)
  now apply subst_comp_proper.
Qed.

Obligation 4 of TermCategory.
  repeat intro; simpl.
  now sigma.
Qed.

Obligation 5 of TermCategory.
  repeat intro; simpl.
  now sigma.
Qed.

Obligation 6 of TermCategory.
  repeat intro; simpl.
  now sigma.
Qed.

Global Canonical Structure TermCategory.

Definition welltyped_type (g: welltyped_env): Type :=
  { t: term | exists s, typing (`g) t (sort s) conv }.

Definition welltyped_term (g: welltyped_env) (t: welltyped_type g): Type :=
  { e: term | typing (`g) e (`t) conv }.
