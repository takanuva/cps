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

(* We build here the term model (which is also the initial model) for our type
   theory. It is a category with family such that contexts (i.e., environments),
   substitutions, types and elements are well-typed syntactic objects modulo the
   equational reasoning. To build this model, we will consider our canonical
   equality relation.

   Let us be honest, I don't really care about proving that this model is indeed
   initial, so please bear with me. I'm very tired. :( *)

Definition welltyped_env: Set :=
  { g: env | valid_env g conv }.

Definition welltyped_sub (d: welltyped_env) (g: welltyped_env): Set :=
  { s: substitution | valid_subst s (`d) (`g) conv }.

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

Definition welltyped_type_eq {g}: relation (welltyped_type g) :=
  fun t u => conv (`g) (`t) (`u).

Program Definition WelltypedTypeSetoid g: Setoid := {|
  carrier := welltyped_type g;
  equiv := welltyped_type_eq
|}.

Obligation 1 of WelltypedTypeSetoid.
  split; repeat intro.
  - apply conv_refl.
  - now apply conv_sym.
  - now apply (conv_trans (`g) (`x) (`y) (`z)).
Qed.

Global Canonical Structure WelltypedTypeSetoid.

Definition welltyped_term (g: welltyped_env) (t: welltyped_type g): Type :=
  { e: term | typing (`g) e (`t) conv }.

Definition welltyped_term_eq {g t}: relation (welltyped_term g t) :=
  fun e f => conv (`g) (`e) (`f).

Program Definition WelltypedTermSetoid g t: Setoid := {|
  carrier := welltyped_term g t;
  equiv := welltyped_term_eq
|}.

Obligation 1 of WelltypedTermSetoid.
  split; repeat intro.
  - apply conv_refl.
  - now apply conv_sym.
  - now apply (conv_trans (`g) (`x) (`y) (`z)).
Qed.

Global Canonical Structure WelltypedTermSetoid.

(* TODO: move me? Maybe? *)

Local Fixpoint iterate (n: nat) {T: Type} (f: T -> T) (x: T): T :=
  match n with
  | 0 => x
  | S m => f (iterate m f x)
  end.

Definition terminal_substitution (g: env): @substitution term :=
  iterate (length g) (fun s => subst_comp s (subst_lift 1)) subst_ids.

Program Definition TermModel: CwF := {|
  cwf_cat := welltyped_env;
  cwf_empty := {|
    terminal := [];
    terminal_hom g := terminal_substitution (`g)
  |};
  cwf_ty := welltyped_type;
  cwf_el := welltyped_term
|}.

Obligation 1 of TermModel.
  constructor.
Qed.

Obligation 2 of TermModel.
  destruct g as (g, ?H); simpl.
  induction g; simpl.
  - do 2 constructor.
  - apply valid_subst_comp with g.
    + apply IHg; clear IHg.
      dependent destruction H.
      * now apply valid_env_typing with t s.
      * now apply valid_env_typing with t s.
    + clear IHg.
      dependent destruction H.
      * now apply valid_subst_lift with s.
      * (* Oops! We need to allow lifting to consider definitions. *)
        admit.
Admitted.

Admit Obligations.
