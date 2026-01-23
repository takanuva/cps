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
   substitutions, types and elements (i.e., terms) are well-typed syntactic
   objects. To build this model, we will consider our canonical notion of
   equality.

   Let us be honest, I don't really care about proving that this model is indeed
   initial, so please bear with me. I'm very tired. :( *)

Definition welltyped_env: Set :=
  { g: env | valid_env g conv }.

Definition welltyped_subst (g: welltyped_env) (d: welltyped_env): Set :=
  { s: substitution | valid_subst s (`g) (`d) conv }.

Definition welltyped_type (g: welltyped_env): Type :=
  { t: term | exists s, typing (`g) t (sort s) conv }.

Definition welltyped_term (g: welltyped_env) (t: welltyped_type g): Type :=
  { e: term | typing (`g) e (`t) conv }.

(* Substitution equality amounts to extensional equality (i.e., instantiation
   on any possible term always produces the same result for both). Types and
   terms are treated modulo the convertibility relation (remember that both are
   always typed). *)

Definition welltyped_subst_eq {g d}: relation (welltyped_subst g d) :=
  fun s t => subst_equiv (`s) (`t).

Definition welltyped_type_eq {g}: relation (welltyped_type g) :=
  fun t u => conv (`g) (`t) (`u).

Definition welltyped_term_eq {g t}: relation (welltyped_term g t) :=
  fun e f => conv (`g) (`e) (`f).

(* We declare well-typed substitution as a setoid. *)

Program Definition WelltypedSubstSetoid g d: Setoid := {|
  carrier := @welltyped_subst g d;
  equiv := @welltyped_subst_eq g d
|}.

Obligation 1 of WelltypedSubstSetoid.
  (* This is indeed true, but unfortunately the sigma library gives us an
     incorrect notion of equality; gotta fix that. *)
  admit.
Admitted.

Global Canonical Structure WelltypedSubstSetoid.

(* Given that, well-typed environments and well-typed substitutions indeed form
   a category with the identity substitution and substitution composition. *)

Program Definition TermCategory: Category := {|
  obj := welltyped_env;
  hom := welltyped_subst;
  id X := subst_ids;
  post X Y Z f g := subst_comp g f
|}.

(* Identity substitution is well-typed. *)

Obligation 1 of TermCategory.
  destruct X as (g, ?H); simpl.
  now constructor.
Qed.

(* Composition of well-typed substitutions is well-typed. *)

Obligation 2 of TermCategory.
  destruct f as (s, ?H).
  destruct g as (t, ?H).
  simpl.
  now apply valid_subst_comp with (`Y).
Qed.

(* Composition is respectful of morphism equality. *)

Obligation 3 of TermCategory.
  repeat intro; simpl.
  (* Oh boy, no way this is correct... but this needs fixing in sigma! *)
  now apply subst_comp_proper.
Qed.

(* Identity is neutral on the right. *)

Obligation 4 of TermCategory.
  repeat intro; simpl.
  now sigma.
Qed.

(* Identity is neutral on the left. *)

Obligation 5 of TermCategory.
  repeat intro; simpl.
  now sigma.
Qed.

(* Identity is associative. *)

Obligation 6 of TermCategory.
  repeat intro; simpl.
  now sigma.
Qed.

Global Canonical Structure TermCategory.

(* We do have a terminal object in this category: the empty environment. Any
   morphism from G to [] is indeed unique, extensionally: it is necessarily the
   substitution (subst_lift (length G)). However, to get it typed with the plain
   sigma-calculus operators, we define it as the composition of shifting.

   TODO: move the iterate function? Maybe? *)

Local Fixpoint iterate (n: nat) {T: Type} (f: T -> T) (x: T): T :=
  match n with
  | 0 => x
  | S m => f (iterate m f x)
  end.

Definition terminal_sub (g: env): @substitution term :=
  iterate (length g) (fun s => subst_comp s (subst_lift 1)) subst_ids.

Lemma terminal_sub_simpl:
  forall g,
  subst_equiv (terminal_sub g) (subst_lift (length g)).
Proof.
  admit.
Admitted.

Lemma terminal_sub_is_unique:
  forall g s,
  valid_subst s g [] conv ->
  subst_equiv s (subst_lift (length g)).
Proof.
  (* TODO: we have to reason about how each well-typed substitution can map the
     variables to make composition work. Alternatively: show a normal form! *)
Admitted.

(* We declare well-typed types and well-typed terms as setoids, preparing to
   build our category with families. *)

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

(* Finally, we can build the term model as a category with families, picking
   the term category, well-typed types and well-typed terms. *)

Program Definition TermModel: CwF := {|
  cwf_cat := welltyped_env;
  cwf_empty := {|
    terminal := [];
    terminal_hom g := terminal_sub (`g)
  |};
  cwf_ty := welltyped_type;
  cwf_tsub G D s t := inst (`s) (`t);
  cwf_el := welltyped_term;
  cwf_esub G D A s t := inst (`s) (`t);
  cwf_ext G A := decl_var (`A) :: (`G)
|}.

(* The empty context is well-typed. *)

Obligation 1 of TermModel.
  constructor.
Qed.

(* The terminal substitution is well-typed. *)

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
      * (* Oops! We need to allow lifting to consider definitions! *)
        admit.
Admitted.

(* The terminal substitution is unique. *)

Obligation 3 of TermModel.
  destruct X as (g, ?H).
  destruct f as (s, ?H).
  compute in H0.
  repeat intro; simpl.
  rewrite terminal_sub_simpl; auto.
  now apply terminal_sub_is_unique.
Qed.

(* Instantiation of well-typed substitution and type is well-typed too. *)

Obligation 4 of TermModel.
  destruct s as (s, ?H); simpl.
  destruct t as (t, (u, ?H)); simpl.
  (* As sorts are stable under substitution... *)
  exists u; change (sort u) with (inst s (sort u)).
  now apply typing_inst with (`G).
Qed.

(* Instantiation of well-typed substitution and term is well-typed too. *)

Obligation 5 of TermModel.
  destruct s as (s, ?H); simpl.
  destruct t as (e, ?H); simpl.
  now apply typing_inst with (`G).
Qed.

(* Environment extension with well-typed type is well-typed. *)

Obligation 6 of TermModel.
  destruct A as (t, (s, ?H)); simpl.
  now apply valid_env_var with s.
Qed.

Admit Obligations.
