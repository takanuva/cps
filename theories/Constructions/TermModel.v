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

Definition terminal_subst (g: env): @substitution term :=
  iterate (length g) (fun s => subst_comp s (subst_lift 1)) subst_ids.

Lemma terminal_subst_simpl:
  forall g,
  subst_equiv (terminal_subst g) (subst_lift (length g)).
Proof.
  induction g; simpl.
  - unfold terminal_subst.
    now sigma.
  - unfold terminal_subst.
    simpl; rewrite IHg.
    now sigma.
Qed.

Lemma terminal_subst_is_unique:
  forall g s,
  valid_subst s g [] conv ->
  subst_equiv s (terminal_subst g).
Proof.
  intros.
  (* Simplify this definition to something equivalent, just so sigma may help us
     a bit more. *)
  rewrite terminal_subst_simpl.
  dependent induction H.
  - clear IHinfer; simpl.
    now sigma.
  - clear IHinfer; simpl.
    reflexivity.
  - rename g2 into d, f into s, g0 into t.
    (* Composition gets complicated as we have an arbitrary substitution t on
       the mix. We proceed with our inductive hypothesis, showing that s has to
       be a lift with the appropriate length. *)
    clear IHinfer2.
    specialize (IHinfer1 _ _ eq_refl eq_refl).
    (* We know that s is equivalent to the terminal substitution; an important
       property is that: composition with the terminal substitution on the left
       will always produce the terminal substitution again, as we show here. *)
    rewrite IHinfer1.
    clear H; clear IHinfer1 s.
    (* Now that we have simplified our goal, we perform another induction to
       show that, no matter which t : G -> D we have, it can't produce anything
       that won't be skipped by the lift by (length d) here. *)
    dependent induction H0.
    + clear IHinfer.
      now sigma.
    + clear IHinfer.
      now sigma.
    + (* Most complicated case: we need both inductive hypotheses to show that
         we'll accumulate the right amount of shifting! Luckly we can just
         rewrite these and sigma will do the work. *)
      specialize (IHinfer1 _ _ _ eq_refl).
      specialize (IHinfer2 _ _ _ eq_refl).
      rewrite <- IHinfer2.
      rewrite <- IHinfer1.
      now sigma.
    + (* Similar to the above. *)
      clear IHinfer2 IHinfer3.
      specialize (IHinfer1 _ _ _ eq_refl).
      rewrite <- IHinfer1; simpl.
      now sigma.
Qed.

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
    terminal_hom := terminal_subst
  |};
  cwf_ty := welltyped_type;
  cwf_tsub G D s t := inst (`s) (`t);
  cwf_el := welltyped_term;
  cwf_esub G D A s t := inst (`s) (`t);
  cwf_ext G A := decl_var (`A) :: (`G);
  cwf_snoc G D s t e := subst_cons (`e) (`s);
  cwf_proj G A := subst_lift 1;
  cwf_zero G A := bound 0
|}.

(* The empty context is well-typed. *)

Obligation 1 of TermModel.
  constructor.
Qed.

(* The terminal substitution is well-typed. *)

Obligation 2 of TermModel.
  destruct x as (g, ?H); simpl.
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
  now apply terminal_subst_is_unique.
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

(* Consing a well-typed term and a well-typed substitution is well-typed. *)

Obligation 7 of TermModel.
  destruct s as (s, ?H); simpl.
  destruct t as (t, (u, ?H)); simpl.
  destruct e as (e, ?H); simpl.
  simpl in H1.
  now apply valid_subst_cons with u.
Qed.

(* The shift substitution is well-typed. *)

Obligation 8 of TermModel.
  destruct A as (t, (u, ?H)); simpl.
  now apply valid_subst_lift with u.
Qed.

(* The variable zero is well-typed, given a well-typed environment. *)

Obligation 9 of TermModel.
  destruct A as (t, (u, ?H)); simpl.
  apply typing_var with t.
  - now apply valid_env_var with u.
  - constructor.
  - now sigma.
Qed.

Admit Obligations.
