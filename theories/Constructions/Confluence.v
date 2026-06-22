(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Equality.
Require Import Morphisms.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.

(* I can, of course, prove that this reduction relation is confluent. However,
   that will require a lot of code and a lot of time that I don't have at the
   moment. I might be tempted to come back here at some point and follow the
   procedure in the "Coq Coq Correct!" paper to actually prove this. *)

Conjecture step_is_confluent:
  forall g, confluent (step g).

Corollary step_is_church_rosser:
  forall g,
  church_rosser (step g).
Proof.
  intros.
  apply confluence_implies_church_rosser.
  apply step_is_confluent.
Qed.

Lemma conv_trans:
  forall g,
  transitive (conv g).
Proof.
  (* TODO: Bowman's paper says this is transitive, and, intuitively, I agree.
     I'm not really sure yet how to prove this, tho. I'll come back here later.

     More recent note: I hate my past self. *)
  admit.
Admitted.

Global Hint Resolve conv_trans: cps.

Global Instance conv_equivalence:
  forall g, Equivalence (conv g).
Proof.
  split.
  - apply conv_refl.
  - apply conv_sym.
  - apply conv_trans.
Qed.
