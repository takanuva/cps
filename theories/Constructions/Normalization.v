(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.

Import ListNotations.

(* We're dealing with a subset of Coq's theory inside of Coq. Although it might
   be possible that strong normalization for this is actually provable, at some
   point it would become hopeless because of the incompleteness theorem. Also, I
   do think that proving this (in a proof assistant) for a predicative hierarchy
   with an impredicative universe is still an open problem. So, we will merely
   conjecture that this system is strongly normalizing and go on, just like the
   people in the "Coq Coq Correct!" paper did. *)

Conjecture strong_normalization:
  forall g e t,
  typing g e t conv -> SN (step g) e.

(* For typeable terms, the normal form is computable. *)

Lemma normal_form_is_decidable:
  forall g e t,
  typing g e t conv ->
  exists2 f,
  rt(step g) e f & normal (step g) f.
Proof.
  intros.
  apply strong_normalization in H.
  induction H using SN_ind.
  destruct step_is_decidable with g x as [ (y, ?H) | ?H ].
  - destruct H2 with y as (z, ?, ?).
    + now apply t_step.
    + exists z; eauto with cps.
  - exists x.
    + apply rt_refl.
    + intros y ?.
      now apply H0 with y.
Qed.

Definition bottom: term :=
  pi iset (bound 0).

Lemma bottom_typeable:
  forall R,
  typing [] bottom iset R.
Proof.
  intros.
  repeat econstructor.
  - (* Use vm_compute to bypass opaque definitions. *)
    now vm_compute.
  - (* By definition, as set is impredicative. *)
    reflexivity.
Qed.

Corollary consistency:
  ~exists e, typing [] e bottom conv.
Proof.
  admit.
Admitted.
