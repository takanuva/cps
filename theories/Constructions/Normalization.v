(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Local.Prelude.
Require Import Local.Category.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Inversion.

Import ListNotations.

(* -------------------------------------------------------------------------- *)

(* Quick and dirty trial to actually prove strong normalization by using the
   proof given by Zongpu Xie in their master's thesis, along with Coquand's
   paper on the matter. Just cause it's fun! *)

Section Normalization.

  Variable M: CwF.

  Local Notation CTX := (obj (cwf_cat M)).
  Local Notation SUBST := (hom (cwf_cat M)).
  Local Notation TYPE := (cwf_type M).

  Local Notation NIL := (cwf_empty M).
  Local Notation SNOC := (cwf_ctxext M).

  (* Following both Coquand and Xie, a telescope is defined inductively as:
     - () is telescope;
     - if X is a telescope and A is a TYPE <X>, then (X.A) is a telescope;

     Along with a recursive interpretation function <->, where:
     - <()> is NIL;
     - <X.A> is SNOC <X> A.

     As noted by Coquand, we may have <X> == <Y> without X = Y. These will be
     the objects of the category. Our morphisms are syntactic objects which
     represeting  weakening, namely as:
     - () is a morphism from () to ();
     - if f is a morphism from X to Y, weak f is a morphism from X.A to Y;
     - if f is a morphism from X to Y, plus f is a morphism from X.(subst <f> A)
       to Y.A;

     Again along an interpretation <f: X -> Y>: <X> -> <Y> from weakenings into
     substitutions such that:
     - <()> is ();
     - <weak f> is weak <f>;
     - <plus f> is plus <f>.

     Both object and morphisms capture, syntactically, how a context and a
     substitution were built. Both are also inductive-recursive, which is quite
     annoying as this is not supported by Coq's type theory. We thus build the
     telescope and its interpretation together. *)

  Inductive telescope: CTX -> Type :=
    | telescope_nil:
      telescope NIL
    | telescope_snoc:
      forall (G: CTX) (X: telescope G) (T: TYPE G),
      telescope (SNOC G T).

End Normalization.

(* -------------------------------------------------------------------------- *)

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

(* For this one, we'll follow the proof given by Coquand and Gallier in "A Proof
   Of Strong Normalization For The Theory Of Constructions Using A Kripe-Like
   Interpretation", as their Lemma 5.19. *)

Corollary consistency:
  ~exists e, typing [] e bottom conv.
Proof.
  (* Assume there's an e that is typeable as bottom. *)
  intros (e, ?).
  (* So there's a term in normal form that also is. *)
  assert (exists2 f, typing [] f bottom conv & normal (step []) f) as (f, ?, ?).
  - (* We calculate it from strong normalization and subject reduction. *)
    destruct normal_form_is_decidable with ([]: env) e bottom as (f, ?, ?).
    + assumption.
    + exists f; auto.
      now apply subject_reduction with e.
  - (* So, forget the non-normal one. *)
    clear e H; rename f into e.
    admit.
Admitted.
