(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Relations.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.Equational.
(* TODO: I've defined not_free_context in the wrong file so fix this, please? *)
Require Import Local.Reduction.
Require Import Local.Machine.
Require Import Local.Observational.

(*
  The contification transformation, as presented by Kennedy:

    C[D[f x1 j, ..., f xn j]] { f<x, k> = c }

                       ->s                      (CONTI)

    C[D[f x1, ..., f xn] { f<x> = c[j/k] }]

  In the above, D is a multi-hole context, it is minimal (or, alternatively, C
  is maximal in the left-hand side), and f is not free in C nor D.
*)

Definition CONTI (R: relation pseudoterm): Prop :=
  forall h n (ts us: list pseudoterm) (b1 b2 c: pseudoterm),
  not_free_context 0 h ->
  drop n ts us ->
  (* Of course this definition is still wrong. *)
  R void void.

Inductive cont: relation pseudoterm :=
  | cont_conti:
    CONTI cont
  | cont_bind_left:
    LEFT cont
  | cont_bind_right:
    RIGHT cont.

Lemma sema_cont:
  inclusion cont sema.
Proof.
  induction 1.
  - admit.
  - now apply sema_bind_left.
  - now apply sema_bind_right.
Admitted.

Lemma barb_cont:
  inclusion cont barb.
Proof.
  intros b c ?.
  apply barb_sema.
  apply sema_cont.
  assumption.
Qed.

Theorem contification_is_sound:
  forall b c,
  cont b c ->
  machine_equiv b c.
Proof.
  intros b c ?.
  apply machine_equiv_characterization.
  now apply barb_cont.
Qed.
