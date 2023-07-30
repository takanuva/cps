(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.

(** ** Type system *)

Definition env: Set :=
  list pseudoterm.

Inductive simple: pseudoterm -> Prop :=
  | simple_base:
    simple base
  | simple_negation:
    forall ts,
    Forall simple ts -> simple (negation ts).

Definition valid_env (g: env): Prop :=
  Forall simple g.

(* We are free to take a simpler definition here since we're only dealing with
   simple types. Reasoning about dependent types will require extra care! *)

Inductive typing: env -> relation pseudoterm :=
  | typing_bound:
    forall g n t,
    valid_env g ->
    item t g n ->
    typing g n t
  | typing_jump:
    forall g k xs ts,
    typing g k (negation ts) ->
    Forall2 (typing g) (rev xs) ts ->
    typing g (jump k xs) void
  | typing_bind:
    forall g b ts c,
    typing (ts ++ g) c void ->
    typing (negation ts :: g) b void ->
    typing g (bind b ts c) void.

Global Hint Constructors typing: cps.

Lemma typing_bound_is_simple:
  forall g n t,
  typing g (bound n) t ->
  simple t.
Proof.
  intros.
  dependent destruction H.
  replace t with (nth n g void).
  - apply Forall_nth.
    + assumption.
    + apply item_valid_index with t.
      assumption.
  - apply nth_item.
    assumption.
Qed.

Lemma typing_bound_cant_be_void:
  forall g n,
  ~typing g (bound n) void.
Proof.
  intros g n ?.
  apply typing_bound_is_simple in H.
  inversion H.
Qed.
