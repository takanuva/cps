(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Export List.
Require Import Arith.
Import ListNotations.

(** To help proof automation, create a hint database. *)

Create HintDb cps.

(** A lot of proofs on pseudoterm lists may be solved by simple induction on the
    [Forall P] proposition over them, so we'll add a tactic for that. *)

Tactic Notation "list" "induction" "over" hyp(H) :=
  induction H; simpl;
  [ reflexivity
  | f_equal; auto ].

(** A predicate indicating an object is the nth element of a list. *)

Inductive item {T} (e: T): list T -> nat -> Prop :=
  | item_car:
    forall cdr,
    item e (e :: cdr) 0
  | item_cdr:
    forall car cdr n,
    item e cdr n -> item e (car :: cdr) (S n).

Global Hint Constructors item: cps.

Lemma item_ignore_head:
  forall {T} xs x ys k,
  k >= length xs ->
  @item T x (xs ++ ys) k -> @item T x ys (k - length xs).
Proof.
  induction xs; intros.
  - simpl in H0 |- *.
    rewrite Nat.sub_0_r.
    assumption.
  - simpl in H, H0 |- *.
    destruct k.
    + exfalso.
      inversion H.
    + inversion_clear H0.
      apply IHxs; auto.
      lia.
Qed.

Lemma item_ignore_tail:
  forall {T} xs x ys k,
  length xs > k ->
  @item T x (xs ++ ys) k -> @item T x xs k.
Proof.
  induction xs; intros.
  - inversion H.
  - simpl in H, H0 |- *.
    destruct k.
    + inversion_clear H0; auto.
      constructor.
    + inversion_clear H0.
      constructor.
      eapply IHxs; eauto.
      lia.
Qed.

Lemma item_insert_head:
  forall {T} xs ys x k,
  @item T x ys k -> @item T x (xs ++ ys) (k + length xs).
Proof.
  induction xs; simpl; intros.
  - rewrite Nat.add_0_r.
    assumption.
  - replace (k + S (length xs)) with (S (k + length xs)); try lia.
    constructor; auto.
Qed.

Lemma item_insert_tail:
  forall {T} xs ys x k,
  @item T x xs k -> @item T x (xs ++ ys) k.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
Qed.
