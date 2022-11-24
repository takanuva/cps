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

Lemma item_valid_index:
  forall {T} x xs k,
  @item T x xs k ->
  k < length xs.
Proof.
  induction 1; simpl; auto with arith.
Qed.

Lemma item_exists:
  forall {T} xs k,
  k < length xs ->
  exists x,
  @item T x xs k.
Proof.
  induction xs; intros.
  - inversion H.
  - destruct k.
    + exists a.
      constructor.
    + destruct IHxs with k.
      * simpl in H; lia.
      * exists x.
        constructor.
        assumption.
Qed.

Lemma item_repeat:
  forall {T} x y k p,
  @item T x (repeat y k) p ->
  x = y.
Proof.
  induction k; intros.
  - inversion H.
  - destruct p.
    + inversion H; auto.
    + inversion H; eauto.
Qed.

Lemma nth_item:
  forall {T} x xs y k,
  @item T x xs k -> nth k xs y = x.
Proof.
  induction 1; simpl.
  - reflexivity.
  - assumption.
Qed.

Lemma item_nth:
  forall {T} x xs y k,
  nth k xs y = x ->
  x <> y ->
  @item T x xs k.
Proof.
  induction xs; intros.
  - destruct k; simpl in H; congruence.
  - destruct k; simpl in H.
    + rewrite H.
      constructor.
    + constructor.
      apply IHxs with y; auto.
Qed.

Section SetoidFix.

  (* The code in this section is taken and adapted from coq-ext-lib. *)

  Variable A: Type.
  Variable R: A -> A -> Prop.
  Variable Rwf: well_founded R.
  Variable P: A -> Type.
  Variable F: forall x, (forall y, R y x -> P y) -> P x.
  Variable r: forall x, P x -> P x -> Prop.

  Hypothesis Hstep:
    forall x f g,
    (forall y p, r y (f y p) (g y p)) ->
    r x (@F x f) (@F x g).

  Lemma Fix_F_equiv_inv:
    forall x r' s',
    r x (Fix_F _ F r') (Fix_F _ F s').
  Proof.
    intros.
    induction (Rwf x).
    rewrite <- (Fix_F_eq _ F r').
    rewrite <- (Fix_F_eq _ F s').
    apply Hstep; auto.
  Qed.

  Theorem Fix_equiv:
    forall x,
    r x (Fix Rwf P F x) (@F x (fun y _ => Fix Rwf P F y)).
  Proof.
    intros.
    unfold Fix.
    rewrite <- Fix_F_eq.
    apply Hstep; intros.
    apply Fix_F_equiv_inv.
  Qed.

End SetoidFix.
