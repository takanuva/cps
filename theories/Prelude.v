(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Export List.
Require Import Arith.
Require Import Equality.
Require Import Relations.
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

Lemma item_rev:
  forall {T} x xs k,
  @item T x xs k ->
  @item T x (rev xs) (length xs - S k).
Proof.
  induction xs; simpl; intros.
  - inversion H.
  - destruct k.
    * dependent destruction H.
      replace (length xs - 0) with (0 + length xs); try lia.
      rewrite <- rev_length.
      apply item_insert_head.
      constructor.
    * dependent destruction H.
      apply item_insert_tail.
      apply IHxs; auto.
Qed.

Lemma item_unique:
  forall {T} x y xs k,
  @item T x xs k ->
  @item T y xs k ->
  x = y.
Proof.
  induction 1; intros.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H0.
    auto.
Qed.

Lemma Forall2_length:
  forall {A} {B} R xs ys,
  @Forall2 A B R xs ys ->
  length xs = length ys.
Proof.
  induction 1; simpl; lia.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive insert {T}: T -> nat -> relation (list T) :=
  | insert_head:
    forall t xs,
    insert t 0 xs (t :: xs)
  | insert_tail:
    forall t n x xs1 xs2,
    insert t n xs1 xs2 ->
    insert t (S n) (x :: xs1) (x :: xs2).

Lemma insert_app:
  forall {T} i t n g h,
  @insert T t n g h ->
  @insert T t (length i + n) (i ++ g) (i ++ h).
Proof.
  induction i; simpl; intros.
  - assumption.
  - constructor.
    apply IHi; auto.
Qed.

Lemma item_insert_ge:
  forall {T} t m g h,
  @insert T t m g h ->
  forall n u,
  n >= m ->
  @item T u g n ->
  @item T u h (1 + n).
Proof.
  induction 1; intros.
  - constructor.
    assumption.
  - constructor.
    destruct n0; try lia.
    dependent destruction H1.
    apply IHinsert; auto with arith.
Qed.

Lemma item_insert_lt:
  forall {T} t m g h,
  @insert T t m g h ->
  forall n u,
  n < m ->
  @item T u g n ->
  @item T u h n.
Proof.
  induction 1; intros.
  - inversion H.
  - destruct n0.
    + dependent destruction H1.
      constructor.
    + rename n0 into m.
      dependent destruction H1.
      constructor.
      apply IHinsert; auto with arith.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive switch {T}: nat -> relation (list T) :=
  | switch_head:
    forall x1 x2 xs,
    switch 0 (x1 :: x2 :: xs) (x2 :: x1 :: xs)
  | switch_tail:
    forall n x xs1 xs2,
    switch n xs1 xs2 -> switch (S n) (x :: xs1) (x :: xs2).

Lemma switch_sym:
  forall {T} n g h,
  @switch T n g h -> @switch T n h g.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma switch_app:
  forall {T} n g h i,
  @switch T n h i ->
  @switch T (length g + n) (g ++ h) (g ++ i).
Proof.
  induction g; simpl; intros.
  - assumption.
  - constructor; auto.
Qed.

Lemma Forall_switch:
  forall T P g,
  @Forall T P g ->
  forall n h,
  @switch T n g h ->
  @Forall T P h.
Proof.
  induction 2; simpl.
  - dependent destruction H.
    dependent destruction H0.
    constructor; auto.
  - dependent destruction H.
    constructor; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive join {T}: nat -> relation (list T) :=
  | join_head:
    forall x xs,
    join 0 (x :: x :: xs) (x :: xs)
  | join_tail:
    forall n x xs1 xs2,
    join n xs1 xs2 ->
    join (S n) (x :: xs1) (x :: xs2).

Goal
  forall T n xs1 xs2,
  @join T n xs1 xs2 ->
  exists t,
  @insert T t n xs2 xs1.
Proof.
  induction 1.
  - exists x.
    constructor.
  - destruct IHjoin as (t, ?).
    exists t.
    constructor.
    assumption.
Qed.

Lemma join_app:
  forall {T} n g h i,
  @join T n h i ->
  @join T (length g + n) (g ++ h) (g ++ i).
Proof.
  induction g; simpl; intros.
  - assumption.
  - constructor; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive drop {T}: nat -> relation (list T) :=
  | drop_head:
    forall x xs,
    drop 0 (x :: xs) xs
  | drop_tail:
    forall n x xs1 xs2,
    drop n xs1 xs2 ->
    drop (S n) (x :: xs1) (x :: xs2).

Lemma drop_app:
  forall {T} n g h i,
  @drop T n h i ->
  @drop T (length g + n) (g ++ h) (g ++ i).
Proof.
  induction g; simpl; intros.
  - assumption.
  - constructor; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Section SetoidFix.

  (* The code in this section is taken from coq-ext-lib and slightly adapted;
     the original is on GitHub: https://github.com/coq-community/coq-ext-lib. *)

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
