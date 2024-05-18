(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Pi.Calculus.

Set Primitive Projections.

Notation nodes := (list (option type)).

Record env: Type := env_mk {
  env_nodes:
    nodes;
  env_edges:
    relation nat
}.

Global Coercion env_nodes: env >-> list.

Definition env_empty: env := {|
  env_nodes := [];
  env_edges x y := False
|}.

Record env_wellformed (g: env): Prop := {
  env_wellformed_domain:
    forall i j,
    env_edges g i j ->
    exists ts,
    nth i g None = Some (channel I ts);
  env_wellformed_codomain:
    forall i j,
    env_edges g i j ->
    exists ts,
    nth j g None = Some (channel O ts)
}.

Inductive type_composition: type -> type -> type -> Prop :=
  | type_composition_oi:
    forall ts t1 t2 t3,
    t1 = channel O ts ->
    t2 = dual t1 ->
    t3 = dual t1 ->
    type_composition t1 t2 t3
  | type_composition_io:
    forall ts t1 t2 t3,
    t1 = channel O ts ->
    t2 = dual t1 ->
    t3 = dual t1 ->
    type_composition t2 t1 t3
  | type_composition_oo:
    forall ts t1 t2 t3,
    t1 = channel O ts ->
    t2 = channel O ts ->
    t3 = channel O ts ->
    type_composition t1 t2 t3.

Definition type_coherent: relation type :=
  fun t1 t2 =>
    exists t3, type_composition t1 t2 t3.

Lemma type_composition_sym:
  forall t1 t2 t3,
  type_composition t1 t2 t3 ->
  type_composition t2 t1 t3.
Proof.
  destruct 1; subst.
  - now apply type_composition_io with ts.
  - now apply type_composition_oi with ts.
  - now apply type_composition_oo with ts.
Qed.

Lemma type_coherent_sym:
  symmetric type_coherent.
Proof.
  intros t1 t2 ?.
  destruct H as (t3, ?).
  exists t3.
  now apply type_composition_sym.
Qed.

Record env_coherent (g: env) (h: env): Prop := {
  env_coherent_pointwise:
    forall i t1 t2,
    nth i g None = Some t1 ->
    nth i h None = Some t2 ->
    type_coherent t1 t2;
  env_coherent_acyclic:
    well_founded (union (env_edges g) (env_edges h))
}.

Inductive env_composition_nodes: nodes -> nodes -> nodes -> Prop :=
  | env_composition_nodes_nil_left:
    forall h,
    env_composition_nodes [] h h
  | env_composition_nodes_nil_right:
    forall g,
    env_composition_nodes g [] g
  | env_composition_nodes_cons_left:
    forall g h i t,
    env_composition_nodes g h i ->
    env_composition_nodes (t :: g) (None :: h) (t :: i)
  | env_composition_nodes_cons_right:
    forall g h i t,
    env_composition_nodes g h i ->
    env_composition_nodes (None :: g) (t :: h) (t :: i)
  | env_composition_nodes_cons_compose:
    forall g h i t1 t2 t3,
    env_composition_nodes g h i ->
    type_composition t1 t2 t3 ->
    env_composition_nodes (Some t1 :: g) (Some t2 :: h) (Some t3 :: i).

Definition lower_bound i (R: relation nat): Prop :=
  forall j, ~R j i.

Definition upper_bound i (R: relation nat): Prop :=
  forall j, ~R i j.

Inductive env_composition_edges: env -> env -> relation nat :=
  | env_composition_edges_mk:
    forall g h,
    let x := union (env_edges g) (env_edges h) in
    forall i j,
    x i j ->
    lower_bound i x ->
    upper_bound j x ->
    env_composition_edges g h i j.

Inductive env_composition: env -> env -> env -> Prop :=
  | env_composition_mk:
    forall g: env,
    forall h: env,
    forall i: nodes,
    env_composition_nodes g h i ->
    env_composition g h (env_mk i (env_composition_edges g h)).

Goal
  forall g h,
  env_coherent g h ->
  exists i,
  env_composition g h i.
Proof.
  destruct 1 as (?H, ?H).
  assert (exists i, env_composition_nodes g h i) as (i, ?).
  - clear H0.
    destruct g as (g, R).
    destruct h as (h, S).
    simpl in H |- *.
    clear R S.
    generalize dependent h.
    induction g; intros.
    + eexists; constructor.
    + destruct h.
      * eexists; constructor.
      * destruct IHg with h as (i, ?); intros.
        --- apply H with (S i); now simpl.
        --- destruct a, o.
            +++ destruct H with 0 t t0 as (?t, ?); simpl; auto.
                eexists; constructor.
                *** eassumption.
                *** eassumption.
            +++ eexists; constructor.
                eassumption.
            +++ eexists; constructor.
                eassumption.
            +++ eexists; constructor.
                eassumption.
  - eexists.
    constructor.
    eassumption.
Qed.

Definition env_equiv (g h: env): Prop :=
  env_nodes g = env_nodes h /\ same_relation (env_edges g) (env_edges h).

Lemma env_equiv_refl:
  reflexive env_equiv.
Proof.
  split; intros.
  - reflexivity.
  - firstorder.
Qed.

Lemma env_equiv_sym:
  symmetric env_equiv.
Proof.
  destruct 1; split.
  - auto.
  - destruct H0; firstorder.
Qed.

Lemma env_equiv_trans:
  transitive env_equiv.
Proof.
  destruct 1, 1; split.
  - now transitivity y.
  - destruct H0; destruct H2; firstorder.
Qed.

Lemma env_composition_nodes_sym:
  forall g h i,
  env_composition_nodes g h i ->
  env_composition_nodes h g i.
Proof.
  induction 1.
  - constructor.
  - constructor.
  - now constructor.
  - now constructor.
  - constructor.
    + assumption.
    + now apply type_composition_sym.
Qed.

Lemma env_composition_edges_switch:
  forall g h,
  inclusion (env_composition_edges g h) (env_composition_edges h g).
Proof.
  intros g h x y ?.
  dependent destruction H; constructor.
  - destruct H; firstorder.
  - intros z ?.
    apply H0 with z.
    destruct H2; firstorder.
  - intros z ?.
    apply H1 with z.
    destruct H2; firstorder.
Qed.

Lemma env_composition_sym:
  forall g h i1,
  env_composition g h i1 ->
  exists2 i2,
  (* We don't have propositional extensionality... *)
  env_composition h g i2 & env_equiv i1 i2.
Proof.
  destruct 1; simpl.
  apply env_composition_nodes_sym in H.
  eexists.
  - constructor.
    eassumption.
  - split; simpl.
    + reflexivity.
    + split; intros x y ?.
      * now apply env_composition_edges_switch.
      * now apply env_composition_edges_switch.
Qed.

Lemma env_composition_unit_left:
  forall g,
  exists2 h,
  env_composition env_empty g h & env_equiv g h.
Proof.
  intros.
  eexists (env_mk g _).
  - constructor; simpl.
    destruct g as (g, R).
    simpl; clear R.
    induction g.
    + constructor.
    + constructor.
  - constructor; simpl.
    + reflexivity.
    + split; intros x y ?.
      * constructor.
        --- now right.
        --- (* Hmm... *)
            admit.
        --- (* Oh, well... *)
            admit.
      * dependent destruction H.
        destruct H; simpl in *.
        --- exfalso.
            contradiction.
        --- assumption.
Admitted.

Lemma env_composition_unit_right:
  forall g,
  exists2 h,
  env_composition g env_empty h & env_equiv g h.
Proof.
  intros.
  destruct env_composition_unit_left with g as (h, ?, ?).
  destruct env_composition_sym with env_empty g h as (i, ?, ?); auto.
  exists i.
  - assumption.
  - now apply env_equiv_trans with h.
Qed.

(* Ohhh... this is why the length is at most 1... *)

Goal
  forall g,
  env_wellformed g ->
  forall x y,
  env_edges g x y ->
  forall z,
  (~env_edges g z x) /\ (~env_edges g y z).
Proof.
  split; intro.
  - destruct env_wellformed_domain with g x y as (ts1, ?); auto.
    destruct env_wellformed_codomain with g z x as (ts2, ?); auto.
    rewrite H2 in H3.
    dependent destruction H3.
  - destruct env_wellformed_codomain with g x y as (ts1, ?); auto.
    destruct env_wellformed_domain with g y z as (ts2, ?); auto.
    rewrite H2 in H3.
    dependent destruction H3.
Qed.
