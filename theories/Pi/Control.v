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

Local Notation nodes := (list (option type)).

Definition has_input_type (g: nodes) (n: nat): Prop :=
  exists ts,
  nth n g None = Some (channel I ts).

Definition has_output_type (g: nodes) (n: nat): Prop :=
  exists ts,
  nth n g None = Some (channel O ts).

Record env: Type := env_mk {
  env_nodes:
    nodes;
  env_edges:
    relation nat;
  env_wellformed_domain:
    forall i j,
    env_edges i j ->
    has_input_type env_nodes i;
  env_wellformed_codomain:
    forall i j,
    env_edges i j ->
    has_output_type env_nodes j
}.

Global Coercion env_nodes: env >-> list.

Local Notation exfalso := (False_rect _).

Definition env_empty: env := {|
  env_nodes := [];
  env_edges x y := False;
  env_wellformed_domain i j H := exfalso H;
  env_wellformed_codomain i j H := exfalso H
|}.

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

(* -------------------------------------------------------------------------- *)

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

(* TODO: check consistency within codebase. Are we writing "_is_a_function" or
   "_is_deterministic"? *)

Lemma type_composition_is_a_function:
  forall t1 t2 t3,
  type_composition t1 t2 t3 ->
  forall t4,
  type_composition t1 t2 t4 ->
  t3 = t4.
Proof.
  intros.
  dependent destruction H.
  - dependent destruction H2.
    + now subst.
    + now subst.
    + now subst.
  - dependent destruction H2.
    + now subst.
    + now subst.
    + now subst.
  - dependent destruction H2.
    + now subst.
    + now subst.
    + now subst.
Qed.

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

Definition type_coherent: relation type :=
  fun t1 t2 =>
    exists t3, type_composition t1 t2 t3.

Goal
  ~(type_coherent (channel I []) (channel I [])).
Proof.
  intro.
  destruct H.
  dependent destruction H.
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

Lemma env_composition_nodes_is_a_function:
  forall g h i1,
  env_composition_nodes g h i1 ->
  forall i2,
  env_composition_nodes g h i2 ->
  i1 = i2.
Proof.
  induction 1; intros.
  - now dependent destruction H.
  - now dependent destruction H.
  - dependent destruction H0.
    + f_equal.
      now apply IHenv_composition_nodes.
    + f_equal.
      now apply IHenv_composition_nodes.
  - dependent destruction H0.
    + f_equal.
      now apply IHenv_composition_nodes.
    + f_equal.
      now apply IHenv_composition_nodes.
  - dependent destruction H1.
    assert (t3 = t5) by now apply type_composition_is_a_function with t1 t2.
    subst; f_equal.
    now apply IHenv_composition_nodes.
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

Lemma env_composition_nodes_input_inversion:
  forall g h i,
  env_composition_nodes g h i ->
  forall x ts,
  nth x g None = Some (channel I ts) ->
  nth x i None = Some (channel I ts).
Proof.
  induction 1; intros.
  - exfalso.
    destruct x; inversion H.
  - assumption.
  - destruct x.
    + assumption.
    + simpl.
      now apply IHenv_composition_nodes.
  - destruct x.
    + exfalso.
      inversion H0.
    + simpl.
      now apply IHenv_composition_nodes.
  - destruct x.
    + simpl in H1 |- *.
      (* We have a composition of t1 and t2 into t3; since t1 is an input type,
         it means that t3 also has to be an input type, and t2 had to be a dual
         output type. *)
      dependent destruction H1.
      dependent destruction H0.
      reflexivity.
    + simpl.
      now apply IHenv_composition_nodes.
Qed.

(* Local Definition lower_bound i (R: relation nat): Prop :=
  forall j, ~R j i.

Local Definition upper_bound i (R: relation nat): Prop :=
  forall j, ~R i j. *)

Inductive env_composition_edges: env -> env -> nodes -> relation nat :=
  | env_composition_edges_mk:
    forall g h i x y ts1 ts2,
    let R := union (env_edges g) (env_edges h) in
    t(R) x y ->
    env_composition_nodes g h i ->
    nth x i None = Some (channel I ts1) ->
    nth y i None = Some (channel O ts2) ->
    env_composition_edges g h i x y.

Lemma env_composition_wellformed_domain:
  forall g h i x y,
  env_composition_edges g h i x y ->
  exists ts,
  nth x i None = Some (channel I ts).
Proof.
  intros.
  destruct H.
  now exists ts1.
Qed.

Lemma env_composition_wellformed_codomain:
  forall g h i x y,
  env_composition_edges g h i x y ->
  exists ts,
  nth y i None = Some (channel O ts).
Proof.
  intros.
  destruct H.
  now exists ts2.
Qed.

Inductive env_composition: env -> env -> env -> Prop :=
  | env_composition_mk:
    forall g: env,
    forall h: env,
    forall i: nodes,
    env_composition_nodes g h i ->
    env_composition g h (env_mk i (env_composition_edges g h i)
      (env_composition_wellformed_domain g h i)
      (env_composition_wellformed_codomain g h i)).

Goal
  forall g h,
  env_coherent g h ->
  exists i,
  env_composition g h i.
Proof.
  destruct 1 as (?H, ?H).
  assert (exists i, env_composition_nodes g h i) as (i, ?).
  - clear H0.
    destruct g as (g, R, ?H, ?H).
    destruct h as (h, S, ?H, ?H).
    simpl in H |- *.
    clear R S H0 H1 H2 H3.
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
  - exists (env_mk i (env_composition_edges g h i)
      (env_composition_wellformed_domain g h i)
      (env_composition_wellformed_codomain g h i)).
    constructor.
    assumption.
Qed.

Lemma env_composition_edges_switch:
  forall g h i,
  inclusion (env_composition_edges g h i) (env_composition_edges h g i).
Proof.
  intros g h i x y ?.
  destruct H.
  econstructor.
  - clear H0 H1 H2.
    induction H.
    + apply t_step.
      destruct H; firstorder.
    + now apply t_trans with y.
  - now apply env_composition_nodes_sym.
  - eassumption.
  - eassumption.
Qed.

Lemma env_composition_edges_switch_iff:
  forall g h i,
  same_relation (env_composition_edges g h i) (env_composition_edges h g i).
Proof.
  split; intros x y ?.
  - now apply env_composition_edges_switch.
  - now apply env_composition_edges_switch.
Qed.

Lemma env_composition_sym:
  forall g h i1,
  env_composition g h i1 ->
  exists2 i2,
  (* We don't have propositional extensionality... *)
  env_composition h g i2 & env_equiv i1 i2.
Proof.
  destruct 1; simpl.
  assert (env_composition_nodes h g i).
  - now apply env_composition_nodes_sym.
  - exists (env_mk i (env_composition_edges h g i)
      (env_composition_wellformed_domain h g i)
      (env_composition_wellformed_codomain h g i)).
    + now constructor.
    + constructor; simpl.
      * reflexivity.
      * apply env_composition_edges_switch_iff.
Qed.

Lemma type_composition_unit_left:
  forall g,
  env_composition_nodes [] g g.
Proof.
  destruct g.
  - constructor.
  - constructor.
Qed.

Goal
  forall g,
  env_composition_nodes g [] g.
Proof.
  intros.
  apply env_composition_nodes_sym.
  apply type_composition_unit_left.
Qed.

Lemma env_composition_unit_left:
  forall g,
  exists2 h,
  env_composition env_empty g h & env_equiv g h.
Proof.
  intros.
  assert (env_composition_nodes [] g g) by apply type_composition_unit_left.
  exists (env_mk g (env_composition_edges env_empty g g)
      (env_composition_wellformed_domain env_empty g g)
      (env_composition_wellformed_codomain env_empty g g)).
  - now constructor.
  - split; simpl.
    + reflexivity.
    + split; intros x y ?.
      * assert (exists ts1, nth x g None = Some (channel I ts1)) as (ts1, ?) by
          now apply env_wellformed_domain with y.
        assert (exists ts2, nth y g None = Some (channel O ts2)) as (ts2, ?) by
          now apply env_wellformed_codomain with x.
        econstructor; eauto with cps.
      * dependent destruction H0; simpl in *.
        apply clos_trans_t1n_iff in H0.
        destruct H0; destruct H0; try easy.
        clear H2 H3; exfalso.
        destruct H4; destruct H2; try easy.
        --- rename y0 into z.
            apply env_wellformed_codomain in H0 as (ts3, ?).
            apply env_wellformed_domain in H2 as (ts4, ?).
            rewrite H0 in H2.
            inversion H2.
        --- clear H4 z.
            rename y0 into z.
            apply env_wellformed_codomain in H0 as (ts3, ?).
            apply env_wellformed_domain in H2 as (ts4, ?).
            rewrite H0 in H2.
            inversion H2.
Qed.

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

(* -------------------------------------------------------------------------- *)

Definition active (g: env) (y: nat): Prop :=
  exists2 t,
  nth y g None = Some t & (forall x, ~env_edges g x y).

Goal
  forall (g: env) y,
  has_input_type g y ->
  active g y.
Proof.
  intros g y (ts1, ?).
  exists (channel I ts1).
  - assumption.
  - intros x ?H.
    apply env_wellformed_codomain in H0 as (ts2, ?).
    rewrite H in H0.
    inversion H0.
Qed.

(* -------------------------------------------------------------------------- *)
