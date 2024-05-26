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
    relation nat
}.

Global Coercion env_nodes: env >-> list.

Record env_wellformed (g: env): Prop := {
  env_wellformed_domain:
    forall i j,
    env_edges g i j ->
    has_input_type g i;
  env_wellformed_codomain:
    forall i j,
    env_edges g i j ->
    has_output_type g j;
  env_wellformed_acyclic:
    well_founded (env_edges g)
}.

Definition env_empty: env := {|
  env_nodes := [];
  env_edges x y := False
|}.

Lemma env_empty_is_wellformed:
  env_wellformed env_empty.
Proof.
  constructor; intros.
  - exfalso.
    inversion H.
  - exfalso.
    inversion H.
  - constructor.
    intros b ?.
    exfalso.
    inversion H.
Qed.

(*
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
*)

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

Lemma type_composition_is_commutative:
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
  now apply type_composition_is_commutative.
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

Lemma env_composition_nodes_is_commutative:
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
    + now apply type_composition_is_commutative.
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

Inductive env_composition_edges: env -> env -> nodes -> relation nat :=
  | env_composition_edges_mk:
    forall g h i x y,
    let R := union (env_edges g) (env_edges h) in
    t(R) x y ->
    env_composition_nodes g h i ->
    has_input_type i x ->
    has_output_type i y ->
    env_composition_edges g h i x y.

Inductive env_composition: env -> env -> env -> Prop :=
  | env_composition_mk:
    forall g h i R,
    same_relation R (env_composition_edges g h i) ->
    env_composition_nodes g h i ->
    env_composition g h (env_mk i R).

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
    simpl in H |- *; clear R S.
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
  - set (R := env_composition_edges g h i).
    assert (same_relation R R) by firstorder.
    exists (env_mk i R).
    now constructor.
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
  - now apply env_composition_nodes_is_commutative.
  - eassumption.
  - eassumption.
Qed.

Lemma env_composition_edges_is_commutative:
  forall g h i,
  inclusion (env_composition_edges g h i) (env_composition_edges h g i).
Proof.
  intros g h i x y ?.
  destruct H; constructor.
  - clear H0 H1 H2.
    induction H.
    + destruct H.
      * auto with cps.
      * auto with cps.
    + eauto with cps.
  - now apply env_composition_nodes_is_commutative.
  - assumption.
  - assumption.
Qed.

Lemma env_composition_is_commutative:
  forall g h i,
  env_composition g h i ->
  env_composition h g i.
Proof.
  destruct 1.
  constructor.
  - split; intros x y ?.
    + apply H in H1.
      now apply env_composition_edges_is_commutative.
    + apply H.
      now apply env_composition_edges_is_commutative.
  - now apply env_composition_nodes_is_commutative.
Qed.

(* -------------------------------------------------------------------------- *)

Definition active (g: env) (y: nat): Prop :=
  exists2 t,
  nth y g None = Some t & (forall x, ~env_edges g x y).

Goal
  forall g y,
  env_wellformed g ->
  has_input_type g y ->
  active g y.
Proof.
  intros g y ?H (ts1, ?).
  exists (channel I ts1).
  - assumption.
  - intros x ?H.
    apply env_wellformed_codomain in H1 as (ts2, ?).
    + rewrite H0 in H1.
      inversion H1.
    + assumption.
Qed.

(* -------------------------------------------------------------------------- *)
