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

Record env: Set := {
  env_nodes:
    list (option type);
  env_edges:
    list (nat * nat)
}.

Global Coercion env_nodes: env >-> list.

Definition env_adjacency (g: env): relation nat :=
  fun x y =>
    In (x, y) (env_edges g).

Record env_wellformed (g: env): Prop := {
  env_wellformed_domain:
    forall i j,
    env_adjacency g i j ->
    exists ts,
    nth i g None = Some (channel I ts);
  env_wellformed_codomain:
    forall i j,
    env_adjacency g i j ->
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

Lemma type_coherent_sym:
  symmetric type_coherent.
Proof.
  intros t1 t2 ?.
  destruct H as (t3, ?).
  exists t3.
  dependent destruction H; subst.
  - now apply type_composition_io with ts.
  - now apply type_composition_oi with ts.
  - now apply type_composition_oo with ts.
Qed.

Record env_coherent (g: env) (h: env): Prop := {
  env_coherent_pointwise:
    forall i t1 t2,
    nth i g None = Some t1 ->
    nth i h None = Some t2 ->
    type_coherent t1 t2;
}.
