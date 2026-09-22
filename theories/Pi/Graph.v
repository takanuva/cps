(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Setoid.
Require Import Relations.
Require Import Equality.
Require Import Local.AbstractRewriting.
Set Implicit Arguments.

(** This library is based on the paper "Algebraic Graphs with Class (Functional
    Pearl)" by Andrey Mokhov, and by his "algebraic-graphs" Haskell package,
    found at: https://hackage.haskell.org/package/algebraic-graphs/. *)

Import ListNotations.

Section Algebraic.

  Context {V: Set}.

  Inductive graph: Set :=
    | empty: graph
    | vertex: V -> graph
    | overlay: graph -> graph -> graph
    | connect: graph -> graph -> graph.

  Inductive has_vertex: graph -> V -> Prop :=
    | has_vertex_singleton:
      forall v,
      has_vertex (vertex v) v
    | has_vertex_overlay_left:
      forall g1 g2 v,
      has_vertex g1 v ->
      has_vertex (overlay g1 g2) v
    | has_vertex_overlay_right:
      forall g1 g2 v,
      has_vertex g2 v ->
      has_vertex (overlay g1 g2) v
    | has_vertex_connect_left:
      forall g1 g2 v,
      has_vertex g1 v ->
      has_vertex (connect g1 g2) v
    | has_vertex_connect_right:
      forall g1 g2 v,
      has_vertex g2 v ->
      has_vertex (connect g1 g2) v.

  Inductive has_edge: graph -> V -> V -> Prop :=
    | has_edge_overlay_left:
      forall g1 g2 v1 v2,
      has_edge g1 v1 v2 ->
      has_edge (overlay g1 g2) v1 v2
    | has_edge_overlay_right:
      forall g1 g2 v1 v2,
      has_edge g2 v1 v2 ->
      has_edge (overlay g1 g2) v1 v2
    | has_edge_connect_left:
      forall g1 g2 v1 v2,
      has_edge g1 v1 v2 ->
      has_edge (connect g1 g2) v1 v2
    | has_edge_connect_right:
      forall g1 g2 v1 v2,
      has_edge g2 v1 v2 ->
      has_edge (connect g1 g2) v1 v2
    | has_edge_connect_product:
      forall g1 g2 v1 v2,
      has_vertex g1 v1 ->
      has_vertex g2 v2 ->
      has_edge (connect g1 g2) v1 v2.

  Lemma graph_vertex_from_edge_left:
    forall g v1 v2,
    has_edge g v1 v2 ->
    has_vertex g v1.
  Proof.
    induction 1.
    - now apply has_vertex_overlay_left.
    - now apply has_vertex_overlay_right.
    - now apply has_vertex_connect_left.
    - now apply has_vertex_connect_right.
    - now apply has_vertex_connect_left.
  Qed.

  Lemma graph_vertex_from_edge_right:
    forall g v1 v2,
    has_edge g v1 v2 ->
    has_vertex g v2.
  Proof.
    induction 1.
    - now apply has_vertex_overlay_left.
    - now apply has_vertex_overlay_right.
    - now apply has_vertex_connect_left.
    - now apply has_vertex_connect_right.
    - now apply has_vertex_connect_right.
  Qed.

  Structure isomorphic (g1: graph) (g2: graph): Prop := {
    isomorphic_vertices:
      forall v,
      has_vertex g1 v <-> has_vertex g2 v;
    isomorphic_edges:
      forall v1 v2,
      has_edge g1 v1 v2 <-> has_edge g2 v1 v2
  }.

  Lemma isomorphic_refl:
    reflexive isomorphic.
  Proof.
    constructor; split; auto.
  Qed.

  Lemma isomorphic_sym:
    symmetric isomorphic.
  Proof.
    constructor; split; firstorder.
  Qed.

  Lemma isomorphic_trans:
    transitive isomorphic.
  Proof.
    constructor; split; intros.
    - now apply H0, H.
    - now apply H, H0.
    - now apply H0, H.
    - now apply H, H0.
  Qed.

  Global Instance isomorphic_is_an_equivalence:
    Equivalence isomorphic.
  Proof.
    constructor.
    - exact isomorphic_refl.
    - exact isomorphic_sym.
    - exact isomorphic_trans.
  Qed.

  Lemma overlay_is_commutative:
    forall g1 g2,
    isomorphic (overlay g1 g2) (overlay g2 g1).
  Proof.
    constructor; split; intros.
    - dependent destruction H.
      + now apply has_vertex_overlay_right.
      + now apply has_vertex_overlay_left.
    - dependent destruction H.
      + now apply has_vertex_overlay_right.
      + now apply has_vertex_overlay_left.
    - dependent destruction H.
      + now apply has_edge_overlay_right.
      + now apply has_edge_overlay_left.
    - dependent destruction H.
      + now apply has_edge_overlay_right.
      + now apply has_edge_overlay_left.
  Qed.

  Lemma overlay_is_associative:
    forall g1 g2 g3,
    isomorphic (overlay g1 (overlay g2 g3)) (overlay (overlay g1 g2) g3).
  Proof.
    constructor; split; intros.
    - dependent destruction H.
      + apply has_vertex_overlay_left.
        now apply has_vertex_overlay_left.
      + dependent destruction H.
        * apply has_vertex_overlay_left.
          now apply has_vertex_overlay_right.
        * now apply has_vertex_overlay_right.
    - dependent destruction H.
      + dependent destruction H.
        * now apply has_vertex_overlay_left.
        * apply has_vertex_overlay_right.
          now apply has_vertex_overlay_left.
      + apply has_vertex_overlay_right.
        now apply has_vertex_overlay_right.
    - dependent destruction H.
      + apply has_edge_overlay_left.
        now apply has_edge_overlay_left.
      + dependent destruction H.
        * apply has_edge_overlay_left.
          now apply has_edge_overlay_right.
        * now apply has_edge_overlay_right.
    - dependent destruction H.
      + dependent destruction H.
        * now apply has_edge_overlay_left.
        * apply has_edge_overlay_right.
          now apply has_edge_overlay_left.
      + apply has_edge_overlay_right.
        now apply has_edge_overlay_right.
  Qed.

  Definition edge (v1: V) (v2: V): graph :=
    connect (vertex v1) (vertex v2).

  Definition edges (es: list (V * V)): graph :=
    fold_right overlay empty (map (fun e => edge (fst e) (snd e)) es).

  Definition vertices (vs: list V): graph :=
    fold_right overlay empty (map vertex vs).

  Definition clique (vs: list V): graph :=
    fold_right connect empty (map vertex vs).

  Fixpoint graph_fold {T} a x y z (g: graph): T :=
    match g with
    | empty => a
    | vertex v => x v
    | overlay g1 g2 => y (graph_fold a x y z g1) (graph_fold a x y z g2)
    | connect g1 g2 => z (graph_fold a x y z g1) (graph_fold a x y z g2)
    end.

End Algebraic.

Global Arguments graph: clear implicits.

Section Monadic.

  Context {V: Set}.
  Context {W: Set}.

  Definition graph_pure: V -> graph V :=
    vertex.

  Definition graph_bind (f: V -> graph W): graph V -> graph W :=
    graph_fold empty f overlay connect.

  Definition graph_map (f: V -> W): graph V -> graph W :=
    graph_bind (fun v => vertex (f v)).

End Monadic.

Section Extra.

  Context {V: Set}.

  Definition graph_induce (f: V -> bool): graph V -> graph V :=
    let g v :=
      if f v then
        vertex v
      else
        empty
    in graph_bind g.

  Lemma graph_induce_vertex_simpl:
    forall f v,
    graph_induce f (vertex v) =
      if f v then vertex v else empty.
  Proof.
    auto.
  Qed.

  Lemma graph_induce_overlay_simpl:
    forall g1 g2 f,
    graph_induce f (overlay g1 g2) =
      overlay (graph_induce f g1) (graph_induce f g2).
  Proof.
    auto.
  Qed.

  Lemma graph_induce_connect_simpl:
    forall g1 g2 f,
    graph_induce f (connect g1 g2) =
      connect (graph_induce f g1) (graph_induce f g2).
  Proof.
    auto.
  Qed.

  Lemma graph_induce_reflects_vertex:
    forall g f w,
    has_vertex (graph_induce f g) w ->
    has_vertex g w.
  Proof.
    induction g; intros.
    - exfalso.
      inversion H.
    - rewrite graph_induce_vertex_simpl in H.
      destruct (f v).
      + dependent destruction H.
        constructor.
      + exfalso.
        inversion H.
    - rewrite graph_induce_overlay_simpl in H.
      dependent destruction H.
      + apply has_vertex_overlay_left.
        now apply IHg1 with f.
      + apply has_vertex_overlay_right.
        now apply IHg2 with f.
    - rewrite graph_induce_connect_simpl in H.
      dependent destruction H.
      + apply has_vertex_connect_left.
        now apply IHg1 with f.
      + apply has_vertex_connect_right.
        now apply IHg2 with f.
  Qed.

  Lemma graph_induce_reflects_edge:
    forall g f w1 w2,
    has_edge (graph_induce f g) w1 w2 ->
    has_edge g w1 w2.
  Proof.
    induction g; intros.
    - exfalso.
      inversion H.
    - exfalso.
      rewrite graph_induce_vertex_simpl in H.
      destruct (f v).
      + inversion H.
      + inversion H.
    - rewrite graph_induce_overlay_simpl in H.
      dependent destruction H.
      + apply has_edge_overlay_left.
        now apply IHg1 with f.
      + apply has_edge_overlay_right.
        now apply IHg2 with f.
    - rewrite graph_induce_connect_simpl in H.
      dependent destruction H.
      + apply has_edge_connect_left.
        now apply IHg1 with f.
      + apply has_edge_connect_right.
        now apply IHg2 with f.
      + apply has_edge_connect_product.
        * now apply graph_induce_reflects_vertex with f.
        * now apply graph_induce_reflects_vertex with f.
  Qed.

End Extra.
