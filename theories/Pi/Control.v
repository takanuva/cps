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
Require Import Local.Substitution.
Require Import Local.Pi.Graph.
Require Import Local.Pi.Calculus.

Set Primitive Projections.

(* Typing judgements in the linear pi-calculus, and in subsets such as the
   control pi-calculus, need an additional graph structure on names to enforce
   acyclicity. We'll represent this by using an algebraic graph with pairs of
   de Bruijn *level* and type as vertices. *)

Definition env: Set :=
  graph (nat * type).

Definition env_type (g: env) (n: nat) (t: type) :=
  has_vertex g (n, t).

Definition has_input_type (g: env) (n: nat): Prop :=
  exists ts,
  env_type g n (channel I ts).

Definition has_output_type (g: env) (n: nat): Prop :=
  exists ts,
  env_type g n (channel O ts).

Definition has_free_name (g: env) (n: nat): Prop :=
  exists t,
  env_type g n t.

Definition env_edge (g: env) (i: nat) (j: nat): Prop :=
  exists t u,
  has_edge g (i, t) (j, u).

Record env_wellformed (g: env): Prop := {
  env_wellformed_domain:
    forall i j,
    env_edge g i j ->
    has_input_type g i;
  env_wellformed_codomain:
    forall i j,
    env_edge g i j ->
    has_output_type g j;
  env_wellformed_unique:
    forall t u i,
    env_type g i t ->
    env_type g i u ->
    t = u;
  env_wellformed_acyclic:
    well_founded (env_edge g)
}.

Lemma empty_is_wellformed:
  env_wellformed empty.
Proof.
  constructor; intros.
  - exfalso.
    destruct H as (t, (u, ?)).
    inversion H.
  - exfalso.
    destruct H as (t, (u, ?)).
    inversion H.
  - exfalso.
    inversion H.
  - constructor; intros.
    destruct H as (t, (u, ?)).
    inversion H.
Qed.

Lemma env_wellformed_isomorphism:
  forall g1 g2,
  env_wellformed g1 ->
  isomorphic g1 g2 ->
  env_wellformed g2.
Proof.
  constructor; intros.
  - destruct H1 as (t, (u, ?)).
    apply H0 in H1.
    destruct env_wellformed_domain with g1 i j as (ts, ?).
    + assumption.
    + now exists t, u.
    + exists ts.
      now apply H0.
  - destruct H1 as (t, (u, ?)).
    apply H0 in H1.
    destruct env_wellformed_codomain with g1 i j as (ts, ?).
    + assumption.
    + now exists t, u.
    + exists ts.
      now apply H0.
  - apply H0 in H1, H2.
    now apply env_wellformed_unique with g1 i.
  - intro x.
    induction (env_wellformed_acyclic g1 H) with x.
    constructor; intros.
    apply H2.
    destruct H3 as (t, (u, ?)).
    exists t, u.
    now apply H0.
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
  - dependent destruction H2; now subst.
  - dependent destruction H2; now subst.
  - dependent destruction H2; now subst.
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

Record env_coherent (g1: env) (g2: env): Prop := {
  env_coherent_pointwise:
    forall i t1 t2,
    env_type g1 i t1 ->
    env_type g2 i t2 ->
    exists t3,
    type_composition t1 t2 t3;
  env_coherent_acyclic:
    well_founded (union (env_edge g1) (env_edge g2))
}.

Axiom env_composition: env -> env -> env.

Inductive env_composition_vertex: env -> env -> nat -> type -> Prop :=
  | env_composition_left:
    forall g1 g2 n t,
    env_type g1 n t ->
    ~has_free_name g2 n ->
    env_composition_vertex g1 g2 n t
  | env_composition_right:
    forall g1 g2 n t,
    env_type g2 n t ->
    ~has_free_name g1 n ->
    env_composition_vertex g1 g2 n t
  | env_composition_both:
    forall g1 g2 n t u v,
    env_type g1 n t ->
    env_type g2 n u ->
    type_composition t u v ->
    env_composition_vertex g1 g2 n v.

Lemma env_composition_vertex_inversion:
  forall g1 g2 n t,
  env_type (env_composition g1 g2) n t <-> env_composition_vertex g1 g2 n t.
Proof.
  split; intros.
  - admit.
  - admit.
Admitted.

Lemma env_composition_preserves_wellformedness:
  forall g1 g2,
  env_coherent g1 g2 ->
  env_wellformed g1 ->
  env_wellformed g2 ->
  env_wellformed (env_composition g1 g2).
Proof.
  constructor; intros.
  - destruct H2 as (t, (u, ?)).
    admit.
  - destruct H2 as (t, (u, ?)).
    admit.
  - (* We check the inversion hypothesis for the existence of the vertices
       [i: t] and [i: u] in the composition. This is mostly straightforward, as
       it will either exist in [g1] and not [g2], or the other way around. In
       the case that it exists in both, uniqueness follows from the fact that
       type composition itself is unique. *)
    apply env_composition_vertex_inversion in H2.
    apply env_composition_vertex_inversion in H3.
    destruct H2, H3.
    + firstorder.
    + firstorder.
    + firstorder.
    + firstorder.
    + firstorder.
    + firstorder.
    + firstorder.
    + firstorder.
    + assert (t0 = t) by now apply env_wellformed_unique with g1 n.
      assert (u0 = u) by now apply env_wellformed_unique with g2 n.
      subst; now apply type_composition_is_a_function with t u.
  - (* It's not true that composition preserves acyclicity of the graphs. The
       proof comes directly from the hypothesis that they are coherent. We play
       a simple bisimulation game. *)
    intro x; apply env_coherent_acyclic in H.
    induction H with x.
    constructor; intros.
    admit.
Admitted.

(* -------------------------------------------------------------------------- *)

(* Whenever we are removing something from an action type, we will remove some
   number of the most recently introduced variables simultaneously. In order to
   implement that, since we're using de Bruijn levels, we simply remove all the
   vertices that have a level higher then some number. *)

Definition env_hiding (g: env) (n: nat): env :=
  (* Keep vertices smaller or equal to n. *)
  graph_induce (fun v => n <=? fst v) g.

Lemma env_hiding_preserves_wellformedness:
  forall g,
  env_wellformed g ->
  forall n,
  env_wellformed (env_hiding g n).
Proof.
  (* Removing edges doesn't break any of the desired properties. *)
  constructor; intros.
  - destruct H0 as (t, (u, ?)).
    (* We removed some vertices from [g]. If, after that, we still have an edge
       from [i: t] to [j: u], we can check that [i] was already present in [g],
       and by our hypothesis, there are ts types such that [i: !ts] exists in
       [g]. As, also by our hypothesis, associations are unique, [!ts] and [t]
       are the same, and, since the resulting graph has a vertex [i: t] still,
       we check that this vertex is indeed [i: !ts] as required. *)
    destruct env_wellformed_domain with g i j as (ts, ?).
    + assumption.
    + exists t, u.
      eapply graph_induce_reflects_edge.
      eassumption.
    + exists ts.
      apply graph_vertex_from_edge_left with (j, u).
      rewrite env_wellformed_unique with g (channel I ts) t i.
      * assumption.
      * assumption.
      * assumption.
      * apply graph_vertex_from_edge_left with (j, u).
        eapply graph_induce_reflects_edge.
        eassumption.
  - (* Same reasoning as above, accordingly. *)
    destruct H0 as (t, (u, ?)).
    destruct env_wellformed_codomain with g i j as (ts, ?).
    + assumption.
    + exists t, u.
      eapply graph_induce_reflects_edge.
      eassumption.
    + exists ts.
      apply graph_vertex_from_edge_right with (i, t).
      rewrite env_wellformed_unique with g (channel O ts) u j.
      * assumption.
      * assumption.
      * assumption.
      * apply graph_vertex_from_edge_right with (i, t).
        eapply graph_induce_reflects_edge.
        eassumption.
  - (* Hiding can't add any new vertex. If both [i: t] and [i: u] already
       existed inside of [g], by our hypothesis they are the same thing. *)
    apply env_wellformed_unique with g i.
    + assumption.
    + eapply graph_induce_reflects_vertex.
      eassumption.
    + eapply graph_induce_reflects_vertex.
      eassumption.
  - (* Since [g] is acyclic, we can't possibly get a cycle by just removing
       some vertices. We start from an arbitrary vertex [x]. If the opponent can
       give us an [y] such that a vertex exists in the resulting graph from [x]
       to [y], we can check that it already existed in [g] and keep following
       the same path, known to be terminating. We win the game once the opponent
       can't find more edges, either because it reached the same end as in [g]
       or possibly earlier if it reached a removed vertex. *)
    intro x.
    induction env_wellformed_acyclic with g x; auto.
    constructor; intros y (t, (u, ?)).
    apply H1; exists t, u.
    eapply graph_induce_reflects_edge.
    eassumption.
Qed.

(* -------------------------------------------------------------------------- *)

Definition env_singleton (n: nat) (t: type): env :=
  vertex (n, t).

Lemma env_singleton_is_wellformed:
  forall n t,
  env_wellformed (env_singleton n t).
Proof.
  constructor; intros.
  - (* There are no edges. *)
    exfalso.
    destruct H as (u, (v, ?)).
    inversion H.
  - (* Still no edges. *)
    exfalso.
    destruct H as (u, (v, ?)).
    inversion H.
  - (* There's a single vertex, clearly it's equal to itself. *)
    unfold env_singleton, env_type in H, H0.
    dependent destruction H.
    dependent destruction H0.
    reflexivity.
  - (* Hey! Still no edges! Instant win in the bisimulation game. *)
    intro x.
    constructor; intros y (u, (v, ?)).
    exfalso.
    inversion H.
Qed.

(* -------------------------------------------------------------------------- *)

(* A variable is said to be active if it is associated to some type in the graph
   and it has no edge pointing to it. *)

Definition active (g: env) (y: nat): Prop :=
  exists2 t,
  env_type g y t & (forall x, ~env_edge g x y).

(* TODO: do we need this one? *)

Lemma input_type_is_always_active:
  forall g y,
  env_wellformed g ->
  has_input_type g y ->
  active g y.
Proof.
  intros.
  destruct H0 as (ts1, ?).
  exists (channel I ts1); intros.
  - assumption.
  - intro.
    apply env_wellformed_codomain in H1 as (ts2, ?).
    + assert (channel I ts1 = channel O ts2).
      * now apply env_wellformed_unique with g y.
      * inversion H2.
    + assumption.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive mode_composition: mode -> mode -> mode -> Prop :=
  | mode_composition_io:
    mode_composition I O O
  | mode_composition_oi:
    mode_composition O I O
  | mode_composition_ii:
    mode_composition I I I.

Definition env_mode (m: mode) (g: env): Prop :=
  forall i t,
  env_type g i t ->
  get_mode t = m.

(* -------------------------------------------------------------------------- *)

Inductive typing: mode -> term -> env -> Prop :=
  (* Rule for typing an inactive process:

      ------------ (ZERO)
        |-I 0 |>

     The inactive process is only typeable in an empty action type, with input
     mode (clearly, there's no active output). In order to add unused (output)
     variables, we will use weakening. *)
  | typing_zero:
    typing I inactive empty
  (* Rule for typing the composition of two processes:

        |-(m) p |> G    |-(n) q |> H    G >< H
      ------------------------------------------- (PAR)
               |-(m * n) p | q |> G * H

     Parallel composition first assumes that [p] and [q] are typeable. We check
     then that their action types, [G] and [H] respectively, are coherent with
     each other in order to avoid cycles and multiple inputs on the same name.
     We note that the modes must be able to be composed together, otherwise this
     won't be defined (we don't add this explicitly in the hypotheses as Honda
     et al. do). *)
  | typing_par:
    forall m n o p q g h,
    typing m p g ->
    typing n q h ->
    env_coherent g h ->
    mode_composition m n o ->
    typing o (parallel p q) (env_composition g h)
  (* Rule for typing name restriction:

         |-(m) p |> G     G(x) = ti
      ------------------------------- (RES)
           |-(m) (x: ti)p |> G/x

     In order to type a restriction, we assume that [p] is typeable in some
     action type [G] such that [x: ti] is a vertex within it. Note that this
     will require that the name [x] is defined as a replicated input in [p]. *)
  | typing_res:
    forall m p g t,
    typing m p g ->
    alternating I t ->
    (* TODO: which level is variable 0...? *)
    env_type g 42 t ->
    typing m (restriction t p) (env_hiding g 42)
  (* Rule for weakening, which is explicit:

        |-(m) p |> G   x undefined in G
      ----------------------------------- (WEAK)
            |-(m) p |> G, x: ?(ts)

     If [p] is typeable in some action type [G], it's also typeable in some
     action type which extends [G] by adding a new vertex [x: t] if [x] isn't
     defined in [G] and if [t] is an output type. Basically, it says that we may
     ignore any unused free variables which have output types. *)
  | typing_weak:
    forall m p g n t,
    typing m p g ->
    alternating O t ->
    ~has_free_name g n ->
    typing m p (env_composition g (env_singleton n t))
  (*
       |-O p |> G, ys: ts    md(G) = ?
    ------------------------------------- (IN)
      |-I !x(ys: ts).p |> x: !(ts) -> G
  *)
  (* | typing_in: (* TODO: fix this! *)
    forall p g n ts h i,
    typing O p g ->
    nth (length ts + n) g None = None ->
    env_mode O g ->
    Forall (alternating O) ts ->
    (* We're hiding ys from G, which only had output types, so it can't have any
       edge and thus all variables must be active. *)
    env_hiding (length ts) g h ->
    env_prefix n (channel I ts) h i ->
    typing I (replication n ts p) i *)
  (*
    --------------------------------------- (FOUT)
      |-O x<ys> |> (x: ?(ts)) * (ys: ~ts)

    Note that in here we do not expect the names in ys to be all different, and,
    because of that, if y_i = y_j, then we expect t_i = t_j.

    It's also important to notice that we're not checking, individually, the
    composition of each individual names. While this won't be a problem in here,
    it would be in case we had linear types as in the linear pi-calculus studied
    by Yoshida. If we are to consider the full thing, we might want to rework
    this rule to cover this possibility.
  *)
  (* | typing_out:
  *).

(*
Lemma typing_bout:
  (*
        |-I P |> A, ys: ts     A >< x: ?(ts)
    -------------------------------------------- (BOUT)
            |-O x[ys] p |> A * x: ?(ts)
  *)
*)

Definition typed (p: term): Prop :=
  exists m g,
  typing m p g.

Lemma typing_env_wellformed:
  forall m p g,
  typing m p g ->
  env_wellformed g.
Proof.
  induction 1.
  - apply empty_is_wellformed.
  - now apply env_composition_preserves_wellformedness.
  - now apply env_hiding_preserves_wellformedness.
  - apply env_composition_preserves_wellformedness.
    + admit.
    + assumption.
    + apply env_singleton_is_wellformed.
Admitted.
