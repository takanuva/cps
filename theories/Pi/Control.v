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

Definition has_output_mode (g: env): Prop :=
  forall n t,
  env_type g n t -> get_mode t = O.

Definition env_edge (g: env) (i: nat) (j: nat): Prop :=
  exists t u,
  has_edge g (i, t) (j, u).

Definition introduced_vars (g: env): nat :=
  graph_fold 0 (fun v => 1 + fst v) max max g.

Local Coercion introduced_vars: env >-> nat.

Lemma introduced_vars_overlay:
  forall g1 g2,
  introduced_vars (overlay g1 g2) =
    max (introduced_vars g1) (introduced_vars g2).
Proof.
  auto.
Qed.

Lemma introduced_vars_connect:
  forall g1 g2,
  introduced_vars (connect g1 g2) =
    max (introduced_vars g1) (introduced_vars g2).
Proof.
  auto.
Qed.

(* Goal
  forall i t g,
  env_type g i t ->
  i < introduced_vars g.
Proof.
  unfold introduced_vars; simpl.
  induction g; simpl; intros.
  - exfalso.
    inversion H.
  - unfold env_type in H.
    dependent destruction H.
    simpl; lia.
  - unfold env_type in H.
    dependent destruction H.
    + specialize (IHg1 H).
      lia.
    + specialize (IHg2 H).
      lia.
  - unfold env_type in H.
    dependent destruction H.
    + specialize (IHg1 H).
      lia.
    + specialize (IHg2 H).
      lia.
Qed. *)

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
  env_wellformed_sequential:
    forall n,
    has_free_name g n ->
    forall m,
    m < n ->
    has_free_name g m
}.

Lemma env_wellformed_acyclic:
  forall g,
  env_wellformed g ->
  well_founded (env_edge g).
Proof.
  intros.
  (* Given the domain and codomain constraints, paths can have length of at most
     one; i.e., a vertex can't be both target and source of an edge. *)
  intro x.
  constructor; intros y ?.
  constructor; intros z ?.
  exfalso.
  (* In here, [y] is the culprint. *)
  apply env_wellformed_domain in H0 as (ts1, ?); auto.
  apply env_wellformed_codomain in H1 as (ts2, ?); auto.
  now eapply env_wellformed_unique with (u := channel O ts2) in H0.
Qed.

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
  - exfalso.
    destruct H as (t, ?).
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
  - destruct H1 as (t, ?).
    apply H0 in H1.
    destruct env_wellformed_sequential with g1 n m as (u, ?).
    + assumption.
    + now exists t.
    + assumption.
    + apply H0 in H3.
      now exists u.
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
  (* *)
  env_coherent_length:
    introduced_vars g1 = introduced_vars g2;
  (* *)
  env_coherent_pointwise:
    forall i t1 t2,
    env_type g1 i t1 ->
    env_type g2 i t2 ->
    exists t3,
    type_composition t1 t2 t3;
  (* *)
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
  - admit.
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
  - (* For any name preserved, every smaller names are also preserved. *)
    rename n0 into j.
    destruct H0 as (t, ?).
    admit.
Admitted.

(* -------------------------------------------------------------------------- *)

Definition env_singleton (n: nat) (t: type): env :=
  vertex (n, t).

Fixpoint env_extend (g: env) (k: nat) (ts: list type): env :=
  match ts with
  | [] => g
  | t :: ts => overlay (env_extend g k ts) (env_singleton (length ts + k) t)
  end.

Lemma introduced_vars_singleton:
  forall n t,
  introduced_vars (env_singleton n t) = 1 + n.
Proof.
  auto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Lemma env_singleton_is_wellformed:
  forall t,
  env_wellformed (env_singleton 0 t).
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
  - (* We're only using index zero. *)
    exfalso.
    destruct H as (t', ?).
    unfold env_type, env_singleton in H.
    dependent destruction H.
    inversion H0.
Qed. *)

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

Global Instance env_dbTraverse: dbTraverse env nat :=
  fun f k g =>
    graph_bind (fun v => vertex (f k (fst v), snd v)) g.

Global Instance env_dbTraverseLaws: dbTraverseLaws env nat.
Proof.
  split; unfold Substitution.traverse; intros.
  - unfold env_dbTraverse, graph_bind.
    induction x; simpl.
    + reflexivity.
    + rewrite H.
      now destruct v.
    + now rewrite IHx1, IHx2.
    + now rewrite IHx1, IHx2.
  - specialize (H k (vertex (n, channel O []))).
    now dependent destruction H.
  - unfold env_dbTraverse, graph_bind.
    induction x; simpl.
    + reflexivity.
    + now rewrite H with (l := 0).
    + now rewrite IHx1, IHx2.
    + now rewrite IHx1, IHx2.
  - unfold env_dbTraverse, graph_bind.
    induction x; simpl.
    + reflexivity.
    + reflexivity.
    + now rewrite IHx1, IHx2.
    + now rewrite IHx1, IHx2.
Qed.

Lemma inst_env_empty:
  forall s,
  inst s empty = empty.
Proof.
  auto.
Qed.

Lemma inst_env_vertex:
  forall s n t,
  inst s (vertex (n, t)) = vertex (s 0 n, t).
Proof.
  auto.
Qed.

Lemma inst_env_overlay:
  forall s g1 g2,
  inst s (overlay g1 g2) = overlay (s 0 g1) (s 0 g2).
Proof.
  auto.
Qed.

Lemma inst_env_connect:
  forall s g1 g2,
  inst s (connect g1 g2) = connect (s 0 g1) (s 0 g2).
Proof.
  auto.
Qed.

Global Hint Rewrite inst_env_empty using sigma_solver: sigma.
Global Hint Rewrite inst_env_vertex using sigma_solver: sigma.
Global Hint Rewrite inst_env_overlay using sigma_solver: sigma.
Global Hint Rewrite inst_env_connect using sigma_solver: sigma.

Lemma lifting_over_introduced_vars_is_noop:
  forall (a: env) k n,
  k >= a ->
  lift n k a = a.
Proof.
  unfold introduced_vars; induction a; intros.
  - sigma.
    (* TODO: why sigma doesn't work here...? *)
    autorewrite with sigma.
    reflexivity.
  - destruct v as (j, t); simpl in H.
    (* TODO: why??? *)
    sigma; autorewrite with sigma.
    f_equal; f_equal; simpl.
    (* Ok, this doesn't work because it's [j] and not [var j]... TODO: fix! *)
    replace j with (var j) by auto.
    now sigma.
  - (* TODO: what is happening here? *)
    sigma; autorewrite with sigma; simpl; f_equal.
    + rewrite <- IHa1 with (k := k) (n := n) at 2.
      * now sigma.
      * simpl in H |- *; lia.
    + rewrite <- IHa2 with (k := k) (n := n) at 2.
      * now sigma.
      * simpl in H |- *; lia.
  - (* TODO: sigh... *)
    sigma; autorewrite with sigma; simpl; f_equal.
    + rewrite <- IHa1 with (k := k) (n := n) at 2.
      * now sigma.
      * simpl in H |- *; lia.
    + rewrite <- IHa2 with (k := k) (n := n) at 2.
      * now sigma.
      * simpl in H |- *; lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* Convert a de Bruijn index to level. *)
Local Notation i2l k i := (k - i - 1).

(* *)
Inductive typing: mode -> term -> env -> Prop :=
  (* Rule for typing an inactive process:

      ------------ (ZERO)
        |-I 0 |>

     The inactive process is only typeable in an empty action type, with input
     mode (clearly, there's no active output). In order to add unused (output)
     variables, we will use weakening, which has no change on the term. *)
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
     et al. do). As this definition is very awkward in a de Bruijn setting, we
     consider a trivial new constraint that [G] and [H] must have the same names
     defined in each (which can, of course, be done by weakening). *)
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
    env_type g (i2l g 0) t ->
    typing m (restriction t p) (env_hiding g (i2l g 0))
  (* Rule for weakening, which is explicit:

        |-(m) p |> G   x undefined in G
      ----------------------------------- (WEAK)
            |-(m) p |> G, x: ?(ts)

     If [p] is typeable in some action type [G], it's also typeable in some
     action type which extends [G] by adding a new vertex [x: t] if [x] isn't
     defined in [G] and if [t] is an output type. Basically, it says that we may
     ignore any unused free variables which have output types. In a de Bruijn
     setting, we make room for [x] by using a lift (both in the term and in the
     graph, of course). *)
  | typing_weak:
    forall m p g k t,
    typing m p g ->
    alternating O t ->
    typing m (lift 1 k p)
      (overlay (env_singleton (i2l g k) t) (lift 1 (i2l g k) g))
  (* Rule for input:

         |-O p |> G, ys: ts     G(x) is undefined     md(G) = ?
      ----------------------------------------------------------- (IN)
                   |-I !x(ys: ts).p |> x: !(ts) -> G

     As action types are identifiable up to graph isomorphism, we assume that
     our continuation [p] is typeable in some action type [G] extended with
     types for each of the input variables; in this, we also assume that [ys]
     do not appear in [G] already. So, if [x] is undefined in [G] (and thus in
     [p] too), for which we always make room by using a lift, and there is no
     input type in [G], we can enclose [p] by the input of [ys] through [x],
     making sure that [x] will have an input type now and that there will be
     edges from it to every variable in [G]. *)
  | typing_in:
    forall x ts p g,
    typing O p (env_extend g g ts) ->
    has_output_mode g ->
    Forall (alternating O) ts ->
    typing I (replication x ts (lift 1 (x + length ts) p))
      (* We note that we can derive that [g] doesn't mention [ys]. *)
      (connect (* TODO: why are we adding 1 in here...? *)
        (env_singleton (i2l (1 + g) x) (channel I ts))
        (lift 1 (i2l (1 + g) x) g))
  (* Rule for free output:

              x: ?(ts) >< (ys: ~ts)
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
  *)
  | typing_iso:
    (* We close the typing rules up to graph isomorphism on action types. *)
    forall m p g h,
    typing m p g ->
    isomorphic g h ->
    typing m p h.

(*
Lemma typing_bout:
  (*
        |-I P |> A, ys: ts     A >< x: ?(ts)
    -------------------------------------------- (BOUT)
            |-O x[ys] p |> A * x: ?(ts)
  *)
*)

Lemma typing_types_free_vars:
  forall m p g,
  typing m p g ->
  forall k,
  free k p -> k < g.
Proof.
  induction 1; intros.
  - exfalso; apply H.
    constructor.
  - apply free_parallel_inversion in H3.
    destruct H3.
    + apply IHtyping1 in H3.
      admit.
    + apply IHtyping2 in H3.
      admit.
  - apply free_restriction_inversion in H2.
    apply IHtyping in H2.
    admit.
  - rename k0 into j.
    rewrite introduced_vars_overlay.
    rewrite introduced_vars_singleton.
    admit.
  - apply free_replication_inversion in H2.
    rewrite introduced_vars_connect.
    rewrite introduced_vars_singleton.
    destruct H2; subst.
    + admit.
    + admit.
  - admit.
Admitted.

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
  - admit.
  - admit.
  - now apply env_wellformed_isomorphism with g.
Admitted.
