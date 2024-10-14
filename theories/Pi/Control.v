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

Lemma env_conherence_implies_wellformedness:
  forall g h,
  env_coherent g h ->
  forall i,
  env_composition g h i ->
  env_wellformed i.
Proof.
  intros.
  destruct H as (?H, ?H).
  constructor.
  - intros x y ?.
    destruct H0.
    apply H0 in H2.
    destruct H2.
    assumption.
  - intros x y ?.
    destruct H0.
    apply H0 in H2.
    destruct H2.
    assumption.
  - destruct H0.
    intros x; simpl.
    specialize (H1 x).
    set (S := union (env_edges g) (env_edges h)) in H1.
    replace (Acc S) with (SN (transp S)) in H1 by auto.
    induction H1 using SN_ind.
    constructor; intros y ?.
    apply H3; clear H2.
    apply H0 in H4; clear H0.
    destruct H4.
    clear H1 H2 H3 H4 H5.
    induction H0.
    + destruct H0.
      * apply t_step.
        now left.
      * apply t_step.
        now right.
    + eauto with cps.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive env_hiding_edges: nat -> relation nat -> relation nat :=
  | env_hiding_edges_mk:
    forall (R: relation nat) n x y,
    R (n + x) (n + y) ->
    env_hiding_edges n R x y.

Inductive env_hiding: nat -> env -> env -> Prop :=
  | env_hiding_mk:
    forall n g R S h,
    drop 0 n g h ->
    same_relation S (env_hiding_edges n R) ->
    env_hiding n (env_mk g R) (env_mk h S).

Lemma env_hiding_preserves_wellformedness:
  forall n g h,
  env_wellformed g ->
  env_hiding n g h ->
  env_wellformed h.
Proof.
  constructor; intros.
  - destruct H as (?H, _, _).
    destruct H0; simpl in *.
    apply H2 in H1.
    destruct H1.
    specialize (H _ _ H1).
    clear H1 H2 y.
    dependent induction H0.
    + assumption.
    + now apply IHdrop.
  - destruct H as (_, ?H, _).
    destruct H0; simpl in *.
    apply H2 in H1.
    destruct H1.
    specialize (H _ _ H1).
    clear H1 H2 x.
    dependent induction H0.
    + assumption.
    + now apply IHdrop.
  - destruct H as (_, _, ?H).
    destruct H0; simpl in *.
    clear H0 h.
    intros x.
    specialize (H (n + x)).
    replace (Acc R) with (SN (transp R)) in H by auto.
    remember (n + x) as i.
    generalize dependent x.
    induction H using SN_ind.
    intros; subst.
    constructor; intros y ?.
    eapply H2; eauto.
    apply H1 in H0.
    destruct H0.
    apply t_step.
    assumption.
Qed.

(* -------------------------------------------------------------------------- *)

Definition env_singleton (n: nat) (t: type) := {|
  env_nodes := repeat None n ++ [Some t];
  env_edges x y := False
|}.

Definition env_singleton_holes:
  forall i t n,
  n <> i ->
  nth i (env_singleton n t) None = None.
Proof.
  intros.
  destruct (lt_eq_lt_dec n i) as [ [ ? | ? ] | ? ].
  - unfold env_singleton; simpl.
    rewrite app_nth2.
    + rewrite repeat_length.
      remember (i - n) as m.
      destruct m.
      * exfalso.
        lia.
      * now destruct m.
    + rewrite repeat_length.
      lia.
  - exfalso.
    contradiction.
  - unfold env_singleton; simpl.
    rewrite app_nth1.
    + apply nth_repeat.
    + now rewrite repeat_length.
Qed.

Definition env_singleton_is_always_coherent:
  forall g,
  env_wellformed g ->
  forall n t,
  nth n g None = None ->
  env_coherent g (env_singleton n t).
Proof.
  intros.
  constructor; intros.
  - exfalso.
    destruct (Nat.eq_dec n i); subst.
    + rewrite H0 in H1.
      inversion H1.
    + clear H0 H1 t1.
      rewrite env_singleton_holes in H2.
      * inversion H2.
      * assumption.
  - clear H0.
    intros x.
    apply env_wellformed_acyclic in H.
    specialize (H x).
    replace (Acc (env_edges g)) with (SN (transp (env_edges g))) in H by auto.
    induction H using SN_ind.
    constructor; intros y ?.
    apply H2.
    destruct H0.
    + apply t_step.
      assumption.
    + exfalso.
      inversion H0.
Qed.

Lemma env_singleton_composition_inversion:
  forall n g t h,
  env_composition_nodes g (env_singleton n t) h ->
  forall k,
  k <> n ->
  nth k g None = nth k h None.
Proof.
  induction n; simpl; intros.
  - dependent destruction H.
    + destruct k; try lia.
      now destruct k.
    + destruct k; try lia.
      now dependent destruction H.
    + destruct k; try lia.
      now dependent destruction H.
  - destruct k.
    + now dependent destruction H; simpl.
    + assert (k <> n) by lia.
      dependent destruction H; simpl.
      * clear IHn H0.
        generalize dependent k.
        induction n; destruct k; simpl; intros.
        --- exfalso; contradiction.
        --- now destruct k.
        --- reflexivity.
        --- now erewrite <- IHn with k by lia.
      * now apply IHn with t.
      * now apply IHn with t.
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

Inductive env_prefix_edges: nat -> nodes -> relation nat :=
  | env_prefix_edges_mk:
    forall n g y,
    active g y ->
    has_output_type g y ->
    env_prefix_edges n g n y.

Inductive env_prefix: nat -> type -> env -> env -> Prop :=
  | env_prefix_mk:
    forall n t g h R S,
    alternating I t ->
    nth n (env_nodes g) None = None ->
    env_composition g (env_singleton n t) h ->
    same_relation S (union R (env_prefix_edges n g)) ->
    env_prefix n t (env_mk g R) (env_mk h S).

Lemma env_prefix_preserves_wellformedness:
  forall n t g h,
  env_prefix n t g h ->
  env_wellformed g ->
  env_wellformed h.
Proof.
  intros.
  destruct H.
  constructor; intros.
  - destruct H0 as (?H, _, _); simpl in *.
    apply H3 in H4 as [ ?H | ?H ].
    + rename i into x, j into y.
      apply H0 in H4 as (ts, ?).
      destruct H2; simpl.
      exists ts.
      now apply env_composition_nodes_input_inversion with g h.
    + apply env_composition_is_commutative in H2.
      assert (has_input_type (env_singleton n t) i) as (ts, ?).
      * destruct H4.
        dependent destruction H.
        exists ts; simpl.
        clear H1 H2 H3 H0 H4 H5 y.
        induction n; eauto.
      * destruct H2; simpl.
        exists ts.
        eapply env_composition_nodes_input_inversion; eauto.
  - destruct H0 as (_, ?H, _); simpl in *.
    assert (j <> n).
    + intros ?H; subst.
      apply H3 in H4 as [ ?H | ?H ].
      * apply H0 in H4 as (ts, ?).
        rewrite H1 in H4.
        inversion H4.
      * dependent destruction H4.
        destruct H5 as (ts, ?).
        rewrite x, H1 in H5.
        inversion H5.
    + apply H3 in H4 as [ ?H | ?H ].
      * dependent destruction H2; simpl.
        apply H4 in H5 as (ts, ?).
        erewrite env_singleton_composition_inversion in H5; eauto.
        now exists ts.
      * dependent destruction H2; simpl.
        dependent destruction H5; simpl.
        destruct H6 as (ts, ?).
        rewrite x in H6; clear x.
        erewrite env_singleton_composition_inversion in H6; eauto.
        now exists ts.
  - destruct H0 as (?H, ?H, ?H); simpl in *.
    intros x.
    specialize (H5 x).
    replace (Acc R) with (SN (transp R)) in H5 by auto.
    induction H5 using SN_ind.
    constructor; intros.
    apply H3 in H7 as [ ? | ? ].
    + apply H6.
      apply t_step.
      assumption.
    + destruct H7 as (x, i, y, ?, ?).
      clear H5 H6.
      (* This has to be the last step. *)
      constructor; intros z ?.
      exfalso.
      apply H3 in H5 as [ ? | ? ].
      * apply H4 in H5 as (ts, ?).
        rewrite H1 in H5.
        inversion H5.
      * destruct H5 as (_, j, z, ?, ?).
        destruct H6 as (ts, ?).
        rewrite H1 in H6.
        inversion H6.
Qed.

(* -------------------------------------------------------------------------- *)

Definition env_mode (m: mode) (g: nodes): Prop :=
  forall i t,
  nth i g None = Some t ->
  get_mode t = m.

Inductive mode_composition: mode -> mode -> mode -> Prop :=
  | mode_composition_io:
    mode_composition I O O
  | mode_composition_oi:
    mode_composition O I O
  | mode_composition_ii:
    mode_composition I I I.

Inductive typing: mode -> term -> env -> Prop :=
  (*
    -------------- (ZERO)
      |-I 0 |>
  *)
  | typing_zero:
    typing I inactive env_empty

  (*
      |-(m) p |> G    |-(n) q |> H    G >< H    G * H = I    m * n = o
    -------------------------------------------------------------------- (PAR)
                              |-(o) (p | q) |> I

    TODO: maybe we should require that a composition only exists when the action
    types are coherent with each other, as composition by itself does not imply
    that there is no cycle in the resulting term.
  *)
  | typing_par:
    forall m n o p q g h i,
    typing m p g ->
    typing n q h ->
    env_coherent g h ->
    env_composition g h i ->
    mode_composition m n o ->
    typing o (parallel p q) i

  (*
       |-(m) p |> G, x: !(ts)
    ---------------------------- (RES)
      |-(m) (x: !(ts))(p) |> G
  *)
  | typing_res:
    forall m p g h t,
    typing m p g ->
    alternating I t ->
    nth 0 g None = Some t ->
    env_hiding 1 g h ->
    typing m (restriction t p) h

  (*
           |-(m) p |> G
    -------------------------- (WEAK)
      |-(m) p |> G, x: ?(ts)
  *)
  | typing_weak:
    forall m p g n t h,
    typing m p g ->
    alternating O t ->
    nth n g None = None ->
    env_composition g (env_singleton n t) h ->
    typing m p h

  (*
       |-O p |> G, ys: ts    md(G) = ?
    ------------------------------------- (IN)
      |-I !x(ys: ts).p |> x: !(ts) -> G
  *)
  | typing_in:
    forall p g n ts h i,
    typing O p g ->
    nth (length ts + n) g None = None ->
    env_mode O g ->
    Forall (alternating O) ts ->
    (* We're hiding ys from G, which only had output types, so it can't have any
       edge and thus all variables must be active. *)
    env_hiding (length ts) g h ->
    env_prefix n (channel I ts) h i ->
    typing I (replicated_input n ts p) i.

Lemma typing_env_wellformed:
  forall m p g,
  typing m p g ->
  env_wellformed g.
Proof.
  induction 1.
  - apply env_empty_is_wellformed.
  - now apply env_conherence_implies_wellformedness with g h.
  - now apply env_hiding_preserves_wellformedness with 1 g.
  - apply env_conherence_implies_wellformedness with g (env_singleton n t).
    + apply env_singleton_is_always_coherent.
      * assumption.
      * assumption.
    + assumption.
  - apply env_prefix_preserves_wellformedness with n (channel I ts) h.
    + assumption.
    + apply env_hiding_preserves_wellformedness with (length ts) g.
      * assumption.
      * assumption.
Qed.
