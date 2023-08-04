(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.Reduction.
(* TODO: we only use the convergency predicate from the following. Move it? *)
Require Import Local.Observational.

(** ** Type system *)

Definition env: Set :=
  list pseudoterm.

Inductive simple: pseudoterm -> Prop :=
  | simple_base:
    simple base
  | simple_negation:
    forall ts,
    Forall simple ts -> simple (negation ts).

Notation valid_env g :=
  (Forall simple g).

(* We are free to take a simpler definition here since we're only dealing with
   simple types. Reasoning about dependent types will require much more care! *)

Inductive typing: env -> relation pseudoterm :=
  | typing_bound:
    forall g n t,
    valid_env g ->
    item t g n ->
    typing g n t
  | typing_jump:
    forall g k xs ts,
    typing g k (negation ts) ->
    Forall2 (typing g) (rev xs) ts ->
    typing g (jump k xs) void
  | typing_bind:
    forall g b ts c,
    typing (negation ts :: g) b void ->
    typing (ts ++ g) c void ->
    typing g (bind b ts c) void.

Global Hint Constructors typing: cps.

Lemma valid_env_typing:
  forall g e t,
  typing g e t ->
  valid_env g.
Proof.
  induction 1.
  - assumption.
  - assumption.
  - dependent destruction IHtyping1.
    assumption.
Qed.

Lemma typing_bound_is_simple:
  forall g n t,
  typing g (bound n) t ->
  simple t.
Proof.
  intros.
  dependent destruction H.
  replace t with (nth n g void).
  - apply Forall_nth.
    + assumption.
    + apply item_valid_index with t.
      assumption.
  - apply nth_item.
    assumption.
Qed.

Lemma typing_bound_cant_be_void:
  forall g n,
  ~typing g (bound n) void.
Proof.
  intros g n ?.
  apply typing_bound_is_simple in H.
  inversion H.
Qed.

(* -------------------------------------------------------------------------- *)

Section Structural.

  (* TODO: the three proofs use almost identical cases for jump and bind; can we
     just generalize stuff a bit and avoid duplication in here? *)

  Variable R: env -> pseudoterm -> Prop.

  Definition WEAKENING: Prop :=
    forall g c,
    R g c ->
    forall t,
    simple t ->
    R (t :: g) (lift 1 0 c).

  Definition EXCHANGE: Prop :=
    forall g c,
    R g c ->
    forall n h,
    switch n g h ->
    R h (switch_bindings n c).

  Definition CONTRACTION: Prop :=
    forall g c t,
    R (t :: t :: g) c ->
    R (t :: g) (subst 0 0 c).

End Structural.

(* -------------------------------------------------------------------------- *)

Lemma valid_env_insert:
  forall u,
  simple u ->
  forall n g h,
  insert u n g h ->
  valid_env g <-> valid_env h.
Proof.
  induction 2; split; intros.
  - firstorder.
  - dependent destruction H0.
    assumption.
  - dependent destruction H1.
    firstorder.
  - dependent destruction H1.
    firstorder.
Qed.

Local Hint Resolve -> valid_env_insert: cps.

Lemma typing_lift1:
  forall e g t,
  typing g e t ->
  forall u n h,
  simple u ->
  insert u n g h ->
  typing h (lift 1 n e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - rename n0 into m.
    dependent destruction H.
    destruct (le_gt_dec m n).
    + rewrite lift_bound_ge; try lia.
      constructor; eauto with cps.
      eapply item_insert_ge; eauto.
    + rewrite lift_bound_lt; try lia.
      constructor; eauto with cps.
      eapply item_insert_lt; eauto.
  - inversion H0.
  - dependent destruction H0.
    rewrite lift_distributes_over_jump.
    econstructor.
    + apply IHe with g u; eauto.
    + clear IHe H0.
      apply Forall_rev in H.
      rewrite <- map_rev.
      generalize dependent ts.
      induction xs using rev_ind; intros.
      * simpl in H, H1 |- *.
        dependent destruction H1.
        constructor.
      * rewrite rev_app_distr in H, H1 |- *; simpl in H, H1 |- *.
        dependent destruction H.
        dependent destruction H1.
        constructor; eauto.
  - dependent destruction H0.
    rewrite lift_distributes_over_bind.
    constructor.
    + apply IHe1 with (negation ts :: g) u; eauto.
      replace (negation (traverse_list (lift 1) n ts)) with (negation ts).
      * constructor.
        assumption.
      * f_equal.
        apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        (* From H0. *)
        admit.
    + apply IHe2 with (ts ++ g) u; eauto.
      rewrite Nat.add_comm.
      replace (traverse_list (lift 1) n ts) with ts.
      * apply insert_app.
        assumption.
      * apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        (* From H0. *)
        admit.
Admitted.

Theorem weakening:
  WEAKENING (fun g c => typing g c void).
Proof.
  intros g c ? t ?.
  apply typing_lift1 with g t.
  - apply H.
  - assumption.
  - constructor.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma valid_env_switch_bindings:
  forall n g h,
  switch n g h ->
  valid_env g <-> valid_env h.
Proof.
  induction 1; split; intros.
  - dependent destruction H.
    dependent destruction H0.
    firstorder.
  - dependent destruction H.
    dependent destruction H0.
    firstorder.
  - dependent destruction H0.
    firstorder.
  - dependent destruction H0.
    firstorder.
Qed.

Local Hint Resolve -> valid_env_switch_bindings: cps.

Lemma typing_switch_bindings:
  forall e g t,
  typing g e t ->
  forall n h,
  switch n g h ->
  typing h (switch_bindings n e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - rename n0 into m.
    dependent destruction H.
    (* TODO: there's gotta be a better way... *)
    assert ((m > n) \/ (m = n) \/ (S m = n) \/ (S m < n))
      as [ ? | [ ? | [ ? | ? ] ] ] by lia.
    + unfold switch_bindings.
      rewrite lift_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      constructor; eauto with cps.
      admit.
    + dependent destruction H2.
      unfold switch_bindings.
      rewrite lift_bound_lt; try lia.
      rewrite subst_bound_eq; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite Nat.add_comm; simpl.
      constructor; eauto with cps.
      admit.
    + dependent destruction H2.
      unfold switch_bindings.
      rewrite lift_bound_lt; try lia.
      rewrite subst_bound_gt; try lia.
      constructor; eauto with cps.
      simpl.
      admit.
    + unfold switch_bindings.
      rewrite lift_bound_ge; try lia.
      rewrite subst_bound_gt; try lia.
      constructor; eauto with cps.
      simpl.
      admit.
  - inversion H0.
  - dependent destruction H0.
    rewrite switch_bindings_distributes_over_jump.
    econstructor.
    + apply IHe with g; eauto.
    + clear IHe H0.
      apply Forall_rev in H.
      rewrite <- map_rev.
      generalize dependent ts.
      induction xs using rev_ind; intros.
      * simpl in H, H1 |- *.
        dependent destruction H1.
        constructor.
      * rewrite rev_app_distr in H, H1 |- *; simpl in H, H1 |- *.
        dependent destruction H.
        dependent destruction H1.
        constructor; eauto.
  - dependent destruction H0.
    rewrite switch_bindings_distributes_over_bind.
    constructor.
    + apply IHe1 with (negation ts :: g); eauto.
      replace (negation (traverse_list switch_bindings n ts))
        with (negation ts).
      * constructor.
        assumption.
      * f_equal.
        apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        (* From H0. *)
        admit.
    + apply IHe2 with (ts ++ g); eauto.
      rewrite Nat.add_comm.
      replace (traverse_list switch_bindings n ts) with ts.
      * apply switch_app.
        assumption.
      * apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        (* From H0. *)
        admit.
Admitted.

Theorem exchange:
  EXCHANGE (fun g c => typing g c void).
Proof.
  intros g c ? n h ?.
  apply typing_switch_bindings with g.
  - assumption.
  - assumption.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma valid_env_join:
  forall n g h,
  join n g h ->
  valid_env g <-> valid_env h.
Proof.
  induction 1; split; intros.
  - dependent destruction H.
    assumption.
  - dependent destruction H.
    firstorder.
  - dependent destruction H0.
    firstorder.
  - dependent destruction H0.
    firstorder.
Qed.

Local Hint Resolve -> valid_env_join: cps.

Lemma typing_subst0:
  forall e g t,
  typing g e t ->
  forall n h,
  join n g h ->
  typing h (subst 0 n e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - rename n0 into m.
    dependent destruction H.
    destruct (lt_eq_lt_dec m n) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_gt; try lia.
      constructor; eauto with cps.
      admit.
    + dependent destruction e.
      rewrite subst_bound_eq; try lia.
      rewrite lift_bound_ge; try lia.
      replace (m + 0) with m; try lia.
      constructor; eauto with cps.
      admit.
    + rewrite subst_bound_lt; try lia.
      constructor; eauto with cps.
      admit.
  - inversion H0.
  - dependent destruction H0.
    rewrite subst_distributes_over_jump.
    econstructor.
    + apply IHe with g; eauto.
    + clear IHe H0.
      apply Forall_rev in H.
      rewrite <- map_rev.
      generalize dependent ts.
      induction xs using rev_ind; intros.
      * simpl in H, H1 |- *.
        dependent destruction H1.
        constructor.
      * rewrite rev_app_distr in H, H1 |- *; simpl in H, H1 |- *.
        dependent destruction H.
        dependent destruction H1.
        constructor; eauto.
  - dependent destruction H0.
    rewrite subst_distributes_over_bind.
    constructor.
    + apply IHe1 with (negation ts :: g); eauto.
      replace (negation (traverse_list (subst 0) n ts)) with (negation ts).
      * constructor.
        assumption.
      * f_equal.
        apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        (* From H0. *)
        admit.
    + apply IHe2 with (ts ++ g); eauto.
      rewrite Nat.add_comm.
      replace (traverse_list (subst 0) n ts) with ts.
      * apply join_app.
        assumption.
      * apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        (* From H0. *)
        admit.
Admitted.

Theorem contraction:
  CONTRACTION (fun g c => typing g c void).
Proof.
  intros g c t ?.
  apply typing_subst0 with (t :: t :: g).
  - assumption.
  - constructor.
Qed.

(* -------------------------------------------------------------------------- *)

Theorem progress:
  forall g b,
  typing g b void ->
  (exists k, converges b k) \/ (exists c, head b c).
Proof.
  intros.
  dependent induction H.
  - exfalso.
    eapply typing_bound_cant_be_void with g n.
    constructor; auto.
  - clear IHtyping.
    dependent destruction H.
    left; exists n.
    constructor.
  - clear IHtyping2.
    destruct IHtyping1; auto.
    + destruct H1 as (k, ?).
      destruct k.
      * right.
        admit.
      * left; exists k.
        constructor.
        assumption.
Admitted.

(* -------------------------------------------------------------------------- *)

Lemma valid_env_drop:
  forall n g h,
  drop n g h ->
  valid_env g -> valid_env h.
Proof.
  induction 1; intros.
  - dependent destruction H.
    assumption.
  - dependent destruction H0.
    firstorder.
Qed.

Local Hint Resolve valid_env_drop: cps.

Lemma typing_remove_binding:
  forall e g t,
  typing g e t ->
  forall n h,
  drop n g h ->
  not_free n e ->
  typing h (remove_binding n e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - rename n0 into m.
    dependent destruction H.
    unfold remove_binding.
    destruct (lt_eq_lt_dec m n) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_gt; try lia.
      constructor; eauto with cps.
      admit.
    + exfalso.
      dependent destruction H2.
      contradiction.
    + rewrite subst_bound_lt; try lia.
      constructor; eauto with cps.
      admit.
  - inversion H0.
  - unfold remove_binding.
    dependent destruction H0.
    dependent destruction H3.
    rewrite subst_distributes_over_jump.
    econstructor.
    + apply IHe with g; eauto.
    + clear IHe H0 H3.
      apply Forall_rev in H, H4.
      rewrite <- map_rev.
      generalize dependent ts.
      induction xs using rev_ind; intros.
      * simpl in H, H1, H4 |- *.
        dependent destruction H1.
        constructor.
      * rewrite rev_app_distr in H, H1, H4 |- *; simpl in H, H1, H4 |- *.
        dependent destruction H.
        dependent destruction H1.
        dependent destruction H4.
        constructor; eauto.
  - unfold remove_binding.
    dependent destruction H0.
    rewrite subst_distributes_over_bind.
    constructor.
    + apply IHe1 with (negation ts :: g); eauto.
      replace (negation (traverse_list (subst 0) n ts)) with (negation ts).
      * constructor.
        assumption.
      * f_equal.
        apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        (* From H0. *)
        admit.
      * dependent destruction H2.
        assumption.
    + apply IHe2 with (ts ++ g); eauto.
      rewrite Nat.add_comm.
      replace (traverse_list (subst 0) n ts) with ts.
      * apply drop_app.
        assumption.
      * apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        (* From H0. *)
        admit.
      * dependent destruction H2.
        rewrite Nat.add_comm.
        assumption.
Admitted.

Lemma typing_tidy:
  forall b c,
  tidy b c ->
  forall g,
  typing g b void ->
  typing g c void.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    eapply typing_remove_binding.
    + eassumption.
    + constructor.
    + assumption.
  - dependent destruction H0.
    constructor; auto.
  - dependent destruction H0.
    constructor; auto.
Qed.

Lemma typing_beta:
  forall b c,
  beta b c ->
  forall g,
  typing g b void ->
  typing g c void.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    constructor; auto.
    (* Hmmm... *)
    admit.
  - dependent destruction H0.
    constructor; auto.
  - dependent destruction H0.
    constructor; auto.
Admitted.

Theorem subject_reduction:
  forall b c,
  step b c ->
  forall g,
  typing g b void ->
  typing g c void.
Proof.
  intros.
  apply step_characterization in H.
  destruct H.
  - apply typing_beta with b; auto.
  - apply typing_tidy with b; auto.
Qed.

(* -------------------------------------------------------------------------- *)

(* Ohh... I think I made a mistake... *)

Goal
  (* We do NOT have subject expansion! *)
  exists b c,
  beta b c /\ typing [negation []] c void /\ ~typing [negation []] b void.
Proof.
  (*
    k: ~() |- j<j> { j<x> = k<> }   --->   k: ~() |- k<> { j<x> = k<> }
  *)
  exists (bind (jump 0 [bound 0]) [base] (jump 1 [])).
  exists (bind (jump 1 []) [base] (jump 1 [])).
  repeat split.
  - apply (beta_ctxjmp context_hole).
    reflexivity.
  - repeat econstructor.
  - intros ?.
    dependent destruction H.
    dependent destruction H.
    dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    dependent destruction H0.
    dependent destruction H1.
Qed.
