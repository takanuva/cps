(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Observational.

Import ListNotations.

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
    Forall2 (typing g) xs ts ->
    typing g (jump k xs) void
  | typing_bind:
    forall g b ts c,
    typing (negation ts :: g) b void ->
    typing (ts ++ g) c void ->
    typing g (bind b ts c) void.

Global Hint Constructors typing: cps.

Goal
  let G := [base; base; base; negation [base; base]] in
  typing G ex1 void.
Proof.
  compute.
  repeat econstructor.
Qed.

Goal
  let G := [base; base; base; negation [base; base]] in
  typing G ex2 void.
Proof.
  compute.
  repeat econstructor.
Qed.

Goal
  let G := [base; base; base; negation [base; base]] in
  typing G ex3 void.
Proof.
  compute.
  repeat econstructor.
Qed.

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

Lemma simple_types_ignore_substitution:
  forall t,
  simple t ->
  forall s,
  t = inst s t.
Proof.
  induction t using pseudoterm_deepind; intros.
  - inversion H.
  - dependent destruction H0.
    + reflexivity.
    + sigma; f_equal.
      induction H; auto.
      dependent destruction H0.
      simpl; f_equal.
      * sigma; auto.
      * auto.
  - inversion H0.
  - inversion H0.
Qed.

Lemma simple_env_ignores_lift:
  forall ts,
  valid_env ts ->
  forall i k,
  ts = traverse_list (lift i) k ts.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - f_equal; auto.
    rewrite traverse_list_length.
    sigma.
    now apply simple_types_ignore_substitution.
Qed.

Lemma simple_env_ignores_subst:
  forall ts,
  valid_env ts ->
  forall y k,
  ts = traverse_list (subst y) k ts.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - f_equal; auto.
    rewrite traverse_list_length.
    sigma.
    now apply simple_types_ignore_substitution.
Qed.

Lemma not_free_typing:
  forall b g t,
  typing g b t ->
  forall k,
  k >= length g ->
  not_free k b.
Proof.
  induction b using pseudoterm_deepind; intros.
  - dependent destruction H.
    apply item_valid_index in H0.
    constructor.
    lia.
  - inversion H0.
  - dependent destruction H0.
    constructor.
    + eapply IHb; eauto.
    + clear H0 IHb.
      generalize dependent ts.
      induction H; intros.
      * constructor.
      * dependent destruction H1.
        constructor; eauto.
  - dependent destruction H0.
    constructor.
    + eapply IHb1; eauto.
      simpl; lia.
    + apply valid_env_typing in H0_.
      dependent destruction H0_.
      dependent destruction H0.
      clear H IHb1 IHb2 H0_ H0_0 H1 b1 b2 g.
      (* Of course, simple types never have free variables. *)
      admit.
    + eapply IHb2; eauto.
      rewrite app_length; lia.
Admitted.

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
    R (t :: g) (subst (bound 0) 0 c).

End Structural.

(* -------------------------------------------------------------------------- *)

Lemma valid_env_insert:
  forall ts,
  Forall simple ts ->
  forall n g h,
  insert ts n g h ->
  valid_env g <-> valid_env h.
Proof.
  induction 2; split; intros.
  - apply Forall_app.
    now split.
  - clear H.
    induction ts; simpl in H0.
    + assumption.
    + dependent destruction H0.
      now apply IHts.
  - dependent destruction H1.
    constructor.
    + assumption.
    + now apply IHinsert.
  - dependent destruction H1.
    constructor.
    + assumption.
    + now apply IHinsert.
Qed.

Local Hint Resolve -> valid_env_insert: cps.

Lemma typing_lift:
  forall e g t,
  typing g e t ->
  forall us k,
  valid_env us ->
  forall h,
  insert us k g h ->
  typing h (lift (length us) k e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
  - dependent destruction H.
    destruct (le_gt_dec k n).
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
    + eapply IHe; eauto.
    + clear IHe H0.
      generalize dependent ts.
      induction xs; intros.
      * simpl in H, H1 |- *.
        dependent destruction H1.
        constructor.
      * simpl in H, H1 |- *.
        dependent destruction H.
        dependent destruction H1.
        constructor; eauto.
  - dependent destruction H0.
    rewrite lift_distributes_over_bind.
    constructor.
    + replace (negation (traverse_list (lift (length us)) k ts)) with
        (negation ts).
      * eapply IHe1; eauto.
        now constructor.
      * f_equal.
        apply simple_env_ignores_lift.
        apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        assumption.
    + replace (traverse_list (lift (length us)) k ts) with ts.
      * eapply IHe2; eauto.
        rewrite Nat.add_comm.
        now apply insert_app.
      * apply simple_env_ignores_lift.
        apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        assumption.
Qed.

Theorem weakening:
  WEAKENING (fun g c => typing g c void).
Proof.
  intros g c ? t ?.
  replace 1 with (length [t]) by auto.
  apply typing_lift with g.
  - assumption.
  - auto.
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
  - rename n0 into m.
    dependent destruction H.
    (* TODO: there's gotta be a better way... *)
    assert ((m > n) \/ (m = n) \/ (S m = n) \/ (S m < n))
      as [ ? | [ ? | [ ? | ? ] ] ] by lia.
    + unfold switch_bindings.
      sigma.
      constructor; eauto with cps.
      admit.
    + dependent destruction H2.
      unfold switch_bindings.
      sigma.
      constructor; eauto with cps.
      admit.
    + dependent destruction H2.
      unfold switch_bindings.
      sigma.
      constructor; eauto with cps.
      admit.
    + unfold switch_bindings.
      sigma.
      replace (S (S (m + n)) - m - 2) with n by lia.
      constructor; eauto with cps.
      admit.
  - inversion H0.
  - dependent destruction H0.
    rewrite switch_bindings_distributes_over_jump.
    econstructor.
    + apply IHe with g; eauto.
    + clear IHe H0.
      generalize dependent ts.
      induction xs; intros.
      * simpl in H, H1 |- *.
        dependent destruction H1.
        constructor.
      * simpl in H, H1 |- *.
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
  typing h (subst (bound 0) n e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
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
      generalize dependent ts.
      induction xs; intros.
      * simpl in H, H1 |- *.
        dependent destruction H1.
        constructor.
      * simpl in H, H1 |- *.
        dependent destruction H.
        dependent destruction H1.
        constructor; eauto.
  - dependent destruction H0.
    rewrite subst_distributes_over_bind.
    constructor.
    + apply IHe1 with (negation ts :: g); eauto.
      replace (negation (traverse_list (subst (bound 0)) n ts)) with
        (negation ts).
      * constructor.
        assumption.
      * f_equal.
        apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        apply simple_env_ignores_subst.
        assumption.
    + apply IHe2 with (ts ++ g); eauto.
      rewrite Nat.add_comm.
      replace (traverse_list (subst (bound 0)) n ts) with ts.
      * apply join_app.
        assumption.
      * apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        apply simple_env_ignores_subst.
        assumption.
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

Lemma typing_implies_correct_arity:
  forall (h: context) ts g xs,
  typing (negation ts :: g) (h (jump #h xs)) void ->
  length xs = length ts.
Proof.
  (* Of course we have to generalize our induction a bit. *)
  assert (forall (h: context) n ts g xs,
    item (negation ts) g n ->
    typing g (h (jump (n + #h) xs)) void ->
    length xs = length ts).
  - induction h; simpl; intros.
    + rewrite Nat.add_comm in H0; simpl in H0.
      dependent destruction H0.
      dependent destruction H0.
      rename ts0 into us.
      assert (negation ts = negation us).
      * eapply item_unique; eauto.
      * dependent destruction H3; clear H1.
        apply Forall2_length in H2.
        assumption.
    + rename ts0 into us.
      dependent destruction H0.
      apply IHh with (S n) (negation ts :: g).
      * auto with cps.
      * replace (S n + #h) with (n + S #h); try lia.
        assumption.
    + rename ts0 into us.
      dependent destruction H0.
      apply IHh with (length ts + n) (ts ++ g).
      * rewrite Nat.add_comm.
        apply item_insert_head.
        assumption.
      * replace (length ts + n + #h) with (n + (#h + length ts)); try lia.
        assumption.
  (* There we go, now we can show it. *)
  - intros.
    eapply H with (g := negation ts :: g) (n := 0).
    + constructor.
    + eassumption.
Qed.

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
    destruct IHtyping1 as [ (k, ?) | (d, ?) ]; auto.
    + destruct k.
      * dependent destruction H1 using converges_inv; simpl.
        right; eexists.
        apply head_longjmp with (r := context_hole); auto with cps.
        eapply typing_implies_correct_arity; eauto.
      * left; exists k.
        constructor; auto.
    + right; eexists.
      apply head_bind_left; eauto.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma valid_env_drop:
  forall k n g h,
  drop k n g h ->
  valid_env g -> valid_env h.
Proof.
  induction 1; intros.
  - assumption.
  - dependent destruction H0.
    firstorder.
  - dependent destruction H0.
    firstorder.
Qed.

Local Hint Resolve valid_env_drop: cps.

Lemma typing_remove_binding:
  forall e g t,
  typing g e t ->
  forall k h,
  drop k 1 g h ->
  not_free k e ->
  typing h (remove_binding k e) t.
Proof.
  induction e using pseudoterm_deepind; intros.
  - dependent destruction H.
    unfold remove_binding.
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
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
      generalize dependent ts.
      induction xs; intros.
      * simpl in H, H1, H4 |- *.
        dependent destruction H1.
        constructor.
      * simpl in H, H1, H4 |- *.
        dependent destruction H.
        dependent destruction H1.
        dependent destruction H4.
        constructor; eauto.
  - unfold remove_binding.
    dependent destruction H0.
    rewrite subst_distributes_over_bind.
    constructor.
    + apply IHe1 with (negation ts :: g); eauto.
      replace (negation (traverse_list (subst (bound 0)) k ts)) with
        (negation ts).
      * constructor.
        assumption.
      * f_equal.
        apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        apply simple_env_ignores_subst.
        assumption.
      * dependent destruction H2.
        assumption.
    + apply IHe2 with (ts ++ g); eauto.
      rewrite Nat.add_comm.
      replace (traverse_list (subst (bound 0)) k ts) with ts.
      * apply drop_app.
        assumption.
      * apply valid_env_typing in H0_.
        dependent destruction H0_.
        dependent destruction H0.
        apply simple_env_ignores_subst.
        assumption.
      * dependent destruction H2.
        rewrite Nat.add_comm.
        assumption.
Admitted.

Lemma typing_smol:
  forall b c,
  smol b c ->
  forall g,
  typing g b void ->
  typing g c void.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    eapply typing_remove_binding.
    + eassumption.
    + repeat constructor.
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
  - apply typing_smol with b; auto.
Qed.

(* -------------------------------------------------------------------------- *)

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
  - apply beta_ctxjmp with (h := context_hole).
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
