(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
(* TODO: perhaps some definitions should be moved to Syntax. *)
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Axiomatic.

(** ** Beta (generalized jump) reduction. *)

(*
  We have four assumptions: j, x, y, z.

  For (CTXJMP):

    \j.\x.\y.\z.                         \j.\x.\y.\z.
      k@0<x@3, y@2>                        j@4<x@3, y@2, z@1>
      { k<a, b> =                 =>       { k<a, b> =
          j@5<a@1, b@0, z@2> }                 j@5<a@1, b@0, z@2> }

    Does it make sense to keep the continuation binding there on a simply typed
    environment? I.e., does k<..., k, ...> ever make sense? I don't think there
    can be a (simple) type for that... oh, now I get it!

  On our notion of reduction:

    In Thielecke's dissertation, he briefly suggested directed versions of the
    (DISTR) and (JMP) rules as the -` and -> relations and the reduction would
    be then given by -`* ->*. Notice of course that the (JMP) rule always jumps
    to the immediate (closest) continuation. Merro later studies the calculus
    and gives a long jump form, with ki<xs> { k1<ys> = K1 } ... { kn<ys> = Kn }
    reducing to Ki[xs/ys] { k1<ys> = K1 } ... { kn<ys> = Kn }, which is a really
    useful generalization. We'll probably take a similar notion of reduction, as
    distr-redexes always are possible and, worse, they duplicate jmp-redexes,
    thus -`* ->* may only be weakly normalizing at best (there's always an
    infinite sequence).

    Question: do those two notions of reduction commute? I.e., is it possible to
    get terms a -`* b ->* c such that for all a there exists b and c where there
    are no longjmp-redexes in c? I don't think so.
*)

Definition CTXJMP (R: relation pseudoterm): Prop :=
  forall (h: context) xs ts c,
  length xs = length ts ->
  R (bind (h (jump #h xs)) ts c)
    (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c).

Global Hint Unfold CTXJMP: cps.

(*
  The following is called (CONT-BETA) in Kennedy's paper, where it is presented
  as a rewriting rule, so we'll name it simply [beta] here. In fact, it's really
  similar to how beta reduction acts in explicit substitution calculi. Compare
  also to the reduction used for the pi-calculus in Yoshida's paper, where it
  represents the replication law.
*)

Inductive beta: relation pseudoterm :=
  | beta_ctxjmp:
    CTXJMP beta
  | beta_bind_left:
    LEFT beta
  | beta_bind_right:
    RIGHT beta.

Global Hint Constructors beta: cps.

Lemma beta_recjmp:
  RECJMP beta.
Proof.
  unfold RECJMP; intros.
  replace c with (lift 0 (length ts) c) at 2.
  - rewrite lift_lift_simplification; try lia.
    apply beta_ctxjmp with (h := context_hole); auto.
  - apply lift_zero_e_equals_e.
Qed.

Global Hint Resolve beta_recjmp: cps.

Local Lemma beta_ctxjmp_helper:
  forall h r,
  r = h ->
  forall xs ts c,
  length xs = length ts ->
  forall n,
  n = #h ->
  forall a,
  a = jump n xs ->
  forall b,
  b = apply_parameters xs 0 (lift (S n) (length ts) c) ->
  forall ts',
  ts' = ts ->
  forall c',
  c' = c ->
  beta (bind (h a) ts c) (bind (r b) ts' c').
Proof.
  intros.
  rewrite H, H2, H3, H4, H5, H1.
  apply beta_ctxjmp.
  assumption.
Qed.

Lemma beta_lift:
  forall a b,
  beta a b ->
  forall i k,
  beta (lift i k a) (lift i k b).
Proof.
  induction 1; intros.
  - do 2 rewrite lift_distributes_over_bind.
    do 2 rewrite context_lift_is_sound.
    rewrite lift_distributes_over_jump.
    rewrite lift_bound_lt; try lia.
    rewrite lift_distributes_over_apply_parameters.
    eapply beta_ctxjmp_helper with (xs := map _ xs).
    + reflexivity.
    + rewrite map_length.
      rewrite traverse_list_length.
      assumption.
    + reflexivity.
    + f_equal; auto with cps.
    + f_equal; symmetry.
      rewrite lift_lift_permutation.
      * assert (#h = #(context_lift i (S k) h)); auto with cps.
        f_equal; try lia.
        f_equal; auto.
        apply traverse_list_length.
      * rewrite traverse_list_length; lia.
    + reflexivity.
    + reflexivity.
  - do 2 rewrite lift_distributes_over_bind.
    apply beta_bind_left.
    apply IHbeta.
  - do 2 rewrite lift_distributes_over_bind.
    apply beta_bind_right.
    apply IHbeta.
Qed.

Global Hint Resolve beta_lift: cps.

Lemma beta_subst:
  forall a b,
  beta a b ->
  forall y k,
  beta (subst y k a) (subst y k b).
Proof.
  induction 1; intros.
  - do 2 rewrite subst_distributes_over_bind.
    do 2 rewrite context_subst_is_sound.
    rewrite subst_distributes_over_jump.
    rewrite subst_bound_lt; try lia.
    rewrite subst_distributes_over_apply_parameters.
    eapply beta_ctxjmp_helper with (xs := map _ xs).
    + reflexivity.
    + rewrite map_length.
      rewrite traverse_list_length.
      assumption.
    + reflexivity.
    + f_equal; auto with cps.
    + f_equal; symmetry.
      rewrite lift_and_subst_commute.
      * assert (#h = #(context_subst y (S k) h)); auto with cps.
        f_equal; try lia.
        f_equal; auto.
        apply traverse_list_length.
      * rewrite traverse_list_length; lia.
    + reflexivity.
    + reflexivity.
  - do 2 rewrite subst_distributes_over_bind.
    apply beta_bind_left.
    apply IHbeta.
  - do 2 rewrite subst_distributes_over_bind.
    apply beta_bind_right.
    apply IHbeta.
Qed.

Global Hint Resolve beta_subst: cps.

Lemma beta_apply_parameters:
  forall xs k a b,
  beta a b ->
  beta (apply_parameters xs k a) (apply_parameters xs k b).
Proof.
  induction xs; intros.
  - simpl.
    assumption.
  - simpl.
    apply IHxs.
    apply beta_subst.
    assumption.
Qed.

Global Hint Resolve beta_apply_parameters: cps.

Lemma beta_lift_inversion:
  forall i k a b,
  beta (lift i k a) b ->
  exists b',
  b = lift i k b'.
Proof.
  intros.
  dependent induction H.
  - destruct a; try discriminate.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in x; try lia.
        discriminate.
      * rewrite lift_bound_lt in x; try lia.
        discriminate.
    + rewrite lift_distributes_over_bind in x.
      dependent destruction x.
      rewrite traverse_list_length in H |- *.
      edestruct context_equals_lift_inversion as (r, ?, ?, a3, ?); eauto.
      (* TODO: this works but PLEASE clean up this mess! I'm too tired. *)
      destruct a3; try discriminate.
      exfalso.
      destruct (le_gt_dec (#h + S k) n).
      rewrite lift_bound_ge in H2; try lia.
      discriminate.
      rewrite lift_bound_lt in H2; try lia.
      discriminate.
      rewrite lift_distributes_over_jump in H2.
      dependent destruction H2.
      clear a3 x H0.
      rewrite context_lift_bvars in H, x0 |- *.
      rewrite map_length in H.
      eexists (bind (r _) _ _).
      rewrite lift_distributes_over_bind.
      rewrite context_lift_is_sound; f_equal; f_equal.
      rewrite lift_distributes_over_apply_parameters.
      rewrite lift_lift_permutation; try lia.
      f_equal; f_equal; lia.
  - destruct a; try discriminate.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in x; try lia.
        discriminate.
      * rewrite lift_bound_lt in x; try lia.
        discriminate.
    + rewrite lift_distributes_over_bind in x.
      dependent destruction x.
      edestruct IHbeta as (b2', ?); eauto.
      eexists (bind b2' _ _).
      rewrite lift_distributes_over_bind; f_equal.
      assumption.
  - destruct a; try discriminate.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in x; try lia.
        discriminate.
      * rewrite lift_bound_lt in x; try lia.
        discriminate.
    + rewrite lift_distributes_over_bind in x.
      dependent destruction x.
      edestruct IHbeta as (c2', ?); eauto.
      eexists (bind _ _ c2').
      rewrite lift_distributes_over_bind; f_equal.
      assumption.
Qed.

Lemma beta_unlift:
  forall i k a b,
  beta (lift i k a) (lift i k b) ->
  beta a b.
Proof.
  induction i; intros.
  - do 2 rewrite lift_zero_e_equals_e in H.
    assumption.
  - rewrite <- lift_zero_e_equals_e with (k := k) (e := a).
    rewrite <- lift_zero_e_equals_e with (k := k) (e := b).
    rewrite <- subst_lift_simplification with (y := 0) (p := k) (e := a);
      try lia.
    rewrite <- subst_lift_simplification with (y := 0) (p := k) (e := b);
      try lia.
    apply beta_subst.
    apply IHi with k.
    rewrite lift_lift_simplification; try lia.
    rewrite lift_lift_simplification; try lia.
    rewrite Nat.add_comm; simpl.
    assumption.
Qed.

Lemma not_free_beta:
  forall b c,
  beta b c ->
  forall k,
  not_free k b -> not_free k c.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    constructor; auto.
    (* Tricky, tricky induction! *)
    rewrite <- H.
    rewrite <- H in H0_0.
    clear H H0 ts.
    replace #h with (#h + 0) in H0_; auto with arith.
    replace (S n) with (S n + 0) in H0_; auto with arith.
    replace (S n) with (S n + 0); auto with arith.
    replace (S #h) with (S #h + 0); auto.
    generalize dependent H0_.
    generalize O at 1 2 3 5 as o; simpl.
    induction h; intros.
    + simpl in H0_ |- *.
      replace (S (n + o)) with (S (n + o) + 0); auto.
      apply not_free_apply_parameters.
      * dependent destruction H0_.
        assumption.
      * rewrite Nat.add_0_r.
        replace (S (n + o) + length xs) with (n + (S o) + length xs); try lia.
        apply not_free_lift.
        rewrite Nat.add_comm.
        assumption.
    + simpl in H0_ |- *.
      dependent destruction H0_.
      constructor.
      * replace (S (S (n + o))) with (S (n + S o)); try lia.
        replace (S (S (#h + o))) with (S (#h + S o)); try lia.
        apply IHh.
        replace (S (n + S o)) with (S (S (n + o))); try lia.
        replace (#h + S o) with (S (#h + o)); try lia.
        assumption.
      * assumption.
      * assumption.
    + simpl in H0_ |- *.
      dependent destruction H0_.
      constructor.
      * assumption.
      * assumption.
      * replace (length ts + S (n + o)) with (S (n + (length ts + o))); try lia.
        replace (S (#h + length ts + o)) with (S (#h + (length ts + o)));
          try lia.
        apply IHh.
        replace (S (n + (length ts + o))) with (length ts + S (n + o));
          try lia.
        replace (#h + (length ts + o)) with (#h + length ts + o); try lia.
        assumption.
  - dependent destruction H0; auto with cps.
  - dependent destruction H0; auto with cps.
Qed.

(*
  This lemma shows that "free jumps" are preserved in redexes. If we have a
  context H, and the term H[k<xs>] reduces to a term e, given that k is free in
  the hole of H, then e will keep the subterm k<xs>, i.e., there is a R such
  that e = R[k<xs>] and both R and H will bind the same variables in their
  respective holes. This version is specialized for jumps alone.
*)
Lemma beta_noninterference:
  forall h: context,
  forall n,
  n >= #h ->
  forall xs e,
  beta (h (jump n xs)) e ->
  exists2 r: context,
  e = r (jump n xs) & same_path h r.
Proof.
  induction h; simpl; intros.
  (* Case: context_hole. *)
  - exfalso.
    inversion H0.
  (* Case: context_left. *)
  - dependent destruction H0.
    + rename h0 into r.
      assert (h <> r).
      * destruct 1.
        apply context_is_injective in x; auto.
        inversion x; lia.
      * edestruct context_difference as (s, (?, ?)); eauto.
        eexists (context_left s ts c); intuition.
        simpl; f_equal; eassumption.
    + destruct IHh with n xs b2; eauto with arith.
      rewrite H1.
      eexists (context_left x ts c); auto with cps.
    + eexists (context_left h ts c2); auto with cps.
  (* Case: context_right. *)
  - dependent destruction H0.
    + rename h0 into r.
      eexists (context_right _ ts h).
      * simpl; f_equal.
      * auto with cps.
    + eexists (context_right b2 ts h); auto with cps.
    + destruct IHh with n xs c2; eauto with arith.
      rewrite H1.
      eexists (context_right b ts x); auto with cps.
Qed.

Lemma rt_beta_bind_left:
  LEFT rt(beta).
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve rt_beta_bind_left: cps.

Lemma rt_beta_bind_right:
  RIGHT rt(beta).
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve rt_beta_bind_right: cps.

(** ** Tidying reduction. *)

(* TODO: as of now, I conjecture that by adding (ETA) and a generalized (CONTR)
   reduction in here will make our reduction semantics complete with regard to
   the original axiomatic semantics. However, these two complicate the theory
   so lets skip them for now. In the future, we should add those here. *)

Inductive tidy: relation pseudoterm :=
  | tidy_gc:
    GC tidy
  | tidy_bind_left:
    LEFT tidy
  | tidy_bind_right:
    RIGHT tidy.

Global Hint Constructors tidy: cps.

Lemma tidy_context:
  forall a b,
  tidy a b ->
  forall h: context,
  tidy (h a) (h b).
Proof.
  induction h; eauto with cps.
Qed.

Lemma tidy_lift:
  forall a b,
  tidy a b ->
  forall i k,
  tidy (lift i k a) (lift i k b).
Proof.
  (* There's a similar proof on [Axiomatic.v]! *)
  admit.
Admitted.

Lemma tidy_subst:
  forall a b,
  tidy a b ->
  forall y k,
  tidy (subst y k a) (subst y k b).
Proof.
  (* There's a similar proof on [Axiomatic.v]! *)
  admit.
Admitted.

Lemma tidy_apply_parameters:
  forall a b,
  tidy a b ->
  forall xs k,
  tidy (apply_parameters xs k a) (apply_parameters xs k b).
Proof.
  intros.
  generalize dependent k.
  generalize dependent b.
  generalize dependent a.
  induction xs; intros.
  - simpl.
    assumption.
  - simpl.
    apply IHxs.
    apply tidy_subst.
    assumption.
Qed.

Lemma not_free_tidy:
  forall b c,
  tidy b c ->
  forall k,
  not_free k b -> not_free k c.
Proof.
  induction 1; intros.
  - (* We have to change our goal a bit to keep track of which variable we're
       claiming can't appear free. This is trickier in the de Bruijn setting. *)
    replace k with (k + 0) in H0; auto with arith.
    replace k with (k + 0); auto with arith.
    dependent destruction H0.
    simpl in H0_; clear H0 H0_0 ts c.
    generalize dependent k; intro.
    generalize dependent b; intro.
    generalize O as o; simpl.
    unfold remove_binding.
    induction b using pseudoterm_deepind; intros.
    + constructor.
    + constructor.
    + constructor.
    + constructor.
    + dependent destruction H.
      dependent destruction H0_.
      rename n0 into m.
      destruct (lt_eq_lt_dec m n) as [ [ ? | ? ] | ? ].
      * rewrite subst_bound_gt; auto.
        constructor; lia.
      * exfalso; lia.
      * rewrite subst_bound_lt; auto.
        constructor; lia.
    + rewrite subst_distributes_over_negation.
      constructor.
      dependent destruction H0.
      dependent destruction H0_.
      induction H; auto with cps.
      simpl.
      dependent destruction H0.
      dependent destruction H3.
      constructor; auto.
      rewrite traverse_list_length.
      replace (length l + (k + n)) with (k + (length l + n)); try lia.
      apply H; auto.
      replace (S (k + (length l + n))) with (length l + S (k + n)); try lia.
      assumption.
    + rewrite subst_distributes_over_jump.
      dependent destruction H0.
      dependent destruction H0_.
      constructor; auto.
      clear IHb H0 H0_ b.
      induction H.
      * constructor.
      * simpl.
        dependent destruction H1.
        dependent destruction H3.
        constructor; auto.
    + rewrite subst_distributes_over_bind.
      dependent destruction H0.
      dependent destruction H0_1.
      constructor.
      * replace (S (k + n)) with (k + S n); try lia.
        replace (S (S (k + n))) with (S (k + S n)) in H0_1_1; try lia.
        apply IHb1; auto.
      * clear H0_ H0_0 H0_1_1 H0_1_2 IHb1 IHb2 b1 b2.
        induction H; auto with cps.
        simpl.
        dependent destruction H0.
        dependent destruction H3.
        constructor; auto.
        rewrite traverse_list_length.
        replace (length l + (k + n)) with (k + (length l + n)); try lia.
        apply H; auto.
        replace (S (k + (length l + n))) with (length l + S (k + n)); try lia.
        assumption.
      * rewrite traverse_list_length.
        replace (length ts + (k + n)) with (k + (n + length ts)); try lia.
        replace (length ts + n) with (n + length ts) in H0_0; try lia.
        replace (length ts + S (k + n)) with (S (k + (n + length ts)))
          in H0_1_2; try lia.
        apply IHb2; auto.
  - dependent destruction H0; auto with cps.
  - dependent destruction H0; auto with cps.
Qed.

Lemma rt_tidy_bind_left:
  LEFT rt(tidy).
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve rt_tidy_bind_left: cps.

Lemma rt_tidy_bind_right:
  RIGHT rt(tidy).
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve rt_tidy_bind_right: cps.

(** ** One-step reduction. *)

Inductive step: relation pseudoterm :=
  | step_ctxjmp:
    CTXJMP step
  | step_gc:
    GC step
  | step_bind_left:
    LEFT step
  | step_bind_right:
    RIGHT step.

Global Hint Constructors step: cps.

Notation "[ a => b ]" := (step a b)
  (at level 0, a, b at level 200): type_scope.

(*
    \j.\x.\y.\z.                         \j.\x.\y.\z.
      h@1<x@4, k@0, y@3>                   k@0<y@3, z@2>
      { k<a, b> =                 =>       { k<a, b> =
          h@2<b@0, j@6, a@1> }                 h@2<b@0, j@6, a@1> }
      { h<c, d, e> =                       { h<c, d, e> =
          d@1<e@0, z@3> }                      d@1<e@0, z@3> }
*)

Example ex3: pseudoterm :=
  (bind (bind
    (jump 0 [bound 2; bound 3])
    [base; base]
      (jump 2 [bound 1; bound 6; bound 0]))
    [base; negation [base; base]; base]
      (jump 1 [bound 3; bound 0])).

Goal [ex1 => ex3].
Proof.
  apply step_ctxjmp with (h := context_left context_hole ?[ts] ?[c]); auto.
Qed.

Lemma step_characterization:
  same_relation step (union beta tidy).
Proof.
  split; do 3 intro.
  - induction H.
    + left; auto with cps.
    + right; auto with cps.
    + destruct IHstep; auto with cps.
    + destruct IHstep; auto with cps.
  - destruct H.
    + induction H.
      * auto with cps.
      * auto with cps.
      * auto with cps.
    + induction H.
      * auto with cps.
      * auto with cps.
      * auto with cps.
Qed.

Lemma step_beta:
  inclusion beta step.
Proof.
  unfold inclusion; intros.
  apply step_characterization; left.
  assumption.
Qed.

Global Hint Resolve step_beta: cps.

Lemma step_tidy:
  inclusion tidy step.
Proof.
  unfold inclusion; intros.
  apply step_characterization; right.
  assumption.
Qed.

Global Hint Resolve step_tidy: cps.

Lemma step_recjmp:
  RECJMP step.
Proof.
  auto with cps.
Qed.

Global Hint Resolve step_recjmp: cps.

Lemma step_lift:
  forall a b,
  [a => b] ->
  forall i k,
  [lift i k a => lift i k b].
Proof.
  intros.
  apply step_characterization in H.
  destruct H.
  - apply step_characterization; left.
    apply beta_lift; auto.
  - apply step_characterization; right.
    apply tidy_lift; auto.
Qed.

Global Hint Resolve step_lift: cps.

Lemma step_subst:
  forall a b,
  [a => b] ->
  forall y k,
  [subst y k a => subst y k b].
Proof.
  intros.
  apply step_characterization in H.
  destruct H.
  - apply step_characterization; left.
    apply beta_subst; auto.
  - apply step_characterization; right.
    apply tidy_subst; auto.
Qed.

Global Hint Resolve step_subst: cps.

Lemma step_apply_parameters:
  forall xs k a b,
  [a => b] ->
  [apply_parameters xs k a => apply_parameters xs k b].
Proof.
  induction xs; intros.
  - simpl.
    assumption.
  - simpl.
    apply IHxs.
    apply step_subst.
    assumption.
Qed.

Global Hint Resolve step_apply_parameters: cps.

(** ** Multi-step reduction *)

Notation star := rt(step).
Notation "[ a =>* b ]" := (star a b)
  (at level 0, a, b at level 200): type_scope.

Lemma star_step:
  forall a b,
  [a => b] -> [a =>* b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve star_step: cps.

Lemma star_recjmp:
  RECJMP star.
Proof.
  auto with cps.
Qed.

Global Hint Resolve star_recjmp: cps.

Lemma star_ctxjmp:
  CTXJMP star.
Proof.
  auto with cps.
Qed.

Global Hint Resolve star_ctxjmp: cps.

Lemma star_refl:
  forall e,
  [e =>* e].
Proof.
  auto with cps.
Qed.

Global Hint Resolve star_refl: cps.

Lemma star_trans:
  forall a b c,
  [a =>* b] -> [b =>* c] -> [a =>* c].
Proof.
  eauto with cps.
Qed.

Global Hint Resolve star_trans: cps.

Lemma star_bind_left:
  LEFT star.
Proof.
  induction 1.
  - destruct H; auto with cps.
  - apply star_refl.
  - eapply star_trans; eauto.
Qed.

Global Hint Resolve star_bind_left: cps.

Lemma star_bind_right:
  RIGHT star.
Proof.
  induction 1.
  - destruct H; auto with cps.
  - apply star_refl.
  - eapply star_trans; eauto.
Qed.

Global Hint Resolve star_bind_right: cps.

Lemma star_lift:
  forall a b,
  [a =>* b] ->
  forall i k,
  [lift i k a =>* lift i k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve star_lift: cps.

Lemma star_subst:
  forall a b,
  [a =>* b] ->
  forall y k,
  [subst y k a =>* subst y k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve star_subst: cps.

Lemma star_apply_parameters:
  forall xs k a b,
  [a =>* b] ->
  [apply_parameters xs k a =>* apply_parameters xs k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve star_apply_parameters: cps.

(** ** Reduction convertibility *)

Notation conv := rst(step).
Notation "[ a <=> b ]" := (conv a b)
  (at level 0, a, b at level 200): type_scope.

Lemma conv_step:
  forall a b,
  [a => b] -> [a <=> b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve conv_step: cps.

Lemma conv_recjmp:
  RECJMP conv.
Proof.
  auto with cps.
Qed.

Global Hint Resolve conv_recjmp: cps.

Lemma conv_ctxjmp:
  CTXJMP conv.
Proof.
  auto with cps.
Qed.

Global Hint Resolve conv_ctxjmp: cps.

Lemma conv_star:
  forall a b,
  [a =>* b] -> [a <=> b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve conv_star: cps.

Lemma conv_refl:
  forall e,
  [e <=> e].
Proof.
  auto with cps.
Qed.

Global Hint Resolve conv_refl: cps.

Lemma conv_sym:
  forall a b,
  [a <=> b] -> [b <=> a].
Proof.
  auto with cps.
Qed.

Global Hint Resolve conv_sym: cps.

Lemma conv_trans:
  forall a b c,
  [a <=> b] -> [b <=> c] -> [a <=> c].
Proof.
  eauto with cps.
Qed.

Global Hint Resolve conv_trans: cps.

Lemma conv_bind_left:
  LEFT conv.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve conv_bind_left: cps.

Lemma conv_bind_right:
  RIGHT conv.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve conv_bind_right: cps.

Lemma conv_lift:
  forall a b,
  [a <=> b] ->
  forall i k,
  [lift i k a <=> lift i k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve conv_lift: cps.

Lemma conv_subst:
  forall a b,
  [a <=> b] ->
  forall y k,
  [subst y k a <=> subst y k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve conv_subst: cps.

Lemma conv_apply_parameters:
  forall xs k a b,
  [a <=> b] ->
  [apply_parameters xs k a <=> apply_parameters xs k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve conv_apply_parameters: cps.

Global Instance conv_is_a_congruence: Congruence conv.
Proof.
  split.
  - split.
    + exact conv_refl.
    + exact conv_sym.
    + exact conv_trans.
  - apply conv_bind_left.
  - apply conv_bind_right.
Defined.

(** ** Head reduction *)

Definition LONGJMP (R: relation pseudoterm): Prop :=
  forall h r xs ts c,
  static h ->
  static r ->
  length xs = length ts ->
  R (r (bind (h (jump #h xs)) ts c))
    (r (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c)).

Global Hint Unfold LONGJMP: cps.

Inductive head: relation pseudoterm :=
  | head_longjmp:
    LONGJMP head.

Lemma head_bind_left:
  LEFT head.
Proof.
  unfold LEFT; intros.
  dependent destruction H.
  apply (head_longjmp h (context_left r ts c)).
  - assumption.
  - constructor.
    assumption.
  - assumption.
Qed.

Global Hint Resolve head_bind_left: cps.

Lemma head_recjmp:
  RECJMP head.
Proof.
  unfold RECJMP; intros.
  apply (head_longjmp context_hole context_hole).
  - constructor.
  - constructor.
  - assumption.
Qed.

Lemma beta_longjmp:
  LONGJMP beta.
Proof.
  unfold LONGJMP; intros.
  induction H0; simpl.
  - apply beta_ctxjmp.
    assumption.
  - apply beta_bind_left.
    assumption.
Qed.

Global Hint Resolve beta_longjmp: cps.

Lemma step_longjmp:
  LONGJMP step.
Proof.
  auto with cps.
Qed.

Global Hint Resolve step_longjmp: cps.

Lemma step_head:
  forall a b,
  head a b -> [a => b].
Proof.
  destruct 1; auto with cps.
Qed.

Global Hint Resolve step_head: cps.

Lemma star_longjmp:
  LONGJMP star.
Proof.
  auto with cps.
Qed.

Global Hint Resolve star_longjmp: cps.

Lemma star_head:
  forall a b,
  head a b -> [a =>* b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve star_head: cps.

Lemma conv_longjmp:
  LONGJMP conv.
Proof.
  auto with cps.
Qed.

Global Hint Resolve conv_longjmp: cps.

Lemma conv_head:
  forall a b,
  head a b -> [a <=> b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve conv_head: cps.

(** ** Soundness of reduction w.r.t. axiomatic semantics *)

(* TODO: move these lemmas to their proper places!!! Shame on me. *)

Inductive not_free_context: nat -> context -> Prop :=
  | not_free_context_hole:
    forall k,
    not_free_context k context_hole
  | not_free_context_left:
    forall k b ts c,
    not_free_context (S k) b ->
    not_free_list k ts ->
    not_free (k + length ts) c ->
    not_free_context k (context_left b ts c)
  | not_free_context_right:
    forall k b ts c,
    not_free (S k) b ->
    not_free_list k ts ->
    not_free_context (k + length ts) c ->
    not_free_context k (context_right b ts c).

Lemma not_free_context_split:
  forall (h: context) e p,
  not_free p (h e) ->
  not_free_context p h /\ not_free (p + #h) e.
Proof.
  induction h; simpl; split.
  - constructor.
  - rewrite Nat.add_0_r.
    assumption.
  - dependent destruction H.
    edestruct IHh; eauto.
    constructor.
    + assumption.
    + assumption.
    + rewrite Nat.add_comm.
      assumption.
  - dependent destruction H.
    edestruct IHh; eauto.
    replace (n + S #h) with (S n + #h); try lia.
    assumption.
  - dependent destruction H.
    edestruct IHh; eauto.
    constructor.
    + assumption.
    + assumption.
    + rewrite Nat.add_comm.
      assumption.
  - dependent destruction H.
    edestruct IHh; eauto.
    replace (n + (#h + length ts)) with (length ts + n + #h); try lia.
    assumption.
Qed.

Lemma not_free_context_merge:
  forall (h: context) e p,
  not_free_context p h ->
  not_free (p + #h) e ->
  not_free p (h e).
Proof.
  induction h; intros.
  - simpl in H0 |- *.
    rewrite Nat.add_0_r in H0.
    assumption.
  - dependent destruction H.
    simpl; constructor.
    + apply IHh.
      * assumption.
      * simpl in H2.
        replace (S k + #h) with (k + S #h); try lia.
        assumption.
    + assumption.
    + rewrite Nat.add_comm.
      assumption.
  - dependent destruction H.
    simpl; constructor.
    + assumption.
    + assumption.
    + apply IHh.
      * rewrite Nat.add_comm.
        assumption.
      * simpl in H2.
        replace (length ts + k + #h) with (k + (#h + length ts)); try lia.
        assumption.
Qed.

(* TODO: how come I didn't add this lemma at the correct place...? *)

Lemma sema_context:
  forall (h: context) a b,
  [a == b] -> [h a == h b].
Proof.
  induction h; eauto with cps.
Qed.

Lemma context_right_cycle_zero_e_equals_e:
  forall h k,
  context_right_cycle 0 k h = h.
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal.
    + apply IHh.
    + induction ts; simpl; auto.
      rewrite traverse_list_length.
      f_equal; auto.
      apply right_cycle_zero_e_equals_e.
    + apply right_cycle_zero_e_equals_e.
  - f_equal.
    + apply right_cycle_zero_e_equals_e.
    + induction ts; simpl; auto.
      rewrite traverse_list_length.
      f_equal; auto.
      apply right_cycle_zero_e_equals_e.
    + apply IHh.
Qed.

Definition context_remove_binding :=
  context_subst 0.

Lemma context_remove_binding_is_sound:
  forall (h: context) k e,
  remove_binding k (h e) =
    context_remove_binding k h (remove_binding (#h + k) e).
Proof.
  unfold remove_binding, context_remove_binding.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite subst_distributes_over_bind; f_equal.
    replace (S (#h + k)) with (#h + S k); try lia.
    apply IHh.
  - rewrite subst_distributes_over_bind; f_equal.
    replace (#h + length ts + k) with (#h + (k + length ts)); try lia.
    apply IHh.
Qed.

(* TODO: there's something about this in the [Axiomatic.v] file! *)

Lemma context_remove_binding_switch_bindings_simplification:
  forall h k,
  context_remove_binding k (context_switch_bindings k h) =
    context_remove_binding (S k) h.
Proof.
  unfold context_remove_binding.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal.
    + apply IHh.
    + clear IHh.
      induction ts; simpl; auto.
      f_equal; auto.
      do 3 rewrite traverse_list_length.
      replace (length ts + S k) with (S (length ts + k)); try lia.
      admit.
    + rewrite traverse_list_length.
      admit.
  - f_equal.
    + admit.
    + clear IHh.
      induction ts; simpl; auto.
      f_equal; auto.
      do 3 rewrite traverse_list_length.
      replace (length ts + S k) with (S (length ts + k)); try lia.
      admit.
    + rewrite traverse_list_length.
      apply IHh.
Admitted.

Lemma context_remove_binding_lift_simplification:
  forall h k,
  context_remove_binding k (context_lift 1 k h) = h.
Proof.
  unfold context_remove_binding.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal.
    + apply IHh.
    + induction ts; simpl; auto.
      do 2 rewrite traverse_list_length.
      f_equal; auto.
      rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
    + rewrite traverse_list_length.
      rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
  - f_equal.
    + rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
    + induction ts; simpl; auto.
      do 2 rewrite traverse_list_length.
      f_equal; auto.
      rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
    + rewrite traverse_list_length.
      apply IHh.
Qed.

Lemma right_cycle_lift_simplification:
  forall e i k,
  right_cycle i k (lift 1 (k + i) e) = lift 1 k e.
Proof.
  induction e using pseudoterm_deepind; intros.
  - induction i; auto.
  - induction i; auto.
  - induction i; auto.
  - induction i; auto.
  - unfold right_cycle; simpl.
    rewrite sequence_length.
    destruct (le_gt_dec (k + i) n).
    + rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite subst_bound_gt; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite apply_parameters_bound_gt; try lia.
      * rewrite sequence_length; simpl.
        f_equal; lia.
      * rewrite sequence_length; simpl.
        lia.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge; try lia.
        rewrite apply_parameters_high_sequence_bound_in; try lia.
        f_equal; lia.
      * rewrite lift_bound_lt; try lia.
        rewrite apply_parameters_bound_lt; try lia.
        reflexivity.
  - do 2 rewrite lift_distributes_over_negation.
    rewrite right_cycle_distributes_over_negation.
    f_equal.
    induction H; simpl; auto.
    do 3 rewrite traverse_list_length.
    f_equal; auto.
    rewrite Nat.add_assoc.
    apply H.
  - do 2 rewrite lift_distributes_over_jump.
    rewrite right_cycle_distributes_over_jump.
    f_equal.
    + apply IHe.
    + list induction over H.
  - do 2 rewrite lift_distributes_over_bind.
    rewrite right_cycle_distributes_over_bind.
    f_equal.
    + apply IHe1.
    + induction H; simpl; auto.
      do 3 rewrite traverse_list_length.
      f_equal; auto.
      rewrite Nat.add_assoc.
      apply H.
    + rewrite traverse_list_length.
      replace (k + i + length ts) with (k + length ts + i); try lia.
      apply IHe2.
Qed.

Lemma float_free_continuation_into_context:
  forall h a ts c,
  not_free_context 0 h ->
  [bind (h a) ts c ==
    context_remove_binding 0 h (bind (right_cycle #h 0 a)
      (traverse_list (lift #h) 0 ts) (lift #h (length ts) c))].
Proof.
  intro h.
  assert (exists n, n = context_depth h) as (n, ?); eauto.
  generalize dependent h.
  induction n; simpl; intros.
  - destruct h; try discriminate.
    apply sema_eq; simpl; f_equal.
    + rewrite right_cycle_zero_e_equals_e; auto.
    + induction ts; simpl; auto.
      f_equal; auto.
      rewrite lift_zero_e_equals_e; auto.
    + rewrite lift_zero_e_equals_e; auto.
  - destruct h; simpl in H; try lia.
    + dependent destruction H0; simpl.
      eapply sema_trans;
        [| eapply sema_trans ].
      * apply sema_float_left; auto.
      * apply sema_bind_left.
        rewrite context_switch_bindings_is_sound.
        apply IHn; eauto.
        --- rewrite context_switch_bindings_depth; lia.
        --- admit.
      * apply sema_eq; f_equal.
        rewrite context_switch_bindings_bvars.
        rewrite Nat.add_0_r.
        rewrite context_remove_binding_switch_bindings_simplification.
        f_equal; f_equal.
        --- apply right_cycle_switch_bindings_simplification.
        --- induction ts; simpl; auto.
            f_equal; auto.
            do 3 rewrite traverse_list_length.
            rewrite lift_lift_simplification; try lia.
            f_equal; lia.
        --- rewrite traverse_list_length.
            rewrite lift_lift_simplification; try lia.
            f_equal; lia.
    + dependent destruction H0; simpl.
      eapply sema_trans;
        [| eapply sema_trans ].
      * apply sema_float_right; auto.
      * apply sema_bind_right.
        rewrite context_right_cycle_is_sound.
        apply IHn; eauto.
        --- rewrite context_right_cycle_depth; lia.
        --- admit.
      * apply sema_eq; f_equal.
        --- admit.
        --- replace (context_remove_binding 0 (context_right_cycle
              (length ts0) 0 h)) with (context_subst 0 (length ts0) h).
            +++ f_equal; f_equal.
                *** rewrite context_right_cycle_bvars.
                    apply right_cycle_right_cycle_simplification.
                *** rewrite context_right_cycle_bvars.
                    induction ts; simpl; auto.
                    do 3 rewrite traverse_list_length.
                    f_equal; auto.
                    rewrite lift_lift_simplification; try lia.
                    reflexivity.
                *** rewrite context_right_cycle_bvars.
                    rewrite traverse_list_length.
                    rewrite lift_lift_simplification; try lia.
                    reflexivity.
            +++ admit.
Admitted.

(*
  When proving soundness of reduction, we're gonna need to use the (CONTR) rule,
  or rather, it's inverse. This will split a single binding in two, and the term
  may refer to any of them. We'd like to make that there's a single reference to
  the closest one, namely in the jump at subject position. This will allow us to
  freely float the continuation closer to the jump, in order to perform a single
  (JMP) action.
*)

Local Lemma technical1:
  forall xs (h: context) k,
  h (jump (k + #h) xs) =
    remove_binding k (context_lift 1 k h
      (jump (k + #h) (map (lift 1 (k + #h)) xs))).
Proof.
  unfold remove_binding.
  induction h; simpl; intros.
  - rewrite subst_distributes_over_jump; f_equal.
    + rewrite subst_bound_eq; try lia.
      rewrite lift_bound_ge; try lia.
      f_equal; lia.
    + induction xs; simpl; auto.
      f_equal; auto.
      rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
  - rewrite subst_distributes_over_bind; f_equal.
    + replace (k + S #h) with (S k + #h); try lia.
      apply IHh.
    + induction ts; simpl; auto.
      do 2 rewrite traverse_list_length.
      f_equal; auto.
      rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
    + rewrite traverse_list_length.
      rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
  - rewrite subst_distributes_over_bind; f_equal.
    + rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
    + induction ts; simpl; auto.
      do 2 rewrite traverse_list_length.
      f_equal; auto.
      rewrite subst_lift_simplification; try lia.
      rewrite lift_zero_e_equals_e; auto.
    + rewrite traverse_list_length.
      replace (k + (#h + length ts)) with (k + length ts + #h); try lia.
      apply IHh.
Qed.

Theorem sema_ctxjmp:
  CTXJMP sema.
Proof.
  unfold CTXJMP; intros.
  etransitivity;
    [| etransitivity;
      [| etransitivity;
        [| etransitivity ] ] ].
  - rewrite technical1 with (k := 0); simpl.
    symmetry.
    apply sema_contr.
  - apply sema_bind_left.
    apply float_free_continuation_into_context.
    (* Clearly. *)
    admit.
  - apply sema_bind_left.
    rewrite context_lift_bvars.
    rewrite right_cycle_distributes_over_jump.
    rewrite right_cycle_bound_eq; auto.
    rewrite context_remove_binding_lift_simplification.
    apply sema_context.
    apply sema_recjmp.
    do 2 rewrite map_length.
    do 2 rewrite traverse_list_length.
    assumption.
  - apply sema_bind_left.
    apply sema_context.
    rewrite traverse_list_length.
    rewrite traverse_list_length.
    rewrite lift_lift_simplification; try lia.
    rewrite lift_lift_simplification; try lia.
    (* Upon careful inspection... *)
    replace (map (right_cycle #h 0) (map (lift 1 #h) xs)) with
      (map (lift 1 0) xs). (* :D *)
    + apply sema_gc.
      admit.
    + clear H.
      induction xs; simpl; auto.
      f_equal; auto.
      rewrite right_cycle_lift_simplification; auto.
  - apply sema_eq.
    f_equal; f_equal.
    unfold remove_binding.
    rewrite subst_distributes_over_apply_parameters.
    rewrite map_length, Nat.add_0_r.
    f_equal; simpl.
    + clear H.
      induction xs; simpl; auto.
      f_equal; auto.
      rewrite subst_lift_simplification; auto.
      apply lift_zero_e_equals_e.
    + rewrite subst_lift_simplification; try lia.
      f_equal; lia.
Admitted.

Corollary sema_step:
  forall a b,
  [a => b] -> [a == b].
Proof.
  induction 1.
  - apply sema_ctxjmp.
    assumption.
  - apply sema_gc.
    assumption.
  - apply sema_bind_left.
    assumption.
  - apply sema_bind_right.
    assumption.
Qed.

Global Hint Resolve sema_step: cps.

Corollary sema_star:
  forall a b,
  [a =>* b] -> [a == b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve sema_star: cps.

Corollary sema_conv:
  forall a b,
  [a <=> b] -> [a == b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve sema_conv: cps.
