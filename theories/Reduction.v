(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
(* TODO: perhaps some definitions should be moved to Syntax. *)
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Axiomatic.

(** ** One-step reduction. *)

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
  forall (h: context),
  forall xs ts c,
  length xs = length ts ->
  R (bind (h (jump #h xs)) ts c)
    (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c).

Global Hint Unfold CTXJMP: cps.

Inductive step: relation pseudoterm :=
  | step_ctxjmp:
    CTXJMP step
  | step_bind_left:
    LEFT step
  | step_bind_right:
    (* TODO: we probably should require that the bound continuation appears free
       in the left side, so that (GC) won't mess things up. *)
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

Lemma step_recjmp:
  RECJMP step.
Proof.
  unfold RECJMP; intros.
  replace c with (lift 0 (length ts) c) at 2.
  - rewrite lift_lift_simplification; try lia.
    apply step_ctxjmp with (h := context_hole); auto.
  - apply lift_zero_e_equals_e.
Qed.

Global Hint Resolve step_recjmp: cps.

Local Lemma step_ctxjmp_helper:
  forall (h r: context),
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
  [bind (h a) ts c => bind (r b) ts' c'].
Proof.
  intros.
  rewrite H, H2, H3, H4, H5, H1.
  apply step_ctxjmp.
  assumption.
Qed.

Lemma step_lift:
  forall a b,
  [a => b] ->
  forall i k,
  [lift i k a => lift i k b].
Proof.
  induction 1; intros.
  - do 2 rewrite lift_distributes_over_bind.
    do 2 rewrite context_lift_is_sound.
    rewrite lift_distributes_over_jump.
    rewrite lift_bound_lt; try lia.
    rewrite lift_distributes_over_apply_parameters.
    eapply step_ctxjmp_helper with (xs := map _ xs).
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
    apply step_bind_left.
    apply IHstep.
  - do 2 rewrite lift_distributes_over_bind.
    apply step_bind_right.
    apply IHstep.
Qed.

Global Hint Resolve step_lift: cps.

Lemma step_subst:
  forall a b,
  [a => b] ->
  forall y k,
  [subst y k a => subst y k b].
Proof.
  induction 1; intros.
  - do 2 rewrite subst_distributes_over_bind.
    do 2 rewrite context_subst_is_sound.
    rewrite subst_distributes_over_jump.
    rewrite subst_bound_lt; try lia.
    rewrite subst_distributes_over_apply_parameters.
    eapply step_ctxjmp_helper with (xs := map _ xs).
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
    apply step_bind_left.
    apply IHstep.
  - do 2 rewrite subst_distributes_over_bind.
    apply step_bind_right.
    apply IHstep.
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

(*
  This lemma shows that "free jumps" are preserved in redexes. If we have a
  context H, and the term H[k<xs>] reduces to a term e, given that k is free in
  the hole of H, then e will keep the subterm k<xs>, i.e., there is a R such
  that e = R[k<xs>] and both R and H will bind the same variables in their
  respective holes.
*)
Lemma step_noninterference:
  forall h: context,
  forall n,
  n >= #h ->
  forall xs e,
  [h (jump n xs) => e] ->
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

Instance conv_is_an_equivalence: Equivalence conv.
Proof.
  split.
  - exact conv_refl.
  - exact conv_sym.
  - exact conv_trans.
Defined.
