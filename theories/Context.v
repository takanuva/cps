(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Export Setoid.
Require Export Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Metatheory.

Import ListNotations.

Definition LEFT (R: relation pseudoterm): Prop :=
  forall b1 b2 ts c,
  R b1 b2 -> R (bind b1 ts c) (bind b2 ts c).

Global Hint Unfold LEFT: cps.

Definition RIGHT (R: relation pseudoterm): Prop :=
  forall b ts c1 c2,
  R c1 c2 -> R (bind b ts c1) (bind b ts c2).

Global Hint Unfold RIGHT: cps.

Class Congruence (R: relation pseudoterm) := {
  (* A congruence is an equivalence relation. *)
  Congruence_Equivalence :> Equivalence R;
  (* It also is preserved by any contexts. *)
  Congruence_Left: LEFT R;
  Congruence_Right: RIGHT R
}.

(** ** One-hole contexts. *)

Inductive context: Set :=
  | context_hole
  | context_left (b: context) (ts: list pseudotype) (c: pseudoterm)
  | context_right (b: pseudoterm) (ts: list pseudotype) (c: context).

Global Hint Constructors context: cps.

Lemma context_eq_dec:
  forall h r: context,
  { h = r } + { h <> r }.
Proof.
  decide equality.
  - apply pseudoterm_eq_dec.
  - apply list_eq_dec.
    apply pseudotype_eq_dec.
  - apply list_eq_dec.
    apply pseudotype_eq_dec.
  - apply pseudoterm_eq_dec.
Qed.

Reserved Notation "# h" (at level 0, right associativity, format "# h").

Fixpoint context_bvars (h: context): nat :=
  match h with
  | context_hole => 0
  | context_left b ts c => S #b
  | context_right b ts c => #c + length ts
  end

where "# h" := (context_bvars h).

Fixpoint context_depth (h: context): nat :=
  match h with
  | context_hole => 0
  | context_left b ts c => 1 + context_depth b
  | context_right b ts c => 1 + context_depth c
  end.

Fixpoint apply_context (h: context) (e: pseudoterm): pseudoterm :=
  match h with
  | context_hole => e
  | context_left b ts c => bind (apply_context b e) ts c
  | context_right b ts c => bind b ts (apply_context c e)
  end.

Coercion apply_context: context >-> Funclass.

Fixpoint compose_context (h: context) (r: context): context :=
  match h with
  | context_hole => r
  | context_left b ts c => context_left (compose_context b r) ts c
  | context_right b ts c => context_right b ts (compose_context c r)
  end.

Lemma compose_context_is_sound:
  forall h r e,
  compose_context h r e = h (r e).
Proof.
  induction h; intros; simpl.
  - reflexivity.
  - rewrite IHh.
    reflexivity.
  - rewrite IHh.
    reflexivity.
Qed.

Lemma compose_context_bvars:
  forall h r,
  #(compose_context h r) = #h + #r.
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite IHh; auto.
  - rewrite IHh; lia.
Qed.

Lemma compose_context_depth:
  forall h r,
  context_depth (compose_context h r) = context_depth h + context_depth r.
Proof.
  induction h; simpl; auto.
Qed.

Inductive static: context -> Prop :=
  | static_hole:
    static context_hole
  | static_left:
    forall h ts c,
    static h -> static (context_left h ts c).

Global Hint Constructors static: cps.

Lemma static_compose_context:
  forall h r,
  static h -> static r -> static (compose_context h r).
Proof.
  induction 1; simpl; intros.
  - assumption.
  - auto with cps.
Qed.

Definition nonstatic h: Prop :=
  ~static h.

Lemma context_static_nonstatic_dec:
  forall h,
  { static h } + { nonstatic h }.
Proof.
  induction h.
  (* Case: context_hole. *)
  - left; constructor.
  (* Case: context_left. *)
  - destruct IHh; simpl.
    + left; constructor.
      assumption.
    + right; intro.
      inversion_clear H.
      apply n; assumption.
  (* Case: context_right. *)
  - right; intro.
    inversion H.
Qed.

Lemma nonstatic_ind:
  forall P: context -> Prop,
  (* Recursion stops when a right context is found; we never reach a hole. *)
  forall f1: (forall b ts h, P (context_right b ts h)),
  forall f2: (forall h ts c, P h -> P (context_left h ts c)),
  forall h, nonstatic h -> P h.
Proof.
  induction h; intro.
  (* Case: context_hole. *)
  - exfalso; apply H.
    constructor.
  (* Case: context_left. *)
  - apply f2; apply IHh.
    intro; apply H.
    constructor.
    assumption.
  (* Case: context_right. *)
  - apply f1.
Qed.

Lemma context_is_injective:
  forall h r: context,
  h = r ->
  forall a b,
  h a = r b -> a = b.
Proof.
  induction h; destruct r; intros; try discriminate.
  - assumption.
  - dependent destruction H0.
    eauto.
  - dependent destruction H0.
    eauto.
Qed.

Inductive same_path: relation context :=
  | same_path_hole:
    same_path context_hole context_hole
  | same_path_left:
    forall h r ts1 ts2 c1 c2,
    same_path h r ->
    length ts1 = length ts2 ->
    same_path (context_left h ts1 c1) (context_left r ts2 c2)
  | same_path_right:
    forall b1 b2 ts1 ts2 h r,
    same_path h r ->
    length ts1 = length ts2 ->
    same_path (context_right b1 ts1 h) (context_right b2 ts2 r).

Global Hint Constructors same_path: cps.

Lemma same_path_refl:
  forall h,
  same_path h h.
Proof.
  induction h.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Global Hint Resolve same_path_refl: cps.

Lemma same_path_sym:
  forall h r,
  same_path h r -> same_path r h.
Proof.
  induction h; destruct r; inversion 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Global Hint Resolve same_path_sym: cps.

Lemma same_path_trans:
  forall h r s,
  same_path h r -> same_path r s -> same_path h s.
Proof.
  intros.
  generalize dependent s.
  induction H; intros.
  - assumption.
  - inversion_clear H1.
    constructor; auto.
    congruence.
  - inversion_clear H1.
    constructor; auto.
    congruence.
Qed.

Global Hint Resolve same_path_trans: cps.

Global Instance same_path_is_an_equivalence: Equivalence same_path.
Proof.
  split.
  - exact same_path_refl.
  - exact same_path_sym.
  - exact same_path_trans.
Defined.

Lemma same_path_implies_same_bvars:
  forall h r,
  same_path h r -> #h = #r.
Proof.
  induction 1.
  - reflexivity.
  - simpl; lia.
  - simpl; lia.
Qed.

Global Hint Resolve same_path_implies_same_bvars: cps.

Lemma same_path_implies_same_depth:
  forall h r,
  same_path h r -> context_depth h = context_depth r.
Proof.
  induction 1; simpl; auto.
Qed.

Global Hint Resolve same_path_implies_same_depth: cps.

Lemma same_path_same_hole_implies_same_context:
  forall h r,
  same_path h r ->
  forall e,
  h e = r e -> h = r.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - dependent destruction H1.
    f_equal; eauto.
  - dependent destruction H1.
    f_equal; eauto.
Qed.

(*
  The intuition behind the following technical lemma is as follow:

  We have two contexts H and R there are different, but we do have jumps n<xs>
  and m<ys> such that H[n<xs>] = R[m<ys>]. This implies that m<ys> is a subterm
  of H, and n<xs> is a subterm of R, i.e., H and R "mark" two different jumps in
  the same term. We want to, given a term x, rebuild the context H, but we will
  exchange the m<ys> in it by the term x, thus making S[n<xs>] equal to R[x],
  and do the respective thing for R.

  This is useful for proving that redexes are non-overlapping.
*)

Lemma context_difference:
  forall h r: context,
  h <> r ->
  forall n m xs ys,
  h (jump n xs) = r (jump m ys) ->
  forall x,
  exists s: context,
       r x = s (jump n xs)
    /\ same_path h s
    /\ forall y,
       exists u: context,
            h y = u (jump m ys)
         /\ same_path r u
         /\ s y = u x.
Proof.
  induction h; destruct r; simpl; intros.
  (* Case: (context_hole, context_hole). *)
  - exfalso; auto.
  (* Case: (context_hole, context_left). *)
  - discriminate.
  (* Case: (context_hole, context_right). *)
  - discriminate.
  (* Case: (context_left, context_hole). *)
  - discriminate.
  (* Case: (context_left, context_left). *)
  - dependent destruction H0.
    edestruct IHh with (r := r) as (s, ?).
    + congruence.
    + eassumption.
    + exists (context_left s ts0 c0); simpl.
      intuition.
      * f_equal; eassumption.
      * edestruct H3 as (u, ?).
        exists (context_left u ts0 c0); simpl.
        intuition; f_equal; eauto.
  (* Case: (context_left, context_right). *)
  - clear IHh.
    dependent destruction H0.
    eexists (context_left h ts0 (r x)).
    intuition.
    eexists (context_right (h y) ts0 r); intuition.
  (* Case: (context_right, context_hole). *)
  - discriminate.
  (* Case: (context_right, context_left). *)
  - clear IHh.
    dependent destruction H0.
    eexists (context_right (r x) ts0 h).
    intuition.
    eexists (context_left r ts0 (h y)); intuition.
  (* Case: (context_right, context_right). *)
  - dependent destruction H0.
    edestruct IHh with (r := r) as (s, ?).
    + congruence.
    + eassumption.
    + exists (context_right b0 ts0 s); simpl.
      intuition.
      * f_equal; eassumption.
      * edestruct H3 as (u, ?).
        exists (context_right b0 ts0 u); simpl.
        intuition; f_equal; eauto.
Qed.

Fixpoint context_lift i k h: context :=
  match h with
  | context_hole =>
    context_hole
  | context_left b ts c =>
    context_left (context_lift i (S k) b)
      (* TODO: fix lifting. *)
      ts (lift i (k + length ts) c)
  | context_right b ts c =>
    context_right (lift i (S k) b)
      (* TODO: fixt lifting. *)
      ts (context_lift i (k + length ts) c)
  end.

Lemma same_path_context_lift:
  forall h i k,
  same_path h (context_lift i k h).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - constructor.
    + apply IHh.
    + reflexivity.
  - constructor.
    + apply IHh.
    + reflexivity.
Qed.

Global Hint Resolve same_path_context_lift: cps.

Lemma context_lift_is_sound:
  forall (h: context) i k e,
  lift i k (h e) = context_lift i k h (lift i (#h + k) e).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite lift_distributes_over_bind.
    f_equal.
    replace (S (#h + k)) with (#h + S k); try lia.
    apply IHh.
  - rewrite lift_distributes_over_bind.
    f_equal.
    replace (#h + length ts + k) with (#h + (k + length ts)); try lia.
    apply IHh.
Qed.

Lemma context_lift_bvars:
  forall h i k,
  #(context_lift i k h) = #h.
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - now rewrite IHh.
  - now rewrite IHh.
Qed.

Fixpoint context_subst y k h: context :=
  match h with
  | context_hole =>
    context_hole
  | context_left b ts c =>
    context_left (context_subst y (S k) b)
      (* TODO: fix subst. *)
      ts (subst y (k + length ts) c)
  | context_right b ts c =>
    context_right (subst y (S k) b)
      (* TODO: fix subst. *)
      ts (context_subst y (k + length ts) c)
  end.

Lemma same_path_context_subst:
  forall h i k,
  same_path h (context_subst i k h).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - constructor.
    + apply IHh.
    + reflexivity.
  - constructor.
    + apply IHh.
    + reflexivity.
Qed.

Global Hint Resolve same_path_context_subst: cps.

Lemma context_subst_is_sound:
  forall (h: context) y k e,
  subst y k (h e) = context_subst y k h (subst y (#h + k) e).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite subst_distributes_over_bind.
    f_equal.
    replace (S (#h + k)) with (#h + S k); try lia.
    apply IHh.
  - rewrite subst_distributes_over_bind.
    f_equal.
    replace (#h + length ts + k) with (#h + (k + length ts)); try lia.
    apply IHh.
Qed.

Lemma context_subst_bvars:
  forall h y k,
  #(context_subst y k h) = #h.
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - now rewrite IHh.
  - now rewrite IHh.
Qed.

Fixpoint context_right_cycle n k h: context :=
  match h with
  | context_hole =>
    context_hole
  | context_left b ts c =>
    context_left (context_right_cycle n (S k) b)
      (* TODO: fix right_cycle. *)
      ts (right_cycle n (k + length ts) c)
  | context_right b ts c =>
    context_right (right_cycle n (S k) b)
      (* TODO: fix right_cycle. *)
      ts (context_right_cycle n (k + length ts) c)
  end.

Lemma context_right_cycle_is_sound:
  forall (h: context) n k e,
  right_cycle n k (h e) =
    context_right_cycle n k h (right_cycle n (#h + k) e).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite right_cycle_distributes_over_bind.
    f_equal.
    replace (S (#h + k)) with (#h + S k); try lia.
    apply IHh.
  - rewrite right_cycle_distributes_over_bind.
    f_equal.
    replace (#h + length ts + k) with (#h + (k + length ts)); try lia.
    apply IHh.
Qed.

Lemma context_right_cycle_bvars:
  forall h i k,
  #(context_right_cycle i k h) = #h.
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal.
    apply IHh.
  - now rewrite IHh.
Qed.

Lemma context_right_cycle_depth:
  forall h i k,
  context_depth (context_right_cycle i k h) = context_depth h.
Proof.
  induction h; simpl; auto.
Qed.

Fixpoint context_switch_bindings k h: context :=
  match h with
  | context_hole =>
    context_hole
  | context_left b ts c =>
    context_left (context_switch_bindings (S k) b)
      (* TODO: fix switch_bindings. *)
      ts (switch_bindings (k + length ts) c)
  | context_right b ts c =>
    context_right (switch_bindings (S k) b)
      (* TODO: fix switch_bindings. *)
      ts (context_switch_bindings (k + length ts) c)
  end.

Lemma context_switch_bindings_is_sound:
  forall (h: context) k e,
  switch_bindings k (h e) =
    context_switch_bindings k h (switch_bindings (#h + k) e).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - rewrite switch_bindings_distributes_over_bind.
    f_equal.
    replace (S (#h + k)) with (#h + S k); try lia.
    apply IHh.
  - rewrite switch_bindings_distributes_over_bind.
    f_equal.
    replace (#h + length ts + k) with (#h + (k + length ts)); try lia.
    apply IHh.
Qed.

Lemma context_switch_bindings_bvars:
  forall h k,
  #(context_switch_bindings k h) = #h.
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal.
    apply IHh.
  - now rewrite IHh.
Qed.

Global Hint Resolve context_switch_bindings_bvars: cps.

Lemma context_switch_bindings_depth:
  forall h k,
  context_depth (context_switch_bindings k h) = context_depth h.
Proof.
  induction h; simpl; auto.
Qed.

Global Hint Resolve context_switch_bindings_depth: cps.

Lemma static_context_switch_bindings:
  forall h,
  static h ->
  forall k,
  static (context_switch_bindings k h).
Proof.
  induction 1; simpl; auto with cps.
Qed.

Global Hint Resolve static_context_switch_bindings: cps.

Lemma context_switch_bindings_is_involutive:
  forall h k,
  context_switch_bindings k (context_switch_bindings k h) = h.
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - f_equal.
    + apply IHh.
    + apply switch_bindings_is_involutive.
  - f_equal.
    + apply switch_bindings_is_involutive.
    + apply IHh.
Qed.

Inductive context_equals_lift h e1 i k: Prop :=
  | context_equals_lift_mk:
    forall r,
    same_path h r ->
    h = context_lift i k r ->
    forall e3,
    e1 = lift i (#h + k) e3 ->
    context_equals_lift h e1 i k.

Lemma context_equals_lift_inversion:
  forall (h: context) e1 e2 i k,
  h e1 = lift i k e2 ->
  context_equals_lift h e1 i k.
Proof.
  induction h; simpl; intros.
  - econstructor.
    + constructor.
    + reflexivity.
    + simpl; eauto.
  - destruct e2; try discriminate.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in H; auto.
        discriminate.
      * rewrite lift_bound_lt in H; auto.
        discriminate.
    + rewrite lift_distributes_over_bind in H.
      dependent destruction H.
      edestruct IHh as (r, ?, ?, e3, ?); eauto.
      eexists (context_left r ts0 _) e3; simpl.
      * constructor; auto.
      * f_equal; auto.
      * rewrite H1; f_equal.
        lia.
  - destruct e2; try discriminate.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in H; auto.
        discriminate.
      * rewrite lift_bound_lt in H; auto.
        discriminate.
    + rewrite lift_distributes_over_bind in H.
      dependent destruction H.
      edestruct IHh as (r, ?, ?, e3, ?); eauto.
      eexists (context_right _ ts0 r) e3; simpl.
      * constructor; auto.
      * f_equal; auto.
      * rewrite H1; f_equal.
        lia.
Qed.
