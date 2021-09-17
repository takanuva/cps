(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Setoid.
Require Import Morphisms.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Context.

(** ** Axiomatic semantics *)

Definition RECJMP (R: relation pseudoterm): Prop :=
  forall xs ts c,
  length xs = length ts ->
  R (bind (jump 0 xs) ts c)
    (bind (apply_parameters xs 0 (lift 1 (length xs) c)) ts c).

Global Hint Unfold RECJMP: cps.

(* My first intuition was to make the redex as [jump (length ts + k) _], by
   using a bound var (that is not a parameter), but this is too restrictive for
   our "high-order" definition of pseudoterms; lifting k instead solves this,
   and it properly captures the notion of (ETA) for actual terms. *)

Definition ETA (R: relation pseudoterm): Prop :=
  forall b ts k,
  R (bind b ts (jump (lift (length ts) 0 k) (low_sequence (length ts))))
    (subst k 0 b).

Global Hint Unfold ETA: cps.

Definition DISTR (R: relation pseudoterm): Prop :=
  forall b ms m ns n,
  not_free_list 0 ms ->
  R (bind (bind b ms m) ns n)
    (bind (bind
      (switch_bindings 0 b)
      (traverse_list (lift 1) 0 ns)
        (lift 1 (length ns) n))
      (traverse_list remove_binding 0 ms) (bind
        (right_cycle (length ms) 0 m)
        (traverse_list (lift (length ms)) 0 ns)
          (lift (length ms) (length ns) n))).

Global Hint Unfold DISTR: cps.

Definition CONTR (R: relation pseudoterm): Prop :=
  forall b ts c,
  R (bind (bind b (traverse_list (lift 1) 0 ts) (lift 1 (length ts) c)) ts c)
    (bind (remove_binding 0 b) ts c).

Global Hint Unfold CONTR: cps.

Definition GC (R: relation pseudoterm): Prop :=
  forall b ts c,
  not_free 0 b ->
  R (bind b ts c) (remove_binding 0 b).

Global Hint Unfold GC: cps.

(* As of now, I'm still unsure whether we'll need a directed, one-step struct
   relation or just it's congruence version. Just to be sure, we'll define it
   anyway. Note that we do not add contraction here as it is derivable in the
   equivalence closure of this relation. *)

Inductive struct: relation pseudoterm :=
  | struct_recjmp:
    RECJMP struct
  | struct_distr:
    DISTR struct
  | struct_eta:
    ETA struct
  | struct_gc:
    GC struct
  | struct_bind_left:
    LEFT struct
  | struct_bind_right:
    RIGHT struct.

Global Hint Constructors struct: cps.

(* We'll just define our structural congruence as the smallest relation closed
   under the [struct] rules above. *)

Notation cong := rst(struct).
Notation "[ a == b ]" := (cong a b)
  (at level 0, a, b at level 200): type_scope.

Lemma cong_refl:
  forall e,
  [e == e].
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_refl: cps.

Lemma cong_sym:
  forall a b,
  [a == b] -> [b == a].
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_sym: cps.

Lemma cong_trans:
  forall a b c,
  [a == b] -> [b == c] -> [a == c].
Proof.
  eauto with cps.
Qed.

Global Hint Resolve cong_trans: cps.

Lemma cong_struct:
  forall a b,
  struct a b -> [a == b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_struct: cps.

Lemma cong_recjmp:
  RECJMP cong.
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_recjmp: cps.

Lemma cong_distr:
  DISTR cong.
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_distr: cps.

Lemma cong_eta:
  ETA cong.
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_eta: cps.

Lemma cong_gc:
  GC cong.
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_gc: cps.

Lemma cong_bind_left:
  LEFT cong.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve cong_bind_left: cps.

Lemma cong_bind_right:
  RIGHT cong.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve cong_bind_right: cps.

Instance cong_is_a_congruence: Congruence cong.
Proof.
  split.
  - split.
    + exact cong_refl.
    + exact cong_sym.
    + exact cong_trans.
  - exact cong_bind_left.
  - exact cong_bind_right.
Defined.

(* Our (DISTR) rule is particularly annoying to do with de Bruijn indexes and it
   did take some time to approach correctly. Take the following as an example,
   moving from our [ex1] into [ex2].

                                         \j.\x.\y.\z.
    \j.\x.\y.\z.                           h@0<y@3, k@1, x@4>
      h@1<y@3, k@0, x@4>                   { h<c, d, e> =
      { k<a, b> =                 ==           d@1<e@0, z@4> }
          h@2<b@0, j@6, a@1> }             { k<a, b> =
      { h<c, d, e> =                           h@0<b@1, j@6, a@2>
          d@1<e@0, z@3> }                      { h<c, d, e> =
                                                 d@1<e@0, z@5> } }

    We can now show that this equivalence holds. *)

Example ex2: pseudoterm :=
  (bind (bind
    (jump 0 [bound 4; bound 1; bound 3])
    [base; negation [base; base]; base]
      (jump 1 [bound 4; bound 0]))
    [base; base]
      (bind
        (jump 0 [bound 2; bound 6; bound 1])
        [base; negation [base; base]; base]
          (jump 1 [bound 5; bound 0]))).

Goal [ex1 == ex2].
Proof.
  apply cong_distr.
  do 3 constructor.
Qed.

Local Lemma struct_recjmp_helper:
  forall xs ts c x1 x2 x3,
  x1 = apply_parameters xs 0 (lift 1 (length xs) c) ->
  x2 = ts ->
  x3 = c ->
  length xs = length ts ->
  struct (bind (jump 0 xs) ts c) (bind x1 x2 x3).
Proof.
  intros.
  rewrite H, H0, H1.
  apply struct_recjmp; auto.
Qed.

Local Lemma struct_distr_helper:
  forall b ms m ns n x1 x2 x3 x4 x5 x6 x7,
  x1 = switch_bindings 0 b ->
  x2 = lift 1 (length ns) n ->
  x3 = right_cycle (length ms) 0 m ->
  x4 = lift (length ms) (length ns) n ->
  x5 = traverse_list (lift 1) 0 ns ->
  x6 = traverse_list (lift (length ms)) 0 ns ->
  x7 = traverse_list remove_binding 0 ms ->
  not_free_list 0 ms ->
  struct (bind (bind b ms m) ns n) (bind (bind x1 x5 x2) x7 (bind x3 x6 x4)).
Proof.
  intros.
  rewrite H, H0, H1, H2, H3, H4, H5.
  apply struct_distr; auto.
Qed.

Local Lemma struct_eta_helper:
  forall b ts k x1 x2,
  x1 = jump (lift (length ts) 0 k) (low_sequence (length ts)) ->
  x2 = subst k 0 b ->
  struct (bind b ts x1) x2.
Proof.
  intros.
  rewrite H, H0.
  apply struct_eta.
Qed.

Local Lemma struct_gc_helper:
  forall b ts c x1,
  x1 = remove_binding 0 b ->
  not_free 0 b ->
  struct (bind b ts c) x1.
Proof.
  intros.
  rewrite H.
  apply struct_gc; auto.
Qed.

Lemma struct_lift:
  forall a b,
  struct a b ->
  forall i k,
  struct (lift i k a) (lift i k b).
Proof.
  induction 1; intros.
  (* Case: struct_recjmp. *)
  - do 2 rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump.
    apply struct_recjmp_helper.
    + rewrite lift_distributes_over_apply_parameters.
      f_equal.
      rewrite map_length.
      symmetry.
      rewrite lift_lift_permutation; try lia.
      f_equal; lia.
    + reflexivity.
    + reflexivity.
    + rewrite map_length.
      rewrite traverse_list_length.
      assumption.
  (* Case: struct_distr. *)
  - do 5 rewrite lift_distributes_over_bind.
    apply struct_distr_helper.
    + apply lift_and_switch_bindings_commute.
    + symmetry.
      do 2 rewrite traverse_list_length.
      rewrite lift_lift_permutation.
      * reflexivity.
      * lia.
    + do 2 rewrite traverse_list_length.
      apply lift_and_right_cycle_commute with (p := 0).
      lia.
    + do 4 rewrite traverse_list_length.
      symmetry.
      rewrite lift_lift_permutation.
      * f_equal; lia.
      * lia.
    + induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        do 4 rewrite traverse_list_length.
        symmetry.
        rewrite lift_lift_permutation; try lia.
        f_equal; lia.
    + do 2 rewrite traverse_list_length.
      induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        do 4 rewrite traverse_list_length.
        symmetry.
        rewrite lift_lift_permutation; auto with arith.
        f_equal; lia.
    + induction ms; auto; intros.
      inversion_clear H.
      rewrite Nat.add_0_r in H0.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      rewrite Nat.add_0_r.
      apply lift_preserved_by_useless_subst.
      assumption.
    + induction ms; simpl; auto.
      inversion_clear H.
      constructor; auto.
      rewrite traverse_list_length.
      rewrite Nat.add_0_r in H0 |- *.
      apply lifting_over_n_preserves_not_free_n; auto.
      lia.
  (* Case: struct_eta. *)
  - rename k into j, k0 into k.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump.
    eapply struct_eta_helper.
    + replace (k + length ts) with (length ts + k); auto with arith.
      rewrite traverse_list_length; f_equal.
      * symmetry.
        apply lift_lift_permutation; auto with arith.
      * apply lifting_over_n_doesnt_change_low_sequence_n.
        lia.
    + apply lift_distributes_over_subst.
  (* Case: struct_gc. *)
  - rewrite lift_distributes_over_bind.
    rewrite remove_closest_binding_and_lift_commute; auto.
    apply struct_gc.
    apply lifting_over_n_preserves_not_free_n; auto with arith.
  (* Case: struct_bind_left. *)
  - do 2 rewrite lift_distributes_over_bind.
    auto with cps.
  (* Case: struct_bind_right. *)
  - do 2 rewrite lift_distributes_over_bind.
    auto with cps.
Qed.

Global Hint Resolve struct_lift: cps.

Lemma cong_lift:
  forall a b,
  [a == b] ->
  forall i k,
  [lift i k a == lift i k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve cong_lift: cps.

Lemma struct_subst:
  forall a b,
  struct a b ->
  forall c k,
  struct (subst c k a) (subst c k b).
Proof.
  induction 1; intros.
  (* Case: struct_recjmp. *)
  - do 2 rewrite subst_distributes_over_bind.
    rewrite subst_distributes_over_jump.
    apply struct_recjmp_helper.
    + rewrite subst_distributes_over_apply_parameters.
      f_equal.
      rewrite map_length.
      rewrite lift_and_subst_commute; try lia.
      f_equal; lia.
    + reflexivity.
    + reflexivity.
    + rewrite map_length; auto.
      rewrite traverse_list_length; auto.
  (* Case: struct_distr. *)
  - do 5 rewrite subst_distributes_over_bind.
    apply struct_distr_helper.
    + apply subst_and_switch_bindings_commute.
    + do 2 rewrite traverse_list_length.
      rewrite lift_and_subst_commute.
      * reflexivity.
      * lia.
    + do 2 rewrite traverse_list_length.
      apply subst_and_right_cycle_commute with (p := 0).
      lia.
    + do 4 rewrite traverse_list_length.
      rewrite lift_and_subst_commute.
      * f_equal; lia.
      * lia.
    + induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        do 4 rewrite traverse_list_length.
        rewrite lift_and_subst_commute; auto with arith.
        f_equal; lia.
    + do 2 rewrite traverse_list_length.
      induction ns; simpl.
      * reflexivity.
      * f_equal; auto.
        do 4 rewrite traverse_list_length.
        rewrite lift_and_subst_commute; auto with arith.
        f_equal; lia.
    + induction ms; auto; intros.
      inversion_clear H.
      rewrite Nat.add_0_r in H0.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      rewrite Nat.add_0_r.
      apply subst_preserved_by_useless_subst.
      assumption.
    + induction ms; simpl; auto.
      inversion_clear H.
      constructor; auto.
      rewrite traverse_list_length.
      rewrite Nat.add_0_r in H0 |- *.
      apply substing_over_n_preserves_not_free_n; auto.
      lia.
  (* Case: struct_eta. *)
  - rename k into j, k0 into k.
    rewrite subst_distributes_over_bind.
    rewrite subst_distributes_over_jump.
    eapply struct_eta_helper.
    + replace (k + length ts) with (length ts + k); auto with arith.
      rewrite traverse_list_length; f_equal.
      * symmetry.
        apply lift_and_subst_commute; auto with arith.
      * apply substing_over_n_doesnt_change_low_sequence_n; lia.
    + apply subst_distributes_over_itself.
  (* Case: struct_gc. *)
  - rewrite subst_distributes_over_bind.
    rewrite remove_closest_binding_and_subst_commute; auto.
    apply struct_gc.
    apply substing_over_n_preserves_not_free_n; auto with arith.
  (* Case: struct_bind_left. *)
  - do 2 rewrite subst_distributes_over_bind.
    auto with cps.
  (* Case: struct_bind_right. *)
  - do 2 rewrite subst_distributes_over_bind.
    auto with cps.
Qed.

Global Hint Resolve struct_subst: cps.

Lemma cong_subst:
  forall a b,
  [a == b] ->
  forall x k,
  [subst x k a == subst x k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve cong_subst: cps.

Lemma cong_apply_parameters:
  forall xs k a b,
  [a == b] ->
  [apply_parameters xs k a == apply_parameters xs k b].
Proof.
  induction xs; eauto with cps.
Qed.

Global Hint Resolve cong_apply_parameters: cps.

Lemma cong_right_cycle:
  forall a b,
  [a == b] ->
  forall n k,
  [right_cycle n k a == right_cycle n k b].
Proof.
  unfold right_cycle; auto with cps.
Qed.

Global Hint Resolve cong_right_cycle: cps.
