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
    (bind (apply_parameters xs 0 (lift 1 (length ts) c)) ts c).

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

(* Float left: L { M } { N } == L { N } { M } if n doesn't appear in M. *)

Definition FLOAT_LEFT (R: relation pseudoterm): Prop :=
  forall b ms m ns n,
  not_free (length ms) m ->
  not_free_list 0 ms ->
  R (bind (bind b ms m) ns n)
    (bind (bind
      (switch_bindings 0 b)
      (traverse_list (lift 1) 0 ns)
        (lift 1 (length ns) n))
      (traverse_list remove_binding 0 ms)
        (remove_binding (length ms) m)).

(* Float right: L { M } { N } == L { M { N } } if n doesn't appear in L. *)

Definition FLOAT_RIGHT (R: relation pseudoterm): Prop :=
  forall b ms m ns n,
  not_free 1 b ->
  not_free_list 0 ms ->
  R (bind (bind b ms m) ns n)
    (bind
      (* Is this the same as remove_binding 1 b? *)
      (remove_binding 0 (switch_bindings 0 b))
      (traverse_list remove_binding 0 ms)
        (bind
          (right_cycle (length ms) 0 m)
          (traverse_list (lift (length ms)) 0 ns)
            (lift (length ms) (length ns) n))).

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

(* We'll just define the structural congruence, representing the axiomatic
   semantics, as the smallest equivalence relation closed under the [struct]
   rules above. *)

Notation sema := rst(struct).
Notation "[ a == b ]" := (sema a b)
  (at level 0, a, b at level 200): type_scope.

Lemma sema_eq:
  forall a b,
  a = b -> [a == b].
Proof.
  intros.
  destruct H.
  auto with cps.
Qed.

Lemma sema_refl:
  forall e,
  [e == e].
Proof.
  auto with cps.
Qed.

Global Hint Resolve sema_refl: cps.

Lemma sema_sym:
  forall a b,
  [a == b] -> [b == a].
Proof.
  auto with cps.
Qed.

Global Hint Resolve sema_sym: cps.

Lemma sema_trans:
  forall a b c,
  [a == b] -> [b == c] -> [a == c].
Proof.
  eauto with cps.
Qed.

Global Hint Resolve sema_trans: cps.

Lemma sema_struct:
  forall a b,
  struct a b -> [a == b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve sema_struct: cps.

Lemma sema_recjmp:
  RECJMP sema.
Proof.
  auto with cps.
Qed.

Global Hint Resolve sema_recjmp: cps.

Lemma sema_distr:
  DISTR sema.
Proof.
  auto with cps.
Qed.

Global Hint Resolve sema_distr: cps.

Lemma sema_eta:
  ETA sema.
Proof.
  auto with cps.
Qed.

Global Hint Resolve sema_eta: cps.

Lemma sema_gc:
  GC sema.
Proof.
  auto with cps.
Qed.

Global Hint Resolve sema_gc: cps.

Lemma sema_bind_left:
  LEFT sema.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve sema_bind_left: cps.

Lemma sema_bind_right:
  RIGHT sema.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve sema_bind_right: cps.

Instance sema_is_a_congruence: Congruence sema.
Proof.
  split.
  - split.
    + exact sema_refl.
    + exact sema_sym.
    + exact sema_trans.
  - exact sema_bind_left.
  - exact sema_bind_right.
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
  apply sema_distr.
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
  rewrite H, H0, H1, H2.
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
      rewrite H; f_equal.
      lia.
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

Lemma sema_lift:
  forall a b,
  [a == b] ->
  forall i k,
  [lift i k a == lift i k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve sema_lift: cps.

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
      rewrite H; f_equal.
      lia.
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

Lemma sema_subst:
  forall a b,
  [a == b] ->
  forall x k,
  [subst x k a == subst x k b].
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve sema_subst: cps.

Lemma sema_apply_parameters:
  forall xs k a b,
  [a == b] ->
  [apply_parameters xs k a == apply_parameters xs k b].
Proof.
  induction xs; eauto with cps.
Qed.

Global Hint Resolve sema_apply_parameters: cps.

Lemma sema_right_cycle:
  forall a b,
  [a == b] ->
  forall n k,
  [right_cycle n k a == right_cycle n k b].
Proof.
  unfold right_cycle; auto with cps.
Qed.

Global Hint Resolve sema_right_cycle: cps.

Lemma sema_float_left:
  FLOAT_LEFT sema.
Proof.
  unfold FLOAT_LEFT; intros.
  eapply sema_trans.
  - apply sema_distr; auto.
  - apply sema_bind_right.
    apply sema_struct; apply struct_gc_helper.
    + admit.
    + admit.
Admitted.

Lemma sema_float_right:
  FLOAT_RIGHT sema.
Proof.
  unfold FLOAT_RIGHT; intros.
  eapply sema_trans.
  - apply sema_distr; auto.
  - apply sema_bind_left.
    apply sema_gc.
    admit.
Admitted.

(* TODO: you know what to do here. *)

Goal
  forall b k,
  not_free (1 + k) b ->
  remove_binding k (switch_bindings k b) = remove_binding (1 + k) b.
Proof.
  unfold remove_binding.
  unfold switch_bindings.
  induction b using pseudoterm_deepind; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (lt_eq_lt_dec (1 + k) n) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_gt; auto.
      rewrite lift_bound_ge; try lia.
      rewrite subst_bound_gt; try lia.
      rewrite subst_bound_gt; try lia.
      f_equal; lia.
    + exfalso.
      inversion_clear H; auto.
    + rewrite subst_bound_lt; auto.
      rewrite lift_bound_lt; try lia.
      destruct (le_gt_dec k n).
      * rewrite subst_bound_eq; try lia.
        rewrite lift_bound_ge; auto.
        rewrite subst_bound_gt; try lia.
        f_equal; lia.
      * rewrite subst_bound_lt; auto.
        rewrite subst_bound_lt; auto.
  - rewrite lift_distributes_over_negation.
    do 3 rewrite subst_distributes_over_negation.
    f_equal.
    induction H; auto.
    inversion_clear H0.
    inversion_clear H2.
    simpl; f_equal.
    + do 4 rewrite traverse_list_length.
      replace (length l + S (S k)) with (2 + (length l + k)); try lia.
      replace (length l + S k) with (1 + (length l + k)); try lia.
      apply H.
      replace (1 + (length l + k)) with (length l + (1 + k)); try lia.
      assumption.
    + apply IHForall.
      constructor.
      assumption.
  - rewrite lift_distributes_over_jump.
    do 3 rewrite subst_distributes_over_jump.
    inversion_clear H0.
    f_equal.
    + apply IHb.
      assumption.
    + induction H; auto.
      inversion_clear H2.
      simpl; f_equal; auto.
      apply H; auto.
  - rewrite lift_distributes_over_bind.
    do 3 rewrite subst_distributes_over_bind.
    do 2 rewrite traverse_list_length.
    inversion_clear H0.
    f_equal.
    + apply IHb1; auto.
    + clear IHb1 IHb2 H1 H3.
      induction H; auto.
      inversion_clear H2.
      simpl; f_equal; auto.
      do 4 rewrite traverse_list_length.
      replace (length l + S (S k)) with (2 + (length l + k)); try lia.
      replace (length l + S k) with (1 + (length l + k)); try lia.
      apply H.
      replace (1 + (length l + k)) with (length l + (1 + k)); try lia.
      assumption.
    + apply IHb2.
      replace (1 + (k + length ts)) with (length ts + (1 + k)); try lia.
      assumption.
Qed.

Local Lemma technical1:
  forall n k c: nat,
  c < k ->
  (apply_parameters (high_sequence n) k
    (lift (1 + n) (k + n) c)) = lift 1 k c.
Proof.
  intros.
  rewrite lift_bound_lt; try lia.
  rewrite lift_bound_lt; try lia.
  induction n; simpl.
  - reflexivity.
  - rewrite sequence_length.
    rewrite subst_bound_lt; try lia.
    assumption.
Qed.

Local Lemma technical2:
  forall c n k,
  c >= n + k ->
  apply_parameters (high_sequence n) k (1 + n + c) = 1 + c.
Proof.
  intros.
  replace (1 + c) with ((1 + n + c) - n); try lia.
  cut (1 + n + c > k + n); try lia.
  generalize (1 + n + c) as m.
  induction n; simpl; intros.
  - f_equal; lia.
  - rewrite sequence_length.
    rewrite subst_bound_gt; try lia.
    replace (m - S n) with (pred m - n); try lia.
    apply IHn; lia.
Qed.

Local Lemma technical3:
  forall n k c: nat,
  c >= n + k ->
  (apply_parameters (high_sequence n) k
    (lift (1 + n) (k + n) c)) = lift 1 k c.
Proof.
  intros.
  rewrite lift_bound_ge; try lia.
  rewrite lift_bound_ge; try lia.
  apply technical2; auto.
Qed.

Local Lemma technical4:
  forall n k c: nat,
  c >= k ->
  c < n + k ->
  (apply_parameters (high_sequence n) k
    (lift (1 + n) (k + n) c)) = lift 1 k c.
Proof.
  intros.
  rewrite lift_bound_lt; try lia.
  rewrite lift_bound_ge; try lia.
  (* So here, we'll actually replace c with something! *)
  induction n.
  - exfalso.
    lia.
  - (* Are we there yet...? *)
    simpl; rewrite sequence_length.
    destruct (le_gt_dec (n + k) c).
    + clear IHn.
      rewrite subst_bound_eq; try lia.
      rewrite lift_bound_ge; try lia.
      replace c with (n + k); try lia.
      replace (n + k + S n) with (1 + n + (n + k)); try lia.
      apply technical2; auto.
    + rewrite subst_bound_lt; try lia.
      apply IHn; lia.
Qed.

Local Lemma technical5:
  forall c n k,
  apply_parameters (high_sequence n) k (lift (1 + n) (k + n) c) =
    lift 1 k c.
Proof.
  induction c using pseudoterm_deepind; intros.
  - induction n; simpl; auto.
  - induction n; simpl; auto.
  - induction n; simpl; auto.
  - induction n; simpl; auto.
  - rename n0 into m.
    destruct (le_gt_dec k n).
    + destruct (le_gt_dec (m + k) n).
      * apply technical3; auto.
      * apply technical4; auto.
    + apply technical1; auto.
  - do 2 rewrite lift_distributes_over_negation.
    rewrite apply_parameters_distributes_over_negation.
    f_equal.
    induction H; auto.
    simpl; f_equal; auto.
    do 3 rewrite traverse_list_length.
    rewrite plus_assoc.
    apply H.
  - do 2 rewrite lift_distributes_over_jump.
    rewrite apply_parameters_distributes_over_jump.
    f_equal.
    + apply IHc.
    + list induction over H.
  - do 2 rewrite lift_distributes_over_bind.
    rewrite apply_parameters_distributes_over_bind.
    rewrite traverse_list_length.
    f_equal.
    + apply IHc1.
    + clear IHc1 IHc2.
      induction H; auto.
      simpl; f_equal; auto.
      do 3 rewrite traverse_list_length.
      rewrite plus_assoc.
      apply H.
    + replace (k + n + length ts) with (k + length ts + n); try lia.
      apply IHc2.
Qed.

(*
  Turns out the rule (CONTR) is derivable!
  To show that L { m<x> = M } { m'<x> = M } == L[m/m'] { m<x> = M }...

  In a named version of the calculus, start with symmetry... then:

    1)                           L[m/m'] { m<x> = M } ==      (by LEFT, ETA-1)
    2)                L { m'<y> = m<y> } { m<x> = M } ==      (by DISTR)
    3)   L { m<x> = M } { m'<y> = m<y> { m<x> = M } } ==      (by RIGHT, RECJMP)
    4) L { m<x> = M } { m'<y> = M[y/x] { m<x> = M } } ==      (by RIGHT, GC)
    5)              L { m<x> = M } { m'<y> = M[y/x] } ==      (by ALPHA)
    6)                   L { m<x> = M } { m'<x> = M }

  This is a bit bureaucratic when using de Bruijn indexes; we of course don't
  need an alpha conversion, but we'll need a (FLOAT-LEFT) in the end to fix the
  bindings' positions, "undoing" the (DISTR) we did, but it should still work.
*)

Theorem sema_contr:
  CONTR sema.
Proof.
  unfold CONTR; intros.
  apply sema_sym.
  (* Is there a more elegant way? *)
  eapply sema_trans;
    [| eapply sema_trans;
      [| eapply sema_trans;
        [| eapply sema_trans;
          [| eapply sema_trans ] ] ] ].
  - apply sema_bind_left.
    apply sema_sym.
    apply sema_eta with (ts := traverse_list (lift 1) 0 ts).
  - apply sema_distr.
    induction ts; simpl.
    + constructor.
    + constructor; auto.
      rewrite traverse_list_length.
      apply lifting_more_than_n_makes_not_free_n; lia.
  - apply sema_bind_right.
    rewrite traverse_list_length.
    rewrite lift_bound_ge; auto.
    rewrite Nat.add_0_r.
    rewrite right_cycle_distributes_over_jump.
    rewrite right_cycle_bound_eq; auto.
    apply sema_recjmp.
    rewrite map_length.
    rewrite traverse_list_length.
    apply sequence_length.
  - apply sema_bind_right.
    apply sema_gc.
    rewrite right_cycle_low_sequence_n_equals_high_sequence_n; auto.
    rewrite traverse_list_length.
    rewrite lift_lift_simplification; try lia.
    (* This was annoying to show, but it's true! *)
    rewrite technical5.
    apply lifting_more_than_n_makes_not_free_n; lia.
  - (* The term is in the form [(switch_bindings 0 b) { M } { N }] now, as we
       have changed [b] with the (DISTR) call above. Note that when applying
       (FLOAT-LEFT) here we will change the term into [b { M } { N }]: only [b]
       will actually change, as [M] is already equal to [lift 1 0 N] here (thus
       moving [N] left makes it equal to [M], and moving [M] right makes it
       equal to [N]). *)
    apply sema_float_left.
    + rewrite traverse_list_length.
      apply lifting_more_than_n_makes_not_free_n; lia.
    + induction ts; auto with cps.
      simpl; constructor; auto.
      rewrite traverse_list_length.
      rewrite Nat.add_0_r.
      apply lifting_more_than_n_makes_not_free_n; lia.
  - (* The term is finally in the form [b { M } { N }], which is what we want,
       but we still need to prove that as the term form is a bit different. *)
    apply sema_eq; f_equal.
    + f_equal.
      * apply switch_bindings_is_involutive.
      * induction ts; auto.
        simpl; f_equal; auto.
        do 3 rewrite traverse_list_length.
        rewrite Nat.add_0_r.
        unfold remove_binding.
        rewrite subst_lift_simplification; auto.
        rewrite lift_zero_e_equals_e; auto.
      * do 3 rewrite traverse_list_length.
        rewrite right_cycle_low_sequence_n_equals_high_sequence_n; auto.
        rewrite lift_lift_simplification; try lia.
        (* Here's that annoying thing again! *)
        rewrite technical5.
        unfold remove_binding.
        rewrite subst_lift_simplification; auto.
        rewrite lift_zero_e_equals_e.
        reflexivity.
    + induction ts; auto.
      simpl; f_equal; auto.
      do 2 rewrite traverse_list_length.
      rewrite Nat.add_0_r.
      unfold remove_binding.
      rewrite subst_lift_simplification; auto.
      apply lift_zero_e_equals_e.
    + rewrite traverse_list_length.
      unfold remove_binding.
      rewrite subst_lift_simplification; auto.
      apply lift_zero_e_equals_e.
Qed.
