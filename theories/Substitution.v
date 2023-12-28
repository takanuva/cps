(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Relations.
Require Import Morphisms.

Import ListNotations.
Set Implicit Arguments.

(* TODO: move this tactic! Also... TODO: use this tactic more! *)

Tactic Notation "simplify" "decidable" "equality" :=
  repeat progress match goal with
  | |- context H [le_gt_dec ?m ?n] =>
    (destruct (le_gt_dec m n) as [ ? | _ ];
      [ exfalso; lia | idtac ]) +
    (destruct (le_gt_dec m n) as [ _ | ? ];
      [ idtac | exfalso; lia ])
  | |- context H [Nat.eq_dec ?m ?n] =>
    (destruct (Nat.eq_dec m n) as [ ? | _ ];
      [ exfalso; lia | idtac ]) +
    (destruct (Nat.eq_dec m n) as [ _ | ? ];
      [ idtac | exfalso; lia ])
  end.

(* *)

Section DeBruijn.

  Variable X: Set.

  (* *)

  Inductive substitution: Set :=
    | subst_ids
    | subst_lift (i: nat)
    | subst_cons (y: X) (s: substitution)
    | subst_comp (s: substitution) (t: substitution)
    | subst_upn (i: nat) (s: substitution).

  Definition subst_app (xs: list X) (s: substitution): substitution :=
    fold_right subst_cons s xs.

  (* TODO: turn this into a definition afterwards. *)

  Local Notation subst_drop i s :=
    (subst_comp (subst_lift i) s).

  Class deBruijn: Type := {
    var:
      nat -> X;
    traverse:
      (nat -> nat -> X) -> nat -> X -> X
  }.

  Context `{db: deBruijn}.

  Class deBruijnLaws: Type := {
    traverse_var:
      forall f k n,
      traverse f k (var n) = f k n;
    traverse_ids:
      forall k x,
      traverse (fun _ n => var n) k x = x;
    traverse_ext:
      forall f g k,
      (forall j n, j >= k -> f j n = g j n) ->
      forall x,
      traverse f k x = traverse g k x;
    traverse_fun:
      forall f g x k j,
      (* TODO: is there a nicer way to represent this...? *)
      traverse f k (traverse g j x) =
        traverse (fun i n => traverse f (i + k - j) (g i n)) j x
  }.

  Context `{db_laws: deBruijnLaws}.

  Definition lift_fun i k n :=
    if le_gt_dec k n then
      var (i + n)
    else
      var n.

  Definition lift (i: nat): nat -> X -> X :=
    traverse (lift_fun i).

  Fixpoint inst_fun (s: substitution) (k: nat) (n: nat): X :=
    if le_gt_dec k n then
      match s with
      | subst_ids =>
        var n
      | subst_lift i =>
        var (i + n)
      | subst_cons y s =>
        if Nat.eq_dec k n then
          lift k 0 y
        else
          inst_fun s k (n - 1)
      | subst_comp s t =>
        traverse (inst_fun t) k (inst_fun s k n)
      | subst_upn i s =>
        inst_fun s (i + k) n
      end
    else
      var n.

  Definition inst (s: substitution): nat -> X -> X :=
    traverse (inst_fun s).

  Global Coercion inst: substitution >-> Funclass.

  Definition subst (y: X): nat -> X -> X :=
    inst (subst_cons y subst_ids).

  Definition subst_equiv (s: substitution) (t: substitution): Prop :=
    forall k x,
    s k x = t k x.

  Global Instance subst_equivalence:
    Equivalence subst_equiv.
  Proof.
    split; now congruence.
  Qed.

  Global Instance inst_proper:
    Proper (subst_equiv ==> eq ==> eq ==> eq) inst.
  Proof.
    intros s t ? k _ () x _ ().
    apply H.
  Qed.

  Global Instance subst_cons_proper:
    Proper (eq ==> subst_equiv ==> subst_equiv) subst_cons.
  Proof.
    intros y _ () s t ? k x.
    unfold inst.
    apply traverse_ext.
    intros; simpl.
    destruct (lt_eq_lt_dec j n) as [ [ ? | ? ] | ? ].
    - simplify decidable equality.
      do 2 rewrite <- traverse_var.
      apply H.
    - now simplify decidable equality.
    - now simplify decidable equality.
  Qed.

  Global Instance subst_comp_proper:
    Proper (subst_equiv ==> subst_equiv ==> subst_equiv) subst_comp.
  Proof.
    intros s t ? u v ? k x.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (le_gt_dec j n).
    - replace (inst_fun s j n) with (s j (var n)).
      + rewrite H.
        unfold inst.
        rewrite traverse_var.
        apply traverse_ext.
        intros.
        do 2 rewrite <- traverse_var.
        apply H0.
      + unfold inst.
        now rewrite traverse_var.
    - reflexivity.
  Qed.

  Global Instance subst_upn_proper:
    Proper (eq ==> subst_equiv ==> subst_equiv) subst_upn.
  Proof.
    intros i _ () s t ? k x.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (le_gt_dec j n).
    - do 2 rewrite <- traverse_var.
      apply H.
    - reflexivity.
  Qed.

  (* ---------------------------------------------------------------------- *)

  Implicit Types x y z: X.
  Implicit Types s t u v: substitution.
  Implicit Types n m i k j: nat.

  Lemma subst_lift_unfold:
    forall i k x,
    lift i k x = subst_lift i k x.
  Proof.
    (* We have intensional equality between lift i and inst (subst_lift i)! *)
    auto.
  Qed.

  Lemma subst_subst_unfold:
    forall y k x,
    subst y k x = subst_cons y subst_ids k x.
  Proof.
    (* This is by definition, but we need a way to unfold it. *)
    auto.
  Qed.

  (* ---------------------------------------------------------------------- *)

  (* Id: x[I] = x *)
  Lemma subst_Id:
    forall k x,
    subst_ids k x = x.
  Proof.
    intros.
    unfold inst.
    rewrite traverse_ext with (g := fun _ n => var n).
    - now rewrite traverse_ids.
    - simpl; intros.
      now destruct (le_gt_dec j n).
  Qed.

  (* FVarCons: 0[y, s] = y *)
  Lemma subst_FVarCons:
    forall s k n y,
    k = n ->
    subst_cons y s k (var n) = subst_lift k 0 y.
  Proof.
    intros; subst.
    unfold inst at 1.
    rewrite traverse_var at 1; simpl.
    now simplify decidable equality.
  Qed.

  (* RVarCons: (1+n)[y, s] = n[s] *)
  Lemma subst_RVarCons:
    forall s y k n,
    n > k ->
    subst_cons y s k (var n) = s k (var (n - 1)).
  Proof.
    intros.
    unfold inst.
    do 2 rewrite traverse_var; simpl.
    now simplify decidable equality.
  Qed.

  (* VarShift1: n[S] = 1+n *)
  Lemma subst_VarShift1:
    forall i n k,
    n >= k ->
    subst_lift i k (var n) = var (i + n).
  Proof.
    intros.
    unfold inst.
    rewrite traverse_var; simpl.
    now simplify decidable equality.
  Qed.

  (* VarShift2: n[S o s] = (1+n)[s] *)
  Lemma subst_VarShift2:
    forall s i n k,
    n >= k ->
    subst_comp (subst_lift i) s k (var n) = s k (var (i + n)).
  Proof.
    intros.
    unfold inst.
    rewrite traverse_var; simpl.
    now simplify decidable equality.
  Qed.

  (* FVarLift1: 0[U(s)] = 0 *)
  Lemma subst_FVarLift1:
    forall n k i s,
    i + k > n ->
    subst_upn i s k (var n) = var n.
  Proof.
    admit.
  Admitted.

  (* TODO FVarLift2: 0[U(s) o t] = 0[t] *)
  Lemma subst_FVarLift2:
    forall s t k i n,
    i + k > n ->
    subst_comp (subst_upn i s) t k (var n) = t k (var n).
  Proof.
    intros.
    unfold inst.
    rewrite traverse_var; simpl.
    destruct (le_gt_dec k n).
    - (* now rewrite inst_fun_bvar by lia. *)
      admit.
    - (* rewrite traverse_var.
      now rewrite inst_fun_bvar by lia. *)
      admit.
  Admitted.

  (* RVarLift1: (1+n)[U(s)] = n[s o S] *)
  Lemma subst_RVarLift1:
    forall i k s n,
    i + k <= n ->
    subst_upn i s k (var n) = subst_comp s (subst_lift i) k (var (n - i)).
  Proof.
    admit.
  Admitted.

  (* RVarLift2: (1+n)[U(s) o t] = n[s o S o t] *)
  Lemma subst_RVarLift2:
    forall i k s t n,
    i + k <= n ->
    subst_comp (subst_upn i s) t k (var n) =
      subst_comp s (subst_comp (subst_lift i) t) k (var (n - i)).
  Proof.
    admit.
  Admitted.

  (* Clos: x[s][t] = x[s o t] *)
  Lemma subst_Clos:
    forall s t k j x,
    t j (s k x) = subst_comp (subst_upn k s) (subst_upn j t) 0 x.
  Proof.
    intros.
    replace k with (k + 0) at 1 by lia.
    (*
    rewrite <- subst_inst_lift.
    unfold inst.
    rewrite traverse_fun.
    apply traverse_ext; simpl; intros l n _.
    replace (l + j - 0) with (l + j) by lia.
    destruct (le_gt_dec l n).
    - (* The term on the right-hand side is just inst_fun (subst_upn j t). *)
      fold (inst t).
      replace (l + j) with (j + l) by lia.
      rewrite <- subst_inst_lift.
      (* Both sides are intensionally equal now! *)
      reflexivity.
    - rewrite traverse_var.
      now rewrite inst_fun_bvar by lia.
    *)
  Admitted.

  Lemma foo:
    forall s k n,
    k > n ->
    s k (var n) = var n.
  Proof.
    admit.
  Admitted.

  Lemma bar:
    forall i k s x,
    subst_upn i s k x = s (i + k) x.
  Proof.
    admit.
  Admitted.

  Lemma baz:
    forall s i k n,
    subst_comp s (subst_lift i) k (var n) =
      s (i + k) (var (i + n)).
  Proof.
    admit.
  Admitted.

  (* ---------------------------------------------------------------------- *)

  Local Notation "s ~ t" := (subst_equiv s t) (at level 70, no associativity).

  (* ShiftZero (additional!): S^0 ~ I *)
  Lemma subst_ShiftZero:
    forall n,
    n = 0 ->
    subst_lift n ~ subst_ids.
  Proof.
    intros n ? k x; subst.
    (* Intensionally equal! *)
    reflexivity.
  Qed.

  (* LiftZero (additional!): U^0(s) ~ s *)
  Lemma subst_LiftZero:
    forall n s,
    n = 0 ->
    subst_upn n s ~ s.
  Proof.
    intros n s ? k x; subst.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (le_gt_dec j n).
    - reflexivity.
    - (* now rewrite inst_fun_bvar by lia. *)
      admit.
  Admitted.

  (* VarShift: (0, S) ~ I *)
  Lemma subst_VarShift:
    forall n i,
    i = 1 + n ->
    (* Nice generalization! *)
    subst_cons (var n) (subst_lift i) ~ subst_lift n.
  Proof.
    intros n i ? k x; subst.
    unfold inst.
    apply traverse_ext.
    simpl; intros j m ?.
    destruct (lt_eq_lt_dec j m) as [ [ ? | ? ] | ? ].
    - simplify decidable equality.
      f_equal; lia.
    - simplify decidable equality.
      unfold lift.
      rewrite traverse_var.
      unfold lift_fun; simpl.
      f_equal; lia.
    - now simplify decidable equality.
  Qed.

  (* ShiftCons: S o (y, s) ~ s *)
  Lemma subst_ShiftCons:
    forall i y s,
    i > 0 ->
    subst_comp (subst_lift i) (subst_cons y s) ~
      subst_comp (subst_lift (i - 1)) s.
  Proof.
    intros i y s ? k x.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (lt_eq_lt_dec j n) as [ [ ? | ? ] | ? ].
    - simplify decidable equality.
      do 2 rewrite traverse_var.
      simplify decidable equality.
      f_equal; lia.
    - simplify decidable equality.
      do 2 rewrite traverse_var.
      simplify decidable equality.
      f_equal; lia.
    - now simplify decidable equality.
  Qed.

  (* IdL: I o s ~ s *)
  Lemma subst_IdL:
    forall s,
    subst_comp subst_ids s ~ s.
  Proof.
    intros s k x.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (le_gt_dec j n).
    - now rewrite traverse_var.
    - (* now rewrite inst_fun_bvar. *)
      admit.
  Admitted.

  (* IdR: s o I ~ s *)
  Lemma subst_IdR:
    forall s,
    subst_comp s subst_ids ~ s.
  Proof.
    intros s k x.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (le_gt_dec j n).
    - rewrite traverse_ext with (g := fun _ n => var n).
      + now rewrite traverse_ids.
      + intros i m ?.
        now destruct (le_gt_dec i m).
    - (* now rewrite inst_fun_bvar. *)
      admit.
  Admitted.

  (* AssEnv: (s o t) o u ~ s o (t o u) *)
  Lemma subst_AssEnv:
    forall s t u,
    subst_comp (subst_comp s t) u ~ subst_comp s (subst_comp t u).
  Proof.
    intros s t u k x.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (le_gt_dec j n).
    - rewrite traverse_fun.
      apply traverse_ext.
      intros i m ?.
      destruct (le_gt_dec i m).
      + now replace (i + j - j) with i by lia.
      + (* rewrite inst_fun_bvar by lia.
        rewrite traverse_var.
        now rewrite inst_fun_bvar by lia. *)
        admit.
    - reflexivity.
  Admitted.

  (* TODO MapEnv: (y, s) o t ~ (y[t], s o t) *)
  Lemma subst_MapEnv:
    forall y s t,
    subst_comp (subst_cons y s) t ~ subst_cons (t 0 y) (subst_comp s t).
  Proof.
    intros y s t k x.
    unfold inst.
    apply traverse_ext; simpl; intros.
    destruct (lt_eq_lt_dec j n) as [ [ ? | ? ] | ? ].
    - now simplify decidable equality.
    - simplify decidable equality.
      replace (traverse (inst_fun t)) with (inst t) by auto.
      (*
      rewrite subst_lift_inst_commute by lia.
      f_equal; lia.
      *)
      admit.
    - now simplify decidable equality.
  Admitted.

  (* SCons: (0[s], S o s) ~ s *)
  Lemma subst_SCons:
    forall s k n m,
    k = 0 ->
    m = 1 + n ->
    (* We want to simplify a drop! Notice k has to be 0 to avoid lifting. *)
    subst_cons (s k (var n)) (subst_comp (subst_lift m) s) ~
      subst_comp (subst_lift n) s.
  Proof.
    intros s k n m ? ?; subst.
    intros k x; unfold inst.
    apply traverse_ext.
    intros j m ?; simpl.
    destruct (lt_eq_lt_dec j m) as [ [ ? | ? ] | ? ].
    - simplify decidable equality.
      repeat f_equal; lia.
    - simplify decidable equality.
      replace (traverse (inst_fun s)) with (inst s) by auto.
      (*
      rewrite subst_lift_inst_commute by lia.
      unfold lift; rewrite traverse_var.
      unfold lift_fun; simpl.
      replace (j + 0) with j by lia.
      do 2 f_equal; lia.
      *)
      admit.
    - now simplify decidable equality.
  Admitted.

  (* ShiftLift1: S o U(s) ~ s o S, variants A and B *)
  Lemma subst_ShiftLift1A:
    forall i j s,
    i >= j ->
    subst_comp (subst_lift i) (subst_upn j s) ~
      subst_comp (subst_lift (i - j)) (subst_comp s (subst_lift j)).
  Proof.
    admit.
  Admitted.

  Lemma subst_ShiftLift1B:
    forall i j s,
    i <= j ->
    subst_comp (subst_lift i) (subst_upn j s) ~
      subst_comp (subst_upn (j - i) s) (subst_lift i).
  Proof.
    admit.
  Admitted.

  (* ShiftLift2: S o (U(s) o t) ~ s o S o t, variants A and B *)
  Lemma subst_ShiftLift2A:
    forall i j s t,
    i >= j ->
    subst_comp (subst_lift i) (subst_comp (subst_upn j s) t) ~
      subst_comp (subst_lift (i - j)) (subst_comp s
        (subst_comp (subst_lift j) t)).
  Proof.
    admit.
  Admitted.

  Lemma subst_ShiftLift2B:
    forall i j s t,
    i <= j ->
    subst_comp (subst_lift i) (subst_comp (subst_upn j s) t) ~
      subst_comp (subst_upn (j - i) s) (subst_comp (subst_lift i) t).
  Proof.
    admit.
  Admitted.

  (* Lift1: U(s) o U(t) ~ U(s o t), variants A and B *)
  Lemma subst_Lift1A:
    forall s t k j,
    k >= j ->
    subst_comp (subst_upn k s) (subst_upn j t) ~
      subst_upn j (subst_comp (subst_upn (k - j) s) t).
  Proof.
    admit.
  Admitted.

  Lemma subst_Lift1B:
    forall s t k j,
    j >= k ->
    subst_comp (subst_upn k s) (subst_upn j t) ~
      subst_upn k (subst_comp s (subst_upn (j - k) t)).
  Proof.
    admit.
  Admitted.

  (* TODO Lift2: U(s) o (U(t) o u) ~ U(s o t) o u, variants A and B *)
  Lemma subst_Lift2A:
    forall s t u k j,
    k >= j ->
    subst_comp (subst_upn k s) (subst_comp (subst_upn j t) u) ~
      subst_comp (subst_upn j (subst_comp (subst_upn (k - j) s) t)) u.
  Proof.
    admit.
  Admitted.

  Lemma subst_Lift2B:
    forall s t u k j,
    j >= k ->
    subst_comp (subst_upn k s) (subst_comp (subst_upn j t) u) ~
      subst_comp (subst_upn k (subst_comp s (subst_upn (j - k) t))) u.
  Proof.
    admit.
  Admitted.

  (* LiftEnv: U(s) o (y, t) ~ (y, s o t) *)
  Lemma subst_LiftEnv:
    forall n s y t,
    n > 0 ->
    subst_comp (subst_upn n s) (subst_cons y t) ~
      subst_cons y (subst_comp (subst_upn (n - 1) s) t).
  Proof.
    intros n s y t ? k x.
    unfold inst.
    apply traverse_ext; intros j m ?.
    simpl.
    destruct (lt_eq_lt_dec j m) as [ [ ? | ? ] | ? ].
    - simplify decidable equality.
      admit.
    - simplify decidable equality.
      (*
      rewrite inst_fun_bvar by lia.
      rewrite traverse_var.
      now simplify decidable equality. *)
      admit.
    - now simplify decidable equality.
  Admitted.

  (* LiftId: U(I) ~ I *)
  Lemma subst_LiftId:
    forall i,
    subst_upn i subst_ids ~ subst_ids.
  Proof.
    admit.
  Admitted.

  (* ShiftShift (additional!): S^i o S^j = S^(i + j) *)
  Lemma subst_ShiftShift:
    forall i j,
    subst_comp (subst_lift i) (subst_lift j) ~ subst_lift (i + j).
  Proof.
    admit.
  Admitted.

  (* ---------------------------------------------------------------------- *)

End DeBruijn.

(* *)

Arguments deBruijn: clear implicits.
Arguments deBruijnLaws: clear implicits.
Arguments substitution {X}.
Arguments subst_ids {X}.
Arguments subst_lift {X}.
Arguments subst_cons {X}.
Arguments subst_comp {X}.
Arguments subst_upn {X}.
Arguments subst_app {X}.

(* *)

Create HintDb sigma.

Ltac sigma_solver :=
  match goal with
  | |- @deBruijnLaws _ _ =>
    typeclasses eauto
  | |- ?G =>
    lia
  end.

(* *)

Global Hint Rewrite subst_lift_unfold: sigma.
Global Hint Rewrite subst_subst_unfold: sigma.

Global Hint Rewrite subst_Id using sigma_solver: sigma.
Global Hint Rewrite subst_FVarCons using sigma_solver: sigma.
Global Hint Rewrite subst_RVarCons using sigma_solver: sigma.
Global Hint Rewrite subst_VarShift1 using sigma_solver: sigma.
Global Hint Rewrite subst_VarShift2 using sigma_solver: sigma.
Global Hint Rewrite subst_FVarLift1 using sigma_solver: sigma.
Global Hint Rewrite subst_FVarLift2 using sigma_solver: sigma.
Global Hint Rewrite subst_RVarLift1 using sigma_solver: sigma.
Global Hint Rewrite subst_RVarLift2 using sigma_solver: sigma.
Global Hint Rewrite subst_Clos using sigma_solver: sigma.
Global Hint Rewrite foo using sigma_solver: sigma.
Global Hint Rewrite bar using sigma_solver: sigma.
Global Hint Rewrite baz using sigma_solver: sigma.

Global Hint Rewrite subst_ShiftZero using sigma_solver: sigma.
Global Hint Rewrite subst_LiftZero using sigma_solver: sigma.
Global Hint Rewrite subst_VarShift using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftCons using sigma_solver: sigma.
Global Hint Rewrite subst_IdL using sigma_solver: sigma.
Global Hint Rewrite subst_IdR using sigma_solver: sigma.
Global Hint Rewrite subst_AssEnv using sigma_solver: sigma.
Global Hint Rewrite subst_MapEnv using sigma_solver: sigma.
Global Hint Rewrite subst_SCons using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftLift1A using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftLift1B using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftLift2A using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftLift2B using sigma_solver: sigma.
Global Hint Rewrite subst_Lift1A using sigma_solver: sigma.
Global Hint Rewrite subst_Lift1B using sigma_solver: sigma.
Global Hint Rewrite subst_Lift2A using sigma_solver: sigma.
Global Hint Rewrite subst_Lift2B using sigma_solver: sigma.
Global Hint Rewrite subst_LiftEnv using sigma_solver: sigma.
Global Hint Rewrite subst_LiftId using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftShift using sigma_solver: sigma.

(* TODO: figure out a way to restrict these rewritings. *)

Create HintDb sigma_cleanup.

Lemma minus_Sn_Sm:
  forall n m,
  S n - S m = n - m.
Proof.
  auto.
Qed.

Global Hint Rewrite Nat.sub_0_r: sigma_cleanup.
Global Hint Rewrite Nat.add_0_r: sigma_cleanup.
Global Hint Rewrite Nat.add_0_l: sigma_cleanup.
Global Hint Rewrite Nat.add_sub_assoc using lia: sigma_cleanup.
Global Hint Rewrite <- plus_n_Sm: sigma_cleanup.
Global Hint Rewrite plus_Sn_m: sigma_cleanup.
Global Hint Rewrite minus_Sn_Sm: sigma_cleanup.

(* *)

Ltac sigma :=
  (* TODO: is it possible to fold var in here...? *)
  (rewrite_strat topdown (hints sigma));
  (* TODO: we want to restrict the context in those... somehow... *)
  (rewrite_strat try topdown (hints sigma_cleanup)).

(* -------------------------------------------------------------------------- *)

Section Tests.

  (* For now, we're not actually checking that the rewriting rules above are
     confluent and complete (although we indeed want them to be), as we need to
     expand them a bit from the definition of the sigma calculus. In order to
     make up for that, lets just check that the rewriting rules tactic is enough
     to validate the algebraic laws for both the sigma SP calculus, which was
     used by the autosubst library, and for the confluent sigma calculus. For
     reference, both calculi are described in the "Confluence Properties of Weak
     and Strong Calculi" paper. *)

  Variable X: Set.
  Context `{db_laws: deBruijnLaws X}.

  Implicit Types x y z: X.
  Implicit Types s t u: @substitution X.

  (* Lets first check the laws for the sigma SP calculus... we note that these
     differ a bit from the paper because they take non-zero indexes to be zero
     applied to the lifting substitution in there, i.e., n = 0[S^n]. *)

  Goal
    forall y s,
    (* FVarCons: 0[y, s] = y *)
    subst_cons y s 0 (var 0) = y.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall y s n,
    (* RVarCons: (1+n)[y, s] = n[s] *)
    subst_cons y s 0 (var (1 + n)) = s 0 (var n).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall n,
    (* VarShift1: n[S] = 1+n *)
    subst_lift 1 0 (var n) = var (1 + n).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall x,
    (* Id: x[I] = x *)
    subst_ids 0 x = x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall x s t,
    (* Clos: x[s][t] = x[s o t] *)
    t 0 (s 0 x) = subst_comp s t 0 x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall k x,
    (* VarShift: (0, S) ~ I *)
    subst_cons (var 0) (subst_lift 1) k x = x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall y s k x,
    (* ShiftCons: S o (y, s) ~ s *)
    subst_comp (subst_lift 1) (subst_cons y s) k x = s k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s k x,
    (* IdL: I o s ~ s *)
    subst_comp subst_ids s k x = s k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s k x,
    (* IdR: s o I ~ s *)
    subst_comp s subst_ids k x = s k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s t u k x,
    (* AssEnv: (s o t) o u ~ s o (t o u) *)
    subst_comp (subst_comp s t) u k x = subst_comp s (subst_comp t u) k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall y s t k x,
    (* MapEnv: (y, s) o t ~ (y[t], s o t) *)
    subst_comp (subst_cons y s) t k x = subst_cons (t 0 y) (subst_comp s t) k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s k x,
    (* SCons: (0[s], S o s) ~ s *)
    subst_cons (s 0 (var 0)) (subst_comp (subst_lift 1) s) k x = s k x.
  Proof.
    intros.
    now sigma.
  Qed.

  (* Now, lets check the additional laws for the confluent sigma calculus...
     notice that the confluent sigma calculus seems to drop the (VarShift) and
     the (SCons) rule, although we still want those because it allows us to
     equate more terms in the presence of metavariables. *)

  Goal
    forall s n,
    (* VarShift2: n[S o s] = (1+n)[s] *)
    subst_comp (subst_lift 1) s 0 (var n) = s 0 (var (1 + n)).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s,
    (* FVarLift1: 0[U(s)] = 0 *)
    subst_upn 1 s 0 (var 0) = var 0.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s t,
    (* FVarLift2: 0[U(s) o t] = 0[t] *)
    subst_comp (subst_upn 1 s) t 0 (var 0) = t 0 (var 0).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s n,
    (* RVarLift1: (1+n)[U(s)] = n[s o S] *)
    subst_upn 1 s 0 (var (1 + n)) = subst_comp s (subst_lift 1) 0 (var n).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s t n,
    (* RVarLift2: (1+n)[U(s) o t] = n[s o S o t] *)
    subst_comp (subst_upn 1 s) t 0 (var (1 + n)) =
      subst_comp s (subst_comp (subst_lift 1) t) 0 (var n).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s k x,
    (* ShiftLift1: S o U(s) ~ s o S *)
    subst_comp (subst_lift 1) (subst_upn 1 s) k x =
      subst_comp s (subst_lift 1) k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s t k x,
    (* ShiftLift2: S o (U(s) o t) ~ s o S o t *)
    subst_comp (subst_lift 1) (subst_comp (subst_upn 1 s) t) k x =
      subst_comp s (subst_comp (subst_lift 1) t) k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s t k x,
    (* Lift1: U(s) o U(t) ~ U(s o t) *)
    subst_comp (subst_upn 1 s) (subst_upn 1 t) k x =
      subst_upn 1 (subst_comp s t) k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s t u k x,
    (* Lift2: U(s) o (U(t) o u) ~ U(s o t) o u *)
    subst_comp (subst_upn 1 s) (subst_comp (subst_upn 1 t) u) k x =
      subst_comp (subst_upn 1 (subst_comp s t)) u k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s t y k x,
    (* LiftEnv: U(s) o (y, t) ~ (y, s o t) *)
    subst_comp (subst_upn 1 s) (subst_cons y t) k x =
      subst_cons y (subst_comp s t) k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall k x,
    (* LiftId: U(I) ~ I *)
    subst_upn 1 subst_ids k x = subst_ids k x.
  Proof.
    intros.
    now sigma.
  Qed.

  (* We can also check some rules from the original de Bruijn implementation!
     These rules are used in the "Coq in Coq" paper I was originally following,
     but they can be found in older papers such as Huet's "Residual Theory in
     lambda-calculus". *)

  Local Ltac equal_modulo_arith :=
    (* TODO: do we want this to be global...? *)
    reflexivity || assumption || lia || (f_equal; equal_modulo_arith).

  Local Hint Extern 0 => equal_modulo_arith: core.

  Goal
    (* Lifting by zero is a no-op. *)
    forall k x,
    lift 0 k x = x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    (* Instantiation and lifting commutation. *)
    forall x s i k j,
    k <= j ->
    lift i k (inst s j x) = inst s (i + j) (lift i k x).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    (* Lifting permutation. *)
    forall x i j k l,
    k <= l ->
    lift i k (lift j l x) = lift j (i + l) (lift i k x).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    (* Lifting simplification. *)
    forall x i j k l,
    k <= l + j ->
    l <= k ->
    lift i k (lift j l x) = lift (i + j) l x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    (* Simplification of substitution and lifting. *)
    forall x y i p k,
    p <= i + k ->
    k <= p ->
    subst y p (lift (1 + i) k x) = lift i k x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall i x y p k,
    lift i (p + k) (subst y p x) = subst (lift i k y) p (lift i (1 + p + k) x).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall x y z p k,
    subst y (p + k) (subst z p x) =
      subst (subst y k z) p (subst y (1 + p + k) x).
  Proof.
    intros.
    now sigma.
  Qed.

End Tests.
