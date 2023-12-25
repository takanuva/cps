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

  Class deBruijn: Type := {
    var:
      nat -> X;
    traverse:
      (nat -> nat -> X) -> nat -> X -> X;
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

  Context `{db: deBruijn}.

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
    lift i k x = inst (subst_lift i) k x.
  Proof.
    (* We have intensional equality between lift i and inst (subst_lift i)! *)
    auto.
  Qed.

  (* ---------------------------------------------------------------------- *)

  Lemma subst_ids_simpl:
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

  Lemma inst_fun_bvar:
    forall s k n,
    n < k ->
    inst_fun s k n = var n.
  Proof.
    intros.
    destruct s; simpl;
    now simplify decidable equality.
  Qed.

  Lemma subst_bvar:
    forall s k n,
    n < k ->
    s k (var n) = var n.
  Proof.
    intros.
    unfold inst.
    rewrite traverse_var.
    now rewrite inst_fun_bvar.
  Qed.

  Lemma subst_fvar_cons:
    forall s k n x,
    k = n ->
    subst_cons x s k (var n) = subst_lift k 0 x.
  Proof.
    intros; subst.
    unfold inst at 1.
    rewrite traverse_var at 1; simpl.
    now simplify decidable equality.
  Qed.

  Lemma subst_rvar_cons:
    forall s x k n,
    n > k ->
    subst_cons x s k (var n) = s k (var (n - 1)).
  Proof.
    intros.
    unfold inst.
    do 2 rewrite traverse_var; simpl.
    now simplify decidable equality.
  Qed.

  Lemma subst_var_shift1:
    forall i n k,
    n >= k ->
    subst_lift i k (var n) = var (i + n).
  Proof.
    intros.
    unfold inst.
    rewrite traverse_var; simpl.
    now simplify decidable equality.
  Qed.

  Lemma subst_inst_lift:
    forall n s k x,
    subst_upn n s k x = s (n + k) x.
  Proof.
    intros.
    unfold inst.
    rewrite <- traverse_ids with (x := x) (k := n + k) at 1.
    rewrite traverse_fun.
    apply traverse_ext.
    intros j m ?.
    rewrite traverse_var; simpl.
    (* Oh well... *)
    destruct (le_gt_dec (j + k - (n + k)) m).
    - f_equal; lia.
    - now rewrite inst_fun_bvar by lia.
  Qed.

  Lemma lift_lift_permutation:
    forall x i j k l,
    k <= l ->
    lift i k (lift j l x) = lift j (i + l) (lift i k x).
  Proof.
    intros.
    do 4 rewrite subst_lift_unfold.
    replace l with ((l - k) + k) at 1 by lia.
    rewrite <- subst_inst_lift.
    unfold inst.
    do 2 rewrite traverse_fun.
    apply traverse_ext; simpl; intros p n ?.
    destruct (le_gt_dec p n).
    - remember (l - k + p) as m.
      rewrite traverse_var.
      destruct (le_gt_dec m n).
      + rewrite traverse_var; simpl.
        simplify decidable equality.
        f_equal; lia.
      + rewrite traverse_var; simpl.
        now simplify decidable equality.
    - remember (l - k + p) as m.
      rewrite traverse_var.
      destruct (le_gt_dec m n).
      + rewrite traverse_var; simpl.
        now simplify decidable equality.
      + rewrite traverse_var; simpl.
        now simplify decidable equality.
  Qed.

  Lemma lift_lift_simplification:
    forall x i j k l,
    k <= l + j ->
    l <= k ->
    lift i k (lift j l x) = lift (i + j) l x.
  Proof.
    intros.
    do 3 rewrite subst_lift_unfold.
    unfold inst.
    rewrite traverse_fun.
    apply traverse_ext; simpl; intros p n ?.
    destruct (le_gt_dec p n).
    - rewrite traverse_var.
      simplify decidable equality.
      f_equal; lia.
    - rewrite traverse_var.
      now simplify decidable equality.
  Qed.

  Lemma subst_lift_inst_commute:
    forall s x i k j,
    k <= j ->
    lift i k (inst s j x) = inst s (i + j) (lift i k x).
  Proof.
    (* By induction on the kind of substitution we're doing. *)
    induction s; intros.
    (* Case: identity. *)
    - (* Identity can't change a thing. *)
      now do 2 rewrite subst_ids_simpl.
    (* Case: lifting. *)
    - (* We'll just need to merge these lifts, both of them. *)
      apply lift_lift_permutation.
      lia.
    (* Case: consing. *)
    - do 2 rewrite subst_lift_unfold.
      replace j with ((j - k) + k) at 1 by lia.
      rewrite <- subst_inst_lift.
      unfold inst.
      do 2 rewrite traverse_fun.
      apply traverse_ext; simpl; intros l n ?.
      (* Are we in scope for any change at all? *)
      destruct (le_gt_dec l n).
      + (* Some change... *)
        remember (j - k + l) as m.
        (* Will we be performing the substitution or...? *)
        destruct (lt_eq_lt_dec m n) as [ [ ? | ? ] | ? ].
        * (* We're too big, so follow by inductive hypothesis... *)
          rewrite traverse_var.
          simplify decidable equality.
          fold (lift_fun i) (lift i).
          do 2 rewrite <- traverse_var.
          fold (inst s).
          replace (l + k - k) with l by lia.
          rewrite IHs by lia.
          unfold lift, lift_fun.
          rewrite traverse_var.
          simplify decidable equality.
          replace (i + (n - 1)) with (i + n - 1) by lia.
          replace (l + (i + j) - k) with (i + m) by lia.
          reflexivity.
        * (* We're doing the substitution now, then lifting... *)
          rewrite traverse_var.
          subst; simplify decidable equality.
          fold (lift_fun i) (lift i).
          (* Of course, we can simplify these lifts! *)
          rewrite lift_lift_simplification by lia.
          f_equal; lia.
        * (* We're just lifting... *)
          rewrite traverse_var.
          simplify decidable equality.
          rewrite traverse_var.
          now simplify decidable equality.
      + (* No change whatsoever. *)
        do 2 rewrite traverse_var.
        now simplify decidable equality.
    (* Case: composition. *)
    - (* We just need to split the occurrences to use the hypotheses. *)
      do 2 rewrite subst_lift_unfold.
      replace j with ((j - k) + k) at 1 by lia.
      rewrite <- subst_inst_lift.
      unfold inst.
      do 2 rewrite traverse_fun.
      apply traverse_ext; simpl; intros l n ?.
      destruct (le_gt_dec l n).
      + remember (j - k + l) as m.
        (* Will we be performing the substitution or...? *)
        destruct (le_gt_dec m n).
        * (* There's a long way to go, but these are fine. *)
          rewrite traverse_var.
          simplify decidable equality.
          fold (lift_fun i) (lift i).
          fold (inst s2).
          rewrite IHs2 by lia.
          f_equal; try lia.
          do 2 rewrite <- traverse_var.
          fold (inst s1).
          rewrite IHs1 by lia.
          f_equal; try lia.
          unfold lift, lift_fun.
          rewrite traverse_var.
          (* Finally! *)
          now simplify decidable equality.
        * (* Just lifting for now. *)
          do 2 rewrite traverse_var.
          now simplify decidable equality.
      + (* Nothing at all! *)
        do 2 rewrite traverse_var.
        now simplify decidable equality.
    (* Case: entering a binder. *)
    - (* We can just adjust the distance and use the inductive hypothesis. *)
      do 2 rewrite subst_inst_lift.
      rewrite IHs by lia.
      f_equal; lia.
  Qed.

  Lemma subst_comp_clos:
    forall s t k j x,
    t j (s k x) = subst_comp (subst_upn k s) (subst_upn j t) 0 x.
  Proof.
    intros.
    replace k with (k + 0) at 1 by lia.
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
  Qed.

  Lemma subst_var_shift2:
    forall s i n k,
    n >= k ->
    subst_comp (subst_lift i) s k (var n) = s k (var (i + n)).
  Proof.
    intros.
    unfold inst.
    rewrite traverse_var; simpl.
    now simplify decidable equality.
  Qed.

  Lemma subst_fvar_lift2:
    forall s t k i n,
    i + k > n ->
    subst_comp (subst_upn i s) t k (var n) = t k (var n).
  Proof.
    intros.
    unfold inst.
    rewrite traverse_var; simpl.
    destruct (le_gt_dec k n).
    - now rewrite inst_fun_bvar by lia.
    - rewrite traverse_var.
      now rewrite inst_fun_bvar by lia.
  Qed.

  (* ---------------------------------------------------------------------- *)

  Local Notation "s ~ t" := (subst_equiv s t) (at level 70, no associativity).

  Lemma subst_shift_zero:
    forall n,
    n = 0 ->
    subst_lift n ~ subst_ids.
  Proof.
    intros n ? k x; subst.
    unfold inst.
    now apply traverse_ext.
  Qed.

  Lemma subst_lift_zero:
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
    - now rewrite inst_fun_bvar.
  Qed.

  (* Notice the generalization in the following rule! *)

  Lemma subst_var_shift:
    forall n i,
    i = 1 + n ->
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

  Lemma subst_shift_cons:
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

  Lemma subst_id_left:
    forall s,
    subst_comp subst_ids s ~ s.
  Proof.
    intros s k x.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (le_gt_dec j n).
    - now rewrite traverse_var.
    - now rewrite inst_fun_bvar.
  Qed.

  Lemma subst_id_right:
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
    - now rewrite inst_fun_bvar.
  Qed.

  Lemma subst_comp_assoc:
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
      + rewrite inst_fun_bvar by lia.
        rewrite traverse_var.
        now rewrite inst_fun_bvar by lia.
    - reflexivity.
  Qed.

  Lemma subst_comp_cons_map:
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
      rewrite subst_lift_inst_commute by lia.
      f_equal; lia.
    - now simplify decidable equality.
  Qed.

  Lemma subst_cons_simpl:
    forall s k n m,
    k = 0 ->
    m = 1 + n ->
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
      rewrite subst_lift_inst_commute by lia.
      unfold lift; rewrite traverse_var.
      unfold lift_fun; simpl.
      replace (j + 0) with j by lia.
      do 2 f_equal; lia.
    - now simplify decidable equality.
  Qed.

  (* This goes on the opposite direction than the confluent sigma calculus! *)

  Lemma subst_comp_shift1:
    forall s i,
    subst_comp s (subst_lift i) ~ subst_comp (subst_lift i) (subst_upn i s).
  Proof.
    intros s i k x.
    unfold inst.
    apply traverse_ext; intros.
    simpl.
    destruct (le_gt_dec j n).
    - rewrite traverse_var.
      simplify decidable equality.
      rewrite <- traverse_var.
      fold (lift_fun i) (lift i) (inst s).
      rewrite subst_lift_inst_commute by lia.
      rewrite subst_lift_unfold.
      rewrite subst_var_shift1 by lia.
      unfold inst; now rewrite traverse_var.
    - reflexivity.
  Qed.

  Lemma subst_comp_shift2:
    forall s t i,
    subst_comp s (subst_comp (subst_lift i) t) ~
      subst_comp (subst_lift i) (subst_comp (subst_upn i s) t).
  Proof.
    intros s t i k x.
    unfold inst.
    apply traverse_ext; intros.
    simpl.
    destruct (le_gt_dec j n).
    - (* Hm... *)
      admit.
    - reflexivity.
  Admitted.

  Lemma subst_lift_cons:
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
      rewrite inst_fun_bvar by lia.
      rewrite traverse_var.
      now simplify decidable equality.
    - now simplify decidable equality.
  Admitted.

  Lemma subst_lift_comp1:
    forall s t k j,
    k = j ->
    subst_comp (subst_upn k s) (subst_upn j t) ~
      subst_upn j (subst_comp (subst_upn (k - j) s) t).
  Proof.
    intros s t k _ () j x.
    unfold inst.
    apply traverse_ext; intros l n ?.
    simpl.
    destruct (le_gt_dec l n).
    - replace (k - k + (k + l)) with (k + l) by lia.
      destruct (le_gt_dec (k + l) n).
      + replace (traverse (inst_fun t)) with (inst t) by auto.
        rewrite <- subst_inst_lift.
        unfold inst.
        apply traverse_ext; intros p m ?.
        simpl.
        now destruct (le_gt_dec p m).
      + rewrite inst_fun_bvar by lia.
        rewrite traverse_var.
        rewrite inst_fun_bvar by lia.
        now simplify decidable equality.
    - reflexivity.
  Qed.

  Lemma subst_lift_comp2:
    forall s t k j,
    k >= j ->
    subst_comp (subst_upn k s) (subst_upn j t) ~
      subst_upn j (subst_comp (subst_upn (k - j) s) t).
  Proof.
    admit.
  Admitted.

  Lemma subst_lift_comp3:
    forall s t k j,
    j >= k ->
    subst_comp (subst_upn k s) (subst_upn j t) ~
      subst_upn k (subst_comp s (subst_upn (j - k) t)).
  Proof.
    admit.
  Admitted.

  Lemma subst_lift_comp4:
    forall s t u k j,
    k = j ->
    subst_comp (subst_upn k s) (subst_comp (subst_upn j t) u) ~
      subst_comp (subst_upn j (subst_comp (subst_upn (k - j) s) t)) u.
  Proof.
    admit.
  Admitted.

  Lemma subst_lift_comp5:
    forall s t u k j,
    k >= j ->
    subst_comp (subst_upn k s) (subst_comp (subst_upn j t) u) ~
      subst_comp (subst_upn j (subst_comp (subst_upn (k - j) s) t)) u.
  Proof.
    admit.
  Admitted.

  Lemma subst_lift_comp6:
    forall s t u k j,
    j >= k ->
    subst_comp (subst_upn k s) (subst_comp (subst_upn j t) u) ~
      subst_comp (subst_upn k (subst_comp s (subst_upn (j - k) t))) u.
  Proof.
    admit.
  Admitted.

  Lemma subst_shift_shift:
    forall s i j,
    subst_comp (subst_lift i) (subst_lift j) ~ (subst_lift (i + j)).
  Proof.
    admit.
  Admitted.

  Lemma subst_lift_lift:
    forall s k j,
    subst_upn k (subst_upn j s) ~ subst_upn (k + j) s.
  Proof.
    admit.
  Admitted.

  (* ---------------------------------------------------------------------- *)

End DeBruijn.

(* *)

Arguments substitution {X}.
Arguments subst_ids {X}.
Arguments subst_lift {X}.
Arguments subst_cons {X}.
Arguments subst_comp {X}.
Arguments subst_upn {X}.
Arguments subst_app {X}.

(* *)

Create HintDb sigma.

(* *)

Global Hint Rewrite subst_lift_unfold: sigma.
Global Hint Rewrite subst_ids_simpl: sigma.
Global Hint Rewrite subst_bvar using lia: sigma.
Global Hint Rewrite subst_fvar_cons using lia: sigma.
Global Hint Rewrite subst_rvar_cons using lia: sigma.
Global Hint Rewrite subst_var_shift1 using lia: sigma.
Global Hint Rewrite subst_inst_lift: sigma.
Global Hint Rewrite subst_comp_clos: sigma.
Global Hint Rewrite subst_var_shift2 using lia: sigma.
Global Hint Rewrite subst_fvar_lift2 using lia: sigma.

(* *)

Global Hint Rewrite subst_shift_zero using lia: sigma.
Global Hint Rewrite subst_lift_zero using lia: sigma.
Global Hint Rewrite subst_var_shift using lia: sigma.
Global Hint Rewrite subst_shift_cons using lia: sigma.
Global Hint Rewrite subst_id_left: sigma.
Global Hint Rewrite subst_id_right: sigma.
Global Hint Rewrite subst_comp_assoc: sigma.
Global Hint Rewrite subst_comp_cons_map: sigma.
Global Hint Rewrite subst_cons_simpl using lia: sigma.
Global Hint Rewrite subst_comp_shift1: sigma.
Global Hint Rewrite subst_comp_shift2: sigma.
Global Hint Rewrite subst_lift_cons using lia: sigma.
Global Hint Rewrite subst_lift_comp1 using lia: sigma.
Global Hint Rewrite subst_lift_comp2 using lia: sigma.
Global Hint Rewrite subst_lift_comp3 using lia: sigma.
Global Hint Rewrite subst_lift_comp4 using lia: sigma.
Global Hint Rewrite subst_lift_comp5 using lia: sigma.
Global Hint Rewrite subst_lift_comp6 using lia: sigma.
Global Hint Rewrite subst_shift_shift: sigma.
Global Hint Rewrite subst_lift_lift: sigma.

(* TODO: figure out a way to restrict these rewritings. *)

Global Hint Rewrite Nat.sub_0_r: sigma.
Global Hint Rewrite Nat.add_0_r: sigma.
Global Hint Rewrite Nat.add_sub_assoc using lia: sigma.
Global Hint Rewrite <- plus_n_Sm: sigma.

(* *)

Ltac sigma :=
  rewrite_strat
    (topdown
      (choice
        (hints sigma)
        (* TODO: we want to restrict the context in those... somehow... *)
        (progress eval simpl var)
        (progress eval simpl plus)
        (progress eval simpl minus))).

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
  Context `{db: deBruijn X}.

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
    now sigma.
  Qed.

  Goal
    forall y s n,
    (* RVarCons: (1+n)[y, s] = n[s] *)
    subst_cons y s 0 (var (1 + n)) = s 0 (var n).
  Proof.
    now sigma.
  Qed.

  Goal
    forall n,
    (* VarShift1: n[S] = 1+n *)
    subst_lift 1 0 (var n) = var (1 + n).
  Proof.
    now sigma.
  Qed.

  Goal
    forall x,
    (* Id: x[I] = x *)
    subst_ids 0 x = x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall x s t,
    (* Clos: x[s][t] = x[s o t] *)
    t 0 (s 0 x) = subst_comp s t 0 x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall k x,
    (* VarShift: (0, S) ~ I *)
    subst_cons (var 0) (subst_lift 1) k x = x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall y s k x,
    (* ShiftCons: S o (y, s) ~ s *)
    subst_comp (subst_lift 1) (subst_cons y s) k x = s k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall s k x,
    (* IdL: I o s ~ s *)
    subst_comp subst_ids s k x = s k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall s k x,
    (* IdR: s o I ~ s *)
    subst_comp s subst_ids k x = s k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall s t u k x,
    (* AssEnv: (s o t) o u ~ s o (t o u) *)
    subst_comp (subst_comp s t) u k x = subst_comp s (subst_comp t u) k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall y s t k x,
    (* MapEnv: (y, s) o t ~ (y[t], s o t) *)
    subst_comp (subst_cons y s) t k x = subst_cons (t 0 y) (subst_comp s t) k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall s k x,
    (* SCons: (0[s], S o s) ~ s *)
    subst_cons (s 0 (var 0)) (subst_comp (subst_lift 1) s) k x = s k x.
  Proof.
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
    now sigma.
  Qed.

  Goal
    forall s,
    (* FVarLift1: 0[U(s)] = 0 *)
    subst_upn 1 s 0 (var 0) = var 0.
  Proof.
    now sigma.
  Qed.

  Goal
    forall s t,
    (* FVarLift2: 0[U(s) o t] = 0[t] *)
    subst_comp (subst_upn 1 s) t 0 (var 0) = t 0 (var 0).
  Proof.
    now sigma.
  Qed.

  Goal
    forall s n,
    (* RVarLift1: (1+n)[U(s)] = n[s o S] *)
    subst_upn 1 s 0 (var (1 + n)) = subst_comp s (subst_lift 1) 0 (var n).
  Proof.
    now sigma.
  Qed.

  Goal
    forall s t n,
    (* RVarLift2: (1+n)[U(s) o t] = n[s o S o t] *)
    subst_comp (subst_upn 1 s) t 0 (var (1 + n)) =
      subst_comp s (subst_comp (subst_lift 1) t) 0 (var n).
  Proof.
    now sigma.
  Qed.

  Goal
    forall s k x,
    (* ShiftLift1: S o U(s) ~ s o S *)
    subst_comp (subst_lift 1) (subst_upn 1 s) k x =
      subst_comp s (subst_lift 1) k x.
  Proof.
    (* We go in the opposite direction! *)
    now sigma.
  Qed.

  Goal
    forall s t k x,
    (* ShiftLift2: S o (U(s) o t) ~ s o S o t *)
    subst_comp (subst_lift 1) (subst_comp (subst_upn 1 s) t) k x =
      subst_comp s (subst_comp (subst_lift 1) t) k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall s t k x,
    (* Lift1: U(s) o U(t) ~ U(s o t) *)
    subst_comp (subst_upn 1 s) (subst_upn 1 t) k x =
      subst_upn 1 (subst_comp s t) k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall s t u k x,
    (* Lift2: U(s) o (U(t) o u) ~ U(s o t) o u *)
    subst_comp (subst_upn 1 s) (subst_comp (subst_upn 1 t) u) k x =
      subst_comp (subst_upn 1 (subst_comp s t)) u k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall s t y k x,
    (* LiftEnv: U(s) o (y, t) ~ (y, s o t) *)
    subst_comp (subst_upn 1 s) (subst_cons y t) k x =
      subst_cons y (subst_comp s t) k x.
  Proof.
    now sigma.
  Qed.

  Goal
    forall k x,
    (* LiftId: U(I) ~ I *)
    subst_upn 1 subst_ids k x = subst_ids k x.
  Proof.
    now sigma.
  Qed.

  (* We can also check some rules from the original de Bruijn implementation! *)

  Goal
    (* Substitution and lifting commutation. *)
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
    forall x i j k l,
    k <= l + j ->
    l <= k ->
    (* Lifting simplification. *)
    lift i k (lift j l x) = lift (i + j) l x.
  Proof.
    intros.
    (* It seems there are missing rules to make this one work... *)
    admit.
  Admitted.

End Tests.
