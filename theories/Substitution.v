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
    | subst_app (ys: list X) (s: substitution)
    | subst_comp (s: substitution) (t: substitution)
    | subst_upn (i: nat) (s: substitution).

  Class deBruijn: Type := {
    var:
      nat -> X;
    traverse:
      (nat -> nat -> X) -> nat -> X -> X
  }.

  Context `{db: deBruijn}.

  (* TODO: review these laws. This works for now, but it begs to be simplified
     in some way... *)

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
      (* Is there a nicer way to represent this law...? *)
      traverse f k (traverse g j x) =
        traverse (fun i n => traverse f (i + k - j) (g i n)) j x
  }.

  Context `{db_laws: deBruijnLaws}.

  Definition lift_fun i k n :=
    if le_gt_dec k n then
      var (i + n)
    else
      var n.

  Definition lift (i: nat) (k: nat): X -> X :=
    traverse (lift_fun i) k.

  Fixpoint inst_fun (s: substitution): nat -> nat -> X :=
    fun k n =>
      if le_gt_dec k n then
        match s with
        | subst_ids =>
          var n
        | subst_lift i =>
          var (i + n)
        | subst_app ys s =>
          match nth_error ys (n - k) with
          | Some y => lift k 0 y
          | None => inst_fun s k (n - length ys)
          end
        | subst_comp s t =>
          traverse (inst_fun t) k (inst_fun s k n)
        | subst_upn i s =>
          inst_fun s (i + k) n
        end
      else
        var n.

  (* Ideally, we'd like to use this simpler definition given below, which can
     generate nice code by a reasonable optimizer, but it isn't defined by
     structural recursion. Instead, we merely check that it would be fine to
     use it (as we may wanna use that in the paper). *)

  Goal
    forall y ys s k n,
    k <= n ->
    inst_fun (subst_app (y :: ys) s) k n =
      if Nat.eq_dec k n then
        lift k 0 y
      else
        (* Recursive call with ys. *)
        inst_fun (subst_app ys s) k (n - 1).
  Proof.
    intros.
    destruct (Nat.eq_dec k n).
    - simpl.
      simplify decidable equality.
      replace (n - k) with 0 by lia.
      now simpl.
    - simpl.
      simplify decidable equality.
      remember (n - k) as m.
      destruct m; simpl.
      + exfalso.
        lia.
      + replace (n - 1 - k) with m by lia.
        replace (n - 1 - length ys) with (n - S (length ys)) by lia.
        reflexivity.
  Qed.

  Definition inst_rec (s: substitution): nat -> X -> X :=
    traverse (inst_fun s).

  Definition subst (y: X) (k: nat): X -> X :=
    inst_rec (subst_app [y] subst_ids) k.

  Definition inst (s: substitution): X -> X :=
    inst_rec s 0.

  Global Coercion inst_rec: substitution >-> Funclass.

  Definition smap (s: substitution) (k: nat): list X -> list X :=
    fold_right (fun t ts => s k t :: ts) [].

  Definition bsmap (s: substitution) (k: nat): list X -> list X :=
    fold_right (fun t ts => s (length ts + k) t :: ts) [].

  (* TODO: move these auxiliary lemmas to cleanup section below. *)

  Lemma smap_length:
    forall s k x,
    length (smap s k x) = length x.
  Proof.
    induction x; simpl; congruence.
  Qed.

  Lemma smap_nil:
    forall s k,
    smap s k [] = [].
  Proof.
    auto.
  Qed.

  Lemma smap_cons:
    forall s k x xs,
    smap s k (x :: xs) = s k x :: smap s k xs.
  Proof.
    auto.
  Qed.

  Lemma smap_upn:
    forall xs s i k,
    smap (subst_upn i s) k xs = smap s (i + k) xs.
  Proof.
    induction xs; simpl; intros.
    - reflexivity.
    - rewrite IHxs; f_equal.
      admit.
  Admitted.

  Lemma bsmap_length:
    forall s k x,
    length (bsmap s k x) = length x.
  Proof.
    induction x; simpl; congruence.
  Qed.

  Lemma bsmap_nil:
    forall s k,
    bsmap s k [] = [].
  Proof.
    auto.
  Qed.

  Lemma bsmap_cons:
    forall s k x xs,
    bsmap s k (x :: xs) = s (length xs + k) x :: bsmap s k xs.
  Proof.
    intros; simpl.
    now rewrite bsmap_length.
  Qed.

  Lemma bsmap_upn:
    forall xs s i k,
    bsmap (subst_upn i s) k xs = bsmap s (i + k) xs.
  Proof.
    induction xs; simpl; intros.
    - reflexivity.
    - rewrite IHxs; f_equal.
      rewrite bsmap_length.
      admit.
  Admitted.

  (* ... *)

  Definition subst_equiv (s: substitution) (t: substitution): Prop :=
    forall k x,
    s k x = t k x.

  Global Instance subst_equivalence:
    Equivalence subst_equiv.
  Proof.
    split; congruence.
  Qed.

  Global Instance inst_proper:
    Proper (subst_equiv ==> eq ==> eq) inst.
  Proof.
    intros s t ? x _ ().
    admit.
  Admitted.

  Global Instance subst_app_proper:
    Proper (eq ==> subst_equiv ==> subst_equiv) subst_app.
  Proof.
    intros ys _ () s t ? k x.
    unfold inst.
    apply traverse_ext; intros; simpl.
    destruct (le_gt_dec j n) as [ ? | ? ].
    - destruct (nth_error ys (n - j)).
      + reflexivity.
      + do 2 rewrite <- traverse_var.
        admit.
    - reflexivity.
  Admitted.

  Global Instance subst_comp_proper:
    Proper (subst_equiv ==> subst_equiv ==> subst_equiv) subst_comp.
  Proof.
    intros s t ? u v ? k x.
    unfold inst.
    apply traverse_ext.
    simpl; intros.
    destruct (le_gt_dec j n).
    - rewrite <- traverse_var.
      admit.
    - reflexivity.
  Admitted.

  Global Instance subst_upn_proper:
    Proper (eq ==> subst_equiv ==> subst_equiv) subst_upn.
  Proof.
    intros i _ () s t ? k x.
    unfold inst.
    admit.
  Admitted.

  Global Instance subst_smap_proper:
    Proper (subst_equiv ==> eq ==> eq ==> eq) smap.
  Proof.
    intros s t ? k _ () xs _ ().
    induction xs; intros.
    - reflexivity.
    - simpl; f_equal.
      + admit.
      + apply IHxs.
  Admitted.

  Global Instance subst_bsmap_proper:
    Proper (subst_equiv ==> eq ==> eq ==> eq) bsmap.
  Proof.
    intros s t ? k _ () xs _ ().
    induction xs; intros.
    - reflexivity.
    - simpl; f_equal.
      + admit.
      + apply IHxs.
  Admitted.

  (* ---------------------------------------------------------------------- *)

  Implicit Types x y z: X.
  Implicit Types s t u v: substitution.
  Implicit Types n m i k j: nat.

  Lemma subst_lift_unfold:
    forall i k x,
    lift i k x = subst_lift i k x.
  Proof.
    auto.
  Qed.

  Lemma subst_subst_unfold:
    forall y k x,
    subst y k x = subst_app [y] subst_ids k x.
  Proof.
    auto.
  Qed.

  Lemma inst_fun_bvar:
    forall s k n,
    n < k ->
    s k (var n) = var n.
  Proof.
    admit.
  Admitted.

  (* Lemma lift_lift_permutation:
    forall x i j k l,
    k <= l ->
    lift i k (lift j l x) = lift j (i + l) (lift i k x).
  Proof.
    admit.
  Admitted.

  Lemma lift_lift_simplification:
    forall x i j k l,
    k <= l + j ->
    l <= k ->
    lift i k (lift j l x) = lift (i + j) l x.
  Proof.
    admit.
  Admitted. *)

  Lemma subst_ids_simpl:
    forall k x,
    subst_ids k x = x.
  Proof.
    admit.
  Admitted.

  Lemma subst_lift_inst_commute:
    forall s x i k j,
    k <= j ->
    lift i k (s j x) = s (i + j) (lift i k x).
  Proof.
    admit.
  Admitted.

  (* TODO: rename me. This is probably not enough to keep confluence! *)

  (* Lemma baz:
    forall s i k n,
    k <= n ->
    subst_comp s (subst_lift i) k (var n) =
      s (i + k) (var (i + n)).
  Proof.
    intros.
    (* This can be greatly simplified by adding a few lemmas... *)
    unfold inst.
    do 2 rewrite traverse_var.
    generalize dependent k.
    generalize dependent i.
    generalize dependent n.
    destruct s; simpl; intros.
    - simplify decidable equality.
      rewrite traverse_var.
      now simplify decidable equality.
    - simplify decidable equality.
      rewrite traverse_var.
      simplify decidable equality.
      f_equal; lia.
    - simplify decidable equality.
      fold (lift_fun i).
      fold (lift i).
      replace (i + n - (i + k)) with (n - k) by lia.
      remember (nth_error ys (n - k)) as y.
      destruct y.
      + now rewrite lift_lift_simplification by lia.
      + rewrite <- traverse_var.
        fold (inst s).
        rewrite subst_lift_inst_commute by lia.
        unfold lift, lift_fun.
        symmetry in Heqy.
        apply nth_error_None in Heqy.
        rewrite traverse_var.
        simplify decidable equality.
        unfold inst.
        rewrite traverse_var.
        f_equal; lia.
    - simplify decidable equality.
      fold (lift_fun i) (lift i).
      fold (inst s2).
      rewrite subst_lift_inst_commute by lia.
      do 2 rewrite <- traverse_var.
      fold (inst s1).
      rewrite subst_lift_inst_commute by lia.
      do 2 f_equal.
      unfold lift, lift_fun.
      rewrite traverse_var.
      now simplify decidable equality.
    - simplify decidable equality.
      rename i0 into j.
      replace (i + (j + k)) with (j + (i + k)) by lia.
      destruct (le_gt_dec (i + k) n).
      + fold (lift_fun j) (lift j).
        do 2 rewrite <- traverse_var.
        fold (inst s).
        rewrite subst_lift_inst_commute by lia.
        f_equal.
        unfold lift, lift_fun.
        rewrite traverse_var.
        now simplify decidable equality.
      + do 2 rewrite inst_fun_bvar by lia.
        rewrite traverse_var.
        now simplify decidable equality.
  Qed. *)

  (* ---------------------------------------------------------------------- *)

  Lemma subst_Inst:
    forall s k x,
    inst_rec s k x = inst (subst_upn k s) x.
  Proof.
    admit.
  Admitted.

  (* Id: x[I] = x *)
  Lemma subst_Id:
    forall x,
    inst subst_ids x = x.
  Proof.
    admit.
  Admitted.

  (* FVarCons: 0[y, s] = y *)
  Lemma subst_FVarCons:
    forall s n y ys,
    n = 0 ->
    inst (subst_app (y :: ys) s) (var n) = y.
  Proof.
    admit.
  Admitted.

  (* RVarCons: (1+n)[y, s] = n[s] *)
  Lemma subst_RVarCons:
    forall s y ys n,
    n > 0 ->
    inst (subst_app (y :: ys) s) (var n) = inst (subst_app ys s) (var (n - 1)).
  Proof.
    admit.
  Admitted.

  (* New rule! *)
  Lemma subst_VarApp:
    forall s ys n,
    n >= length ys ->
    inst (subst_app ys s) (var n) = inst s (var (n - length ys)).
  Proof.
    admit.
  Admitted.

  (* VarShift1: n[S] = 1+n *)
  Lemma subst_VarShift1:
    forall i n,
    inst (subst_lift i) (var n) = var (i + n).
  Proof.
    admit.
  Admitted.

  (* VarShift2: n[S o s] = (1+n)[s] *)
  Lemma subst_VarShift2:
    forall s i n,
    inst (subst_comp (subst_lift i) s) (var n) = inst s (var (i + n)).
  Proof.
    admit.
  Admitted.

  (* FVarLift1: 0[U(s)] = 0 *)
  Lemma subst_FVarLift1:
    forall n i s,
    i > n ->
    inst (subst_upn i s) (var n) = var n.
  Proof.
    admit.
  Admitted.

  (* FVarLift2: 0[U(s) o t] = 0[t] *)
  Lemma subst_FVarLift2:
    forall s t i n,
    i > n ->
    inst (subst_comp (subst_upn i s) t) (var n) = inst t (var n).
  Proof.
    admit.
  Admitted.

  (* RVarLift1: (1+n)[U(s)] = n[s o S] *)
  Lemma subst_RVarLift1:
    forall i s n,
    i <= n ->
    inst (subst_upn i s) (var n) =
      inst (subst_comp s (subst_lift i)) (var (n - i)).
  Proof.
    admit.
  Admitted.

  (* RVarLift2: (1+n)[U(s) o t] = n[s o S o t] *)
  Lemma subst_RVarLift2:
    forall i s t n,
    i <= n ->
    inst (subst_comp (subst_upn i s) t) (var n) =
      inst (subst_comp s (subst_comp (subst_lift i) t)) (var (n - i)).
  Proof.
    admit.
  Admitted.

  (* Clos: x[s][t] = x[s o t] *)
  Lemma subst_Clos:
    forall s t x,
    inst t (inst s x) = inst (subst_comp s t) x.
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
    admit.
  Admitted.

  (* LiftZero (additional!): U^0(s) ~ s *)
  Lemma subst_LiftZero:
    forall n s,
    n = 0 ->
    subst_upn n s ~ s.
  Proof.
    admit.
  Admitted.

  (* VarShift: (0, S) ~ I *)
  Lemma subst_VarShift:
    forall n i,
    i = 1 + n ->
    (* Nice generalization! *)
    subst_app [var n] (subst_lift i) ~ subst_lift n.
  Proof.
    admit.
  Admitted.

  (* ShiftCons: S o (y, s) ~ s *)
  Lemma subst_ShiftCons:
    forall i y ys s,
    i > 0 ->
    subst_comp (subst_lift i) (subst_app (y :: ys) s) ~
      subst_comp (subst_lift (i - 1)) (subst_app ys s).
  Proof.
    admit.
  Admitted.

  (* New rule! Generalizes ShiftCons... *)
  Lemma subst_ShiftApp:
    forall i ys s,
    i >= length ys ->
    subst_comp (subst_lift i) (subst_app ys s) ~
      subst_comp (subst_lift (i - length ys)) s.
  Proof.
    admit.
  Admitted.

  (* IdL: I o s ~ s *)
  Lemma subst_IdL:
    forall s,
    subst_comp subst_ids s ~ s.
  Proof.
    admit.
  Admitted.

  (* IdR: s o I ~ s *)
  Lemma subst_IdR:
    forall s,
    subst_comp s subst_ids ~ s.
  Proof.
    admit.
  Admitted.

  (* AssEnv: (s o t) o u ~ s o (t o u) *)
  Lemma subst_AssEnv:
    forall s t u,
    subst_comp (subst_comp s t) u ~ subst_comp s (subst_comp t u).
  Proof.
    admit.
  Admitted.

  (* MapEnv: (y, s) o t ~ (y[t], s o t) *)
  Lemma subst_MapEnv:
    forall ys s t,
    (* Note that we generalize this to the polyadic case! *)
    subst_comp (subst_app ys s) t ~ subst_app (smap t 0 ys) (subst_comp s t).
  Proof.
    admit.
  Admitted.

  (* SCons: (0[s], S o s) ~ s *)
  Lemma subst_SCons:
    forall s n m,
    m = 1 + n ->
    (* We want to simplify a drop! Notice k has to be 0 to avoid lifting. *)
    (* TODO: I believe this can be generalized... do we want it? *)
    subst_app [inst s (var n)] (subst_comp (subst_lift m) s) ~
      subst_comp (subst_lift n) s.
  Proof.
    admit.
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

  (* Lift2: U(s) o (U(t) o u) ~ U(s o t) o u, variants A and B *)
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
    forall n s y ys t,
    n > 0 ->
    (* TODO: this can be generalized. Do we want it...? *)
    subst_comp (subst_upn n s) (subst_app (y :: ys) t) ~
      subst_app [y] (subst_comp (subst_upn (n - 1) s) (subst_app ys t)).
  Proof.
    admit.
  Admitted.

  (* New rule! Hmm... *)
  Lemma subst_LiftApp:
    forall n s ys t,
    n >= length ys ->
    subst_comp (subst_upn n s) (subst_app ys t) ~
      subst_app ys (subst_comp (subst_upn (n - length ys) s) t).
  Proof.
    admit.
  Admitted.

  (* New rule! Hmm... *)
  Lemma subst_LiftApp2:
    forall n s ys zs t,
    n >= length ys ->
    subst_comp (subst_upn n s) (subst_app (ys ++ zs) t) ~
      subst_app ys (subst_comp (subst_upn (n - length ys) s) (subst_app zs t)).
  Proof.
    admit.
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

  (* LiftLift (additional!): U^i(U^j(s)) = U^(i+j)(s) *)
  Lemma subst_LiftLift:
    forall i j s,
    subst_upn i (subst_upn j s) ~ subst_upn (i + j) s.
  Proof.
    admit.
  Admitted.

  (* New rule! *)
  Lemma subst_AppNil:
    forall s,
    subst_app [] s ~ s.
  Proof.
    admit.
  Admitted.

  (* New rule! *)
  Lemma subst_AppApp:
    forall s xs ys,
    subst_app xs (subst_app ys s) ~ subst_app (xs ++ ys) s.
  Proof.
    admit.
  Admitted.

  (* ---------------------------------------------------------------------- *)

End DeBruijn.

(* *)

Global Opaque lift subst inst_rec inst smap bsmap.

(* *)

Arguments substitution {X}.
Arguments subst_ids {X}.
Arguments subst_lift {X}.
Arguments subst_app {X}.
Arguments subst_comp {X}.
Arguments subst_upn {X}.
Arguments subst_app {X}.

(* *)

(* TODO: turn this into a definition afterwards...? *)

Global Notation subst_drop i :=
  (subst_comp (subst_lift i)).

Global Notation subst_cons y :=
  (subst_app [y]).

(* *)

Create HintDb sigma.

Ltac sigma_solver :=
  match goal with
  | |- @deBruijnLaws _ _ =>
    typeclasses eauto
  | |- ?G =>
    (* idtac "trying to solve" G; *)
    (* TODO: rewrite those if they are within the context of a substitution;
       this can most certainly be done by using proper setoid rewriting. *)
    try repeat (rewrite smap_length
         || rewrite bsmap_length
         || rewrite app_length
         || rewrite last_length
         || simpl length);
    lia
  end.

(* *)

Global Hint Rewrite subst_lift_unfold: sigma.
Global Hint Rewrite subst_subst_unfold: sigma.

(* Global Hint Rewrite subst_BVar using sigma_solver: sigma. *)
(* Global Hint Rewrite subst_LiftInst using sigma_solver: sigma. *)
Global Hint Rewrite subst_Inst using sigma_solver: sigma.
Global Hint Rewrite subst_Id using sigma_solver: sigma.
Global Hint Rewrite subst_FVarCons using sigma_solver: sigma.
Global Hint Rewrite subst_RVarCons using sigma_solver: sigma.
Global Hint Rewrite subst_VarApp using sigma_solver: sigma.
Global Hint Rewrite subst_VarShift1 using sigma_solver: sigma.
Global Hint Rewrite subst_VarShift2 using sigma_solver: sigma.
Global Hint Rewrite subst_FVarLift1 using sigma_solver: sigma.
Global Hint Rewrite subst_FVarLift2 using sigma_solver: sigma.
Global Hint Rewrite subst_RVarLift1 using sigma_solver: sigma.
Global Hint Rewrite subst_RVarLift2 using sigma_solver: sigma.
Global Hint Rewrite subst_Clos using sigma_solver: sigma.
(* -------------------------------------------------------------------------- *)
(* Global Hint Rewrite baz using sigma_solver: sigma. *)
(* -------------------------------------------------------------------------- *)

Global Hint Rewrite subst_ShiftZero using sigma_solver: sigma.
Global Hint Rewrite subst_LiftZero using sigma_solver: sigma.
Global Hint Rewrite subst_VarShift using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftCons using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftApp using sigma_solver: sigma.
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
Global Hint Rewrite subst_LiftApp using sigma_solver: sigma.
Global Hint Rewrite subst_LiftApp2 using sigma_solver: sigma.
Global Hint Rewrite subst_LiftId using sigma_solver: sigma.
Global Hint Rewrite subst_ShiftShift using sigma_solver: sigma.
Global Hint Rewrite subst_LiftLift using sigma_solver: sigma.
Global Hint Rewrite subst_AppNil using sigma_solver: sigma.
Global Hint Rewrite subst_AppApp using sigma_solver: sigma.

(* TODO: rewrite those only within the context of a substitution! *)

Global Hint Rewrite smap_length using sigma_solver: sigma.
Global Hint Rewrite smap_nil using sigma_solver: sigma.
Global Hint Rewrite smap_cons using sigma_solver: sigma.
Global Hint Rewrite smap_upn using sigma_solver: sigma.
Global Hint Rewrite bsmap_length using sigma_solver: sigma.
Global Hint Rewrite bsmap_nil using sigma_solver: sigma.
Global Hint Rewrite bsmap_cons using sigma_solver: sigma.
Global Hint Rewrite bsmap_upn using sigma_solver: sigma.

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
  simpl length;
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
    forall k x,
    (* Id: x[I] = x *)
    subst_ids k x = x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall s t x,
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
    forall i k x,
    (* LiftId: U(I) ~ I *)
    subst_upn i subst_ids k x = subst_ids k x.
  Proof.
    intros.
    now sigma.
  Qed.

  (* We can also check some rules from the original de Bruijn implementation!
     These rules are used in the "Coq in Coq" paper I was originally following,
     but they can be found in older papers such as Huet's "Residual Theory in
     lambda-calculus". *)

  Local Ltac equal_modulo_arith :=
    reflexivity || assumption || lia || (progress f_equal; equal_modulo_arith).

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
    lift i k (s j x) = s (i + j) (lift i k x).
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    (* Instantiation and substitution commutation. *)
    forall x y i k j,
    k <= j ->
    lift i k (subst y j x) = subst y (i + j) (lift i k x).
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

  (* This rule appears in the simulation proof for the CBN CPS translation. *)
  Goal
    forall b n,
    subst (subst (var 1) n (var 0)) 0
      (lift (2 + n) 1 b) =
    subst (var 1) n (lift (2 + n) 1 b).
  Proof.
    intros.
    sigma.
    replace (S (S n)) with (2 + n) by auto.
    (* This is not yet proved by sigma. TODO: figure out why! Nevertheless, a
       simple check on n seems almost enough... *)
    destruct n.
    - now sigma.
    - admit.
  Admitted.

  (* An useful property. This is required by the machine semantics; luckly, we
     can solve it using sigma with a very simple case analysis. *)
  Goal
    forall s p k n,
    s (p + k) (var (p + n)) = lift p 0 (s k (var n)).
  Proof.
    intros.
    destruct (le_gt_dec k n).
    - now sigma.
    - now sigma.
  Qed.

  (* TODO: can we make right_cycle_right_cycle_simplification simpler? *)

End Tests.
