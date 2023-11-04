(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Relations.
Require Import Morphisms.
Set Implicit Arguments.

(* *)

Create HintDb sigma.

(* *)

Section DeBruijn.

  Variable X: Set.

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
      forall f g,
      (forall k n, f k n = g k n) ->
      forall x k,
      traverse f k x = traverse g k x;
    traverse_fun:
      forall f g x k j,
      traverse f k (traverse g j x) =
        traverse (fun i n => traverse f (i + k - j) (g i n)) j x
  }.

  Context `{deBruijn}.

  #[nonuniform]
  Local Coercion var: nat >-> X.

  Inductive substitution: Type :=
    | subst_id
    | subst_lift (i: nat)
    | subst_cons (y: X) (s: substitution)
    | subst_comp (s: substitution) (t: substitution).

  Coercion subst_lift: nat >-> substitution.

  Local Notation I := subst_id.
  Local Notation L i := (subst_lift i).
  Local Notation "( x1 , .. , xn , s )" :=
    (subst_cons x1 .. (subst_cons xn s) ..) (at level 0, right associativity).
  Local Notation "s 'o' t" :=
    (subst_comp s t) (at level 11, left associativity).

  Definition __lift (i: nat): nat -> X -> X :=
    traverse (fun k n =>
      if le_gt_dec k n then
        var (i + n)
      else
        var n).

  Tactic Notation "simplify" "decidable" "equality" :=
    match goal with
    | |- context H [le_gt_dec ?m ?n] =>
      (destruct (le_gt_dec m n) as [ ? | _ ];
        [ exfalso; lia | idtac ]) +
      (destruct (le_gt_dec m n) as [ _ | ? ];
        [ idtac | exfalso; lia ])
    end.

  Goal
    forall i j k l x,
    k <= l + j ->
    l <= k ->
    __lift i k (__lift j l x) = __lift (i + j) l x.
  Proof.
    intros.
    unfold __lift.
    rewrite traverse_fun.
    apply traverse_ext; clear x; intros.
    rename k0 into p.
    destruct (le_gt_dec p n); simpl.
    - rewrite traverse_var.
      simplify decidable equality.
      f_equal; lia.
    - rewrite traverse_var.
      simplify decidable equality.
      reflexivity.
  Qed.

  Fixpoint apply_subst (s: substitution) (k: nat) (n: nat): X :=
    if le_gt_dec k n then
      match s with
      | I =>
        var n
      | L i =>
        var (i + n)
      | (y, s) =>
        let x := match n - k with
                 | 0 => y
                 | S m => apply_subst s 0 m
                 end
        in __lift k 0 x
      | s o t =>
        traverse (apply_subst t) k (apply_subst s k n)
      end
    else
      var n.

  Goal
    forall i k x,
    (* We have intensional equality between these. *)
    __lift i k x = traverse (apply_subst i) k x.
  Proof.
    intros.
    reflexivity.
  Qed.

  Definition instantiate (s: substitution): X -> X :=
    traverse (apply_subst s) 0.

  Coercion instantiate: substitution >-> Funclass.

  Notation up s :=
    (0, s o 1).

  (* TODO: should we delcare this as a setoid...? *)

  Definition subst_equiv (s: substitution) (t: substitution): Prop :=
    forall x: X,
    s x = t x.

  Lemma lift_zero_e_equals_e:
    forall k x,
    __lift 0 k x = x.
  Proof.
    intros.
    unfold __lift.
    replace x with (traverse (fun _ n => n) k x) at 2.
    - apply traverse_ext; simpl; intros.
      now destruct (le_gt_dec k0 n).
    - apply traverse_ids.
  Qed.

  Goal
    forall y s,
    (y, s) 0 = y.
  Proof.
    intros.
    unfold instantiate; simpl.
    rewrite traverse_var; simpl.
    now rewrite lift_zero_e_equals_e.
  Qed.

  Goal
    forall y s n,
    (y, s) (S n) = s n.
  Proof.
    intros.
    unfold instantiate; simpl.
    do 2 rewrite traverse_var; simpl.
    now rewrite lift_zero_e_equals_e.
  Qed.

  Goal
    forall (i n: nat),
    L i n = i + n.
  Proof.
    intros.
    unfold instantiate; simpl.
    rewrite traverse_var; simpl.
    reflexivity.
  Qed.

  Goal
    forall x,
    I x = x.
  Proof.
    intros.
    (* This is not obvious, but it follows by definition! *)
    apply lift_zero_e_equals_e.
  Qed.

  Goal
    forall s t x,
    (s o t) x = t (s x).
  Proof.
    intros.
    unfold instantiate.
    rewrite traverse_fun; simpl.
    apply traverse_ext; clear x; intros.
    replace (k + 0 - 0) with k; try lia.
    destruct s;
    simpl;
    destruct (le_gt_dec k n);
    simpl;
    auto;
    rewrite traverse_var;
    destruct t;
    simpl;
    destruct (le_gt_dec k n);
    try lia; auto.
  Qed.

  Goal
    subst_equiv 0 I.
  Proof.
    intros x.
    unfold instantiate.
    apply traverse_ext; clear x; intros.
    simpl; reflexivity.
  Qed.

  Goal
    subst_equiv (0, 1) I.
  Proof.
    intros x.
    unfold instantiate; simpl.
    apply traverse_ext; clear x; intros.
    destruct (le_gt_dec k n).
    - remember (n - k) as m.
      destruct m.
      + unfold __lift.
        rewrite traverse_var; simpl.
        f_equal; lia.
      + unfold __lift.
        rewrite traverse_var; simpl.
        f_equal; lia.
    - reflexivity.
  Qed.

  Goal
    forall y s,
    subst_equiv (1 o (y, s)) s.
  Proof.
    intros y s x.
    unfold instantiate; simpl.
    apply traverse_ext; clear x; intros.
    destruct (le_gt_dec k n).
    - rewrite traverse_var.
      simplify decidable equality.
      (* TODO: should the above simplify this match as well...? *)
      remember (S n - k) as m.
      destruct m.
      + exfalso; lia.
      + replace m with (n - k) by lia.
        clear Heqm m.
        (* This law is valid! *)
        admit.
    - destruct s; simpl.
      + now simplify decidable equality.
      + now simplify decidable equality.
      + now simplify decidable equality.
      + now simplify decidable equality.
  Admitted.

  Goal
    forall s,
    subst_equiv (I o s) s.
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    subst_equiv (s o I) s.
  Proof.
    admit.
  Admitted.

  Goal
    forall s t u,
    subst_equiv (s o (t o u)) (s o t o u).
  Proof.
    admit.
  Admitted.

  Goal
    forall y s t,
    subst_equiv ((y, s) o t) (t y, s o t).
  Proof.
    admit.
  Admitted.

  Goal
    (* This rule is useful for rewriting as that we can deal with metavariables
       in the proof. *)
    forall (s: substitution),
    subst_equiv (s 0, 1 o s) s.
  Proof.
    admit.
  Admitted.

End DeBruijn.

(* Global Opaque instantiate. *)

Arguments subst_id {X}.
Arguments subst_lift {X}.
Arguments subst_cons {X}.
Arguments subst_comp {X}.

(*
  Global Hint Rewrite traverse_subst_instantiate: subst.
  Global Hint Rewrite instantiate_cons_zero: subst.
  Global Hint Rewrite instantiate_cons_succ: subst.
  Global Hint Rewrite instantiate_lift: subst.
  Global Hint Rewrite instantiate_id: subst.
  Global Hint Rewrite instantiate_comp: subst.
  Global Hint Rewrite subst_cons_lift_simpl: subst.
  Global Hint Rewrite subst_lift_cons_simpl: subst.
  Global Hint Rewrite subst_comp_left_identity: subst.
  Global Hint Rewrite subst_comp_right_identity: subst.
  Global Hint Rewrite subst_comp_assoc: subst.
  Global Hint Rewrite subst_comp_cons_distr: subst.
  Global Hint Rewrite subst_cons_eta: subst.
*)

(* -------------------------------------------------------------------------- *)

(* Below we have some tests. TODO: remove this and move into proper places. *)

Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Machine.

Global Instance pseudoterm_deBruijn: deBruijn pseudoterm.
Proof.
  apply (Build_deBruijn bound traverse); intros.
  - simpl.
    reflexivity.
  - generalize dependent k.
    induction x using pseudoterm_deepind; simpl; auto; intros.
    + f_equal.
      list induction over H.
    + f_equal; auto.
      list induction over H.
    + f_equal; auto.
      list induction over H.
  - generalize dependent k.
    induction x using pseudoterm_deepind; simpl; auto; intros.
    + f_equal.
      (* TODO: make list induction rewrite a few things as well... *)
      list induction over H0.
      now do 2 rewrite traverse_list_length.
    + f_equal; auto.
      list induction over H0.
    + f_equal; auto.
      list induction over H0.
      now do 2 rewrite traverse_list_length.
  - generalize dependent j.
    generalize dependent k.
    induction x using pseudoterm_deepind; simpl; auto; intros.
    + f_equal; lia.
    + f_equal.
      list induction over H.
      do 3 rewrite traverse_list_length.
      rewrite H.
      admit.
    + f_equal; auto.
      list induction over H.
    + f_equal; auto.
      * admit.
      * admit.
      * admit.
Admitted.
