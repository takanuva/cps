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
  match goal with
  | |- context H [le_gt_dec ?m ?n] =>
    (destruct (le_gt_dec m n) as [ ? | _ ];
      [ exfalso; lia | idtac ]) +
    (destruct (le_gt_dec m n) as [ _ | ? ];
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
      forall f g,
      (forall k n, f k n = g k n) ->
      forall x k,
      traverse f k x = traverse g k x
  }.

  Context `{dB: deBruijn}.

  (* Goal
    forall f g x k j,
    traverse f k (traverse g j x) =
      traverse (fun i n => traverse f (i + k - j) (g i n)) j x.
  Proof.
    intros.
    admit.
  Admitted. *)

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
    forall x k,
    s k x = t k x.

  (* ---------------------------------------------------------------------- *)

  Implicit Types x y z: X.
  Implicit Types s t u: substitution.
  Implicit Types n m i k j: nat.

  Goal
    forall i,
    lift i = inst (subst_lift i).
  Proof.
    (* We have intensional equality between these! *)
    auto.
  Qed.

  Lemma lift_zero_e_equals_e:
    forall n k x,
    n = 0 ->
    subst_lift n k x = x.
  Proof.
    intros; subst.
    unfold inst.
    rewrite traverse_ext with (g := fun _ n => var n).
    - now rewrite traverse_ids.
    - clear k x; simpl; intros.
      now destruct (le_gt_dec k n).
  Qed.

  Lemma subst_fvar_cons:
    forall s x,
    subst_cons x s 0 (var 0) = x.
  Proof.
    intros.
    unfold inst.
    rewrite traverse_var; simpl.
    now apply lift_zero_e_equals_e.
  Qed.

  (* ---------------------------------------------------------------------- *)

End DeBruijn.

Arguments substitution {X}.
Arguments subst_ids {X}.
Arguments subst_lift {X}.
Arguments subst_cons {X}.
Arguments subst_comp {X}.
Arguments subst_upn {X}.
Arguments subst_app {X}.

Create HintDb sigma.

Local Hint Rewrite lift_zero_e_equals_e using lia: sigma.
Local Hint Rewrite subst_fvar_cons: sigma.

Ltac sigma :=
  rewrite_db sigma;
  simpl var.

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

  Local Notation "s ~ t" := (subst_equiv s t) (at level 70, no associativity).

  (* Lets first check the laws for the sigma SP calculus... we note that these
     differ a bit from the paper because they take non-zero indexes to be zero
     applied to the lifting substitution in there, i.e., n = 0[S^n]. *)

  Goal
    forall x s,
    (* FVarCons: 0[x, s] = x *)
    subst_cons x s 0 (var 0) = x.
  Proof.
    intros.
    now sigma.
  Qed.

  Goal
    forall x s n,
    (* RVarCons: (1+n)[x, s] = n[s] *)
    subst_cons x s 0 (var (1 + n)) = s 0 (var n).
  Proof.
    admit.
  Admitted.

  Goal
    forall n,
    (* VarShift1: n[S] = 1+n *)
    subst_lift 1 0 (var n) = var (1 + n).
  Proof.
    admit.
  Admitted.

  Goal
    forall x,
    (* Id: x[I] = x *)
    subst_ids 0 x = x.
  Proof.
    admit.
  Admitted.

  Goal
    forall x s t,
    (* Clos: x[s][t] = x[s o t] *)
    t 0 (s 0 x) = subst_comp s t 0 x.
  Proof.
    admit.
  Admitted.

  Goal
    (* VarShift: (0, S) ~ I *)
    subst_cons (var 0) (subst_lift 1) ~ subst_ids.
  Proof.
    admit.
  Admitted.

  Goal
    forall x s,
    (* ShiftCons: S o (x, s) ~ s *)
    subst_comp (subst_lift 1) (subst_cons x s) ~ s.
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    (* IdL: I o s ~ s *)
    subst_comp subst_ids s ~ s.
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    (* IdR: s o I ~ s *)
    subst_comp s subst_ids ~ s.
  Proof.
    admit.
  Admitted.

  Goal
    forall s t u,
    (* AssEnv: (s o t) o u ~ s o (t o u) *)
    subst_comp (subst_comp s t) u ~ subst_comp s (subst_comp t u).
  Proof.
    admit.
  Admitted.

  Goal
    forall x s t,
    (* MapEnv: (x, s) o t ~ (x[t], s o t) *)
    subst_comp (subst_cons x s) t ~ subst_cons (t 0 x) (subst_comp s t).
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    (* SCons: (0[s], S o s) ~ s *)
    subst_cons (s 0 (var 0)) (subst_comp (subst_lift 1) s) ~ s.
  Proof.
    admit.
  Admitted.

  (* Now, lets check the additional laws for the confluent sigma calculus...
     notice that the confluent sigma calculus seems to drop the (VarShift) and
     the (SCons) rule, although we still want those because it allows us to
     equate more terms in the presence of metavariables. *)

  Goal
    forall s n,
    (* VarShift2: n[S o s] = (1+n)[s] *)
    subst_comp (subst_lift 1) s 0 (var n) = s 0 (var (1 + n)).
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    (* FVarLift1: 0[U(s)] = 0 *)
    subst_upn 1 s 0 (var 0) = var 0.
  Proof.
    admit.
  Admitted.

  Goal
    forall s t,
    (* FVarLift2: 0[U(s) o t] = 0[t] *)
    subst_comp (subst_upn 1 s) t 0 (var 0) = t 0 (var 0).
  Proof.
    admit.
  Admitted.

  Goal
    forall s n,
    (* RVarLift1: (n+1)[U(s)] = n[s o S] *)
    subst_upn 1 s 0 (var (n + 1)) = subst_comp s (subst_lift 1) 0 (var n).
  Proof.
    admit.
  Admitted.

  Goal
    forall s t n,
    (* RVarLift2: (n+1)[U(s) o t] = n[s o S o t] *)
    subst_comp (subst_upn 1 s) t 0 (var (n + 1)) =
      subst_comp s (subst_comp (subst_lift 1) t) 0 (var n).
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    (* ShiftLift1: S o U(s) ~ s o S *)
    subst_comp (subst_lift 1) (subst_upn 1 s) ~ subst_comp s (subst_lift 1).
  Proof.
    admit.
  Admitted.

  Goal
    forall s t,
    (* ShiftLift2: S o (U(s) o t) ~ s o S o t *)
    subst_comp (subst_lift 1) (subst_comp (subst_upn 1 s) t) ~
      subst_comp s (subst_comp (subst_lift 1) t).
  Proof.
    admit.
  Admitted.

  Goal
    forall s t,
    (* Lift1: U(s) o U(t) ~ U(s o t) *)
    subst_comp (subst_upn 1 s) (subst_upn 1 t) ~ subst_upn 1 (subst_comp s t).
  Proof.
    admit.
  Admitted.

  Goal
    forall s t u,
    (* Lift2: U(s) o (U(t) o u) ~ U(s o t) o u *)
    subst_comp (subst_upn 1 s) (subst_comp (subst_upn 1 t) u) ~
      subst_comp (subst_upn 1 (subst_comp s t)) u.
  Proof.
    admit.
  Admitted.

  Goal
    forall s t x,
    (* LiftEnv: U(s) o (x, t) ~ (x, s o t) *)
    subst_comp (subst_upn 1 s) (subst_cons x t) ~ subst_cons x (subst_comp s t).
  Proof.
    admit.
  Admitted.

  Goal
    (* LiftId: U(I) ~ I *)
    subst_upn 1 subst_ids ~ subst_ids.
  Proof.
    admit.
  Admitted.

End Tests.
