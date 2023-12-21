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
    (* traverse_var:
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
        traverse (fun i n => traverse f (i + k - j) (g i n)) j x *)
  }.

  Context `{dB: deBruijn}.

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

  Goal
    forall i,
    lift i = inst (subst_lift i).
  Proof.
    (* We have intensional equality between these! *)
    auto.
  Qed.

  Definition subst_equiv (s: substitution) (t: substitution): Prop :=
    forall x k,
    inst s k x = inst t k x.

  Global Instance inst_proper:
    Proper (subst_equiv ==> eq ==> eq ==> eq) inst.
  Proof.
    intros s t ? k _ () x _ ().
    apply H.
  Qed.

End DeBruijn.

Arguments substitution {X}.
Arguments subst_ids {X}.
Arguments subst_lift {X}.
Arguments subst_cons {X}.
Arguments subst_comp {X}.
Arguments subst_upn {X}.
Arguments subst_app {X}.

Create HintDb sigma.

Ltac sigma :=
  idtac.

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

  (* Lets first check the laws for the sigma SP calculus... *)

  Goal
    forall x s,
    (* 0[x, s] = x *)
    subst_cons x s 0 (var 0) = x.
  Proof.
    admit.
  Admitted.

  Goal
    forall x s n,
    subst_cons x s 0 (var (1 + n)) = s 0 (var n).
  Proof.
    admit.
  Admitted.

  Goal
    forall n,
    subst_lift 1 0 (var n) = var (1 + n).
  Proof.
    admit.
  Admitted.

  Goal
    forall x,
    subst_ids 0 x = x.
  Proof.
    admit.
  Admitted.

  Goal
    forall x s t,
    t 0 (s 0 x) = subst_comp s t 0 x.
  Proof.
    admit.
  Admitted.

  Goal
    subst_cons (var 0) (subst_lift 1) ~ subst_ids.
  Proof.
    admit.
  Admitted.

  Goal
    forall x s,
    subst_comp (subst_lift 1) (subst_cons x s) ~ s.
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    subst_comp subst_ids s ~ s.
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    subst_comp s subst_ids ~ s.
  Proof.
    admit.
  Admitted.

  Goal
    forall s t u,
    subst_comp (subst_comp s t) u ~ subst_comp s (subst_comp t u).
  Proof.
    admit.
  Admitted.

  Goal
    forall x s t,
    subst_comp (subst_cons x s) t ~ subst_cons (t 0 x) (subst_comp s t).
  Proof.
    admit.
  Admitted.

  Goal
    forall s,
    subst_cons (s 0 (var 0)) (subst_comp (subst_lift 1) s) ~ s.
  Proof.
    admit.
  Admitted.

End Tests.
