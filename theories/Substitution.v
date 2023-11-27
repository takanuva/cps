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

(* *)

Create HintDb sigma.

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

  Context `{deBruijn}.

  #[nonuniform]
  Local Coercion var: nat >-> X.

  (* TODO: we may want to mess around. We actually only need lift and cons in
     here... id and comp are derivable. We could move those out, then we'd get
     something similar to the primitives de Bruijn used. Or we could move up
     into here to have something similar to the confluent sigma calculus... we
     could also move app in here, as it's useful for parallel substitution. So
     this will be a problem for future me (I'm so sorry). *)

  Inductive substitution: Type :=
    | subst_id
    | subst_lift (i: nat)
    | subst_cons (y: X) (s: substitution)
    | subst_comp (s: substitution) (t: substitution).

  Fixpoint subst_upn (i: nat) (s: substitution): substitution :=
    match i with
    | 0 =>
      s
    | S i =>
      subst_cons 0 (subst_comp (subst_upn i s) (subst_lift 1))
    end.

  Definition subst_app (xs: list X) (s: substitution): substitution :=
    fold_right subst_cons s xs.

  Definition lift (i: nat): nat -> X -> X :=
    traverse (fun k n =>
      if le_gt_dec k n then
        var (i + n)
      else
        var n).

  (* Goal
    forall i j k l x,
    k <= l + j ->
    l <= k ->
    lift i k (lift j l x) = lift (i + j) l x.
  Proof.
    intros; unfold lift.
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
  Qed. *)

  Fixpoint apply_subst (s: substitution) (k: nat) (n: nat): X :=
    if le_gt_dec k n then
      match s with
      | subst_id =>
        var n
      | subst_lift i =>
        var (i + n)
      | subst_cons y s =>
        let x := match n - k with
                 | 0 => y
                 | S m => apply_subst s 0 m
                 end
        in lift k 0 x
      | subst_comp s t =>
        traverse (apply_subst t) k (apply_subst s k n)
      end
    else
      var n.

  Local Notation instantiate_rec s k :=
    (traverse (apply_subst s) k).

  Definition instantiate (s: substitution): X -> X :=
    instantiate_rec s 0.

  Global Coercion instantiate: substitution >-> Funclass.

  Definition test (x: X) (s: substitution): X :=
    instantiate s x.

  #[nonuniform]
  Global Coercion test: X >-> Funclass.

  Goal
    forall i k x,
    (* We have intensional equality between these. *)
    lift i k x = instantiate_rec (subst_lift i) k x.
  Proof.
    auto.
  Qed.

  (* TODO: should we delcare this as a setoid...? *)

  Definition subst_equiv (s: substitution) (t: substitution): Prop :=
    (* TODO: It should be a sufficient and necessary condition to check only for
       vars in here, so this would simplify stuff. *)
    forall x,
    instantiate s x = instantiate t x.

  (* Lemma lift_zero_e_equals_e:
    forall k x,
    lift 0 k x = x.
  Proof.
    intros; unfold lift.
    replace x with (traverse (fun _ n => n) k x) at 2.
    - apply traverse_ext; simpl; intros.
      now destruct (le_gt_dec k0 n).
    - apply traverse_ids.
  Qed. *)

  Global Instance instantiate_proper:
    Proper (subst_equiv ==> eq ==> eq) instantiate.
  Proof.
    intros x y ? a b ?; subst.
    apply H0.
  Qed.

End DeBruijn.

Arguments substitution {X}.
Arguments subst_id {X}.
Arguments subst_lift {X}.
Arguments subst_cons {X}.
Arguments subst_comp {X}.
Arguments subst_upn {X} {H}.
Arguments subst_app {X}.
