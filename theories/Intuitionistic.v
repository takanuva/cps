(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.

Import ListNotations.

Variant polarity: Set :=
  | cartesian
  | linear
  | consumed.

Definition consume: list polarity -> list polarity :=
  map (fun x => match x with
                | cartesian => cartesian
                | linear => consumed
                | consumed => consumed
                end).

Inductive lift_var (P: nat -> Prop): pseudoterm -> Prop :=
  | lift_var_bound:
    forall n,
    P n ->
    lift_var P (bound n).

(* Generalized from Kennedy's paper; this judgement implies that a CPS-calculus
   term behaves without control effects (read: no call/cc). TODO: generalize
   functions for multiple returns and branching (i.e., allow for products and
   coproducts), also for continuations appearing at any position (for, e.g.,
   Fischer's translation). *)

Inductive intuitionistic: list polarity -> pseudoterm -> Prop :=
  (*
     k in D, xs in G
    ----------------- (RET)
      G; D |- k<xs>
  *)
  | intuitionistic_ret:
    forall e k xs,
    item linear e k ->
    Forall (lift_var (item cartesian e)) xs ->
    intuitionistic e (jump k xs)
  (*
     k in D, x, ys in G
    -------------------- (APP)
      G; D |- x<ys, k>
  *)
  | intuitionistic_app:
    forall e x ys k ysk,
    ysk = ys ++ [bound k] ->
    item linear e k ->
    Forall (lift_var (item cartesian e)) ys ->
    intuitionistic e (jump x ysk)
  (*
     G; D, k |- b     G, ys; D |- c
    -------------------------------- (CON)
        G; D |- b { k<ys> = c }
  *)
  | intuitionistic_con:
    forall e b ts c,
    intuitionistic (linear :: e) b ->
    intuitionistic (repeat cartesian (length ts) ++ e) c ->
    intuitionistic e (bind b ts c)
  (*
     G, x; D |- b     G, ys; k 
    ----------------------------------------------- (FUN)
     G; D |- b { x<ys, k> = c }
  *)
  | intuitionistic_fun:
    forall e b ts u tsu c,
    tsu = ts ++ [u] ->
    intuitionistic (cartesian :: e) b ->
    intuitionistic (linear :: repeat cartesian (length ts) ++ consume e) c ->
    intuitionistic e (bind b tsu c).

Require Import Local.Lambda.PlotkinCBV.

Lemma plotkin_cbv_is_intuitionistic:
  forall e b,
  cbv_cps e b ->
  forall n,
  (forall k, k >= n -> not_free k e) ->
  intuitionistic (linear :: repeat cartesian n) b.
Proof.
  induction 1; intros.
  - rename n0 into m.
    admit.
  - admit.
  - admit.
Admitted.
