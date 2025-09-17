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
Require Import Local.Context.
Require Import Local.Reduction.

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
    -----------------
      G; D |- k<xs>
  *)
  | intuitionistic_ret:
    forall g k xs,
    item linear g k ->
    Forall (lift_var (item cartesian g)) xs ->
    intuitionistic g (jump k xs)
  (*
     k in D, x, ys in G
    --------------------
      G; D |- x<ys, k>
  *)
  | intuitionistic_app:
    forall g x k ys,
    item linear g k ->
    item cartesian g x ->
    Forall (lift_var (item cartesian g)) ys ->
    intuitionistic g (jump x (bound k :: ys))
  (*
     G; D, k |- b     G, ys; D |- c
    --------------------------------
        G; D |- b { k<ys> = c }
  *)
  | intuitionistic_con:
    forall g b ts c,
    intuitionistic (linear :: g) b ->
    intuitionistic (repeat cartesian (length ts) ++ g) c ->
    intuitionistic g (bind b ts c)
  (*
     G, x; D |- b     G, ys; k
    ----------------------------
     G; D |- b { x<ys, k> = c }
  *)
  | intuitionistic_fun:
    forall g b ts u tsu c,
    tsu = ts ++ [u] ->
    intuitionistic (cartesian :: g) b ->
    intuitionistic (linear :: repeat cartesian (length ts) ++ consume g) c ->
    intuitionistic g (bind b tsu c).

Lemma item_consume_cartesian_stable:
  forall g k,
  item cartesian g k ->
  item cartesian (consume g) k.
Proof.
  induction g; intros.
  - inversion H.
  - dependent destruction H; simpl.
    + constructor.
    + constructor.
      now apply IHg.
Qed.

Lemma anchor_is_intuitionistic:
  forall g,
  item linear g 0 ->
  intuitionistic (cartesian :: cartesian :: g) (jump 1 [bound 2; bound 0]).
Proof.
  intros.
  eapply intuitionistic_app with (ys := [_]); simpl.
  - now repeat constructor.
  - repeat constructor.
  - repeat constructor.
Qed.

Lemma intuitionistic_step:
  forall b c,
  step b c ->
  forall g,
  intuitionistic g b ->
  intuitionistic g c.
Proof.
  induction 1; intros.
  - admit.
  - admit.
  - dependent destruction H0.
    + apply intuitionistic_con.
      * now apply IHstep.
      * assumption.
    + rename ts0 into ts.
      apply intuitionistic_fun with ts u.
      * reflexivity.
      * now apply IHstep.
      * assumption.
Admitted.

Require Import Local.Lambda.PlotkinCBV.

Local Lemma technical1:
  forall g t e,
  (forall k, free k (abstraction t e) -> item cartesian (linear :: g) (S k)) ->
  forall k,
  free k (lift 1 1 e) ->
  item cartesian (cartesian :: consumed :: consume g) k.
Proof.
  intros.
  (* Notice that if k is zero then this is trivial. *)
  destruct k.
  - constructor.
  - (* Now, k can't be zero as this contradicts H0. *)
    destruct k.
    + exfalso.
      apply H0.
      apply lifting_more_than_n_makes_not_free_n; auto.
    + (* For the general case, we can proceed by our hypothesis. *)
      do 2 constructor.
      apply item_consume_cartesian_stable.
      (* Proceed by steps, of course. *)
      assert (free k (abstraction t e)).
      * intro; apply H0; clear H0.
        dependent destruction H1.
        replace (S (S n)) with (n + 1 + 1) by lia.
        apply not_free_lift.
        now rewrite Nat.add_comm.
      * apply H in H1.
        now dependent destruction H1.
Qed.

Local Lemma technical2:
  forall g f x,
  (forall k, free k (application f x) -> item cartesian (linear :: g) (S k)) ->
  forall k,
  free k (lift 1 0 f) ->
  item cartesian (linear :: g) k.
Proof.
  intros.
  (* Clearly, k can't ever be zero. *)
  destruct k.
  - exfalso.
    apply H0.
    apply lifting_more_than_n_makes_not_free_n; auto.
  - (* Proceed as the general case above. *)
    constructor.
    assert (free k (application f x)).
    + intro; apply H0; clear H0.
      dependent destruction H1.
      replace (S n) with (n + 1 + 0) by lia.
      apply not_free_lift.
      now rewrite Nat.add_comm.
    + apply H in H1.
      now dependent destruction H1.
Qed.

Local Lemma technical3:
  forall g f x,
  (forall k, free k (application f x) -> item cartesian (linear :: g) (S k)) ->
  forall k,
  free k (lift 2 0 x) ->
  forall p,
  item cartesian (cartesian :: p :: g) k.
Proof.
  intros.
  (* Similar to the above, k can't possibly be zero. *)
  destruct k.
  - exfalso.
    apply H0.
    apply lifting_more_than_n_makes_not_free_n; auto with arith.
  - (* Yet again, k can't be zero. *)
    destruct k.
    + exfalso.
      apply H0.
      apply lifting_more_than_n_makes_not_free_n; auto.
    + (* Now, proceed once more by the general case as above. *)
      do 2 constructor.
      assert (free k (application f x)).
      * intro; apply H0; clear H0.
        dependent destruction H1.
        replace (S (S n)) with (n + 2 + 0) by lia.
        apply not_free_lift.
        now rewrite Nat.add_comm.
      * apply H in H1.
        now dependent destruction H1.
Qed.

Lemma plotkin_cbv_is_intuitionistic:
  forall e b,
  cbv_cps e b ->
  forall g,
  item linear g 0 ->
  (forall k, free k e -> item cartesian g (S k)) ->
  intuitionistic g b.
Proof.
  induction 1; intros.
  (* Case: bound. *)
  - (* For variables, the CBV translation will return the value. *)
    apply intuitionistic_ret.
    + assumption.
    + repeat constructor.
      apply H0.
      now inversion 1.
  (* Case: abstraction. *)
  - (* Abstractions have a single variable in the lambda calculus, which will be
       followed by the current continuation in Plotkin's translation. So declare
       a function and immediately return it. *)
    eapply intuitionistic_fun with (ts := [_]).
    + reflexivity.
    + apply intuitionistic_ret.
      * now constructor.
      * repeat constructor.
    + simpl.
      (* Proceed by induction. *)
      apply IHcbv_cps; intros.
      * constructor.
      * dependent destruction H0.
        constructor; simpl.
        now apply technical1 with t e.
  (* Case: application. *)
  - (* For CBV, we execute the left-hand side, then execute the right-hand
       side, then apply the function properly. Sure. *)
    apply intuitionistic_con; simpl.
    + apply IHcbv_cps1; auto with cps; intros.
      dependent destruction H1.
      constructor; simpl.
      now apply technical2 with f x.
    + apply intuitionistic_con; simpl.
      * apply IHcbv_cps2; auto with cps; intros.
        dependent destruction H1.
        constructor; simpl.
        now apply technical3 with f x.
      * now apply anchor_is_intuitionistic.
Qed.

Theorem cbv_program_is_intuitionistic:
  forall e,
  closed e ->
  forall b,
  cbv_cps e b ->
  intuitionistic [linear] b.
Proof.
  intros.
  apply plotkin_cbv_is_intuitionistic with e; intros.
  - assumption.
  - constructor.
  - exfalso.
    apply H1.
    apply H.
Qed.

Require Import Local.Lambda.PlotkinCBN.

Lemma plotkin_cbn_is_intuitionistic:
  forall e b,
  cbn_cps e b ->
  forall g,
  item linear g 0 ->
  (forall k, free k e -> item cartesian g (S k)) ->
  intuitionistic g b.
Proof.
  induction 1; intros.
  (* Case: bound. *)
  - (* For variables, the CBN translation will force the value. *)
    apply intuitionistic_app.
    + assumption.
    + apply H0.
      now inversion 1.
    + constructor.
  (* Case: abstraction. *)
  - (* Abstraction for the CBN case is exactly the same as in the CBV one. *)
    eapply intuitionistic_fun with (ts := [_]).
    + reflexivity.
    + apply intuitionistic_ret.
      * now constructor.
      * repeat constructor.
    + simpl.
      (* Proceed by induction. *)
      apply IHcbn_cps; intros.
      * constructor.
      * dependent destruction H0.
        constructor; simpl.
        now apply technical1 with t e.
  (* Case: application. *)
  - (* Things a little bit different in here from CBV; we do one continuation,
       then we do a thunk declaration, and we apply the anchor. *)
    apply intuitionistic_con; simpl.
    + apply IHcbn_cps1; auto with cps; intros.
      dependent destruction H1.
      constructor; simpl.
      now apply technical2 with f x.
    + (* Here the anchor is on the left. *)
      eapply intuitionistic_fun with (ts := []); simpl.
      * reflexivity.
      * now apply anchor_is_intuitionistic.
      * apply IHcbn_cps2; auto with cps; intros.
        dependent destruction H1.
        constructor; simpl.
        (* The third technicall lemma requires a tiny tweak in here too, since
           now the thunk can't proceed with older continuations. *)
        apply technical3 with f x; auto.
        intros j ?; constructor.
        apply item_consume_cartesian_stable.
        specialize (H2 _ H1).
        now dependent destruction H2.
Qed.

Theorem cbn_program_is_intuitionistic:
  forall e,
  closed e ->
  forall b,
  cbn_cps e b ->
  intuitionistic [linear] b.
Proof.
  intros.
  apply plotkin_cbn_is_intuitionistic with e; intros.
  - assumption.
  - constructor.
  - exfalso.
    apply H1.
    apply H.
Qed.
