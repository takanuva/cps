(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Reduction.
Require Import Local.TypeSystem.

(** ** Normalization. *)

Lemma SN_unlift:
  forall i k e,
  SN step (lift i k e) -> SN step e.
Proof.
  intros.
  apply SN_preimage with (lift i k); intros.
  - apply step_lift; auto.
  - assumption.
Qed.

Lemma SN_unsubst:
  forall y k e,
  SN step (subst y k e) -> SN step e.
Proof.
  intros.
  apply SN_preimage with (subst y k); intros.
  - apply step_subst; auto.
  - assumption.
Qed.

Lemma SN_bind_left:
  forall b ts c,
  SN step (bind b ts c) -> SN step b.
Proof.
  intros.
  apply SN_preimage with (fun b => bind b ts c); auto with cps.
Qed.

Lemma SN_bind_right:
  forall b ts c,
  SN step (bind b ts c) -> SN step c.
Proof.
  intros.
  apply SN_preimage with (fun c => bind b ts c); auto with cps.
Qed.

Definition sumup {T} (f: T -> nat) (ts: list T): nat :=
  fold_right Nat.add 0 (map f ts).

Lemma sumup_app:
  forall {T} f a b,
  @sumup T f (a ++ b) = sumup f a + sumup f b.
Proof.
  induction a; simpl; intros.
  - reflexivity.
  - unfold sumup; simpl.
    rewrite plus_assoc_reverse; f_equal.
    apply IHa.
Defined.

Fixpoint count (t: pseudoterm): nat :=
  match t with
  | base =>
    1
  | negation ts =>
    1 + sumup count ts
  | _ =>
    0
  end.

Lemma count_is_well_founded:
  well_founded (ltof _ count).
Proof.
  apply well_founded_ltof.
Defined.

Lemma count_arg:
  forall {t ts g},
  t = negation (negation ts :: g) ->
  count (negation ts) < count t.
Proof.
  intros.
  rewrite H; simpl.
  replace (negation ts :: g) with ([negation ts] ++ g); auto.
  rewrite sumup_app; simpl; auto with arith.
Qed.

Lemma count_ret:
  forall {t ts g},
  t = negation (negation ts :: g) ->
  count (negation g) < count t.
Proof.
  intros.
  rewrite H; simpl.
  replace (negation ts :: g) with ([negation ts] ++ g); auto.
  rewrite sumup_app; simpl; auto with arith.
Qed.

Definition ARR ts (U V: pseudoterm -> Prop): pseudoterm -> Prop :=
  fun b =>
    forall c: pseudoterm,
    U c -> V (bind b ts c).

(* TODO: interpret ~(G, b)... by subst? *)
Definition L: pseudoterm -> pseudoterm -> Prop :=
  Fix count_is_well_founded (fun _ => pseudoterm -> Prop) (fun t f =>
    match t as x return (t = x -> pseudoterm -> Prop) with
    (* Given ~(G, ~T)... *)
    | negation (negation ts :: g) =>
      fun H =>
        ARR ts (f _ (count_arg H)) (f _ (count_ret H))
    (* By default... *)
    | _ =>
      fun _ =>
        SN step
    end eq_refl).

Lemma L_composition:
  forall ts g,
  L (negation (negation ts :: g)) =
    ARR ts (L (negation ts)) (L (negation g)).
Proof.
  intros.
  unfold L.
  rewrite Fix_eq.
  - fold L.
    reflexivity.
  - intros.
    destruct x; simpl; auto.
    destruct ts0; simpl; auto.
    destruct p; simpl; auto.
    do 2 rewrite H; auto.
Defined.

Definition candidate: Type :=
  pseudoterm -> Prop.

(* A neutral term should no trigger a reduction interacting with its context.
   I.e., in the lambda calculus, they are neither abstractions, which would
   trigger a reduction with ([] x), nor <a, b>, which would trigger a reduction
   with (pi1 []) or (pi2 []). Since the CPS calculus "works at a distance", we
   would probably need something that DOESN'T jump to bound variables. So I'll
   probably need to index this by the (size of the) environment. *)
Axiom neutral: pseudoterm -> Prop.

Record reducible (P: candidate): Prop := {
  cr1:
    forall e,
    P e -> SN step e;
  cr2:
    forall a b,
    P a -> [a => b] -> P b;
  cr3:
    forall a,
    (* Since the CPS calculus is non-erasing, do we really need to restrict
       ourselves to neutral terms here...? *)
    neutral a -> (forall b, [a => b] -> P b) -> P a
}.

Lemma cr2_star:
  forall P,
  reducible P ->
  forall a b,
  P a -> [a =>* b] -> P b.
Proof.
  induction 3.
  - apply cr2 with x; auto.
  - assumption.
  - auto.
Qed.

Lemma reducible_SN:
  reducible (SN step).
Proof.
  constructor; intros.
  - assumption.
  - apply H.
    assumption.
  - constructor.
    assumption.
Qed.

Lemma reducible_ARR:
  forall g ts,
  reducible (L (negation g)) ->
  reducible (L (negation ts)) ->
  reducible (L (negation (negation ts :: g))).
Proof.
  constructor; intros.
  - rewrite L_composition in H1.
    unfold ARR in H1.
    cut (exists c, L (negation ts) c).
    + destruct 1 as (c, ?H).
      apply SN_bind_left with ts c.
      apply cr1 with (L (negation g)); auto.
    + (* We should add a free jump here, right...? *)
      admit.
  - rewrite L_composition in H1 |- *.
    unfold ARR in H1 |- *; intros.
    apply cr2 with (bind a ts c); auto.
    apply step_bind_left; auto.
  - rewrite L_composition in H2 |- *.
    unfold ARR in H2 |- *; intros.
    assert (SN step c).
    + eapply cr1 with (L (negation ts)); auto.
    + induction H4; clear H4.
      apply cr3; intros.
      * assumption.
      * (* Oh no! Are we really neutral here?

           We'll probably have to change candidates from sets of terms to
           relations between environments and terms. Could we derive then that x
           is neutral based on that, e.g., such that a { k<xs: ts> = x } is
           neutral in G? *)
        admit.
      * dependent destruction H4.
        -- (* It is neutral, so we CAN'T have a redex here! *)
           admit.
        -- apply H2; auto.
        -- apply H5; auto.
           apply cr2 with x; auto.
Admitted.

Lemma reducible_L:
  forall t,
  reducible (L t).
Proof.
  intros.
  induction count_is_well_founded with t.
  clear H; rename H0 into H; unfold ltof in H.
  (* Ok, start wordering about the type... *)
  destruct x; try exact reducible_SN.
  destruct ts; try exact reducible_SN.
  destruct p; try exact reducible_SN.
  (* "Arrow types", in a way... *)
  rename ts0 into ts, ts into g.
  apply reducible_ARR.
  - apply H.
    eapply count_ret; eauto.
  - apply H.
    eapply count_arg; eauto.
Qed.

Lemma SN_L:
  forall t e,
  L t e -> SN step e.
Proof.
  intros.
  apply cr1 with (L t); auto.
  apply reducible_L.
Qed.

(*
Lemma fundamental:
  forall e g,
  typing g e void ->
  forall cs,
  Forall2 L g cs ->
  SN (beta cs 0 e).
Proof.
  induction e; inversion_clear 1.
  (* Case: bound. *)
  - exfalso.
    (* Commands don't have types, but variables do. *)
    apply typing_bound_cant_be_void with g n; auto with cps.
  (* Case: jump. *)
  - clear IHe.
    admit.
  (* Case: bind. *)
  - admit.
Admitted.
*)
