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
Require Import Local.Context.
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

Lemma sumup_count_is_well_founded:
  well_founded (ltof _ (sumup count)).
Proof.
  apply well_founded_ltof.
Qed.

Lemma count_arg:
  forall {t ts g},
  t = (negation ts :: g) ->
  sumup count ts < sumup count t.
Proof.
  (* Still not sure: ts ++ g, or simply ts? *)
  admit.
Admitted.

Lemma count_ret:
  forall {t ts g},
  t = (negation ts :: g) ->
  sumup count g < sumup count t.
Proof.
  admit.
Admitted.

Definition ARR ts (U V: pseudoterm -> Prop): pseudoterm -> Prop :=
  fun b =>
    forall c: pseudoterm,
    U c -> V (bind b ts c).

(* A neutral term should not trigger a reduction interacting with its context.
   E.g., in the lambda calculus, they are neither abstractions, which would
   trigger a reduction with ([] x), nor <a, b>, which would trigger a reduction
   with (pi1 []) or (pi2 []). Since the CPS calculus "works at a distance", we
   would probably need something that DOESN'T jump to bound variables. *)
Axiom neutral: env -> pseudoterm -> Prop.

(* TODO: interpret ~(G, b)... by subst? *)
Definition L: env -> pseudoterm -> Prop :=
  Fix sumup_count_is_well_founded (fun _ => pseudoterm -> Prop) (fun t f =>
    match t as x return (t = x -> pseudoterm -> Prop) with
    (* Given (G, ~T)... *)
    | negation ts :: g =>
      fun H =>
        ARR ts (fun c =>
          (* Perhaps we'll need to fix this ts in the neutral... we don't really
             care about jumps to variables which aren't bound in a continuation.
             This is similar to how we dealt with regular terms in the residuals
             theory. *)
          neutral (ts ++ g) c /\ (f _ (count_arg H)) c)
            (f _ (count_ret H))
    (* By default... *)
    | _ =>
      fun _ =>
        SN step
    end eq_refl).

Lemma L_composition:
  forall ts g,
  L (negation ts :: g) =
    ARR ts (fun c => neutral (ts ++ g) c /\ L ts c) (L g).
Proof.
  intros.
  unfold L.
  rewrite Fix_eq.
  - fold L.
    reflexivity.
  - intros.
    destruct x; simpl; auto.
    destruct p; simpl; auto.
    do 2 rewrite H; auto.
Defined.

Definition candidate: Type :=
  pseudoterm -> Prop.

Record reducible g (P: candidate): Prop := {
  cr1:
    forall e,
    P e -> SN step e;
  cr2:
    forall a b,
    P a -> [a => b] -> P b;
  cr3:
    forall a,
    (* Since the CPS calculus seems to be non-erasing, do we really need to
       restrict ourselves to neutral terms here...? *)
    neutral g a -> (forall b, [a => b] -> P b) -> P a
}.

Lemma cr2_star:
  forall g P,
  reducible g P ->
  forall a b,
  P a -> [a =>* b] -> P b.
Proof.
  induction 3.
  - apply cr2 with g x; auto.
  - assumption.
  - auto.
Qed.

Lemma cr4:
  forall g P,
  reducible g P ->
  forall e,
  normal step e -> neutral g e -> P e.
Proof.
  intros.
  apply cr3 with g; intros.
  - assumption.
  - assumption.
  - exfalso.
    firstorder.
Qed.

Lemma reducible_SN:
  forall g,
  reducible g (SN step).
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
  reducible g (L g) ->
  reducible ts (L ts) ->
  reducible (negation ts :: g) (L (negation ts :: g)).
Proof.
  constructor; intros.
  - rewrite L_composition in H1.
    unfold ARR in H1.
    assert (exists2 c, L ts c & neutral (ts ++ g) c).
    + (* We should add a free jump here, right...? *)
      admit.
    + destruct H2 as (c, ?, ?).
      apply SN_bind_left with ts c.
      apply cr1 with g (L g); auto.
  - rewrite L_composition in H1 |- *.
    unfold ARR in H1 |- *; intros.
    apply cr2 with g (bind a ts c); auto.
    auto with cps.
  - rewrite L_composition in H2 |- *.
    unfold ARR in H2 |- *; intros.
    destruct H3.
    assert (SN step c).
    + eapply cr1 with ts (L ts); auto.
    + induction H5; clear H5.
      unfold transp in H6.
      apply cr3 with g; intros.
      * assumption.
      * (* NOW this seems correct to me! Check H1 and H3... *)
        admit.
      * dependent destruction H5.
        --- (* It is neutral, so we CAN'T have a redex here! *)
            exfalso.
            (* We can derive that from H1! *)
            admit.
        --- apply H2; auto.
        --- apply H6; auto.
            +++ (* Sure, from H3 and H5... *)
                admit.
            +++ apply cr2 with ts x; auto.
Admitted.

Lemma reducible_L:
  forall g,
  reducible g (L g).
Proof.
  intros.
  induction sumup_count_is_well_founded with g.
  clear H; rename H0 into H; unfold ltof in H.
  (* Ok, start wordering about the type... *)
  destruct x; try exact reducible_SN.
  - admit.
  - destruct p; try exact reducible_SN.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + (* "Arrow types", in a way... *)
      eapply reducible_ARR.
      * apply H.
        eapply count_ret; eauto.
      * apply H.
        eapply count_arg; eauto.
    + admit.
    + admit.
Admitted.

Lemma SN_L:
  forall g e,
  L g e -> SN step e.
Proof.
  intros.
  apply cr1 with g (L g); auto.
  apply reducible_L.
Qed.

Goal
  forall A B C,
  let g :=
    [negation A; negation B; negation C]
  in L g void.
Proof.
  (* Lets see how things unfold... *)
  intros.
  unfold g.
  rewrite L_composition.
  unfold ARR; intros.
  rewrite L_composition.
  unfold ARR; intros.
  rewrite L_composition; intros.
  unfold ARR; intros.
  rename c into a, c0 into b, c1 into c.
  destruct H.
  destruct H0.
  destruct H1.
  rewrite app_nil_r in H1.
  unfold L.
  rewrite Fix_eq; [|
    intros;
    destruct x; auto;
    destruct p; auto;
    do 2 rewrite H5;
    reflexivity ].
  (* Hmm...! *)
  admit.
Admitted.

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
