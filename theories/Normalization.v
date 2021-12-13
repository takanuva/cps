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

(* A neutral term should not trigger a reduction interacting with its context.
   So, e.g., in the lambda calculus, they are neither abstractions, which would
   trigger a reduction with ([] x), nor <a, b>, which would trigger a reduction
   with (pi1 []) or (pi2 []). Since the CPS calculus "works at a distance", we
   need something that DOESN'T jump to a set of variables. Luckly, as we're only
   dealing with static contexts, they appear in a row, and so this will work in
   a de Bruijn setting. *)
Inductive neutral: nat -> nat -> pseudoterm -> Prop :=
  | neutral_jump:
    forall k n f xs,
    f < k \/ f >= k + n ->
    neutral k n (jump f xs)
  | neutral_bind:
    forall k n b ts c,
    neutral (S k) n b ->
    neutral (k + length ts) n c ->
    neutral k n (bind b ts c).

Lemma neutral_weaken:
  forall e p k n,
  neutral p (k + n) e -> neutral (p + k) n e.
Proof.
  intros.
  dependent induction H.
  - constructor.
    lia.
  - rename k0 into p.
    constructor; auto.
    + apply IHneutral1; auto.
    + replace (p + k + length ts) with (p + length ts + k); try lia.
      apply IHneutral2; auto.
Qed.

Lemma neutral_context_invalid:
  forall (h: context) k n xs,
  n > 0 ->
  ~neutral k n (h (jump (k + #h) xs)).
Proof.
  induction h; intros.
  - simpl; intro.
    dependent destruction H0.
    lia.
  - simpl; intro.
    dependent destruction H0.
    eapply IHh with (n := n) (k := S k); auto.
    replace (S k + #h) with (k + S #h); try lia.
    eassumption.
  - simpl; intro.
    dependent destruction H0.
    eapply IHh with (n := n) (k := k + length ts); auto.
    replace (k + length ts + #h) with (k + (#h + length ts)); try lia.
    eassumption.
Qed.

Definition ARR ts (U V: pseudoterm -> Prop): pseudoterm -> Prop :=
  fun b =>
    forall c: pseudoterm,
    U c -> V (bind b ts c).

Definition cool (ts g: env) (e: pseudoterm): Prop :=
  normal step e /\ neutral (length ts) (length g) e.

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
          cool ts g c /\ (f _ (count_arg H)) c)
            (f _ (count_ret H))
    (* By default... *)
    | _ =>
      fun _ =>
        SN step
    end eq_refl).

Lemma L_composition:
  forall ts g,
  L (negation ts :: g) =
    ARR ts (fun c => cool ts g c /\ L ts c) (L g).
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
    neutral 0 g a -> (forall b, [a => b] -> P b) -> P a
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
  normal step e -> neutral 0 g e -> P e.
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

Definition free_jump (ts g: env): pseudoterm :=
  jump (length ts + length g) (low_sequence (length ts)).

Lemma reducible_isnt_empty:
  forall R ts g,
  reducible (length ts) R ->
  exists2 c,
  R c & cool ts g c.
Proof.
  intros.
  exists (free_jump ts g).
  - apply cr4 with (length ts).
    + assumption.
    + do 2 intro.
      inversion H0.
    + constructor.
      lia.
  - split.
    + do 2 intro.
      inversion H0.
    + constructor.
      lia.
Qed.

Lemma reducible_ARR:
  forall g ts,
  reducible (length g) (L g) ->
  reducible (length ts) (L ts) ->
  reducible (length (negation ts :: g)) (L (negation ts :: g)).
Proof.
  constructor; intros.
  - rewrite L_composition in H1.
    unfold ARR in H1.
    destruct reducible_isnt_empty with (L ts) ts g as (c, ?, ?); auto.
    (* As in the lambda calculus... but instead of a variable, a free jump. *)
    apply SN_bind_left with ts c.
    apply cr1 with (length g) (L g); auto.
  - rewrite L_composition in H1 |- *.
    unfold ARR in H1 |- *; intros.
    apply cr2 with (length g) (bind a ts c); auto.
    auto with cps.
  - rewrite L_composition in H2 |- *.
    unfold ARR in H2 |- *; intros.
    destruct H3 as ((?, ?), ?).
    (* No need to do induction over SN step c as in the lambda calculus: it's
       already cool down in normal form! *)
    apply cr3 with (length g); intros.
    + assumption.
    + (* NOW this seems correct to me! Check H1 and H4... *)
      constructor; auto.
      apply neutral_weaken with (p := 0); auto.
    + dependent destruction H6.
      * (* It is neutral, so we CAN'T have a redex here! *)
        exfalso.
        eapply neutral_context_invalid with
          (k := 0) (n := S (length g)) (h := h); try lia.
        eassumption.
      * apply H2; firstorder.
      * (* In the lambda calculus we'd use cr2 here. *)
        exfalso.
        firstorder.
Qed.

Lemma reducible_L:
  forall g,
  reducible (length g) (L g).
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
  apply cr1 with (length g) (L g); auto.
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

Lemma fundamental:
  forall e g,
  typing g e void -> L g e.
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
  - specialize (IHe1 (negation ts :: g) H0).
    specialize (IHe2 (ts ++ g) H2).
    rewrite L_composition in IHe1.
    admit.
Admitted.

Theorem strong_normalization:
  forall g e,
  typing g e void -> SN step e.
Proof.
  intros.
  eapply cr1.
  - apply reducible_L.
  - (* We use the fundamental lemma here... somehow. *)
    admit.
Admitted.

Corollary consistency:
  forall e,
  ~typing [] e void.
Proof.
  do 2 intro.
  assert (SN step e).
  - apply strong_normalization with [].
    assumption.
  - (* It is closed, so it can't be normalizable! *)
    admit.
Admitted.
