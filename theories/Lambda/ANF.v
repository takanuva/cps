(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Export Local.Lambda.Calculus.
Require Export Local.Lambda.PlotkinCBV.

(* The following comes from Sabry and Felleisen's "Reasoning About Programs in
   Continuation-Passing Style"... this is the set of A-reductions, which extends
   Plotkin's CBV calculus. We can compare the reduction rules from here to the
   companion paper, "The Essence of Compiling with Continuations". We expect a
   few things from here: (1) the simulation should extend to A, I hope, (2) that
   there should be a Galois connection between the CPS-calculus and the ANF
   calculus, so that we can reuse our operational semantics in there.

   Additionaly, we could prove the results from the above paper, as a treat. *)

Inductive evaluation: context -> Prop :=
  | evaluation_hole:
    evaluation context_hole
  | evaluation_application_left:
    forall f x,
    evaluation f ->
    evaluation (context_application_left f x)
  | evaluation_application_right:
    forall v x,
    evaluation x ->
    value v ->
    evaluation (context_application_right v x).

Local Goal
  forall e1 e2,
  cbv e1 e2 ->
  forall h,
  evaluation h ->
  cbv (h e1) (h e2).
Proof.
  induction 2; simpl.
  - assumption.
  - constructor.
    assumption.
  - constructor.
    + assumption.
    + assumption.
Qed.

Local Notation ABS := abstraction.
Local Notation APP := application.

(* Beware of de Bruijn math below. I wish there was a better way to do this. *)

Inductive anf: relation term :=
  (* Eta-v: \x.V x -> V, given x not free in V. *)
  | anf_etav:
    forall t V,
    value V ->
    not_free 0 V ->
    anf (ABS t (APP V 0)) V
  (* Beta-lift: E[(\x.M) N] -> (\x.E[M]) N, if x not free in E. This can be
     split in two cases, since allowing E to be just a hole would lead to a
     reflexive relation. *)
  | anf_beta_lift_left:
    (* Sigma-1: (\x.M) N L -> (\x.M L) N *)
    forall t M N L,
    anf (APP (APP (ABS t M) N) L)
        (APP (ABS t (APP M (lift 1 0 L))) N)
  | anf_beta_lift_right:
    (* Sigma-3: V ((\x.M) N) -> (\x.V M) N *)
    forall V t M N,
    value V ->
    anf (APP V (APP (ABS t M) N))
        (APP (ABS t (APP (lift 1 0 V) M)) N)
  (* Beta-flat: E[M N L] -> (\x.E[x L]) (M N), if x not free in E, L. We are
     free to ignore E in here, because performing a beta-flat in here will then
     make a beta-lift redex, resulting in the expected term. *)
  | anf_beta_flat:
    forall t M N L,
    anf (APP (APP M N) L)
        (APP (ABS t (APP 0 (lift 1 0 L))) (APP M N))
  (* Beta-id: (\x.x) M -> M. *)
  | anf_beta_id:
    forall t M,
    anf (APP (ABS t 0) M) M
  (* Beta-omega: (\x.E[y x]) M -> E[y M], if x not free in E[y]. Is there a way
     to factor this so that we don't need the E...? *)
  | anf_beta_omega:
    forall t E x y M,
    evaluation E ->
    x = context_bvars E ->
    y <> context_bvars E ->
    anf (APP (ABS t (context_lift 1 0 E (APP (lift 1 x (bound y)) x))) M)
        (E (APP y (lift x 0 M))).

(* Count the number of applications on the left-hand side of an application. *)

Fixpoint unnamed_subterms e: nat :=
  match e with
  | bound _ =>
    0
  | abstraction _ b =>
    unnamed_subterms b
  | application (application _ _ as f) x =>
    1 + unnamed_subterms f + unnamed_subterms x
  | application f x =>
    unnamed_subterms f + unnamed_subterms x
  (* TODO: what about pairs and thunks? *)
  | _ =>
    0
  end.

Lemma unnamed_subterms_lift:
  forall e i k,
  unnamed_subterms (lift i k e) = unnamed_subterms e.
Proof.
  sigma.
  induction e; sigma; simpl; intros.
  - destruct (le_gt_dec k n); sigma; auto.
  - apply IHe.
  - rewrite IHe1, IHe2.
    destruct e1; simpl; auto.
    destruct (le_gt_dec k n); sigma; auto.
  - reflexivity.
  - reflexivity.
Qed.

Lemma unnamed_subterms_context_lift:
  forall h i k e,
  unnamed_subterms (context_lift i k h e) = unnamed_subterms (h e).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - apply IHh.
  - rewrite unnamed_subterms_lift.
    rewrite IHh; destruct h; simpl; auto.
  - rewrite unnamed_subterms_lift.
    rewrite IHh; destruct f; simpl; auto.
    destruct (le_gt_dec k n); sigma; auto.
  - reflexivity.
  - reflexivity.
Qed.

Notation cmp a b := (a = b \/ a > b).

Local Goal
  forall a b,
  anf a b ->
  cmp (unnamed_subterms a) (unnamed_subterms b).
Proof.
  induction 1; intros.
  (* Case: eta-v. *)
  - left.
    destruct H; simpl; lia.
  (* Case: sigma-1. *)
  - destruct M; simpl.
    + right.
      rewrite unnamed_subterms_lift.
      lia.
    + right.
      rewrite unnamed_subterms_lift.
      lia.
    + (* Here it decreases! *)
      left.
      rewrite unnamed_subterms_lift.
      lia.
    + right.
      rewrite unnamed_subterms_lift.
      lia.
    + right.
      rewrite unnamed_subterms_lift.
      lia.
  (* Case: sigma-3. *)
  - left.
    destruct H; simpl.
    + auto.
    + rewrite unnamed_subterms_lift.
      sigma; simpl.
      lia.
    + auto.
  (* Case: beta-flat. *)
  - (* Here it decreases! *)
    right; simpl.
    rewrite unnamed_subterms_lift.
    lia.
  (* Case: beta-id. *)
  - left; simpl; auto.
  (* Case: beta-omega. *)
  - (* Aw crap... *)
    left; simpl.
    rewrite unnamed_subterms_context_lift.
    (* We don't actually care about beta in here... *)
    clear H0 H1.
    induction H; simpl.
    + rewrite unnamed_subterms_lift.
      destruct (le_gt_dec x y); simpl.
      * sigma; simpl.
        (* TODO: is there any way to simplify this step? *)
        replace (@inst term term _ _ _ (subst_lift x)) with
          (@lift term term _ _ x 0) by auto.
        now rewrite unnamed_subterms_lift.
      * sigma; simpl.
        (* TODO: is there any way to simplify this step? *)
        replace (@inst term term _ _ _ (subst_lift x)) with
          (@lift term term _ _ x 0) by auto.
        now rewrite unnamed_subterms_lift.
    + rewrite <- IHevaluation.
      (* I was not expecting this to work, but... hey! It did! *)
      destruct f; simpl; lia.
    + rewrite <- IHevaluation.
      destruct H0; simpl; lia.
Qed.

(* Count the number of beta redexes within applications. *)

Definition is_beta e :=
  match e with
  | application (abstraction _ _) _ =>
    1
  | _ =>
    0
  end.

Lemma is_beta_lift:
  forall e i k,
  is_beta (lift i k e) = is_beta e.
Proof.
  destruct e; simpl; intros.
  - destruct (le_gt_dec k n); sigma; auto.
  - reflexivity.
  - destruct e1; simpl; auto.
    destruct (le_gt_dec k n); sigma; auto.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint inner_computations e: nat :=
  match e with
  | bound _ =>
    0
  | abstraction _ b =>
    inner_computations b
  | application f x =>
    is_beta f + is_beta x + inner_computations f + inner_computations x
  (* TODO: what about pairs and thunks? *)
  | _ =>
    0
  end.

(*
  Rules 1, 5 and 6 decrease the term size, while not changing the number of
  inner lets nor the number of unnamed stuff.

  Rules 2 and 3 decrease the number of inner lets, while not changing the number
  of unnamed stuff.

  Rule 4 decreases the number of unnamed stuff.
*)

Local Goal
  forall e1 e2,
  anf e1 e2 ->
  rst(full) e1 e2.
Proof.
  induction 1.
  - (* Ok, eta of course doesn't hold. *)
    admit.
  - eapply rst_trans.
    apply rst_step.
    apply full_application_left.
    apply full_beta.
    apply rst_sym.
    eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl; sigma.
    eauto with cps.
  - eapply rst_trans.
    apply rst_step.
    apply full_application_right.
    apply full_beta.
    apply rst_sym.
    eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl; sigma.
    eauto with cps.
  - apply rst_sym.
    eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl; sigma.
    eauto with cps.
  - eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl; sigma.
    eauto with cps.
  - eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl.
    rewrite context_subst_is_sound.
    simpl.
    rewrite Nat.add_0_r.
    rewrite context_lift_bvars.
    rewrite <- H0.
    sigma.
    (* Of course! *)
    admit.
Admitted.
