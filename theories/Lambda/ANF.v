(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Export Local.Lambda.Calculus.
Require Export Local.Lambda.CallByValue.

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

Goal
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
    (* (\x.M) N L -> (\x.M L) N *)
    forall t M N L,
    anf (APP (APP (ABS t M) N) L)
        (APP (ABS t (APP M (lift 1 0 L))) N)
  | anf_beta_lift_right:
    (* V ((\x.M) N) -> (\x.V M) N *)
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
  (* Beta-omega: (\x.E[y x]) M -> E[y M], if x not free in E[y]. *)
  | anf_beta_omega:
    forall t E x y M,
    evaluation E ->
    x = context_bvars E ->
    y <> context_bvars E ->
    anf (APP (ABS t (context_lift 1 0 E (APP (lift 1 x y) x))) M)
        (E (APP y (lift x 0 M))).

Goal
  forall e1 e2,
  anf e1 e2 ->
  rst(full) e1 e2.
Proof.
  induction 1.
  - (* Ok, eta of course doesn't hold. *)
    admit.
  - eapply rst_trans.
    apply rst_step.
    apply full_app1.
    apply full_beta.
    apply rst_sym.
    eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl.
    (* Sure. *)
    admit.
  - eapply rst_trans.
    apply rst_step.
    apply full_app2.
    apply full_beta.
    apply rst_sym.
    eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl.
    (* Sure. *)
    admit.
  - apply rst_sym.
    eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl.
    replace (lift 0 0 M) with M.
    replace (lift 0 0 N) with N.
    (* Yep! *)
    admit.
    admit.
    admit.
  - eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl.
    (* Sure. *)
    admit.
  - eapply rst_trans.
    apply rst_step.
    apply full_beta.
    simpl.
    rewrite context_subst_is_sound.
    simpl.
    rewrite Nat.add_0_r.
    rewrite context_lift_bvars.
    rewrite <- H0.
    destruct (le_gt_dec x y).
    destruct (lt_eq_lt_dec x x) as [ [ ? | ? ] | ? ]; try lia.
    simpl.
    destruct (lt_eq_lt_dec x (S y)) as [ [ ? | ? ] | ? ]; try lia.
    (* Of course! *)
    admit.
    destruct (lt_eq_lt_dec x x) as [ [ ? | ? ] | ? ]; try lia.
    simpl.
    destruct (lt_eq_lt_dec x y) as [ [ ? | ? ] | ? ]; try lia.
    admit.
Admitted.
