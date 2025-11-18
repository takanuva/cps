(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

(* TODO: question, is Kennedy's translation (the tail-recursive version) really
   the same as Plotkin's CBV then administrative reductions (linear jumps)? I am
   starting to think that maybe there's need for some floating too... *)

Require Import Lia.
Require Import List.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Lambda.Calculus.
Require Import Local.Lambda.PlotkinCBV.
Require Local.Residuals.

Import ListNotations.

Section ModifiedCBV.

  Local Notation jump := Residuals.redexes_jump.
  Local Notation bind := Residuals.redexes_bind.
  Local Notation V := CPS.void.

  Local Notation VAR d n :=
    (* [x] = k<x> *)
    (jump d (var 0) [var (1 + n)]) (only parsing).

  Local Notation ABS d b t1 t2 :=
    (* [\x.e] = k<f> { f<x, k> = [e] } *)
    (bind (jump d (var 1) [var 0]) [t1; t2] b) (only parsing).

  Local Notation APP b c t1 t2 :=
    (* [e f] = [e] { k<f> = [f] { k<v> = f<v, k> } } *)
    (bind b [t1] (bind c [t2]
      (jump false (var 1) [var 2; var 0]))) (only parsing).

  (* The modified CBV translation is just Plotkin's CBV translation, but instead
     it returns marked terms. We underline every jump to a current continuation
     whose content is defined and thus the jump may be performed. We define two
     versions by mutual induction (note the first argument, being a boolean), so
     that we may know whether the current continuation is defined or not. *)

  Inductive modified_cbv_cps: bool -> term -> Residuals.redexes -> Prop :=
    | modified_cbv_cps_bound:
      forall d n,
      modified_cbv_cps d (var n) (VAR d n)
    | modified_cbv_cps_abstraction:
      forall d t e b,
      modified_cbv_cps false (lift 1 1 e) b ->
      modified_cbv_cps d (abstraction t e) (ABS d b CPS.void CPS.void)
    | modified_cbv_cps_application:
      forall d f x b c,
      modified_cbv_cps true (lift 1 0 f) b ->
      modified_cbv_cps true (lift 2 0 x) c ->
      modified_cbv_cps d (application f x) (APP b c CPS.void CPS.void)
    (* TODO: extend this translation for thunks. *).

  (* The modified CBV translation is merely Plotkin's translation, but we mark
     each jump to the current continuation which is a redex. *)

  Local Goal
    forall d e r,
    modified_cbv_cps d e r ->
    cbv_cps e (Residuals.unmark r).
  Proof.
    induction 1; intros; simpl.
    - constructor.
    - now constructor.
    - now constructor.
  Qed.

  Lemma modified_cbv_residuals_generalized:
    forall b e r,
    modified_cbv_cps b e r ->
    forall g,
    (if b then (* Not ideal to use a conditional here, but it works... *)
      exists2 s,
      item (Some (1, s)) g 0 & Residuals.redexes_count s = 0
    else
      True) ->
    exists2 t,
    Residuals.residuals g r r t & Residuals.redexes_count t = 0.
  Proof.
    induction 1; intros.
    - (* Are we performing this jump...? *)
      destruct d.
      + (* If we are, we know that it's defined: this was administrative. *)
        destruct H as (s, ?, ?).
        eexists.
        * constructor; simpl.
          eassumption.
        * simpl.
          rewrite Residuals.mark_unmark_is_sound with s by auto.
          rewrite <- Residuals.mark_lift_is_sound.
          rewrite <- Residuals.mark_apply_parameters_is_sound.
          apply Residuals.redexes_count_mark.
      + (* No jump will be performed, so no problem. *)
        eexists.
        * constructor.
        * reflexivity.
    - specialize (IHmodified_cbv_cps (None :: None :: g) ltac:(trivial)).
      destruct IHmodified_cbv_cps as (b', ?, ?).
      destruct d.
      + destruct H0 as (s, ?, ?).
        eexists; try constructor; simpl.
        * do 2 constructor; simpl.
          eassumption.
        * eassumption.
        * simpl.
          rewrite Residuals.mark_unmark_is_sound with s by auto.
          rewrite <- Residuals.mark_lift_is_sound.
          rewrite <- Residuals.mark_apply_parameters_is_sound.
          rewrite Residuals.redexes_count_mark.
          now simpl.
      + eexists; try constructor; simpl.
        * constructor.
        * eassumption.
        * simpl; lia.
    - (* The continuation given to c will be our anchor, which should be put in
         place, but that itself will not be performed as it represents a source
         redex. *)
      set (anchor := jump false (var 1) [var 2; var 0]).
      specialize (IHmodified_cbv_cps2 (Some (1, anchor) :: None :: g)).
      (* By induction, c is fine. *)
      edestruct IHmodified_cbv_cps2 as (c', ?, ?); intros.
      + eexists; eauto with cps.
      + (* The continuation given to b will be c (along with the anchor), which
           is expected to be performed. *)
        specialize (IHmodified_cbv_cps1 (Some (1, bind c' [V] anchor) :: g)).
        (* By induction, b is fine. *)
        edestruct IHmodified_cbv_cps1 as (b', ?, ?); intros.
        * eexists; eauto with cps.
          simpl; lia.
        * eexists; eauto with cps.
          (* None of these items have marks anymore. *)
          simpl; lia.
  Qed.

  Lemma modified_cbv_residuals:
    forall e r,
    modified_cbv_cps false e r ->
    exists2 s,
    Residuals.residuals [] r r s & Residuals.redexes_count s = 0.
  Proof.
    intros.
    apply modified_cbv_residuals_generalized with false e; intros.
    - assumption.
    - trivial.
  Qed.

  Lemma modified_cbv_regular:
    forall e r,
    modified_cbv_cps false e r ->
    Residuals.regular r.
  Proof.
    intros.
    destruct modified_cbv_residuals with e r as (s, ?, ?).
    - assumption.
    - now exists r, s.
  Qed.

  (* Main idea: do the CPS translation, take the residuals, and then perform
     exhaustive garbage collection to remove all the inlined contexts. NOTE:
     this will NOT work anymore once we introduce thunks and then we'll need be
     a bit smarter. TODO: I'll leave this task for future me. To do this in the
     proper way, we'll either actually perform garbage collection for the marked
     terms alone, OR we could use the notion of an intuitionistic term and show
     there are no unused continuations. Are unused thunks actually fine? TODO:
     check Danvy and Filinski's paper! *)

  Inductive optimal_cbv_cps: term -> Syntax.pseudoterm -> Prop :=
    | optimal_cbv_cps_mk:
      forall e r b c,
      (* The toplevel continuation is not defined, hence false. *)
      modified_cbv_cps false e r ->
      (* This is expected to work on any context, so the empty one suffices,
         producing a term with no marks. *)
      Residuals.residuals [] r r (Residuals.mark b) ->
      (* Then just perform all garbage collection available. *)
      rt(Reduction.smol) b c ->
      normal Reduction.smol c ->
      optimal_cbv_cps e c.

End ModifiedCBV.
