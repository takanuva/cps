(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Equality.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.

Import ListNotations.

Variant universe: Set :=
  | prop
  | type.

Inductive term: Set :=
  (* Sorts. *)
  | sort (u: universe)
  (* Variables. *)
  | bound (n: nat)
  (* Products. *)
  | pi (t: term) (u: term)
  | abstraction (t: term) (e: term)
  | application (e: term) (f: term)
  | definition (e: term) (t: term) (f: term).

Fixpoint traverse g k e: term :=
  match e with
  | sort u =>
    sort u
  | bound n =>
    g k n 
  | pi t u =>
    pi (traverse g k t) (traverse g (S k) u)
  | abstraction t e =>
    abstraction (traverse g k t) (traverse g (S k) e)
  | application e f =>
    application (traverse g k e) (traverse g k f)
  | definition e t f =>
    definition (traverse g k e) (traverse g k t) (traverse g (S k) f)
  end.

Global Instance cc_dbVar: dbVar term :=
  bound.

Global Instance cc_dbTraverse: dbTraverse term term :=
  traverse.

Global Instance cc_dbVarLaws: dbVarLaws term.
Proof.
  split; auto.
Qed.

Global Instance cc_dbTraverseLaws: dbTraverseLaws term term.
Proof.
  split; unfold Substitution.traverse; intros.
  - generalize dependent k.
    induction x; simpl; auto; intros;
    f_equal; auto.
  - apply (H k (bound n)).
  - generalize dependent j.
    generalize dependent k.
    induction x; simpl; auto; intros;
    try now (f_equal; auto).
    + apply (H 0).
    + f_equal.
      * apply IHx1; intros.
        apply H.
      * apply IHx2; intros.
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H.
    + f_equal.
      * apply IHx1; intros.
        apply H.
      * apply IHx2; intros.
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H.
    + f_equal.
      * apply IHx1; intros.
        apply H.
      * apply IHx2; intros.
        apply H.
      * apply IHx3; intros.
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H.
  - generalize dependent k.
    induction x; simpl; intros; auto;
    f_equal; auto.
Qed.

Inductive context: Set :=
  | context_hole
  | context_pi_type (t: context) (u: term)
  | context_pi_body (t: term) (u: context)
  | context_abs_type (t: context) (e: term)
  | context_abs_body (t: term) (e: context)
  | context_app_left (f: context) (e: term)
  | context_app_right (f: term) (e: context)
  | context_def_val (e: context) (t: term) (f: term)
  | context_def_type (e: term) (t: context) (f: term)
  | context_def_body (e: term) (t: term) (f: context).

Fixpoint apply_context (h: context) (x: term): term :=
  match h with
  | context_hole =>
    x
  | context_pi_type t u =>
    pi (apply_context t x) u
  | context_pi_body t u =>
    pi t (apply_context u x)
  | context_abs_type t e =>
    abstraction (apply_context t x) e
  | context_abs_body t e =>
    abstraction t (apply_context e x)
  | context_app_left f e =>
    application (apply_context f x) e
  | context_app_right f e =>
    application f (apply_context e x)
  | context_def_val e t f =>
    definition (apply_context e x) t f
  | context_def_type e t f =>
    definition e (apply_context t x) f
  | context_def_body e t f =>
    definition e t (apply_context f x)
  end.

Coercion apply_context: context >-> Funclass.

Definition decl: Set :=
  option term * term.

Definition decl_var (t: term): decl :=
  (None, t).

Definition decl_def (e: term) (t: term): decl :=
  (Some e, t).

Definition env: Set :=
  list decl.

Inductive step: env -> relation term :=
  (* Beta reduction. *)
  | step_beta:
    forall g t e f,
    step g (application (abstraction t e) f) (subst f 0 e)
  (* Zeta reduction. *)
  | step_zeta:
    forall g e t f,
    step g (definition e t f) (subst e 0 f)
  (* Delta reduction. *)
  | step_delta:
    forall g t e n,
    item (decl_def e t) g n ->
    step g (bound n) (lift (1 + n) 0 e)
  (* Congruence closure. *)
  | step_pi_type:
    forall g t1 t2 u,
    step g t1 t2 ->
    step g (pi t1 u) (pi t2 u)
  | step_pi_body:
    forall g t u1 u2,
    step (decl_var t :: g) u1 u2 ->
    step g (pi t u1) (pi t u2)
  | step_abs_type:
    forall g t1 t2 e,
    step g t1 t2 ->
    step g (abstraction t1 e) (abstraction t2 e)
  | step_abs_body:
    forall g t e1 e2,
    step (decl_var t :: g) e1 e2 ->
    step g (abstraction t e1) (abstraction t e2)
  | step_app_left:
    forall g e1 e2 f,
    step g e1 e2 ->
    step g (application e1 f) (application e2 f)
  | step_app_right:
    forall g e f1 f2,
    step g f1 f2 ->
    step g (application e f1) (application e f2)
  | step_def_val:
    forall g e1 e2 t f,
    step g e1 e2 ->
    step g (definition e1 t f) (definition e2 t f)
  | step_def_type:
    forall g e t1 t2 f,
    step g t1 t2 ->
    step g (definition e t1 f) (definition e t2 f)
  | step_def_body:
    forall g e t f1 f2,
    step (decl_def e t :: g) f1 f2 ->
    step g (definition e t f1) (definition e t f2).

Conjecture step_is_confluent:
  forall g, confluent (step g).

Inductive conv: env -> relation term :=
  | conv_join:
    forall g e1 e2 f,
    rt(step g) e1 f ->
    rt(step g) e2 f ->
    conv g e1 e2
  | conv_eta_left:
    forall g e1 e2 t f1 f2,
    rt(step g) e1 (abstraction t f1) ->
    rt(step g) e2 f2 ->
    conv (decl_var t :: g) f1 (application (lift 1 0 f2) (bound 0)) ->
    conv g e1 e2
  | conv_eta_right:
    forall g e1 e2 t f1 f2,
    rt(step g) e1 f1 ->
    rt(step g) e2 (abstraction t f2) ->
    conv (decl_var t :: g) (application (lift 1 0 f1) (bound 0)) f2 ->
    conv g e1 e2.

(* Lemma step_abs_inversion:
  forall g t1 e1 f,
  step g (abstraction t1 e1) f ->
  exists t2 e2,
  f = abstraction t2 e2.
Proof.
  intros.
  dependent destruction H.
  - do 2 eexists.
    reflexivity.
  - do 2 eexists.
    reflexivity.
Qed.

Lemma rt_step_abs_inversion:
  forall g t1 e1 f,
  rt(step g) (abstraction t1 e1) f ->
  exists t2 e2,
  f = abstraction t2 e2.
Proof.
  intros.
  dependent induction H.
  - now apply step_abs_inversion with g t1 e1.
  - now exists t1, e1.
  - edestruct IHclos_refl_trans1 as (t2, (e2, ?)).
    + reflexivity.
    + subst.
      now apply IHclos_refl_trans2 with t2 e2.
Qed. *)

Lemma conv_refl:
  forall g,
  reflexive (conv g).
Proof.
  repeat intro.
  apply conv_join with x.
  - apply rt_refl.
  - apply rt_refl.
Qed.

Lemma conv_sym:
  forall g,
  symmetric (conv g).
Proof.
  induction 1.
  - now apply conv_join with f.
  - eapply conv_eta_right; eauto with cps.
  - eapply conv_eta_left; eauto with cps.
Qed.

Lemma conv_trans:
  forall g,
  transitive (conv g).
Proof.
  admit.
Admitted.

Inductive typing: env -> relation term :=
  (*
           |- G
    --------------------
      G |- Prop : Type
  *)
  | typing_prop:
    forall g,
    valid_env g ->
    typing g (sort prop) (sort type)
  (*
      (x: T) or (x = e: T) in G
    -----------------------------
             G |- x : T
  *)
  | typing_bound:
    forall g n d t,
    valid_env g ->
    item (d, t) g n ->
    typing g (bound n) (lift (1 + n) 0 t)
  (*
       G, X: T |- U : s
    ----------------------
      G |- Pi X: T.U : s
  *)
  | typing_pi:
    forall g t u s,
    typing (decl_var t :: g) u (sort s) ->
    typing g (pi t u) (sort s)
  (*
          G, x: T |- e: U
    ----------------------------
      G |- \x: T.e : Pi x: T.U
  *)
  | typing_abs:
    forall g t e u,
    typing (decl_var t :: g) e u ->
    typing g (abstraction t e) (pi t u)
  (*
      G |- f : Pi x: T.U     G |- e : T
    -------------------------------------
              G |- f e : U[e/x]
  *)
  | typing_app:
    forall g f e t u,
    typing g f (pi t u) ->
    typing g e t ->
    typing g (application f e) (subst e 0 u)
  (*
      G |- e : T     G, x = e: T |- f : U
    ---------------------------------------
        G |- let x = e: T in f : U[e/x]
  *)
  | typing_def:
    forall g e f t u,
    typing g e t ->
    typing (decl_def e t :: g) f u ->
    typing g (definition e t f) (subst e 0 u)
  (*
      G |- e : T     G |- U : s     G |- T = U
    --------------------------------------------
                     G |- e : U
  *)
  | typing_conv:
    forall g e t u s,
    typing g e t ->
    typing g u (sort s) ->
    conv g t u ->
    typing g e u

with valid_env: env -> Prop :=
  (*
    --------
      |- .
  *)
  | valid_env_nil:
    valid_env []
  (*
      |- G     G |- T: s
    -----------------------
          |- G, x: T
  *)
  | valid_env_var:
    forall g t s,
    valid_env g ->
    typing g t (sort s) ->
    valid_env (decl_var t :: g)
  (*
      |- G     G |- e : T     G |- T : s
    --------------------------------------
              |- G, x = e: T
  *)
  | valid_env_def:
    forall g e t s,
    valid_env g ->
    typing g e t ->
    typing g t (sort s) ->
    valid_env (decl_def e t :: g).

Lemma valid_env_typing:
  forall g e t,
  typing g e t ->
  valid_env g.
Proof.
  induction 1.
  - assumption.
  - assumption.
  - dependent destruction IHtyping.
    assumption.
  - dependent destruction IHtyping.
    assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Conjecture strong_normalization:
  forall g e t,
  typing g e t -> SN (step g) e.
