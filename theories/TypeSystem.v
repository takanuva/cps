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

(** ** Type system *)

Definition env: Set :=
  list pseudoterm.

(* We are free to take a simpler definition here since there are no dependent
   types. We skip several lifting operations on purpose. *)

Inductive typing: env -> relation pseudoterm :=
  | typing_base:
    forall g,
    valid_env g -> typing g base prop
  | typing_negation:
    forall g ts,
    Forall (fun t => typing g t prop) ts ->
    valid_env g ->
    typing g (negation ts) prop
  | typing_bound:
    forall g n t,
    valid_env g ->
    item t g n ->
    typing g n t
  | typing_jump:
    forall g k xs ts,
    typing g k (negation ts) ->
    Forall2 (typing g) xs ts ->
    typing g (jump k xs) void
  | typing_bind:
    forall g b ts c,
    typing (negation ts :: g) b void ->
    Forall (fun t => typing g t prop) ts ->
    typing (ts ++ g) c void ->
    typing g (bind b ts c) void

with valid_env: env -> Prop :=
  | valid_env_nil:
    valid_env []
  | valid_env_term_var:
    forall g t,
    typing g t prop -> valid_env (t :: g).

Global Hint Constructors typing: cps.
Global Hint Constructors valid_env: cps.

Lemma valid_env_typing:
  forall g e t,
  typing g e t -> valid_env g.
Proof.
  induction 1.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - dependent destruction IHtyping1.
    dependent destruction H2.
    assumption.
Qed.

Global Hint Resolve valid_env_typing: cps.

Lemma valid_env_inv:
  forall x g,
  valid_env (x :: g) -> valid_env g.
Proof.
  intros.
  dependent destruction H.
  apply valid_env_typing with x prop; auto.
Qed.

Global Hint Resolve valid_env_inv: cps.

Lemma typing_deepind:
  forall P: (forall g e t, Prop),
  forall f1: (forall g, P g base prop),
  forall f2: (forall g ts,
              Forall (fun t => typing g t prop) ts ->
              Forall (fun t => P g t prop) ts ->
              P g (negation ts) prop),
  forall f3: (forall g n t,
              valid_env g ->
              item t g n ->
              P g n t),
  forall f4: (forall g k xs ts,
              typing g k (negation ts) ->
              Forall2 (typing g) xs ts ->
              P g k (negation ts) ->
              Forall2 (P g) xs ts ->
              P g (jump k xs) void),
  forall f5: (forall g b ts c,
              typing (negation ts :: g) b void ->
              Forall (fun t => typing g t prop) ts ->
              typing (ts ++ g) c void ->
              P (negation ts :: g) b void ->
              Forall (fun t => P g t prop) ts ->
              P (ts ++ g) c void ->
              P g (bind b ts c) void),
  forall g e t,
  typing g e t -> P g e t.
Proof.
  do 6 intro; fix H 4.
  destruct 1.
  - apply f1.
  - apply f2; auto.
    clear f1 f2 f3 f4 f5 H1.
    induction H0; auto.
  - apply f3; auto.
  - apply f4 with ts; auto.
    clear f1 f2 f3 f4 f5 H0.
    induction H1; auto.
  - apply f5; auto.
    clear f1 f2 f3 f4 f5 H0_ H0_0.
    induction H0; auto.
Qed.

Lemma typing_bound_cant_be_void:
  forall g n,
  ~typing g (bound n) void.
Proof.
  intros g n H.
  dependent destruction H.
  induction H0.
  - dependent destruction H.
    inversion H.
  - dependent destruction H.
    eauto with cps.
Qed.

Lemma typing_bound_cant_be_prop:
  forall g n,
  ~typing g (bound n) prop.
Proof.
  intros g n H.
  dependent destruction H.
  induction H0.
  - dependent destruction H.
    inversion H.
  - dependent destruction H.
    eauto with cps.
Qed.

Lemma typing_type_lift_inversion:
  forall g t,
  typing g t prop ->
  forall i k,
  lift i k t = t.
Proof.
  intros until 1.
  dependent induction H using typing_deepind; intros.
  - reflexivity.
  - clear H.
    rewrite lift_distributes_over_negation; f_equal.
    induction H0; simpl.
    + reflexivity.
    + f_equal; auto.
  - absurd (typing g n prop).
    + apply typing_bound_cant_be_prop.
    + constructor; auto.
Qed.
