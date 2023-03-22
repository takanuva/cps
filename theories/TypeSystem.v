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
  forall f1: (forall g,
              valid_env g -> P g base prop),
  forall f2: (forall g ts,
              valid_env g ->
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
  - apply f1; auto.
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
  - clear H0.
    rewrite lift_distributes_over_negation; f_equal.
    induction H1; simpl.
    + reflexivity.
    + f_equal; auto.
  - absurd (typing g n prop).
    + apply typing_bound_cant_be_prop.
    + constructor; auto.
Qed.

Local Hint Resolve typing_type_lift_inversion: cps.

Lemma typing_type_list_lift_inversion:
  forall ts g,
  Forall (fun t : pseudoterm => typing g t prop) ts ->
  forall i k,
  traverse_list (lift i) k ts = ts.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - f_equal; eauto with cps.
Qed.

Local Hint Resolve typing_type_list_lift_inversion: cps.

Lemma typing_type_unlift:
  forall g t i k,
  typing g (lift i k t) prop ->
  typing g t prop.
Proof.
  intros.
  dependent induction H using typing_deepind.
  - destruct t; try discriminate.
    + constructor; auto.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in x; auto.
        discriminate.
      * rewrite lift_bound_lt in x; auto.
        discriminate.
  - destruct t; try discriminate.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in x; auto.
        discriminate.
      * rewrite lift_bound_lt in x; auto.
        discriminate.
    + clear H0.
      dependent destruction x.
      constructor; auto.
      dependent induction H1.
      * destruct ts0; try discriminate.
        constructor.
      * destruct ts0; try discriminate.
        dependent destruction x.
        constructor; eauto.
        eapply H0; auto.
        reflexivity.
  - absurd (typing g n prop).
    + apply typing_bound_cant_be_prop.
    + constructor; auto.
Qed.

Lemma typing_type_preserved_under_any_env:
  forall g t,
  typing g t prop ->
  forall h,
  valid_env h ->
  typing h t prop.
Proof.
  intros until 1.
  dependent induction H using typing_deepind; intros.
  - constructor; auto.
  - clear H H0.
    constructor; auto.
    induction H1; simpl.
    + constructor.
    + constructor; auto.
  - absurd (typing g n prop).
    + apply typing_bound_cant_be_prop.
    + constructor; auto.
Qed.

Local Hint Resolve typing_type_preserved_under_any_env: cps.

Lemma typing_negation_inversion:
  forall g k ts,
  typing g k (negation ts) ->
  forall h,
  valid_env h ->
  Forall (fun t => typing h t prop) ts.
Proof.
  intros until 1.
  dependent destruction H.
  dependent induction H0; intros.
  - dependent destruction H.
    dependent destruction H.
    induction H; simpl.
    + constructor.
    + constructor; auto.
      eapply typing_type_preserved_under_any_env; eauto.
  - apply IHitem; auto.
    eapply valid_env_inv; eauto.
Qed.

Lemma typing_bound_has_type:
  forall t g n,
  item t g n ->
  valid_env g ->
  forall h,
  valid_env h -> typing h t prop.
Proof.
  induction 1; intros.
  - dependent destruction H.
    eapply typing_type_preserved_under_any_env; eauto.
  - apply IHitem; auto.
    eapply valid_env_inv.
    eassumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO: move this to Prelude. *)

Inductive insert item: nat -> relation env :=
  | insert_head:
    forall tail,
    insert item 0 tail (item :: tail)
  | insert_tail:
    forall k head tail1 tail2,
    insert item k tail1 tail2 ->
    insert item (S k) (head :: tail1) (head :: tail2).

Global Hint Constructors insert: cps.

Lemma insert_bound_ge:
  forall x n g h,
  insert x n g h ->
  forall m,
  n <= m ->
  forall y,
  item y g m -> item y h (S m).
Proof.
  induction 1; intros.
  - auto with cps.
  - destruct m.
    + exfalso.
      inversion H0.
    + dependent destruction H1.
      auto with arith cps.
Qed.

Lemma insert_bound_lt:
  forall e n g h,
  insert e n g h ->
  forall m,
  n > m ->
  forall t,
  item t g m -> item t h m.
Proof.
  induction 1; intros.
  - inversion H.
  - destruct m.
    + dependent destruction H1.
      constructor.
    + dependent destruction H1.
      constructor.
      apply IHinsert; auto.
      lia.
Qed.

Lemma insert_app_tail:
  forall x n ts g h,
  insert x n g h ->
  insert x (n + length ts) (ts ++ g) (ts ++ h).
Proof.
  induction ts; simpl; intros.
  - rewrite Nat.add_0_r.
    assumption.
  - rewrite Nat.add_succ_r; simpl.
    constructor; auto.
Qed.

Local Hint Resolve insert_app_tail: cps.

(** ** Weakening *)

Lemma typing_weak_lift:
  forall g e t,
  typing g e t ->
  forall x n h,
  insert x n g h ->
  valid_env h ->
  typing h (lift 1 n e) t.
Proof.
  intros until 1.
  induction H using typing_deepind; intros.
  - auto with cps.
  - rewrite lift_distributes_over_negation.
    erewrite typing_type_list_lift_inversion; eauto.
    apply typing_negation; auto.
    clear H0.
    induction H1.
    + constructor.
    + constructor; auto.
      apply typing_type_unlift with 1 n; eauto.
  - rename n0 into k.
    destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; auto.
      constructor; auto.
      apply insert_bound_ge with x k g; auto.
    + rewrite lift_bound_lt; auto.
      constructor; auto.
      apply insert_bound_lt with x k g; auto.
  - rewrite lift_distributes_over_jump.
    apply typing_jump with ts.
    + apply IHtyping with x; auto.
    + clear IHtyping H H0.
      induction H1; simpl.
      * constructor.
      * constructor; eauto.
  - rewrite lift_distributes_over_bind.
    apply typing_bind.
    + rewrite typing_type_list_lift_inversion with (g := h).
      * apply valid_env_typing in H.
        dependent destruction H.
        apply IHtyping1 with x; eauto with cps.
      * clear H H1 H2 IHtyping1 IHtyping2.
        induction H0; eauto with cps.
    + erewrite typing_type_list_lift_inversion; eauto.
      clear H H1 H2 H3 IHtyping1 IHtyping2.
      induction H0.
      * constructor.
      * constructor; auto.
        apply typing_type_preserved_under_any_env with g; auto.
    + rewrite typing_type_list_lift_inversion with (g := h).
      * apply valid_env_typing in H1.
        apply IHtyping2 with x; auto with cps.
        (* We could use a simpler solution, but let's build it grounds up. *)
        clear H H0 H1 IHtyping1 IHtyping2.
        induction H2; simpl; auto.
        constructor.
        apply typing_type_unlift with 1 n; eauto with cps.
      * clear H H1 H2 IHtyping1 IHtyping2.
        induction H0; eauto with cps.
Qed.

Theorem weakening:
  forall g e t,
  typing g e t ->
  forall x,
  valid_env (x :: g) ->
  typing (x :: g) (lift 1 0 e) t.
Proof.
  intros.
  eapply typing_weak_lift; eauto with cps.
Qed.

Corollary typing_lift:
  forall g e t,
  typing g e t ->
  forall h,
  valid_env (h ++ g) ->
  typing (h ++ g) (lift (length h) 0 e) t.
Proof.
  induction h; simpl; intros.
  - rewrite lift_zero_e_equals_e.
    assumption.
  - rewrite <- lift_lift_simplification with (i := 1) (k := 0) (e := e);
      try lia.
    apply weakening; auto.
    apply IHh.
    eapply valid_env_inv; eauto.
Qed.
