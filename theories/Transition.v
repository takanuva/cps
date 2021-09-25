(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.
(* Huh, we only need the arguments command for same_relation... *)
Require Import Local.AbstractRewriting.
Require Import Local.Reduction.
(* TODO: We take only converges from here; might wanna move it to Syntax. *)
Require Import Local.Observational.

(* TODO: I'll need to define head reduction properly and elsewhere! *)

Inductive head: relation pseudoterm :=
  | head_longjmp:
    forall h,
    static h ->
    forall xs ts c,
    length xs = length ts ->
    head (bind (h (jump #h xs)) ts c)
         (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c)
  | head_bind_left:
    LEFT head.

Inductive label: Set :=
  | label_tau
  | label_jmp (k: nat) (ts: list pseudoterm) (b: pseudoterm).

Inductive transition: label -> relation pseudoterm :=
  | transition_jmp:
    forall xs ts c,
    length xs = length ts ->
    transition (label_jmp 0 ts c) (jump 0 xs)
      (bind
        (apply_parameters xs 0 (lift 1 (length ts) c)) ts c)
  | transition_tau:
    forall k a b ts c,
    transition (label_jmp k ts c) a b ->
    transition label_tau (bind a ts c) b
  | transition_ctx_tau:
    forall a b ts c,
    transition label_tau a b ->
    transition label_tau (bind a ts c) (bind b ts c)
  | transition_ctx_jmp:
    forall k a b ts c us d,
    (* This lift was hinted by the "Proof-relevant pi-calculus" paper! *)
    transition
      (label_jmp k (traverse_list (lift 1) 0 ts) (lift 1 (length ts) c))
      a
      (bind b (traverse_list (lift 1) 0 ts) (lift 1 (length ts) c)) ->
    transition
      (label_jmp (S k) ts c)
      (bind (switch_bindings 0 a) us d)
      (bind (bind (switch_bindings 0 b) us d) ts c).

Definition weak (l: label): relation pseudoterm :=
  match l with
  | label_tau =>
    rt(transition label_tau)
  | label_jmp k ts c =>
    comp rt(transition label_tau) (transition l)
  end.

Inductive transition_label_jmp_invariant k ts c a b: Prop :=
  transition_label_jmp_invariant_ctor
    (h: context)
    (H1: static h)
    (H2: k = #h)
    (xs: list pseudoterm)
    (H3: length xs = length ts)
    (H4: a = h (jump k xs))
    (H5: b = bind
              (h
                (apply_parameters xs 0 (lift (S k) (length ts) c)))
              ts c).

Lemma transition_jmp_preserves_invariant:
  forall k ts c a b,
  transition (label_jmp k ts c) a b ->
  transition_label_jmp_invariant k ts c a b.
Proof.
  intros.
  dependent induction H.
  (* Case: transition_jmp. *)
  - apply transition_label_jmp_invariant_ctor with context_hole xs; simpl.
    + constructor.
    + reflexivity.
    + assumption.
    + reflexivity.
    + reflexivity.
  (* Case: transition_ctx_jmp. *)
  - clear H; rename k0 into k.
    specialize IHtransition with
      k (traverse_list (lift 1) 0 ts) (lift 1 (length ts) c).
    destruct IHtransition; auto.
    dependent destruction H5.
    rewrite traverse_list_length in H3 |- *.
    (* This has all that we need. *)
    apply transition_label_jmp_invariant_ctor with
      (context_left (context_switch_bindings 0 h) us d)
      (map (switch_bindings #h) xs); simpl.
    + constructor.
      apply static_context_switch_bindings; auto.
    + rewrite context_switch_bindings_depth; auto.
    + rewrite map_length.
      assumption.
    + rewrite context_switch_bindings_is_sound.
      rewrite Nat.add_0_r.
      f_equal; f_equal.
      rewrite switch_bindings_distributes_over_jump.
      f_equal.
      apply switch_bindings_bound_eq; auto.
    + f_equal; f_equal.
      rewrite lift_lift_simplification; try lia.
      rewrite context_switch_bindings_is_sound.
      rewrite Nat.add_0_r.
      replace (S #h + 1) with (S (S #h)); try lia.
      f_equal.
      clear H1 d us.
      unfold switch_bindings.
      rewrite lift_distributes_over_apply_parameters.
      rewrite subst_distributes_over_apply_parameters.
      rewrite map_map; f_equal.
      rewrite map_length.
      rewrite lift_lift_simplification; try lia.
      rewrite subst_lift_simplification; try lia.
      reflexivity.
Qed.

Local Lemma transition_ctx_jmp_helper:
    forall k a b ts c us d e f g h,
    transition (label_jmp k e f) a (bind b e f) ->
    e = (traverse_list (lift 1) 0 ts) ->
    f = (lift 1 (length ts) c) ->
    g = (switch_bindings 0 a) ->
    h = (bind (switch_bindings 0 b) us d) ->
    transition (label_jmp (S k) ts c) (bind g us d) (bind h ts c).
Proof.
  intros until 5.
  generalize H; clear H.
  rewrite H0, H1, H2, H3.
  apply transition_ctx_jmp.
Qed.

Lemma transition_tau_longjmp:
  forall h,
  static h ->
  forall xs ts c,
  length xs = length ts ->
  transition label_tau (bind (h (jump #h xs)) ts c)
       (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c).
Proof.
  unfold CTXJMP; intros.
  (* We start by applying (TAU) to fix the binding. *)
  apply transition_tau with #h.
  generalize xs ts c H0; clear xs ts c H0.
  (* Our induction has to happen on #h, not h itself! *)
  assert (exists k, k = #h); eauto.
  destruct H0 as (k, ?).
  replace #h with k; auto.
  generalize h, H, H0; clear h H H0.
  (* Now we can proceed to prove it. *)
  induction k; intros.
  (* Case: zero. *)
  - (* Clearly we're at a hole! *)
    destruct H; try discriminate; simpl.
    (* Immediate jump! *)
    apply transition_jmp.
    assumption.
  (* Case: succ. *)
  - (* We clearly have a left contetx. *)
    destruct H; try discriminate.
    simpl in H0 |- *.
    (* We will apply a (CTX-JMP) here, but there's a lot of housekeeping. *)
    eapply transition_ctx_jmp_helper with
      (e := traverse_list (lift 1) 0 ts)
      (f := lift 1 (length ts) c).
    + apply IHk with
        (h := context_switch_bindings 0 h)
        (xs := map (switch_bindings #h) xs).
      * apply static_context_switch_bindings; auto.
      * rewrite context_switch_bindings_depth; lia.
      * rewrite map_length.
        rewrite traverse_list_length.
        assumption.
    + reflexivity.
    + reflexivity.
    + rewrite context_switch_bindings_is_sound; simpl.
      rewrite context_switch_bindings_is_involutive.
      rewrite context_switch_bindings_depth.
      rewrite Nat.add_0_r.
      rewrite switch_bindings_distributes_over_jump.
      rewrite switch_bindings_bound_eq; try lia.
      f_equal; f_equal.
      rewrite map_switch_bindings_is_involutive; auto.
    + f_equal.
      rewrite context_switch_bindings_is_sound.
      rewrite context_switch_bindings_is_involutive.
      rewrite context_switch_bindings_depth.
      rewrite Nat.add_0_r.
      rewrite traverse_list_length.
      rewrite lift_lift_simplification; try lia.
      replace (S k + 1) with (S (S k)); try lia.
      replace k with #h; try lia.
      f_equal.
      unfold switch_bindings at 1.
      rewrite lift_distributes_over_apply_parameters.
      rewrite subst_distributes_over_apply_parameters.
      do 2 rewrite map_length.
      rewrite map_map; f_equal.
      * symmetry.
        apply map_switch_bindings_is_involutive.
      * rewrite lift_lift_simplification; try lia.
        rewrite subst_lift_simplification; try lia.
        reflexivity.
Qed.

Lemma transition_tau_head:
  forall a b,
  head a b -> transition label_tau a b.
Proof.
  induction 1.
  - apply transition_tau_longjmp; auto.
  - apply transition_ctx_tau; auto.
Qed.

Lemma head_transition_tau:
  forall a b,
  transition label_tau a b -> head a b.
Proof.
  intros.
  dependent induction H.
  (* Case: transition_tau. *)
  - clear IHtransition.
    edestruct transition_jmp_preserves_invariant; eauto.
    rewrite H4.
    rewrite H5.
    replace k with #h; auto.
    apply head_longjmp; auto.
  (* Case: transition_tau_ctx. *)
  - apply head_bind_left.
    apply IHtransition; auto.
Qed.

Theorem head_and_transition_tau_are_equivalent:
  (* Merro, lemma 2.4 (2). *)
  same_relation head (transition label_tau).
Proof.
  split; intros.
  - exact transition_tau_head.
  - exact head_transition_tau.
Qed.
