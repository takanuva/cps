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
  | label_jmp (n: nat) (ts: list pseudoterm) (b: pseudoterm).

Inductive transition: label -> relation pseudoterm :=
  (*
                  x \nin fv(a<b>)
    ---------------------------------------- (JMP)
             a<x> M
      a<b> ----------> M[b/x] { a<x> = M }
  *)
  | transition_jmp:
    forall xs ts c,
    length xs = length ts ->
    transition (label_jmp 0 ts c) (jump 0 xs)
      (bind
        (apply_parameters xs 0 (lift 1 (length ts) c))
        ts c)

  (*
              a<x> N
          M ----------> M'
    ---------------------------- (TAU)
                       t
      M { a<x> = N } -----> M'
  *)
  | transition_tau:

    forall k xs N M M',

    (* Ignore the names for now... *)

    transition (label_jmp k xs N) M M' ->

    transition label_tau
      (bind M xs N)
      M'

  (*
                       t
                   M -----> M'
    ----------------------------------------- (CTX-TAU)
                       t
      M { a<x> = N } -----> M' { a<x> = N }
  *)
  | transition_ctx_tau:
    forall M M' N xs,

    (* Hmm... *)

    transition label_tau M M' ->

    transition label_tau
      (bind M xs N)
      (bind M' xs N)

  (*
          a<x> N
      M ----------> M' { a<x> = N }    a != b    b \nin fv(N)
    ----------------------------------------------------------- (CTX-JMP)
                       a<x> N
      M { b<y> = O } ----------> M' { b<y> = O } { a<x> = N }
  *)
  | transition_ctx_jmp:
    forall M a xs N M' ys O,

    (* This lift was hinted by the "Proof-relevant pi-calculus" paper! *)

    transition
      (label_jmp a (traverse_list (lift 1) 0 xs) (lift 1 (length xs) N))
      M
      (* Notice the "not free" condition in the rule? ;) *)
      (bind M' (traverse_list (lift 1) 0 xs) (lift 1 (length xs) N)) ->

    transition
      (label_jmp (S a) xs N)
      (bind (switch_bindings 0 M) ys O)
      (bind (bind (switch_bindings 0 M') ys O) xs N).

Inductive transition_label_jmp_invariant k ts c a b: Prop :=
  transition_label_jmp_invariant_ctor
    (h: context)
    (H1: static h)
    (H2: #h = k)
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
  - apply transition_label_jmp_invariant_ctor with context_hole xs; simpl.
    + constructor.
    + reflexivity.
    + eassumption.
    + reflexivity.
    + reflexivity.
  - clear H.
    specialize IHtransition with
      a (traverse_list (lift 1) 0 ts) (lift 1 (length ts) c).
    destruct IHtransition; auto.
    dependent destruction H5.
    rewrite traverse_list_length in H3 |- *.
    apply transition_label_jmp_invariant_ctor with
      (context_left (context_switch_bindings 0 h) ys O)
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
      clear H1 O ys.
      unfold switch_bindings.
      rewrite lift_distributes_over_apply_parameters.
      rewrite subst_distributes_over_apply_parameters.
      rewrite map_map; f_equal.
      rewrite map_length.
      rewrite lift_lift_simplification; try lia.
      rewrite subst_lift_simplification; try lia.
      reflexivity.
Qed.

Lemma transition_jmp_inversion:
  forall P: nat -> list pseudoterm -> pseudoterm -> relation pseudoterm,
  forall k ts c a b,
  forall H: (forall h xs,
             static h ->
             #h = k ->
             length xs = length ts ->
             a = h (jump k xs) ->
             b = bind (h
                   (apply_parameters xs 0 (lift (S k) (length ts) c)))
                   ts c ->
             P k ts c a b),
  transition (label_jmp k ts c) a b ->
  P k ts c a b.
Proof.
  intros.
  destruct transition_jmp_preserves_invariant with k ts c a b; auto.
  eapply H; eauto.
Qed.

Local Lemma transition_ctx_jmp_helper:
    forall M a xs N M' ys O,
    forall b c d e,

    transition
      (label_jmp a b c)
      M
      (bind M' b c) ->

    b = (traverse_list (lift 1) 0 xs) ->
    c = (lift 1 (length xs) N) ->
    d = (switch_bindings 0 M) ->
    e = (bind (switch_bindings 0 M') ys O) ->

    transition
      (label_jmp (S a) xs N)
      (bind d ys O)
      (bind e xs N).
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
      (b := traverse_list (lift 1) 0 ts)
      (c := lift 1 (length ts) c).
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
  - clear IHtransition.
    inversion H using transition_jmp_inversion; intros.
    rewrite H3.
    rewrite H4.
    replace k with #h; auto.
    apply head_longjmp; auto.
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
