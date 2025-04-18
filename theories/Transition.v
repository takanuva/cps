(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.
Require Import Local.Reduction.
(* TODO: We take only converges from here; might wanna move it to Syntax. *)
Require Import Local.Observational.

(* This labelled transition semantics comes from Merro's paper, "On the
   Observational Theory of the CPS-calculus". We note that a label is either a
   silent action, tau, or an output action in the form of k<x>M. Merro mentions
   that the transition system is necessarily higher-order (carrying the M) in
   order to preserve some properties, but this doesn't seem to be necessary,
   actually. TODO: remove the M term from the label.

   We note that we give a special purpose for the k de Bruijn index in here, as
   we are reserving it to be the name of the continuation to jump to. I.e., in
   an action k<x>M, we're saying a term performs an action which may interact
   with the discriminating context [] { k<x> = M }. *)

Inductive label: Set :=
  | label_tau
  | label_jmp (k: nat) (ts: list pseudoterm) (b: pseudoterm).

Inductive transition: label -> relation pseudoterm :=
  (*
                x \notin FV(a<b>)
    --------------------------------------- (JMP)
             a<x>M
      a<b> ---------> M[b/x] { a<x> = M }
  *)
  | transition_jmp:
    forall k xs ts c,
    length xs = length ts ->
    transition (label_jmp k ts c) (jump 0 xs)
      (bind
        (apply_parameters xs 0 (lift 1 (length ts) c)) ts c)

  (*
          a<x>N
      M ---------> M' { a<x> = N }      a != b      b \notin FV(N)
    ---------------------------------------------------------------- (CTX-JMP)
                           a<x>N
          M { b<y> = O } ---------> M' { b<y> = O } { a<x> = N }
  *)
  | transition_ctx_jmp:
    forall k a b ts c us d,
    (* This lift was hinted by the "Proof-relevant pi-calculus" paper! *)
    transition
      (label_jmp k (traverse_list (lift 1) 0 ts) (lift 1 (length ts) c))
      a
      (bind b (traverse_list (lift 1) 0 ts) (lift 1 (length ts) c)) ->
    transition
      (label_jmp k ts c)
      (bind (switch_bindings 0 a) us d)
      (bind (bind (switch_bindings 0 b) us d) ts c)

  (*
                a<x>N
            M ---------> M'
    ---------------------------- (TAU)
                       T
      M { a<x> = N } -----> M'
  *)
  | transition_tau:
    forall k a b ts c,
    transition (label_jmp k ts c) a b ->
    transition label_tau (bind a ts c) b

  (*
                        T
                    M -----> M'
    ----------------------------------------- (CTX-TAU)
                       T
      M { a<x> = N } -----> M' { a<x> = N }
  *)
  | transition_ctx_tau:
    forall a b ts c,
    transition label_tau a b ->
    transition label_tau (bind a ts c) (bind b ts c).

Inductive transition_label_jmp_invariant (k: nat) ts c a b: Prop :=
  transition_label_jmp_invariant_ctor
    (h: context)
    (H1: static h)
    (* H2: k = #h *)
    (xs: list pseudoterm)
    (H3: length xs = length ts)
    (H4: a = h (jump #h xs))
    (H5: b = bind
              (h
                (apply_parameters xs 0 (lift (S #h) (length ts) c)))
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
    + assumption.
    + reflexivity.
    + reflexivity.
  (* Case: transition_ctx_jmp. *)
  - clear H.
    edestruct IHtransition; eauto.
    dependent destruction H5.
    (* This has all that we need. *)
    apply transition_label_jmp_invariant_ctor with
      (context_left (context_switch_bindings 0 h) us d)
      (map (switch_bindings #h) xs); simpl.
    + constructor.
      apply static_context_switch_bindings; auto.
    + rewrite traverse_list_length in H3.
      rewrite map_length.
      assumption.
    + rewrite context_switch_bindings_is_sound.
      rewrite Nat.add_0_r.
      f_equal; f_equal.
      rewrite switch_bindings_distributes_over_jump.
      f_equal.
      rewrite switch_bindings_bound_eq; auto.
      rewrite context_switch_bindings_bvars.
      reflexivity.
    + f_equal; f_equal.
      rewrite traverse_list_length.
      rewrite lift_lift_simplification; try lia.
      rewrite context_switch_bindings_is_sound.
      rewrite Nat.add_0_r.
      replace (S #h + 1) with (S (S #h)); try lia.
      f_equal; clear H1 d us.
      (* TODO: I'd like to prove this one with sigma! Can we try later? *)
      rewrite switch_bindings_behavior.
      rewrite right_cycle_characterization.
      rewrite lift_distributes_over_apply_parameters.
      simpl sequence.
      simpl app.
      rewrite apply_parameters_cons.
      rewrite apply_parameters_cons.
      rewrite apply_parameters_nil.
      rewrite subst_distributes_over_apply_parameters.
      rewrite map_map; f_equal.
      rewrite map_length.
      rewrite traverse_list_length in H3.
      rewrite context_switch_bindings_bvars.
      rewrite lift_lift_simplification by lia.
      simpl.
      rewrite subst_lift_simplification by lia.
      rewrite subst_distributes_over_apply_parameters.
      rewrite map_map.
      rewrite map_length.
      rewrite subst_lift_simplification by lia.
      erewrite map_ext; intros.
      * reflexivity.
      * rewrite switch_bindings_behavior.
        rewrite right_cycle_characterization.
        simpl sequence.
        simpl app.
        repeat rewrite apply_parameters_cons.
        rewrite apply_parameters_nil.
        reflexivity.
Qed.

Local Lemma transition_ctx_jmp_helper:
  forall k a b ts c us d e f g h,
  transition (label_jmp k e f) a (bind b e f) ->
  e = (traverse_list (lift 1) 0 ts) ->
  f = (lift 1 (length ts) c) ->
  g = (switch_bindings 0 a) ->
  h = (bind (switch_bindings 0 b) us d) ->
  transition (label_jmp k ts c) (bind g us d) (bind h ts c).
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
  intros.
  (* We start by applying (TAU) to fix the binding. *)
  apply transition_tau with #h.
  generalize xs ts c H0; clear xs ts c H0.
  (* Our induction has to happen on #h, not h itself! *)
  assert (exists k, k = #h) as (k, ?H); eauto.
  generalize #h at 1 as n.
  replace #h with k; auto.
  generalize dependent h.
  (* Now we can proceed to prove it. *)
  induction k; intros.
  (* Case: zero. *)
  - (* Clearly we're at a hole! *)
    destruct H; try discriminate; simpl.
    (* Immediate jump! *)
    apply transition_jmp.
    assumption.
  (* Case: succ. *)
  - (* We clearly have a left context. *)
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
      * rewrite context_switch_bindings_bvars; lia.
      * rewrite map_length.
        rewrite traverse_list_length.
        assumption.
    + reflexivity.
    + reflexivity.
    + rewrite context_switch_bindings_is_sound; simpl.
      rewrite context_switch_bindings_is_involutive.
      rewrite context_switch_bindings_bvars.
      rewrite Nat.add_0_r.
      rewrite switch_bindings_distributes_over_jump.
      rewrite switch_bindings_bound_eq; try lia.
      f_equal; f_equal.
      rewrite map_switch_bindings_is_involutive; auto.
    + f_equal.
      rewrite context_switch_bindings_is_sound.
      rewrite context_switch_bindings_is_involutive.
      rewrite context_switch_bindings_bvars.
      rewrite Nat.add_0_r.
      rewrite traverse_list_length.
      rewrite lift_lift_simplification; try lia.
      replace (S k + 1) with (S (S k)); try lia.
      replace k with #h; try lia.
      f_equal.
      (* Same as in the lemma above... TODO: move this property to its own lemma
         to avoid code duplication, and, if possible, try to prove it with the
         sigma tactic instead. *)
      rewrite switch_bindings_behavior.
      rewrite right_cycle_characterization.
      rewrite lift_distributes_over_apply_parameters.
      simpl sequence.
      simpl app.
      rewrite apply_parameters_cons.
      rewrite apply_parameters_cons.
      rewrite apply_parameters_nil.
      rewrite subst_distributes_over_apply_parameters.
      rewrite map_map; f_equal.
      repeat rewrite map_length.
      rewrite lift_lift_simplification by lia.
      simpl.
      rewrite subst_lift_simplification by lia.
      rewrite subst_distributes_over_apply_parameters.
      rewrite map_map.
      repeat rewrite map_length.
      rewrite subst_lift_simplification by lia.
      erewrite map_ext; intros.
      * rewrite map_switch_bindings_is_involutive.
        reflexivity.
      * rewrite switch_bindings_behavior.
        rewrite right_cycle_characterization.
        simpl sequence.
        simpl app.
        repeat rewrite apply_parameters_cons.
        rewrite apply_parameters_nil.
        reflexivity.
Qed.

Lemma transition_tau_head:
  forall a b,
  head a b -> transition label_tau a b.
Proof.
  intros.
  destruct H.
  induction H0; simpl.
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
    apply (head_longjmp h context_hole); auto with cps.
  (* Case: transition_tau_ctx. *)
  - apply head_bind_left.
    firstorder.
Qed.

Lemma converges_transition_jmp:
  forall k ts c a b,
  transition (label_jmp k ts c) a b ->
  converges a 0.
Proof.
  intros.
  apply transition_jmp_preserves_invariant in H.
  dependent destruction H.
  dependent destruction H4.
  clear H3 H5 k.
  assert (exists k, k = #h + 0) as (k, ?); eauto.
  replace #h with k; try lia.
  generalize dependent k.
  generalize O as n.
  induction H1; simpl; intros.
  - destruct H.
    constructor.
  - constructor.
    apply IHstatic.
    lia.
Qed.

Theorem head_and_transition_tau_are_equivalent:
  (* Merro, lemma 2.4 (2). *)
  same_relation head (transition label_tau).
Proof.
  split; intros.
  - exact transition_tau_head.
  - exact head_transition_tau.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma tau_eq_dec:
  forall l,
  { l = label_tau } + { l <> label_tau }.
Proof.
  induction l.
  - left; reflexivity.
  - right; discriminate.
Defined.

Definition weak (l: label): relation pseudoterm :=
  weak_transition transition tau_eq_dec l.

Definition bisi: relation pseudoterm :=
  bisimilarity transition tau_eq_dec.

Lemma bisi_refl:
  reflexive bisi.
Proof.
  apply bisimilarity_refl.
Qed.

Lemma bisi_sym:
  symmetric bisi.
Proof.
  apply bisimilarity_sym.
Qed.

Lemma bisi_trans:
  transitive bisi.
Proof.
  apply bisimilarity_trans.
Qed.
