(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.TypeSystem.
Require Import Local.Pi.Graph.
Require Import Local.Pi.Calculus.
Require Import Local.Pi.Control.

Section Interpretation.

  Variable pi_base: type.

  Hypothesis pi_base_is_output: alternating O pi_base.

  Definition is_variable (k: pseudoterm) (n: nat): Prop :=
    k = bound n.

  Inductive interpret_type: pseudoterm -> type -> Prop :=
    | interpret_type_base:
      interpret_type base pi_base
    | interpret_type_negation:
      forall ts cs t,
      Forall2 interpret_type ts cs ->
      t = dual (channel I cs) ->
      interpret_type (negation ts) t.

  Inductive interpret: pseudoterm -> term -> Prop :=
    | interpret_jump:
      forall x xs n ns,
      is_variable x n ->
      Forall2 is_variable xs ns ->
      interpret (jump x xs) (output n ns)
    | interpret_bind:
      forall b ts c p cs q q',
      interpret b p ->
      interpret c q ->
      Forall2 interpret_type ts cs ->
      q' = lift 1 (length cs) q ->
      interpret (bind b ts c) (local_env p cs q').

  Local Notation pB := (pi_base).
  Local Notation cO cs := (channel O cs).
  Local Notation cI cs := (channel I cs).

  Goal
    (* TODO: give an example number here. *)
    let p :=
      (* \j.\x.\y.\z.
           (\h)((\k)(h@1<y@3, k@0, x@4>
                   | !k@0(a, b).h@3<b@0, j@7, a@1>)
              | !h@0(c, d, e).d@1<e@0, z@4>) *)
      (restriction
        (cI [pB; cO [dual pB; dual pB]; pB])
        (parallel
          (restriction
            (cI [pB; pB])
            (parallel
              (output 1 [4; 0; 3])
              (replication 0
                [pB; pB]
                (output 3 [1; 7; 0]))))
          (replication 0
            [pB; cO [dual pB; dual pB]; pB]
            (output 1 [4; 0]))))
    in interpret Syntax.ex1 p.
  Proof.
    repeat econstructor.
  Qed.

  Lemma interpret_generates_output:
    forall t c,
    interpret_type t c ->
    alternating O c.
  Proof.
    fix H 3.
    destruct 1.
    - apply pi_base_is_output.
    - subst; simpl.
      constructor.
      induction H0; simpl.
      + constructor.
      + constructor; auto.
        replace I with (inverse O) by auto.
        apply alternating_inverse_dual.
        now apply H with x.
  Qed.

  Lemma interpret_forall_generates_output:
    forall ts cs,
    Forall2 interpret_type ts cs ->
    Forall (alternating O) cs.
  Proof.
    induction 1; simpl.
    - constructor.
    - constructor; auto.
      now apply interpret_generates_output with x.
  Qed.

  Inductive interpret_env: list pseudoterm -> env -> Prop :=
    | interpret_env_nil:
      interpret_env [] empty
    | interpret_env_cons:
      forall t ts c cs k,
      interpret_type t c ->
      interpret_env ts cs ->
      k = (length ts) ->
      interpret_env (t :: ts) (overlay cs (env_singleton k c)).

  Lemma interpret_env_free_name:
    forall g a,
    interpret_env g a ->
    forall n,
    n >= length g ->
    ~has_free_name a n.
  Proof.
    induction 1; simpl; intros.
    - intros (t, ?).
      inversion H0.
    - intros (u, ?).
      unfold env_singleton, env_type in H3.
      dependent destruction H3.
      + eapply IHinterpret_env with n.
        * lia.
        * now exists u.
      + dependent destruction H3.
        lia.
  Qed.

  Lemma interpret_env_is_wellformed:
    forall g a,
    interpret_env g a ->
    env_wellformed a.
  Proof.
    induction g; intros.
    - dependent destruction H.
      apply empty_is_wellformed.
    - dependent destruction H.
      (* We know that c won't appear in cs. There will be a similar case in the
         [Control.v] file, take the lemma from there once it's finished! *)
      admit.
  Admitted.

  Lemma interpret_env_extend:
    forall ts cs,
    Forall2 interpret_type ts cs ->
    forall g a,
    interpret_env g a ->
    interpret_env (ts ++ g) (env_extend a (length g) cs).
  Proof.
    induction 1; simpl; intros.
    - assumption.
    - constructor.
      + assumption.
      + now apply IHForall2.
      + rewrite app_length.
        erewrite Forall2_length with _ l l'.
        * reflexivity.
        * eassumption.
  Qed.

  Lemma local_environment_coherence:
    forall g,
    env_wellformed g ->
    forall k,
    ~has_free_name g k ->
    forall t,
    env_coherent
      (overlay g (env_singleton k (dual t)))
      (connect (env_singleton k t) g).
  Proof.
    constructor; intros.
    - unfold env_type in H1, H2.
      dependent destruction H1.
      + dependent destruction H2.
        * exfalso.
          dependent destruction H2.
          apply H0; exists t1.
          assumption.
        * admit.
      + dependent destruction H2.
        * dependent destruction H1.
          dependent destruction H2.
          (* Yeah... *)
          admit.
        * exfalso.
          dependent destruction H1.
          apply H0; exists t2.
          assumption.
    - intro x.
      induction env_wellformed_acyclic with g x; auto.
      constructor; intros.
      destruct H3.
      + destruct H3 as (u, (v, ?)).
        dependent destruction H3.
        * apply H2.
          now exists u, v.
        * exfalso.
          inversion H3.
      + destruct H3 as (u, (v, ?)).
        dependent destruction H3.
        * exfalso.
          inversion H3.
        * apply H2.
          now exists u, v.
        * dependent destruction H3.
          (* We have to check one more step! TODO: refactor me, please. *)
          constructor; intros z ?.
          destruct H3.
          --- destruct H3 as (w1, (w2, ?)).
              dependent destruction H3.
              +++ exfalso.
                  apply H0.
                  exists w2.
                  now apply graph_vertex_from_edge_right with (z, w1).
              +++ exfalso.
                  inversion H3.
          --- destruct H3 as (w1, (w2, ?)).
              dependent destruction H3.
              +++ exfalso.
                  inversion H3.
              +++ exfalso.
                  apply H0.
                  exists w2.
                  now apply graph_vertex_from_edge_right with (z, w1).
              +++ exfalso.
                  apply H0.
                  now exists w2.
  Admitted.

  Lemma interpretation_preserves_typing:
    forall b p,
    interpret b p ->
    forall g a,
    TypeSystem.typing g b void ->
    interpret_env g a ->
    Control.typing O p a (length g).
  Proof.
    induction 1; intros.
    - admit.
    - dependent destruction H3.
      unfold local_env.
      eapply typing_iso.
      + apply typing_res.
        * eapply typing_par.
          --- apply IHinterpret1 with (g := negation ts :: g).
              +++ assumption.
              +++ constructor; eauto.
                  econstructor; eauto.
          --- apply typing_in with (g := a).
              +++ (* While interpreting the CPS-calculus into the pi-calculus,
                     [[b { k<x> = c }]] becomes [(\k)([b] | !k(x).[c])], with
                     the condition that [k] doesn't appear free in [c]. This
                     amounts to the lift in [H2] and to the [1 + ...] in the
                     goal. *)
                  subst.
                  (* Let's specialize our hypothesis to see how it rolls... *)
                  specialize (IHinterpret2 (ts ++ g)).
                  specialize (IHinterpret2 (env_extend a (length g) cs)).
                  specialize (IHinterpret2 H3_0).
                  admit.
              +++ replace (i2l (1 + length g) 0) with (length g) by lia.
                  apply interpret_env_free_name with g.
                  *** assumption.
                  *** lia.
              +++ now apply interpret_forall_generates_output with ts.
          --- replace (i2l (1 + length g) 0) with (length g) by lia.
              apply local_environment_coherence.
              +++ (* Sure, there aren't even edges! *)
                  now apply interpret_env_is_wellformed with g.
              +++ apply interpret_env_free_name with g.
                  *** assumption.
                  *** lia.
          --- constructor.
        * constructor.
          now apply interpret_forall_generates_output with ts.
        * replace (i2l (1 + length g) 0) with (length g) by lia.
          apply env_composition_vertex_inversion.
          admit.
      + replace (i2l (1 + length g) 0) with (length g) by lia.
        admit.
  Admitted.

End Interpretation.
