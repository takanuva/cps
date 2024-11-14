(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Observational.
Require Import Local.TypeSystem.
Require Import Local.Pi.Graph.
Require Import Local.Pi.Calculus.
Require Import Local.Pi.Control.

Global Hint Unfold env_edge: cps.
Global Hint Resolve dual_is_involutive: cps.
Global Hint Resolve channel_equals_double_dual: cps.

Section Interpretation.

  (* We did not define base types in the typesystem for the pi-calculus, so we
     parametrize everything by some arbitrary interpretation for base types. *)
  Variable pi_base: type.

  (* Of course, since the type system requires types to be I/O alternating, so
     should be the case of anything that is taken to be the base type. *)
  Hypothesis pi_base_is_output: alternating O pi_base.

  (* The CPS-calculus is defined as higher-order, so we make a relation stating
     that a term is indeed some variable. *)
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
    (* Check interpretation for example 1. *)
    in interpret Syntax.ex1 p.
  Proof.
    (* Holds trivially by construction. *)
    repeat econstructor.
  Qed.

  (* To be honest, it's amazing that this is true up to the same [k]; i.e., the
     same number of variables is introduced in head position for both CPS term
     and the resulting process for the interpretation. *)
  Goal
    forall b p,
    interpret b p ->
    forall k,
    converges b k <-> observable p k.
  Proof.
    induction 1; split; intros.
    - dependent destruction H1.
      unfold is_variable in H.
      dependent destruction H.
      constructor.
    - unfold is_variable in H.
      dependent destruction H.
      dependent destruction H1.
      constructor.
    - dependent destruction H3.
      apply observable_restriction.
      apply observable_parallel_left.
      now apply IHinterpret1.
    - unfold local_env in H3.
      dependent destruction H3.
      dependent destruction H3.
      + constructor.
        now apply IHinterpret1.
      + exfalso.
        inversion H3.
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

  Lemma interpret_env_length:
    forall g a,
    interpret_env g a ->
    length g = introduced_vars a.
  Proof.
    unfold introduced_vars.
    induction 1; simpl.
    - reflexivity.
    - simpl in IHinterpret_env.
      rewrite <- IHinterpret_env.
      rewrite H1; lia.
  Qed.

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
    has_output_mode g ->
    forall k,
    ~has_free_name g k ->
    forall t,
    alternating I t ->
    env_coherent
      (overlay g (env_singleton k (dual t)))
      (connect (env_singleton k t) g).
  Proof.
    constructor; intros.
    - admit.
    - unfold env_type in H3, H4.
      dependent destruction H3.
      + dependent destruction H4.
        * exfalso.
          dependent destruction H4.
          apply H1; now exists t1.
        * (* We have a unique output type, so [t1 = t2], and they compose. *)
          exists t1.
          rewrite env_wellformed_unique with g t2 t1 i; auto.
          apply H0 in H3.
          destruct t1; simpl in H3; subst.
          now apply type_composition_oo with ts.
      + dependent destruction H4.
        * dependent destruction H3.
          dependent destruction H4.
          (* Trivial since t2 is an input type. *)
          exists t2; destruct t2.
          dependent destruction H2; simpl.
          apply type_composition_oi with (map dual ts); auto with cps.
        * exfalso.
          dependent destruction H3.
          apply H1; now exists t2.
    - intro x.
      constructor; intros.
      (* Trivially acyclic: all edges we have are from [k] to [|g|]! *)
      admit.
  Admitted.

  Lemma interpretation_preserves_typing:
    forall b p,
    interpret b p ->
    forall g a,
    TypeSystem.typing g b void ->
    interpret_env g a ->
    Control.typing O p a.
  Proof.
    induction 1; intros.
    - admit.
    - subst.
      dependent destruction H3.
      unfold local_env.
      eapply typing_iso.
      + apply typing_res.
        * eapply typing_par.
          --- apply IHinterpret1 with (g := negation ts :: g).
              +++ assumption.
              +++ constructor; eauto.
                  econstructor; eauto.
          --- (* This lifting in q, which means that a continuation doesn't
                 appear free in its own definition, is remarkably convenient in
                 here. It arises by the translation, syntactically, and it is
                 required by the type system! *)
              apply typing_in with (g := a).
              +++ eapply IHinterpret2.
                  *** eassumption.
                  *** rewrite <- interpret_env_length with g a by auto.
                      now apply interpret_env_extend.
              +++ admit.
              +++ now apply interpret_forall_generates_output with ts.
          --- replace (1 + introduced_vars a - 0 - 1) with
                (introduced_vars a) by lia.
              rewrite interpret_env_length with g a by auto.
              (* This lift becomes a no-op! *)
              rewrite lifting_over_introduced_vars_is_noop by auto.
              admit.
          --- constructor.
        * constructor.
          now apply interpret_forall_generates_output with ts.
        * replace (1 + introduced_vars a - 0 - 1) with
            (introduced_vars a) by lia.
          (* We can simplify this a bit. *)
          rewrite lifting_over_introduced_vars_is_noop by auto.
          apply env_composition_vertex_inversion.
          admit.
      + replace (1 + introduced_vars a - 0 - 1) with (introduced_vars a) by lia.
        admit.
  Admitted.

  Lemma interpretation_reflects_typing:
    forall b p,
    interpret b p ->
    forall g a,
    Control.typing O p a ->
    interpret_env g a ->
    TypeSystem.typing g b void.
  Proof.
    (* TODO: I suspect we'll need an equivalent type system to make this work,
       where the typing rules follow the structure of the terms by subsuming
       both graph isomorphism and local weakening. Alternatively, this could be
       seem as an induction scheme for the original type system (indeed, I
       should define it as one). *)
    admit.
  Admitted.

  Theorem control_calculus_typing_correspondence:
    forall b p,
    interpret b p ->
    forall g a,
    interpret_env g a ->
    TypeSystem.typing g b void <-> Control.typing O p a.
  Proof.
    split; intros.
    - now apply interpretation_preserves_typing with b g.
    - now apply interpretation_reflects_typing with p a.
  Qed.

End Interpretation.
