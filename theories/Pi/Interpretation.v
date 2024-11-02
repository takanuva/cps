(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
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
      forall t ts c cs,
      interpret_type t c ->
      interpret_env ts cs ->
      interpret_env (t :: ts) (overlay cs (env_singleton (length ts) c)).

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
      unfold env_singleton, env_type in H2.
      dependent destruction H2.
      + eapply IHinterpret_env with n.
        * lia.
        * now exists u.
      + dependent destruction H2.
        lia.
  Qed.

  Lemma local_environment_coherence:
    forall g k,
    ~has_free_name g k ->
    forall t,
    env_coherent
      (overlay g (env_singleton k (dual t)))
      (connect (env_singleton k t) g).
  Proof.
    constructor; intros.
    - unfold env_type in H0, H1.
      dependent destruction H0.
      + dependent destruction H1.
        * exfalso.
          dependent destruction H1.
          apply H; exists t1.
          assumption.
        * (* So, t1 = t2. *)
          admit.
      + dependent destruction H1.
        * dependent destruction H0.
          dependent destruction H1.
          (* Yeah... *)
          admit.
        * exfalso.
          dependent destruction H0.
          apply H; exists t2.
          assumption.
    - admit.
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
              +++ admit.
              +++ replace (i2l (1 + length g) 0) with (length g) by lia.
                  apply interpret_env_free_name with g.
                  *** assumption.
                  *** lia.
              +++ now apply interpret_forall_generates_output with ts.
          --- replace (i2l (1 + length g) 0) with (length g) by lia.
              apply local_environment_coherence.
              apply interpret_env_free_name with g.
              +++ assumption.
              +++ lia.
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
