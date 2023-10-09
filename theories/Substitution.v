(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Metatheory.

Section DeBruijn.

  (* An algebra for substitution, or de Bruijn algebra, inspired by the work of
     Schafer et al. on the paper Completeness and Decidability of de Bruijn
     Substitution Algebra in Coq. This is in turn inspired by the definition of
     the lambda sigma calculuf of Abadi et al., introduced in their Explicit
     Substitutions paper. *)

  Inductive substitution: Set :=
    | subs_id
    | subs_lift
    | subs_cons (y: pseudoterm) (s: substitution)
    | subs_comp (s: substitution) (t: substitution).

  Fixpoint instantiate_rec (k: nat) (s: substitution) (c: pseudoterm)  :=
    match s with
    | subs_id =>
      c
    | subs_lift =>
      lift 1 k c
    | subs_cons y s =>
      subst y k (instantiate_rec (S k) s c)
    | subs_comp s t =>
      instantiate_rec k t (instantiate_rec k s c)
    end.

  Definition instantiate: substitution -> pseudoterm -> pseudoterm :=
    instantiate_rec 0.

  Coercion instantiate: substitution >-> Funclass.

  Lemma foo:
    forall s n,
    instantiate_rec (S n) s 0 = 0.
  Proof.
    induction s; simpl; intros.
    - reflexivity.
    - rewrite lift_bound_lt; auto with arith.
    - rewrite IHs.
      rewrite subst_bound_lt; auto with arith.
    - rewrite IHs1.
      rewrite IHs2.
      reflexivity.
  Qed.

  Lemma bar:
    forall s c n m,
    m >= n ->
    instantiate_rec (S m) s (lift 1 n c) =
      lift 1 n (instantiate_rec m s c).
  Proof.
    induction s; simpl; intros.
    - reflexivity.
    - symmetry.
      rewrite lift_lift_permutation; try lia.
      reflexivity.
    - rewrite IHs; try lia.
      rewrite lift_and_subst_commute; try lia.
      reflexivity.
    - rewrite IHs1; try lia.
      rewrite IHs2; try lia.
      reflexivity.
  Qed.

  Lemma baz:
    forall r e y p k,
    instantiate_rec (p + k) r (subst y p e) =
      subst (instantiate_rec k r y) p (instantiate_rec (S (p + k)) r e).
  Proof.
    induction r; simpl; intros.
    - reflexivity.
    - rewrite lift_addition_distributes_over_subst.
      reflexivity.
    - specialize IHr with (k := S k); simpl in IHr.
      replace (S (p + k)) with (p + S k); try lia.
      rewrite IHr.
      remember (instantiate_rec (S (p + S k)) r e) as d.
      rewrite subst_addition_distributes_over_itself.
      f_equal; f_equal.
      lia.
    - rewrite IHr1.
      rewrite IHr2.
      reflexivity.
  Qed.

  (*
    So, we have the following axioms to satisfy:

      1) 0[e .: s] = e
      2) S >> (e .: s) = s
      3) I >> s = s
      4) s >> I = s
      5) (s >> r) >> u = s >> (r >> u)
      6) (e .: s) >> r = (e[r] .: s) >> r

    Additionally:

      7) 0 .: S = I
      8) 0[S^n] = n
  *)

  Structure curien_axioms: Prop := {
    H1: forall b s,
        instantiate (subs_cons b s) 0 = b;
    H2: forall b c s,
        subs_comp subs_lift (subs_cons b s) c = s c;
    H3: forall b s,
        subs_comp subs_id s b = s b;
    H4: forall b s,
        subs_comp s subs_id b = s b;
    H5: forall b s r u,
        subs_comp (subs_comp s r) u b = subs_comp s (subs_comp r u) b;
    H6: forall b c s r,
        subs_comp (subs_cons b s) r c = subs_cons (r b) (subs_comp s r) c;
    H7: forall b,
        subs_cons 0 subs_lift b = subs_id b
  }.

  Goal
    curien_axioms.
  Proof.
    split; intros.
    - unfold instantiate; simpl.
      rewrite foo.
      rewrite subst_bound_eq; auto.
      rewrite lift_zero_e_equals_e.
      reflexivity.
    - unfold instantiate; simpl.
      rewrite bar; auto.
      rewrite subst_lift_simplification; auto.
      rewrite lift_zero_e_equals_e.
      reflexivity.
    - unfold instantiate; simpl.
      reflexivity.
    - unfold instantiate; simpl.
      reflexivity.
    - unfold instantiate; simpl.
      reflexivity.
    - unfold instantiate; simpl.
      rewrite baz with (p := 0) (k := 0); simpl.
      reflexivity.
    - unfold instantiate; simpl.
      (* Ok, somehow I still don't got a proof for that, but this is clearly
         true as 0 replaces 0 then unlifts everything. *)
      assert (forall k, subst 0 k (lift 1 (S k) b) = b); auto.
      induction b using pseudoterm_deepind; intros.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + destruct (le_gt_dec (S k) n).
        rewrite lift_bound_ge; try lia.
        rewrite subst_bound_gt; try lia.
        reflexivity.
        rewrite lift_bound_lt; try lia.
        destruct (Nat.eq_dec k n).
        rewrite subst_bound_eq; try lia.
        rewrite lift_bound_ge; try lia.
        rewrite Nat.add_0_r; auto.
        rewrite subst_bound_lt; try lia.
        reflexivity.
      + rewrite lift_distributes_over_negation.
        rewrite subst_distributes_over_negation.
        f_equal.
        induction H; simpl.
        reflexivity.
        f_equal; auto.
        do 2 rewrite traverse_list_length.
        replace (length l + S k) with (S (length l + k)); try lia.
        apply H.
      + rewrite lift_distributes_over_jump.
        rewrite subst_distributes_over_jump.
        f_equal.
        apply IHb.
        clear IHb b.
        induction H; simpl.
        reflexivity.
        f_equal; auto.
      + rewrite lift_distributes_over_bind.
        rewrite subst_distributes_over_bind.
        f_equal.
        apply IHb1.
        clear IHb1 IHb2 b1 b2.
        induction H; auto.
        simpl; f_equal; auto.
        do 2 rewrite traverse_list_length.
        replace (length l + S k) with (S (length l + k)); try lia.
        apply H.
        rewrite traverse_list_length.
        apply IHb2.
  Qed.

End DeBruijn.
