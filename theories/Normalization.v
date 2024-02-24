(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.
Require Import Local.AbstractRewriting.
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Observational.
Require Import Local.TypeSystem.
Require Import Local.Conservation.
Require Import Local.Structural.
Require Import Local.Shrinking.

(** ** Normalization. *)

Lemma SN_beta_and_SN_step_coincide:
  forall c,
  SN beta c <-> SN step c.
Proof.
  split; intros.
  - apply SN_subset with (union beta smol).
    + apply step_characterization.
    + apply shrinking_preserves_strong_normalization.
      * exact smol_is_shrinking.
      * assumption.
  - apply SN_subset with step.
    + apply step_beta.
    + assumption.
Qed.

Definition sumup {T} (f: T -> nat) (ts: list T): nat :=
  fold_right Nat.add 0 (map f ts).

Lemma sumup_app:
  forall {T} f a b,
  @sumup T f (a ++ b) = sumup f a + sumup f b.
Proof.
  induction a; simpl; intros.
  - reflexivity.
  - unfold sumup; simpl.
    rewrite <- Nat.add_assoc; f_equal.
    apply IHa.
Defined.

Lemma sumup_cons:
  forall {T} f a b,
  @sumup T f (a :: b) = f a + sumup f b.
Proof.
  intros.
  reflexivity.
Defined.

Fixpoint count (t: pseudoterm): nat :=
  match t with
  | base =>
    1
  | negation ts =>
    1 + sumup count ts
  | _ =>
    0
  end.

Lemma sumup_count_is_well_founded:
  well_founded (ltof _ (sumup count)).
Proof.
  apply well_founded_ltof.
Defined.

Lemma count_arg:
  forall {t ts g},
  t = (negation ts :: g) ->
  sumup count (ts ++ g) < sumup count t.
Proof.
  intros.
  dependent destruction H.
  rewrite sumup_app, sumup_cons; simpl.
  lia.
Defined.

Lemma count_ret:
  forall {t ts g},
  t = (negation ts :: g) ->
  sumup count g < sumup count t.
Proof.
  intros.
  dependent destruction H.
  rewrite sumup_cons; simpl.
  lia.
Defined.

Lemma count_sub:
  forall {t g},
  t = (base :: g) ->
  sumup count g < sumup count t.
Proof.
  intros.
  dependent destruction H.
  rewrite sumup_cons; simpl.
  lia.
Defined.

Lemma count_switch:
  forall n g h,
  switch n g h ->
  sumup count g = sumup count h.
Proof.
  unfold sumup; induction 1; simpl.
  - lia.
  - now rewrite IHswitch.
Qed.

(* -------------------------------------------------------------------------- *)

Local Notation candidate :=
  (pseudoterm -> Prop).

(*
  We define a family of environment-indexed sets L which is inductively defined
  over the number of type constructors in an environment (rather than a type as
  usual). The idea is that we can build an elimination context with which a term
  can interact, based on the channel names. Our definition is well-founded, but
  follows as:

           1) L [] =
                { b | SN beta b }
           2) L (negation ts :: g) =
                { b | forall c, L (ts ++ g) c -> L g (b { k<ys> = c }) }
           3) L (base :: g) =
                { b | forall x, L g (k<x> { k<y> = b }) }

  I.e., in (1), the empty environment states that the term is always strongly
  normalizing but does not consider which continuations it can jump to. In (2),
  we consider composition with a continuation type, saying that we will keep our
  property of interest (here strong normalization) when our term is within an
  elimination context for such continuation, namely C { k<ys> = c }, for any c
  that is semantically valid. Since in (3) we consider base types, that have no
  elimination context, we have to consider that instead the term is valid upon
  any substitution of the variable, so it means that it does not use it for
  anything in particular, exactly what we would expect for the base type. Notice
  that, for any x (without loss of generality, different from k):

                 G, y: base |- k<x> { k<y> = b }   ~~>   b[x/y]

  ...requiring that this keeps the property of interest for any x ensures the
  good use of the y variable.
*)

Definition ARR ts (U V: candidate): candidate :=
  fun b =>
    forall c,
    U c -> V (bind b ts c).

Definition SUB (V: candidate): candidate :=
  fun b =>
    forall x,
    V (bind (jump 0 [lift 1 0 x]) [base] b).

Definition L: env -> candidate :=
  Fix sumup_count_is_well_founded (fun _ => candidate) (fun t f =>
    match t as x return (t = x -> candidate) with
    (* Given (G, ~T)... *)
    | negation ts :: g =>
      fun H =>
        ARR ts (f _ (count_arg H)) (f _ (count_ret H))
    (* Given (G, b)... *)
    | base :: g =>
      fun H =>
        SUB (f _ (count_sub H))
    (* Empty context means we're done! *)
    | [] =>
      fun _ =>
        SN beta
    (* We don't really care about anything else. *)
    | _ =>
      fun _ _ =>
        False
    end eq_refl).

Lemma L_arr_composition:
  forall ts g,
  L (negation ts :: g) = ARR ts (L (ts ++ g)) (L g).
Proof.
  intros.
  unfold L.
  rewrite Fix_eq.
  - fold L.
    reflexivity.
  - intros.
    destruct x; simpl; auto.
    destruct p; simpl; auto.
    + rewrite H.
      reflexivity.
    + do 2 rewrite H.
      reflexivity.
Qed.

Lemma L_sub_composition:
  forall g,
  L (base :: g) = SUB (L g).
Proof.
  intros.
  unfold L.
  rewrite Fix_eq.
  - fold L.
    reflexivity.
  - intros.
    destruct x; simpl; auto.
    destruct p; simpl; auto.
    + rewrite H.
      reflexivity.
    + do 2 rewrite H.
      reflexivity.
Qed.

Inductive wellbehaved: env -> context -> Prop :=
  | wellbehaved_nil:
    wellbehaved [] context_hole
  | wellbehaved_cons_base:
    forall h g x,
    wellbehaved g h ->
    wellbehaved (base :: g) (compose_context h
      (context_right (jump 0 [lift 1 0 x]) [base]
        context_hole))
  | wellbehaveed_cons_negation:
    forall g h ts c,
    wellbehaved g h ->
    L (ts ++ g) c ->
    wellbehaved (negation ts :: g) (compose_context h
      (context_left context_hole ts c)).

Inductive split_wellbehaved_result: env -> context -> nat -> Prop :=
  | split_wellbehaved_result_mk:
    forall g h n g1 g2 h1 h2,
    g = g1 ++ g2 ->
    n = length g1 ->
    wellbehaved g2 h2 ->
    h = compose_context h2 h1 ->
    length g1 = #h1 ->
    split_wellbehaved_result g h n.

(* TODO: move to [Metatheory.v]. *)

Lemma compose_context_assoc:
  forall h r s,
  compose_context (compose_context h r) s =
    compose_context h (compose_context r s).
Proof.
  induction h; simpl; intros.
  - reflexivity.
  - now rewrite IHh.
  - now rewrite IHh.
Qed.

Lemma split_wellbehaved_context:
  forall g h,
  wellbehaved g h ->
  forall n,
  n < length g ->
  split_wellbehaved_result g h n.
Proof.
  induction 1; simpl; intros.
  - exfalso.
    inversion H.
  - destruct n.
    + econstructor 1 with [] (base :: g) context_hole _.
      * reflexivity.
      * reflexivity.
      * constructor.
        eassumption.
      * simpl.
        rewrite compose_context_assoc.
        now simpl.
      * reflexivity.
    + destruct IHwellbehaved with n; try lia; subst.
      econstructor 1 with (base :: g1) g2 _ h2.
      * reflexivity.
      * now simpl.
      * assumption.
      * rewrite compose_context_assoc.
        reflexivity.
      * rewrite compose_context_bvars; simpl.
        lia.
  - destruct n.
    + econstructor 1 with [] (negation ts :: g) context_hole _.
      * reflexivity.
      * reflexivity.
      * constructor;
        eassumption.
      * simpl.
        rewrite compose_context_assoc.
        now simpl.
      * reflexivity.
    + destruct IHwellbehaved with n; try lia; subst.
      econstructor 1 with (negation ts :: g1) g2 _ h2.
      * reflexivity.
      * now simpl.
      * assumption.
      * rewrite compose_context_assoc.
        reflexivity.
      * rewrite compose_context_bvars; simpl.
        lia.
Qed.

Lemma L_preservation:
  forall g,
  valid_env g ->
  forall c,
  (* Here, g generates a well-behaved context, which is valid as g for any other
     term as well. *)
  (forall h, wellbehaved g h ->
             (forall b, L g b -> SN beta (h b)) ->
             SN beta (h c)) ->
  L g c.
Proof.
  induction g; intros.
  - specialize (H0 context_hole); simpl in H0.
    apply H0; intros.
    + constructor.
    + assumption.
  - dependent destruction H.
    dependent destruction H.
    + rewrite L_sub_composition in H1 |- *.
      unfold SUB in H0 |- *; intros.
      eapply IHg; auto; intros.
      replace (bind (jump 0 [lift 1 0 x]) [base] c) with
        (context_right (jump 0 [lift 1 0 x]) [base] context_hole c); auto.
      rewrite <- compose_context_is_sound.
      apply H1; intros.
      * now constructor.
      * rewrite compose_context_is_sound; simpl.
        apply H2, H3.
    + rewrite L_arr_composition in H1 |- *.
      unfold ARR in H1 |- *; intros d ?.
      eapply IHg; auto; intros.
      replace (bind c ts d) with (context_left context_hole ts d c); auto.
      rewrite <- compose_context_is_sound.
      apply H1; intros.
      * now constructor.
      * rewrite compose_context_is_sound; simpl.
        now apply H4, H5.
Qed.

(* -------------------------------------------------------------------------- *)
(* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- *)
(* -------------------------------------------------------------------------- *)

Record reducibility (g: env) (R: env -> candidate): Prop := {
  reducibility_weakening:
    valid_env g ->
    forall t h,
    insert [t] 0 h g ->
    forall e,
    R h e ->
    R g (lift 1 0 e);
  reducibility_exchange:
    valid_env g ->
    forall n h,
    switch n h g ->
    forall e,
    R h e ->
    R g (switch_bindings n e);
  reducibility_contraction:
    valid_env g ->
    forall h,
    join 0 h g ->
    forall e,
    R h e ->
    R g (subst 0 0 e);
  reducibility_normalization:
    forall c,
    R g c ->
    SN beta c;
  reducibility_nonempty:
    exists c,
    R g c
}.

Goal
  forall ts,
  valid_env ts ->
  forall g b,
  L (ts ++ g) b ->
  exists h: context,
  L g (h b).
Proof.
  intros ts.
  remember (sumup count ts) as n.
  generalize dependent ts.
  induction n using lt_wf_ind.
  destruct ts; simpl; intros; subst.
  - clear H.
    exists context_hole.
    now simpl.
  - dependent destruction H0.
    dependent destruction H0.
    + rewrite L_sub_composition in H2.
      unfold SUB in H2.
      (* Any variable, even fresh, will do it! *)
      specialize (H2 0).
      rewrite lift_bound_ge in H2 by lia; simpl in H2.
      specialize (H (sumup count ts)).
      edestruct H as (h, ?).
      * now apply count_sub.
      * reflexivity.
      * assumption.
      * eassumption.
      * eexists (compose_context h (context_right _ _ context_hole)); simpl.
        rewrite compose_context_is_sound; simpl.
        eassumption.
    + rename ts0 into us.
      rewrite L_arr_composition in H2.
      unfold ARR in H2.
      (* Since sets are not empty... *)
      assert (exists c, L (us ++ ts ++ g) c) as (c, ?) by admit.
      specialize (H2 c H3).
      specialize (H (sumup count ts)).
      edestruct H as (h, ?).
      * unfold sumup; simpl.
        lia.
      * reflexivity.
      * assumption.
      * eassumption.
      * eexists (compose_context h (context_left context_hole _ _)); simpl.
        rewrite compose_context_is_sound; simpl.
        eassumption.
Admitted.

Section Reducibility.

  Variable g: env.

  Hypothesis IH:
    forall h,
    valid_env h ->
    sumup count h < sumup count g ->
    reducibility h L.

  Lemma L_weakening:
    valid_env g ->
    forall t h,
    insert [t] 0 h g ->
    forall e,
    L h e ->
    L g (lift 1 0 e).
  Proof.
    intros.
    dependent destruction H0; simpl in *.
    dependent destruction H.
    dependent destruction H.
    (* Case: base type. *)
    - rewrite L_sub_composition.
      unfold SUB; intros.
      apply L_preservation; auto; intros.
      specialize (H2 e H1).
      eapply sn_beta_backwards_step.
      + apply beta_context.
        apply beta_ctxjmp with (h := context_hole).
        reflexivity.
      + simpl.
        rewrite lift_lift_simplification by lia.
        rewrite subst_lift_simplification by lia.
        admit.
    (* Case: negation type. *)
    - rewrite L_arr_composition.
      unfold ARR; intros.
      apply L_preservation; auto; intros.
      admit.
  Admitted.

  Lemma L_right_cycle_aux:
    forall x xs ts ys e,
    simple x ->
    valid_env ts ->
    valid_env xs ->
    valid_env ys ->
    sumup count (ts ++ xs ++ x :: ys) < sumup count g ->
    L (ts ++ xs ++ x :: ys) e ->
    L (ts ++ x :: xs ++ ys) (right_cycle (length xs) (length ts) e).
  Proof.
    (* TODO: when rewriting the following lemma, might wanna check the statement
       on this one as well. *)
    induction xs using rev_ind; intros.
    - simpl in H4 |- *.
      rewrite right_cycle_zero_e_equals_e.
      assumption.
    - rename x0 into a.
      rewrite <- app_assoc in H4 |- *; simpl in H4 |- *.
      apply reducibility_exchange with (g := ts ++ xs ++ x :: a :: ys)
        (n := length ts + length xs) in H4.
      + replace (a :: ys) with ([a] ++ ys) in H4 by auto.
        apply IHxs in H4.
        * rewrite right_cycle_switch_bindings_simplification in H4.
          rewrite app_length; simpl length.
          rewrite Nat.add_comm.
          assumption.
        * assumption.
        * assumption.
        * apply Forall_app in H1 as (?, ?).
          assumption.
        * apply Forall_app in H1 as (?, ?).
          apply Forall_app; auto.
        * do 3 rewrite sumup_app in H3.
          do 2 rewrite sumup_app.
          do 2 rewrite sumup_cons in H3.
          rewrite sumup_cons.
          rewrite sumup_app.
          rewrite sumup_cons.
          lia.
      + apply IH.
        * apply Forall_app in H1 as (?, ?).
          dependent destruction H5.
          apply Forall_app; split; auto.
          apply Forall_app; split; auto.
        * do 3 rewrite sumup_app in H3.
          do 2 rewrite sumup_app.
          do 2 rewrite sumup_cons in H3.
          do 2 rewrite sumup_cons.
          lia.
      + apply Forall_app in H1 as (?, ?).
        dependent destruction H5.
        apply Forall_app; split; auto.
        apply Forall_app; split; auto.
      + apply switch_app.
        replace (length xs) with (length xs + 0) by lia.
        apply switch_app.
        constructor.
  Qed.

  Lemma L_left_cycle_aux:
    forall x xs ts ys e,
    simple x ->
    valid_env ts ->
    valid_env xs ->
    valid_env ys ->
    sumup count (ts ++ x :: xs ++ ys) < sumup count g ->
    L (ts ++ x :: xs ++ ys) e ->
    L (ts ++ xs ++ x :: ys) (left_cycle (length xs) (length ts) e).
  Proof.
    (* This lemma is kinda ugly, sigh... TODO: I really think I should rewrite
       this lemma, even though it's a technical one. *)
    induction xs; intros.
    - simpl in H |- *.
      unfold left_cycle; simpl.
      (* We have the same term! This has been checked with the [Substitution.v]
         library, which we will use here at some point. *)
      admit.
    - simpl in H4 |- *.
      (* As xs starts with a, move x after it. *)
      apply reducibility_exchange with (g := ts ++ a :: x :: xs ++ ys)
        (n := length ts) in H4.
      + (* I don't like the following line, but oh well... *)
        replace (ts ++ a :: x :: xs ++ ys) with
          ((ts ++ [a]) ++ x :: xs ++ ys) in H4 by now rewrite <- app_assoc.
        (* We can now keep moving x after the remaining of xs. *)
        apply IHxs in H4.
        * (* Undo the technical change. *)
          rewrite <- app_assoc in H4; simpl in H4.
          (* Ok, we have the same term. This has also been checked with the
             sigma tactic. Not sure I'm gonna have time to properly prove this
             lemma manually, but this is true. *)
          admit.
        * assumption.
        * dependent destruction H1.
          apply Forall_app; split; auto.
        * now dependent destruction H1.
        * assumption.
        * (* We have to rewrite a bit, but yeah, same number, we just moved some
             types around. *)
          rewrite <- app_assoc; simpl.
          rewrite sumup_app in H3 |- *.
          unfold sumup in H3 |- *; simpl in H3 |- *.
          lia.
      + apply IH.
        * dependent destruction H1.
          rewrite Forall_app; split; auto.
          constructor; auto.
          constructor; auto.
          now rewrite Forall_app.
        * rewrite sumup_app in H3 |- *.
          unfold sumup in H3 |- *; simpl in H3 |- *.
          lia.
      + dependent destruction H1.
        rewrite Forall_app; split; auto.
        constructor; auto.
        constructor; auto.
        now rewrite Forall_app.
      + replace (length ts) with (length ts + 0) by lia.
        apply switch_app.
        constructor.
  Admitted.

  Lemma L_lift_aux:
    forall ts xs ys e,
    valid_env ts ->
    valid_env xs ->
    valid_env ys ->
    sumup count (xs ++ ts ++ ys) < sumup count g ->
    L (xs ++ ys) e ->
    L (xs ++ ts ++ ys) (lift (length ts) (length xs) e).
  Proof.
    (* TODO: sigh, this lemma is too ugly... please, rewrite it once I have
       enough time to do it. *)
    intros; induction ts.
    - simpl.
      rewrite lift_zero_e_equals_e.
      assumption.
    - dependent destruction H.
      (* Of course this decreases, but still... *)
      assert (sumup count (xs ++ ts ++ ys) < sumup count g).
      + rewrite sumup_app in H3 |- *.
        unfold sumup in H3 |- *; simpl in H3 |- *.
        lia.
      + (* In the inductive case, we first add the new variable as the newest
           one, by using weakening. *)
        specialize (IHts H0 H5).
        apply reducibility_weakening with (t := a) (g := a :: xs ++ ts ++ ys)
          in IHts; simpl.
        * (* And we then proceed to move it to the right position by using our
             helper lemma above. *)
          rewrite lift_lift_permutation in IHts by lia.
          apply L_left_cycle_aux with (ts := []) in IHts; simpl in IHts.
          (* We keep moving the variable a little bit; our assumption already has
             the result. *)
          unfold left_cycle in IHts.
          rewrite lift_lift_simplification in IHts by lia.
          replace (S (length xs)) with (1 + length xs) in IHts by lia.
          rewrite <- lift_lift_permutation in IHts by lia.
          rewrite subst_lift_simplification in IHts by lia.
          rewrite lift_zero_e_equals_e in IHts.
          assumption.
          assumption.
          constructor.
          assumption.
          now apply Forall_app.
          simpl.
          rewrite sumup_cons.
          do 2 rewrite sumup_app in H3 |- *.
          unfold sumup in H3 |- *; simpl in H3 |- *.
          lia.
        * apply IH.
          constructor; auto.
          apply Forall_app; split; auto.
          apply Forall_app; split; auto.
          rewrite sumup_cons.
          do 2 rewrite sumup_app in H3 |- *.
          unfold sumup in H3 |- *; simpl in H3 |- *.
          lia.
        * constructor; auto.
          apply Forall_app; split; auto.
          apply Forall_app; split; auto.
        * constructor.
  Qed.

  Lemma L_exchange:
    valid_env g ->
    forall n h,
    switch n h g ->
    forall e,
    L h e ->
    L g (switch_bindings n e).
  Proof.
    (* For technical details, we need to remember the original value of g. *)
    remember g as g'.
    (* There we go; check where the switch happens. *)
    destruct 2; intros.
    (* Case: exchange happens at the start of the environment. *)
    - dependent destruction H.
      dependent destruction H0.
      destruct H; destruct H0.
      + do 2 rewrite L_sub_composition in H2 |- *.
        unfold SUB in H2 |- *; intros x y.
        apply L_preservation; auto; intros.
        specialize (H2 y x).
        specialize (H0 _ H2).
        admit.
      + rewrite L_arr_composition in H2.
        rewrite L_sub_composition in H2 |- *.
        rewrite L_arr_composition.
        unfold ARR, SUB in H2 |- *; intros.
        admit.
      + rewrite L_sub_composition in H2.
        rewrite L_arr_composition in H2 |- *.
        rewrite L_sub_composition.
        unfold ARR, SUB in H2 |- *; intros.
        admit.
      + rename ts0 into us.
        do 2 rewrite L_arr_composition in H2 |- *.
        unfold ARR in H2 |- *; intros c ? d ?.
        (* Steps we need to follow:

             1) By using weakening, H4 can have a (negation ts) added;
             2) By using our IH, we can move it after the us, so it'll fit as
                the first argument for H2 (we'll have us ++ negation ts :: xs);
             3) Now we can repeatedly add each of ts into H4 by weaneking;
             4) By using our IH, we can move these ts into the right in H4 (so
                we will have us ++ ts ++ xs);
             5) We have to change H3 by moving negation us into the left;
             6) By plugging H4 into H3, we get enough info for the second
                argument for H2;
             7) Since switch bindings is involutive, apply it twice on e in H2.

           If I did math correctly in my head, what's left is exactly with a
           (DISTR), which should preserve strong normalization!
        *)
        assert (L (us ++ negation ts :: xs) (lift 1 (length us) d) /\
                L (us ++ ts ++ xs) (lift (length ts) (length us) d) /\
                L (negation us :: ts ++ xs) (right_cycle (length ts) 0 c))
          as (?H, (?H, ?H)); repeat split.
        * (* TODO: refactor... *)
          rewrite Heqg' in IH.
          apply L_lift_aux with (ts := [negation ts]).
          now repeat constructor.
          assumption.
          assumption.
          rewrite <- Heqg'.
          rewrite sumup_app; simpl.
          do 3 rewrite sumup_cons.
          simpl; lia.
          assumption.
        * (* TODO: refactor... *)
          rewrite Heqg' in IH.
          apply L_lift_aux; auto.
          rewrite <- Heqg'.
          do 2 rewrite sumup_cons.
          do 2 rewrite sumup_app.
          simpl; lia.
        * (* TODO: refactor... *)
          rewrite Heqg' in IH.
          apply L_right_cycle_aux with (ts := []) (xs := ts) in H3.
          assumption.
          now repeat constructor.
          constructor.
          assumption.
          assumption.
          simpl; rewrite <- Heqg'.
          rewrite sumup_app.
          do 3 rewrite sumup_cons.
          simpl count.
          lia.
        * rewrite L_arr_composition in H7.
          unfold ARR in H7.
          specialize (H7 _ H6).
          specialize (H2 _ H5 _ H7).
          rewrite <- switch_bindings_is_involutive with (e := e) (k := 0) in H2.
          clear H3 H4 H5 H6 H7.
          (* Just as expected! Now, H2 is just a (DISTR) application from our
             goal. So our term preserves the strong normalization. *)
          apply L_preservation; auto; intros.
          apply H4 in H2; clear H4.
          admit.
    (* Case: there's an assumption before the exchanged types. *)
    - dependent destruction H.
      destruct H.
      + rewrite L_sub_composition in H2 |- *.
        unfold SUB in H2 |- *; intros.
        specialize (H2 (switch_bindings n x)).
        (* It may be a bit hard to spot, but all we have to do is to apply
           exchange to H2 now and we're done in here. *)
        apply reducibility_exchange with (n := n) (g := xs2) in H2; auto.
        (* Now, H2 holds our goal. We just have to tweak it a bit. *)
        rewrite switch_bindings_distributes_over_bind in H2.
        rewrite switch_bindings_distributes_over_jump in H2.
        unfold switch_bindings at 1 2 in H2; simpl in H2.
        rewrite lift_bound_lt in H2 by lia.
        rewrite subst_bound_lt in H2 by lia.
        replace (S (S (S n))) with (1 + (2 + n)) in H2 by lia.
        rewrite <- lift_lift_permutation in H2 by lia.
        replace (S n) with (1 + n) in H2 by lia.
        rewrite <- lift_and_subst_commute in H2 by lia.
        fold (switch_bindings n (switch_bindings n x)) in H2.
        rewrite switch_bindings_is_involutive in H2.
        replace (switch_bindings n base) with base in H2 by now compute.
        rewrite Nat.add_comm in H2.
        (* There we go! *)
        assumption.
      + rewrite L_arr_composition in H2 |- *.
        unfold ARR in H2 |- *; intros.
        (* We have to apply exchange in H3, so that we can use it as an argument
           to H2, then we will apply exchange again in H2, which will result in
           our goal (modulo some de Bruijn arithmetic gimmicks). *)
        apply reducibility_exchange with (n := (length ts + n)) (g := ts ++ xs1)
          in H3.
        * specialize (H2 _ H3).
          (* TODO: please, refactor me... *)
          apply reducibility_exchange with (n := n) (g := xs2) in H2.
          rewrite switch_bindings_distributes_over_bind in H2.
          rewrite Nat.add_comm in H2.
          rewrite switch_bindings_is_involutive in H2.
          (* TODO: there's something about this in [TypeSystem.v]... *)
          replace (traverse_list switch_bindings n ts) with ts in H2 by admit.
          assumption.
          apply IH.
          assumption.
          unfold sumup; simpl; lia.
          assumption.
          assumption.
        * (* TODO: refactor, please? *)
          apply IH.
          apply Forall_app; split.
          assumption.
          apply valid_env_switch_bindings with n xs2.
          assumption.
          assumption.
          rewrite sumup_app.
          rewrite count_switch with n xs1 xs2.
          unfold sumup; simpl.
          unfold sumup; lia.
          assumption.
        * (* TODO: refactor... *)
          apply Forall_app; split.
          assumption.
          apply valid_env_switch_bindings with n xs2.
          assumption.
          assumption.
        * apply switch_app.
          now apply switch_sym.
  Admitted.

  Lemma L_contraction:
    valid_env g ->
    forall h,
    join 0 h g ->
    forall e,
    L h e ->
    L g (subst 0 0 e).
  Proof.
    intros.
    dependent destruction H0.
    dependent destruction H.
    destruct H.
    (* Case: base type. *)
    - rewrite L_sub_composition.
      do 2 rewrite L_sub_composition in H1.
      unfold SUB in H1 |- *; intros.
      (* We can observe in here that the term from H1 will reduce to the term
         we want to prove is normalizing... namely, for some a and b:

         k<a> { k<x> = j<b> { j<y> = c } }   ~~~>   k<a> { k<x> = c[b/y] } *)
      apply L_preservation; auto; intros.
      (* TODO: check if we really want x in both here... *)
      specialize (H1 x x).
      apply H2 in H1; clear H2.
      apply SN_beta_and_SN_step_coincide in H1.
      admit.
    (* Case: negation type. *)
    - rewrite L_arr_composition in H1 |- *.
      rewrite L_arr_composition in H1.
      unfold ARR in H1 |- *; intros.
      admit.
  Admitted.

  Lemma L_is_normalizing:
    valid_env g ->
    forall e,
    L g e ->
    SN beta e.
  Proof.
    intros.
    destruct H; [| destruct H ].
    (* Case: empty context. *)
    - (* This follows intensionally from H0. *)
      assumption.
    (* Case: base type. *)
    - rewrite L_sub_composition in H0.
      unfold SUB in H0.
      (* We are free to pick any fresh variable in this one. *)
      specialize (H0 0).
      apply reducibility_normalization in H0.
      + set (b := (jump 0 [lift 1 0 0])).
        apply SN_preimage with (fun c => bind b [base] c); auto with cps.
      + apply IH; auto.
    (* Case: negation type. *)
    - rewrite L_arr_composition in H0.
      unfold ARR in H0.
      assert (exists c, L (ts ++ l) c) as (c, ?).
      + apply reducibility_nonempty.
        apply IH.
        * apply Forall_app; now split.
        * now apply count_arg.
      + specialize (H0 c H2).
        apply reducibility_normalization in H0.
        * apply SN_preimage with (fun b => bind b ts c); auto with cps.
        * apply IH; auto.
          unfold sumup; simpl; lia.
  Qed.

  Lemma L_is_nonempty:
    valid_env g ->
    exists c,
    L g c.
  Proof.
    intros.
    (* We're gonna use g but we need to use the L_weakening lemma above for it,
       so Coq requires us to keep it untouched. Let's do that by remembering its
       original value. *)
    remember g as g'.
    dependent destruction H.
    (* Case: empty context. *)
    - (* On the empty context, we merely want terms to halt. This means that in
         here there are no variables to which we may interact. So we just pick
         a random free variable and perform a jump to it. As the environment
         grows around it, we merely use alpha-equality to pick names such that
         these jumps won't interact. In the de Bruijn setting, this is of course
         done by lifting the "neutral" term. *)
      exists (jump 0 []).
      constructor; intros.
      inversion H.
    (* Case: at least one type. *)
    - assert (reducibility l L).
      + apply IH.
        * assumption.
        * unfold sumup.
          destruct H; simpl; lia.
      + edestruct reducibility_nonempty as (y, ?); eauto.
        (* We need to call weakening on the same size as we are currently using
           right now, which is fine as it only uses the existence of items on a
           smaller environment. So, as we changed the variable g in IH, we have
           to undo that work a bit first. *)
        rewrite Heqg' in IH.
        apply L_weakening with (t := x) in H2; subst.
        * now exists (lift 1 0 y).
        * now repeat constructor.
        * constructor.
  Qed.

End Reducibility.

Lemma L_is_reducible:
  forall g,
  valid_env g ->
  reducibility g L.
Proof.
  intro.
  remember (sumup count g) as n.
  generalize dependent g.
  induction n using lt_wf_ind.
  (* We just have to join together the lemmas defined above! *)
  split; subst; intros.
  - apply L_weakening with t h; auto; intros.
    rename h0 into i.
    now apply H with (m := sumup count i) (g := i).
  - apply L_exchange with h; auto; intros.
    rename h0 into i.
    now apply H with (m := sumup count i) (g := i).
  - apply L_contraction with h; auto; intros.
    rename h0 into i.
    now apply H with (m := sumup count i) (g := i).
  - apply L_is_normalizing with g; auto; intros.
    now apply H with (m := sumup count h) (g := h).
  - apply L_is_nonempty; auto; intros.
    now apply H with (m := sumup count h) (g := h).
Qed.

(* -------------------------------------------------------------------------- *)
(* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- *)
(* -------------------------------------------------------------------------- *)

Lemma SN_L:
  forall g,
  valid_env g ->
  forall c,
  L g c -> SN step c.
Proof.
  intros.
  apply SN_beta_and_SN_step_coincide.
  apply reducibility_normalization with g L.
  - now apply L_is_reducible.
  - assumption.
Qed.

Goal
  WEAKENING (fun g e => valid_env g -> L g e).
Proof.
  unfold WEAKENING; intros.
  apply reducibility_weakening with t g.
  - now apply L_is_reducible.
  - assumption.
  - constructor.
  - apply H.
    now dependent destruction H1.
Qed.

Goal
  EXCHANGE (fun g e => valid_env g -> L g e).
Proof.
  unfold EXCHANGE; intros.
  apply reducibility_exchange with g.
  - now apply L_is_reducible.
  - assumption.
  - assumption.
  - apply H.
    now apply valid_env_switch_bindings with n h.
Qed.

Goal
  CONTRACTION (fun g e => valid_env g -> L g e).
Proof.
  unfold CONTRACTION; intros.
  apply reducibility_contraction with (t :: t :: g).
  - now apply L_is_reducible.
  - assumption.
  - constructor.
  - apply H.
    dependent destruction H0.
    now repeat constructor.
Qed.

(*

Definition PRESERVES {T} (P: T -> Prop): relation T :=
  fun a b =>
    P a -> P b.

Definition REFLECTS {T} (P: T -> Prop): relation T :=
  fun a b =>
    P b -> P a.

*)

Lemma fundamental:
  forall e g,
  typing g e void -> L g e.
Proof.
  induction e; inversion_clear 1.
  (* Case: bound. *)
  - exfalso.
    (* Commands don't have types, but variables do. *)
    eapply typing_bound_cant_be_void.
    eauto with cps.
  (* Case: jump. *)
  - clear IHe.
    dependent destruction H0.
    apply L_preservation; auto; intros.
    (* The first step we need to do is to split the context h. As we know that
       it is well-behaved for g, our typing information that g |- n: ~ts says
       that we can split h into a context which defines the continuation at n
       with the appropriate type and some context that plays no part on reducing
       this continuation. *)
    destruct split_wellbehaved_context with g h n; eauto with cps; subst.
    (* The second half of our context contains the definition we want! *)
    apply item_ignore_head in H0; auto.
    replace (length g1 - length g1) with 0 in H0 by lia.
    dependent destruction H0.
    dependent destruction H6.
    rename h into h2, cdr into g2.
    do 2 setoid_rewrite compose_context_is_sound in H3; simpl in H3.
    do 2 rewrite compose_context_is_sound; simpl.
    rewrite H8.
    (* Now that we have a term c that is to be reduced, we can apply successive
       weakening and exchange rules on it to add (g1 ++ [negation ts]) to it's
       environment, making it valid on the same environment as our goal plus the
       parameters. *)
    admit.
  (* Case: bind. *)
  - (* Follows trivially by definition. *)
    specialize (IHe1 (negation ts :: g) H0).
    specialize (IHe2 (ts ++ g) H1).
    rewrite L_arr_composition in IHe1.
    apply IHe1.
    assumption.
Admitted.

Theorem strong_normalization:
  forall g e,
  typing g e void -> SN step e.
Proof.
  intros.
  apply SN_L with g.
  - now apply valid_env_typing with e void.
  - now apply fundamental.
Qed.

Corollary consistency:
  forall e,
  ~typing [] e void.
Proof.
  do 2 intro.
  assert (SN step e).
  - apply strong_normalization with [].
    assumption.
  - (* It is closed, so it can't be normalizable! *)
    induction H0 using SN_ind.
    destruct progress with ([]: list pseudoterm) x as [ (k, ?) | (y, ?) ]; auto.
    + (* Can't converge if it's closed, right? *)
      clear H0 H2.
      apply free_converges with x k.
      * assumption.
      * (* Of course! *)
        eapply not_free_typing; eauto with arith.
    + (* By progress, there's a step. *)
      apply H2 with y.
      * auto with cps.
      * apply subject_reduction with x; auto with cps.
Qed.
