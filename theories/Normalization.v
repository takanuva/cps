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

Lemma L_preservation:
  forall g,
  valid_env g ->
  forall c,
  (* Here, g generates a context, which is valid as g for any other term. *)
  (forall (h: context), (forall b, L g b -> SN beta (h b)) -> SN beta (h c)) ->
  L g c.
Proof.
  induction g; intros.
  - specialize (H0 context_hole); simpl in H0.
    apply H0; intros.
    assumption.
  - dependent destruction H.
    dependent destruction H.
    + rewrite L_sub_composition in H1 |- *.
      unfold SUB in H0 |- *; intros.
      eapply IHg; intros.
      * assumption.
      * replace (bind (jump 0 [lift 1 0 x]) [base] c) with
          (context_right (jump 0 [lift 1 0 x]) [base] context_hole c); auto.
        rewrite <- compose_context_is_sound.
        apply H1; intros.
        rewrite compose_context_is_sound; simpl.
        apply H.
        apply H2.
    + rewrite L_arr_composition in H1 |- *.
      unfold ARR in H1 |- *; intros d ?.
      eapply IHg; intros.
      * assumption.
      * replace (bind c ts d) with (context_left context_hole ts d c); auto.
        rewrite <- compose_context_is_sound.
        apply H1; intros.
        rewrite compose_context_is_sound; simpl.
        apply H3, H4.
        assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- *)
(* -------------------------------------------------------------------------- *)

Record reducibility (g: env) (R: env -> candidate): Prop := {
  reducibility_weakening:
    forall t,
    valid_env (t :: g) ->
    forall e,
    R g e ->
    R (t :: g) (lift 1 0 e);
  reducibility_exchange:
    valid_env g ->
    forall n h,
    switch n g h ->
    forall e,
    R g e ->
    R h (switch_bindings n e);
  reducibility_contraction:
    forall t,
    valid_env (t :: g) ->
    forall e,
    R (t :: t :: g) e ->
    R (t :: g) (subst 0 0 e);
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
    forall t,
    valid_env (t :: g) ->
    forall e,
    L g e ->
    L (t :: g) (lift 1 0 e).
  Proof.
    intros.
    dependent destruction H.
    dependent destruction H.
    (* Case: base type. *)
    - rewrite L_sub_composition.
      unfold SUB; intros.
      apply L_preservation; auto; intros.
      specialize (H e H1).
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

  Lemma L_exchange:
    valid_env g ->
    forall n h,
    switch n g h ->
    forall e,
    L g e ->
    L h (switch_bindings n e).
  Proof.
    destruct 2; intros.
    (* Case: exchange happens at the start of the beginning. *)
    - dependent destruction H.
      dependent destruction H0.
      destruct H; destruct H0.
      + do 2 rewrite L_sub_composition in H2 |- *.
        unfold SUB in H2 |- *; intros x y.
        apply L_preservation; auto; intros.
        specialize (H2 y x).
        specialize (H _ H2).
        admit.
      + rewrite L_sub_composition in H2.
        rewrite L_arr_composition in H2 |- *.
        rewrite L_sub_composition.
        unfold ARR, SUB in H2 |- *; intros.
        admit.
      + rewrite L_arr_composition in H2.
        rewrite L_sub_composition in H2 |- *.
        rewrite L_arr_composition.
        unfold ARR, SUB in H2 |- *; intros.
        admit.
      + rename ts0 into us.
        do 2 rewrite L_arr_composition in H2 |- *.
        unfold ARR in H2 |- *; intros c ? d ?.
        (* Steps we need to follow:

             1) By using weakening, H4 can have a (negation us) added;
             2) By using our IH, we can move it after the ts, so it'll fit as
                the first argument for H2 (we'll have ts ++ negation us :: xs);
             3) Now we can repeatedly add each of us into H4 by weaneking;
             4) By using our IH, we can move these us into the right in H4 (so
                we will have ts ++ us ++ xs);
             5) By plugging H4 into H3 (using IH to move negation ts left), we
                get enough info for the second argument for H2;
             6) Since switch bindings is involutive, apply it twice on e in H2.

           If I did math correctly in my head, what's left is exactly with a
           (DISTR), which should preserve strong normalization!
        *)
        admit.
    (* Case: there's an assumption before the exchanged types. *)
    - dependent destruction H.
      destruct H.
      + rewrite L_sub_composition in H2 |- *.
        unfold SUB in H2 |- *; intros.
        specialize (H2 (switch_bindings n x)).
        (* It may be a bit hard to spot, but all we have to do is to apply
           exchange to H2 now and we're done in here. *)
        apply reducibility_exchange with (n := n) (h := xs2) in H2.
        * (* Now, H2 is our goal. We just have to tweak it a bit. *)
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
          (* There we go. *)
          assumption.
        * apply IH; auto.
        * assumption.
        * assumption.
      + rewrite L_arr_composition in H2 |- *.
        unfold ARR in H2 |- *; intros.
        (* We have to apply exchange in H3, so that we can use it as an argument
           to H2, then we will apply exchange again in H2, which will result in
           our goal (modulo some de Bruijn arithmetic gimmicks). *)
        apply reducibility_exchange with (n := (length ts + n)) (h := ts ++ xs1)
          in H3.
        * specialize (H2 _ H3).
          (* TODO: please, refactor me... *)
          apply reducibility_exchange with (n := n) (h := xs2) in H2.
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
          apply valid_env_switch_bindings with n xs1.
          now apply switch_sym.
          assumption.
          rewrite sumup_app.
          rewrite count_switch with n xs2 xs1.
          unfold sumup; simpl.
          unfold sumup; lia.
          now apply switch_sym.
        * (* TODO: refactor... *)
          apply Forall_app; split.
          assumption.
          apply valid_env_switch_bindings with n xs1.
          now apply switch_sym.
          assumption.
        * apply switch_app.
          now apply switch_sym.
  Admitted.

  Lemma L_contraction:
    forall t,
    valid_env (t :: g) ->
    forall e,
    L (t :: t :: g) e ->
    L (t :: g) (subst 0 0 e).
  Proof.
    intros.
    dependent destruction H.
    destruct H.
    (* Case: base type. *)
    - rewrite L_sub_composition in H1 |- *.
      rewrite L_sub_composition in H1.
      unfold SUB in H1 |- *; intros.
      (* We can observe in here that the term from H1 will reduce to the term
         we want to prove is normalizing... namely, for some a and b:

         k<a> { k<x> = j<b> { j<y> = c } }   ~~~>   k<a> { k<x> = c[b/y] } *)
      apply L_preservation; auto; intros.
      (* TODO: check if we really want x in both here... *)
      specialize (H1 x x).
      specialize (H _ H1).
      apply SN_beta_and_SN_step_coincide in H.
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
        apply reducibility_weakening with (t := x) in H2.
        * now exists (lift 1 0 y).
        * assumption.
        * now repeat constructor.
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
  split; subst; intros.
  - apply L_weakening; intros.
    + now apply H with (m := sumup count h) (g := h).
    + assumption.
    + assumption.
  - apply L_exchange with g; intros.
    + rename h0 into i.
      now apply H with (m := sumup count i) (g := i).
    + assumption.
    + assumption.
    + assumption.
  - apply L_contraction; intros.
    + now apply H with (m := sumup count h) (g := h).
    + assumption.
    + assumption.
  - apply L_is_normalizing with g; intros.
    + now apply H with (m := sumup count h) (g := h).
    + assumption.
    + assumption.
  - apply L_is_nonempty; intros.
    + now apply H with (m := sumup count h) (g := h).
    + assumption.
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
