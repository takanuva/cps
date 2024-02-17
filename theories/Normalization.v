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
Require Import Local.TypeSystem.
Require Import Local.Conservation.
Require Import Local.Structural.
Require Import Local.Shrinking.

(** ** Normalization. *)

(* Lemma SN_bind_left:
  forall b ts c,
  SN beta (bind b ts c) -> SN beta b.
Proof.
  intros.
  apply SN_preimage with (fun b => bind b ts c); auto with cps.
Qed.

Lemma SN_bind_right:
  forall b ts c,
  SN beta (bind b ts c) -> SN beta c.
Proof.
  intros.
  apply SN_preimage with (fun c => bind b ts c); auto with cps.
Qed. *)

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

Local Notation candidate :=
  (pseudoterm -> Prop).

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

Inductive reducibility (g: env) (R: env -> candidate): Prop := {
  reducibility_weakening:
    forall e,
    R g e ->
    forall t,
    valid_env (t :: g) ->
    R (t :: g) (lift 1 0 e);
  (* reducibility_exchange:
    EXCHANGE R;
  reducibility_contraction:
    CONTRACTION R; *)
  reducibility_normalization:
    forall c,
    R g c -> SN beta c;
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

  Hypothesis H:
    forall h,
    valid_env h ->
    sumup count h < sumup count g ->
    reducibility h L.

  Lemma L_weakening:
    forall e,
    L g e ->
    forall t,
    valid_env (t :: g) ->
    L (t :: g) (lift 1 0 e).
  Proof.
    intros.
    dependent destruction H1.
    dependent destruction H1.
    - rewrite L_sub_composition.
      unfold SUB; intros.
      apply L_preservation; auto; intros.
      specialize (H1 e H0).
      eapply sn_beta_backwards_step.
      + apply beta_context.
        apply beta_ctxjmp with (h := context_hole).
        reflexivity.
      + simpl.
        rewrite lift_lift_simplification by lia.
        rewrite subst_lift_simplification by lia.
        admit.
    - rewrite L_arr_composition.
      unfold ARR; intros.
      apply L_preservation; auto; intros.
      admit.
  Admitted.

  Lemma L_is_normalizing:
    forall e,
    L g e ->
    SN beta e.
  Proof.
    admit.
  Admitted.

  Lemma L_is_nonempty:
    valid_env g ->
    exists c,
    L g c.
  Proof.
    intros.
    dependent destruction H0.
    (* Case: empty context. *)
    - (* On the empty context, we merely want terms to halt. This means that in
         here there are no variables to which we may interact. So we just pick
         a random free variable and perform a jump to it. As the environment
         grows around it, we merely use alpha-equality to pick names such that
         these jumps won't interact. In the de Bruijn setting, this is of course
         done by lifting the "neutral" term. *)
      exists (jump 0 []).
      constructor; intros.
      inversion H0.
    (* Case: at least one type. *)
    - assert (reducibility l L).
      + apply H.
        * assumption.
        * unfold sumup.
          destruct H0; simpl; lia.
      + clear H.
        edestruct reducibility_nonempty as (y, ?); eauto.
        apply reducibility_weakening with (t := x) in H.
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
  - apply L_is_normalizing with g; intros.
    + now apply H with (m := sumup count h) (g := h).
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
  apply SN_subset with (union beta smol).
  - apply step_characterization.
  - apply shrinking_preserves_strong_normalization.
    + exact smol_is_shrinking.
    + apply reducibility_normalization with g L.
      * now apply L_is_reducible.
      * assumption.
Qed.

Lemma switch_preserve_sumup:
  forall {T} f n g h,
  @switch T n g h ->
  sumup f g = sumup f h.
Proof.
  induction 1; intros.
  - do 4 rewrite sumup_cons.
    lia.
  - do 2 rewrite sumup_cons.
    lia.
Qed.

Ltac do_stuff :=
  simpl;
  try (rewrite lift_bound_ge; [| lia ]);
  simpl;
  try (rewrite lift_bound_lt; [| lia ]);
  simpl;
  try (rewrite subst_bound_gt; [| lia ]);
  simpl;
  try (rewrite subst_bound_eq; [| lia ]);
  simpl;
  try (rewrite subst_bound_lt; [| lia ]);
  simpl;
  try rewrite lift_zero_e_equals_e;
  simpl.

Lemma hmmm:
  forall e x k p,
  subst x k (switch_bindings (k + S p) e) =
    switch_bindings (k + p) (subst (switch_bindings p x) k e).
Proof.
  induction e using pseudoterm_deepind; intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - unfold switch_bindings.
    destruct (lt_eq_lt_dec (2 + k + p) n) as [ [ ? | ? ] | ? ];
    destruct (lt_eq_lt_dec (k + p) n) as [ [ ? | ? ] | ? ];
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ];
    try lia;
    repeat do_stuff; auto.
    f_equal; lia.
    + admit.
    + admit.
  - admit.
  - admit.
  - rewrite switch_bindings_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    rewrite switch_bindings_distributes_over_bind.
    f_equal.
    + replace (S (k + S p)) with (S k + S p); try lia.
      replace (S (k + p)) with (S k + p); try lia.
      apply IHe1.
    + admit.
    + do 2 rewrite traverse_list_length; simpl.
      replace (k + S p + length ts) with (k + length ts + S p); try lia.
      replace (k + p + length ts) with (k + length ts + p); try lia.
      apply IHe2.
Admitted.

Inductive foobar_inv_case: relation pseudoterm :=
  | foobar_inv_case1:
    foobar_inv_case base base
  | foobar_inv_case2:
    forall ts,
    foobar_inv_case (negation ts) base
  | foobar_inv_case3:
    forall ts,
    foobar_inv_case base (negation ts)
  | foobar_inv_case4:
    forall ts1 ts2,
    foobar_inv_case (negation ts2) (negation ts1).

Lemma foobar_inv:
  forall x1 x2 g,
  valid_env (x1 :: x2 :: g) -> foobar_inv_case x1 x2.
Proof.
  intros.
  dependent destruction H.
  dependent destruction H.
  - dependent destruction H0.
    dependent destruction H.
    + constructor.
    + constructor.
  - dependent destruction H0.
    dependent destruction H0.
    + constructor.
    + constructor.
Qed.

(* Lemma L_weakening:
  forall g e,
  L g e ->
  forall t,
  valid_env (t :: g) ->
  L (t :: g) (lift 1 0 e).
Proof.
  intros.
  dependent destruction H0.
  dependent destruction H0.
  - rewrite L_sub_composition.
    unfold SUB; intros.
    apply L_preservation; auto; intros.
    (* This reduces to (h e), so follows from H and H1. *)
    admit.
  - rewrite L_arr_composition.
    unfold ARR; intros.
    apply L_preservation; auto; intros.
    (* Follows from orthogonality for e and c. *)
    admit.
Admitted. *)

Definition PRESERVES {T} (P: T -> Prop): relation T :=
  fun a b =>
    P a -> P b.

Definition REFLECTS {T} (P: T -> Prop): relation T :=
  fun a b =>
    P b -> P a.

Lemma L_distr:
  forall g,
  valid_env g -> DISTR (REFLECTS (L g)).
Proof.
  unfold DISTR, REFLECTS; intros.
  (* This will be a nightmare in the de Bruijn setting. *)
  apply L_preservation; auto; intros.
  apply H2 in H1.
  (* Should follow! *)
  admit.
Admitted.

Lemma L_exchange:
  forall g n h,
  switch n g h ->
  valid_env g ->
  forall e,
  L g e -> L h (switch_bindings n e).
Proof.
  intros g.
  remember (sumup count g) as k.
  generalize dependent g.
  induction k using lt_wf_ind.
  destruct 2; intros.
  - dependent destruction Heqk.
    destruct foobar_inv with x1 x2 xs; auto.
    + do 2 rewrite L_sub_composition in H1 |- *.
      unfold SUB in H1 |- *; intros x y.
      apply L_preservation; intros.
      * dependent destruction H0.
        dependent destruction H1.
        assumption.
      * specialize (H1 y x).
        apply H2 in H1.
        (* Follows from H1! *)
        admit.
    + rewrite L_arr_composition in H1.
      rewrite L_sub_composition in H1 |- *.
      rewrite L_arr_composition.
      unfold ARR, SUB in H1 |- *; intros.
      admit.
    + rewrite L_sub_composition in H1.
      rewrite L_arr_composition in H1 |- *.
      rewrite L_sub_composition.
      unfold ARR, SUB in H1 |- *; intros.
      admit.
    + do 2 rewrite L_arr_composition in H1 |- *.
      unfold ARR in H1 |- *; intros c1 ?H c2 ?H.
      (* Steps we need to follow:
           1) By using weakening, H3 can have a negation ts1 added;
           2) By using our IH, we can move it after the ts2, so it'll fit as the
              first argument for H1 (we'll have ts2 ++ negation ts1 ++ xs);
           3) Now we can repeatedly add each of ts1 into H3 by weaneking;
           4) By using our IH, we can move these t1 into the right in H3 (so we
              will have ts2 ++ ts1 ++ xs);
           5) By plugging H3 into H2 (using IH to move negation ts2 right), we
              get enough info for the second argument for H1;
           6) Since switch bindings is involutive, apply it twice on e in H1!

         If I did math correctly in my head, we're left exactly with a (DISTR)!
      *)
      apply L_distr.
      * dependent destruction H0.
        dependent destruction H1.
        assumption.
      * (* Clearly, we have simple types... *)
        admit.
      * rewrite switch_bindings_is_involutive.
        replace (traverse_list (lift 1) 0 ts2) with ts2.
        replace (traverse_list remove_binding 0 ts1) with ts1.
        replace (traverse_list (lift (length ts1)) 0 ts2) with ts2.
        apply H1.
        --- admit.
        --- admit.
        --- admit.
        --- admit.
        --- admit.
  - dependent destruction H1.
    assert (valid_env xs1); eauto with cps.
    dependent destruction Heqk.
    dependent destruction H1.
    + rewrite L_sub_composition in H3 |- *.
      unfold SUB in H3 |- *; intros.
      admit.
    + rewrite L_arr_composition in H3 |- *.
      unfold ARR in H3 |- *; intros.
      rewrite <- switch_bindings_is_involutive with (k := n).
      eapply H with (sumup count xs1) xs1.
      * eapply count_ret.
        reflexivity.
      * reflexivity.
      * assumption.
      * assumption.
      * rewrite switch_bindings_distributes_over_bind.
        (* It appears we'd need a limiting on the dependent case! Or rather, we
           should simply ignore types here, making L a set of untyped terms. *)
        replace (traverse_list switch_bindings n ts) with ts.
        rewrite switch_bindings_is_involutive.
        apply H3.
        eapply H with (sumup count (ts ++ xs1)) (ts ++ xs2).
        apply count_arg.
        reflexivity.
        eapply switch_preserve_sumup.
        apply switch_app.
        eassumption.
        rewrite Nat.add_comm.
        apply switch_app.
        apply switch_sym.
        assumption.
        (* Derive from H1 and H2. *)
        admit.
        assumption.
        (* We have simple types. *)
        admit.
Admitted.

Lemma L_contraction:
  forall t g,
  valid_env (t :: g) ->
  forall e,
  L (t :: t :: g) e -> L (t :: g) (subst 0 0 e).
Proof.
  intros.
  dependent destruction H.
  dependent destruction H.
  - rewrite L_sub_composition in H1; unfold SUB in H0; simpl in H0.
    rewrite L_sub_composition in H1; unfold SUB in H0; simpl in H0.
    rewrite L_sub_composition; unfold SUB; simpl; intros.
    (*  k<a> { k<x> = j<b> { j<y> = c } }  --->
        k<a> { k<x> = c[b/y] } *)
    admit.
  - rewrite L_arr_composition; unfold ARR; simpl; intros.
    admit.
Admitted.

(* Record reducible (P: candidate): Prop := {
  cr1:
    forall e,
    P e -> SN beta e;
  cr3:
    exists e,
    P e
}.

Lemma SN_is_reducible:
  reducible (SN beta).
Proof.
  split; intros.
  - assumption.
  - exists (jump 0 []).
    constructor; inversion 1.
Qed.

Lemma ARR_is_reducible:
  forall g ts,
  reducible (L g) ->
  reducible (L (ts ++ g)) ->
  reducible (L (negation ts :: g)).
Proof.
  split; intros.
  - rewrite L_arr_composition in H1.
    unfold ARR in H1; simpl in H1.
    assert (exists c, L (ts ++ g) c) as (c, ?).
    + apply cr3.
      assumption.
    + specialize (H1 c H2); clear H2.
      eapply cr1 in H1.
      * apply SN_bind_left with ts c.
        assumption.
      * eassumption.
  - rewrite L_arr_composition; unfold ARR; simpl.
    destruct cr3 with (L g) as (b, ?); auto.
    exists (lift 1 0 b); intros.
    apply L_weakening with (t := negation ts) in H1.
    + rewrite L_arr_composition in H1.
      unfold ARR in H1; simpl in H1.
      apply H1.
      assumption.
    + admit.
Admitted.

Lemma SUB_is_reducible:
  forall g,
  reducible (L g) ->
  reducible (L (base :: g)).
Proof.
  split; intros.
  - rewrite L_sub_composition in H0.
    unfold SUB in H0; simpl in H0.
    specialize (H0 0).
    apply cr1 in H0.
    + eapply SN_bind_right.
      eassumption.
    + assumption.
  - destruct cr3 with (L g) as (b, ?); auto.
    apply L_weakening with (t := base) in H0.
    + exists (lift 1 0 b).
      assumption.
    + admit.
Admitted.

Lemma L_is_reducible:
  forall g,
  reducible (L g).
Proof.
  induction g.
  - apply SN_is_reducible.
  - destruct a.
    + admit.
    + admit.
    + apply SUB_is_reducible.
      assumption.
    + admit.
    + admit.
    + apply ARR_is_reducible.
      * assumption.
      * admit.
    + admit.
    + admit.
Admitted. *)

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
    admit.
Admitted.
