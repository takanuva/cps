(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
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
Require Import Local.Axiomatic.
Require Import Local.Reduction.
Require Import Local.TypeSystem.

(** ** Normalization. *)

(* TODO: this is clearly true, but please prove it on the right place. *)

Hypothesis beta_is_dec:
  forall b, { exists c, beta b c } + { ~exists c, beta b c }.

Lemma backwards_SN_preservation:
  forall c,
  SN beta c ->
  forall b,
  beta b c -> SN beta b.
Proof.
  (* Yoshida's paper mentions this property, which should indeed be the case as
     jump reduction is nonerasing, but this is probably more complicated than in
     Church's proof because it's not enough here because terms interact with
     their contexts, so I think that reasoning about the inability to remove
     misbehaving terms might not be enough. Also, I believe the proof would be
     classical as well. I think we could potentially prove this by a simulation
     game. The jump that exists in b cannot be erased, so eventually it will
     have to be done and thus we will conclude by the hypothesis. Gotta think
     about this for a bit... *)
  admit.
Admitted.

Theorem uniform_normalization:
  forall b,
  WN beta b <-> SN beta b.
Proof.
  split; intros.
  - destruct H as (c, ?, ?).
    apply clos_rt_rt1n_iff in H.
    induction H.
    + constructor; intros.
      unfold transp in H.
      exfalso.
      apply H0 with y.
      assumption.
    + apply backwards_SN_preservation with y; auto.
  - induction H.
    clear H; unfold transp in H0.
    destruct beta_is_dec with x.
    + destruct e as (y, ?).
      edestruct H0 as (z, ?, ?); eauto.
      exists z; eauto with cps.
    + exists x; auto with cps.
      intros y ?; eapply n.
      exists y; auto.
Qed.

Corollary normalization_characterization:
  forall b,
  WN beta b <-> SN step b.
Proof.
  (* This should follow by postponing GC. *)
  admit.
Admitted.

(* -------------------------------------------------------------------------- *)

Lemma SN_unlift:
  forall i k e,
  SN step (lift i k e) -> SN step e.
Proof.
  intros.
  apply SN_preimage with (lift i k); intros.
  - apply step_lift; auto.
  - assumption.
Qed.

Lemma SN_unsubst:
  forall y k e,
  SN step (subst y k e) -> SN step e.
Proof.
  intros.
  apply SN_preimage with (subst y k); intros.
  - apply step_subst; auto.
  - assumption.
Qed.

Lemma SN_bind_left:
  forall b ts c,
  SN step (bind b ts c) -> SN step b.
Proof.
  intros.
  apply SN_preimage with (fun b => bind b ts c); auto with cps.
Qed.

Lemma SN_bind_right:
  forall b ts c,
  SN step (bind b ts c) -> SN step c.
Proof.
  intros.
  apply SN_preimage with (fun c => bind b ts c); auto with cps.
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

(*

(* A neutral term should not trigger a reduction interacting with its context.
   So, e.g., in the lambda calculus, they are neither abstractions, which would
   trigger a reduction with ([] x), nor <a, b>, which would trigger a reduction
   with (pi1 []) or (pi2 []). Since the CPS calculus "works at a distance", we
   need something that DOESN'T jump to a set of variables. Luckly, as we're only
   dealing with static contexts, they appear in a row, and so this will work in
   a de Bruijn setting. *)
Inductive neutral: nat -> nat -> pseudoterm -> Prop :=
  | neutral_jump:
    forall k n f xs,
    f < k \/ f >= k + n ->
    neutral k n (jump f xs)
  | neutral_bind:
    forall k n b ts c,
    neutral (S k) n b ->
    neutral (k + length ts) n c ->
    neutral k n (bind b ts c).

Lemma neutral_weaken:
  forall e p k n,
  neutral p (k + n) e -> neutral (p + k) n e.
Proof.
  intros.
  dependent induction H.
  - constructor.
    lia.
  - rename k0 into p.
    constructor; auto.
    + apply IHneutral1; auto.
    + replace (p + k + length ts) with (p + length ts + k); try lia.
      apply IHneutral2; auto.
Qed.

Lemma neutral_context_invalid:
  forall (h: context) k n xs,
  n > 0 ->
  ~neutral k n (h (jump (k + #h) xs)).
Proof.
  induction h; intros.
  - simpl; intro.
    dependent destruction H0.
    lia.
  - simpl; intro.
    dependent destruction H0.
    eapply IHh with (n := n) (k := S k); auto.
    replace (S k + #h) with (k + S #h); try lia.
    eassumption.
  - simpl; intro.
    dependent destruction H0.
    eapply IHh with (n := n) (k := k + length ts); auto.
    replace (k + length ts + #h) with (k + (#h + length ts)); try lia.
    eassumption.
Qed.

*)

Definition candidate: Type :=
  pseudoterm -> Prop.

Definition ARR ts (U V: candidate): candidate :=
  fun b =>
    forall c,
    U c -> V (bind b ts c).

Definition SUB (V: candidate): candidate :=
  fun b =>
    forall x,
    (* TODO: See below: perhaps k<x> { k<y> = c } is better! *)
    V (subst x 0 b).

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
        SN step
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

(* Lemma L_ind:
  forall P: env -> pseudoterm -> Prop,
  forall f1: (forall g e, SN step e -> P g e),
  forall f2: (forall g e,
              (forall x, P g (subst x 0 e)) ->
              P (base :: g) e),
  forall f3: (forall g b ts,
              (forall c, L (ts ++ g) c ->
               P (ts ++ g) c /\ P g (bind b ts c)) ->
              P (negation ts :: g) b),
  forall g e, L g e -> P g e.
Proof.
  intros until g.
  remember (sumup count g) as k.
  generalize dependent g.
  induction k using lt_wf_ind; intros.
  destruct g; intros.
  - apply f1.
    exact H0.
  - destruct p.
    + destruct H0.
    + destruct H0.
    + rewrite L_sub_composition in H0.
      unfold SUB in H0.
      apply f2; intros.
      apply H with (sumup count g); auto.
      rewrite Heqk.
      apply count_sub; auto.
    + destruct H0.
    + destruct H0.
    + rewrite L_arr_composition in H0.
      unfold ARR in H0.
      apply f3; intros.
      split.
      * apply H with (sumup count (ts ++ g)); auto.
        rewrite Heqk; apply count_arg; auto.
      * apply H with (sumup count g); auto.
        rewrite Heqk; eapply count_ret; eauto.
    + destruct H0.
    + destruct H0.
Qed. *)

(*

Record reducible g (P: candidate): Prop := {
  cr1:
    forall e,
    P e -> SN step e;
  cr2:
    forall a b,
    P a -> [a => b] -> P b;
  cr3:
    forall a,
    (* Since the CPS calculus seems to be non-erasing, do we really need to
       restrict ourselves to neutral terms here...? *)
    neutral 0 g a -> (forall b, [a => b] -> P b) -> P a
}.

Lemma cr2_star:
  forall g P,
  reducible g P ->
  forall a b,
  P a -> [a =>* b] -> P b.
Proof.
  induction 3.
  - apply cr2 with g x; auto.
  - assumption.
  - auto.
Qed.

Lemma cr4:
  forall g P,
  reducible g P ->
  forall e,
  normal step e -> neutral 0 g e -> P e.
Proof.
  intros.
  apply cr3 with g; intros.
  - assumption.
  - assumption.
  - exfalso.
    firstorder.
Qed.

Lemma reducible_SN:
  forall g,
  reducible g (SN step).
Proof.
  constructor; intros.
  - assumption.
  - apply H.
    assumption.
  - constructor.
    assumption.
Qed.

Definition free_jump (ts g: env): pseudoterm :=
  jump (length ts + length g) (low_sequence (length ts)).

Lemma reducible_isnt_empty:
  forall R ts g,
  reducible (length ts) R ->
  exists2 c,
  R c & cool ts g c.
Proof.
  intros.
  exists (free_jump ts g).
  - apply cr4 with (length ts).
    + assumption.
    + do 2 intro.
      inversion H0.
    + constructor.
      lia.
  - split.
    + do 2 intro.
      inversion H0.
    + constructor.
      lia.
Qed.

Lemma reducible_ARR:
  forall g ts,
  reducible (length g) (L g) ->
  reducible (length ts) (L ts) ->
  reducible (length (negation ts :: g)) (L (negation ts :: g)).
Proof.
  constructor; intros.
  - rewrite L_composition in H1.
    unfold ARR in H1.
    destruct reducible_isnt_empty with (L ts) ts g as (c, ?, ?); auto.
    (* As in the lambda calculus... but instead of a variable, a free jump. *)
    apply SN_bind_left with ts c.
    apply cr1 with (length g) (L g); auto.
  - rewrite L_composition in H1 |- *.
    unfold ARR in H1 |- *; intros.
    apply cr2 with (length g) (bind a ts c); auto.
    auto with cps.
  - rewrite L_composition in H2 |- *.
    unfold ARR in H2 |- *; intros.
    destruct H3 as ((?, ?), ?).
    (* No need to do induction over SN step c as in the lambda calculus: it's
       already cool down in normal form! *)
    apply cr3 with (length g); intros.
    + assumption.
    + (* NOW this seems correct to me! Check H1 and H4... *)
      constructor; auto.
      apply neutral_weaken with (p := 0); auto.
    + dependent destruction H6.
      * (* It is neutral, so we CAN'T have a redex here! *)
        exfalso.
        eapply neutral_context_invalid with
          (k := 0) (n := S (length g)) (h := h); try lia.
        eassumption.
      * apply H2; firstorder.
      * (* In the lambda calculus we'd use cr2 here. *)
        exfalso.
        firstorder.
Qed.

Lemma reducible_L:
  forall g,
  reducible (length g) (L g).
Proof.
  intros.
  induction sumup_count_is_well_founded with g.
  clear H; rename H0 into H; unfold ltof in H.
  (* Ok, start wordering about the type... *)
  destruct x; try exact reducible_SN.
  - admit.
  - destruct p; try exact reducible_SN.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + (* "Arrow types", in a way... *)
      eapply reducible_ARR.
      * apply H.
        eapply count_ret; eauto.
      * apply H.
        eapply count_arg; eauto.
    + admit.
    + admit.
Admitted.

Lemma SN_L:
  forall g e,
  L g e -> SN step e.
Proof.
  intros.
  apply cr1 with (length g) (L g); auto.
  apply reducible_L.
Qed.
*)

Goal
  forall A B C,
  let g :=
    [negation A; base; negation B; negation C]
  in L g void.
Proof.
  (* Lets see how things unfold... *)
  intros.
  unfold g.
  rewrite L_arr_composition.
  unfold ARR; intros.
  rewrite L_sub_composition.
  unfold SUB; intros.
  rewrite L_arr_composition.
  unfold ARR; intros.
  rewrite L_arr_composition; intros.
  unfold ARR; intros.
  rename c into a, c0 into b, c1 into c.
  unfold L.
  rewrite Fix_eq.
  - admit.
  - admit.
Admitted.

Lemma SN_L:
  forall g c,
  L g c -> SN step c.
Proof.
  (* Showing that L implies strong normalization seems to be harder than it is
     in the lambda calculus, as expected; perhaps we'll need a different set of
     conditions than the ones used in it. TODO: consider doing what was done in
     Yoshida's paper, as working with terms in normal form may be easier. *)
  admit.
Admitted.

Goal
  forall x c,
  (* Hmm... could this be a better definition? *)
  [bind (jump 0 [lift 1 0 x]) [void] c == subst x 0 c].
Proof.
  intros.
  etransitivity.
  apply sema_recjmp.
  reflexivity.
  simpl.
  rewrite <- lift_distributes_over_subst.
  etransitivity.
  apply sema_gc.
  apply lifting_more_than_n_makes_not_free_n; lia.
  unfold remove_binding.
  rewrite subst_lift_simplification; try lia.
  rewrite lift_zero_e_equals_e.
  reflexivity.
Qed.

Inductive exchange {T}: nat -> relation (list T) :=
  | exchange_head:
    forall x1 x2 xs,
    exchange 0 (x1 :: x2 :: xs) (x2 :: x1 :: xs)
  | exchange_tail:
    forall k x xs1 xs2,
    exchange k xs1 xs2 -> exchange (S k) (x :: xs1) (x :: xs2).

Lemma exchange_sym:
  forall {T} n g h,
  @exchange T n g h -> @exchange T n h g.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma exchange_app:
  forall {T} n g h i,
  @exchange T n h i -> @exchange T (length g + n) (g ++ h) (g ++ i).
Proof.
  induction g; simpl; intros.
  - assumption.
  - constructor; auto.
Qed.

Lemma exchange_preserve_sumup:
  forall {T} f n g h,
  @exchange T n g h ->
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
  - dependent destruction H.
    dependent destruction H.
    + constructor.
    + constructor.
    + exfalso.
      eapply typing_bound_cant_be_prop.
      eauto with cps.
  - dependent destruction H0.
    dependent destruction H0.
    + constructor.
    + constructor.
    + exfalso.
      eapply typing_bound_cant_be_prop.
      eauto with cps.
  - exfalso.
    eapply typing_bound_cant_be_prop.
    eauto with cps.
Qed.

Lemma L_weakening:
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
    rewrite subst_lift_simplification; try lia.
    rewrite lift_zero_e_equals_e; auto.
  - rewrite L_arr_composition.
    unfold ARR; intros.
    admit.
  - exfalso.
    eapply typing_bound_cant_be_prop.
    eauto with cps.
Admitted.

Lemma L_distr:
  forall g,
  valid_env g -> DISTR (fun a b =>
    L g b -> L g a).
Proof.
  unfold DISTR; intros.
  (* This will be a nightmare in the de Bruijn setting. *)
  admit.
Admitted.

Lemma L_exchange:
  forall g n h,
  exchange n g h ->
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
      * eauto with cps.
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
    + rewrite L_sub_composition in H2 |- *.
      unfold SUB in H2 |- *; intros.
      replace (S k0) with (0 + S k0); auto.
      rewrite hmmm.
      apply H with (sumup count g) g.
      * apply count_sub.
        reflexivity.
      * reflexivity.
      * assumption.
      * assumption.
      * apply H2.
    + rename k0 into p.
      rewrite L_arr_composition in H3 |- *.
      unfold ARR in H3 |- *; intros.
      rewrite <- switch_bindings_is_involutive with (k := p).
      eapply H with (sumup count g) g.
      * eapply count_ret.
        reflexivity.
      * reflexivity.
      * assumption.
      * assumption.
      * rewrite switch_bindings_distributes_over_bind.
        (* It appears we'd need a limiting on the dependent case! Or rather, we
           should simply ignore types here, making L a set of untyped terms. *)
        replace (traverse_list switch_bindings p ts) with ts.
        rewrite switch_bindings_is_involutive.
        apply H3.
        eapply H with (sumup count (ts ++ g)) (ts ++ xs2).
        apply count_arg.
        reflexivity.
        eapply exchange_preserve_sumup.
        apply exchange_app.
        eassumption.
        rewrite Nat.add_comm.
        apply exchange_app.
        apply exchange_sym.
        assumption.
        (* Derive from H1 and H2. *)
        admit.
        assumption.
        (* We have simple types. *)
        admit.
    + exfalso.
      eapply typing_bound_cant_be_prop.
      eauto with cps.
Admitted.

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
    (* Follows from the structural rules on semantic types! But this will be so
       much painful to prove with de Bruijn indexes... *)
    admit.
  (* Case: bind. *)
  - (* Follows trivially by definition. *)
    specialize (IHe1 (negation ts :: g) H0).
    specialize (IHe2 (ts ++ g) H2).
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
  apply fundamental.
  assumption.
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
