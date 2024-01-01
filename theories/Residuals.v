(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.

(** ** Residuals *)

Inductive redexes: Set :=
  | redexes_type
  | redexes_prop
  | redexes_base
  | redexes_void
  | redexes_bound (n: nat)
  | redexes_negation (ts: list pseudoterm)
  | redexes_jump (r: bool) (f: pseudoterm) (xs: list pseudoterm)
  | redexes_bind (b: redexes) (ts: list pseudoterm) (c: redexes).

Fixpoint mark (e: pseudoterm): redexes :=
  match e with
  | type =>
    redexes_type
  | prop =>
    redexes_prop
  | base =>
    redexes_base
  | void =>
    redexes_void
  | bound n =>
    redexes_bound n
  | negation ts =>
    redexes_negation ts
  | jump f xs =>
    redexes_jump false f xs
  | bind b ts c =>
    redexes_bind (mark b) ts (mark c)
  end.

Fixpoint unmark (e: redexes): pseudoterm :=
  match e with
  | redexes_type =>
    type
  | redexes_prop =>
    prop
  | redexes_base =>
    base
  | redexes_void =>
    void
  | redexes_bound n =>
    n
  | redexes_negation ts =>
    negation ts
  | redexes_jump r f xs =>
    jump f xs
  | redexes_bind b ts c =>
    bind (unmark b) ts (unmark c)
  end.

Lemma unmark_mark_is_sound:
  forall e,
  unmark (mark e) = e.
Proof.
  induction e; simpl; auto.
  rewrite IHe1, IHe2; auto.
Qed.

Fixpoint redexes_lift i k e: redexes :=
  match e with
  | redexes_jump r f xs =>
    redexes_jump r (lift i k f) (map (lift i k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_lift i (S k) b)
      (traverse_list (lift i) k ts)
      (redexes_lift i (k + length ts) c)
  | _ =>
    mark (lift i k (unmark e))
  end.

Fixpoint redexes_subst y k e: redexes :=
  match e with
  | redexes_jump r f xs =>
    redexes_jump r (subst y k f) (map (subst y k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_subst y (S k) b)
      (traverse_list (subst y) k ts)
      (redexes_subst y (k + length ts) c)
  | _ =>
    mark (subst y k (unmark e))
  end.

Fixpoint redexes_apply_parameters ys k e: redexes :=
  match ys with
  | [] => e
  | y :: ys => redexes_subst y k (redexes_apply_parameters ys (1 + k) e)
  end.

Lemma mark_lift_is_sound:
  forall c i k,
  mark (lift i k c) = redexes_lift i k (mark c).
Proof.
  induction c; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite lift_distributes_over_bind; simpl.
    f_equal; auto.
Qed.

Lemma mark_subst_is_sound:
  forall c x k,
  mark (subst x k c) = redexes_subst x k (mark c).
Proof.
  induction c; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite subst_distributes_over_bind; simpl.
    f_equal; auto.
Qed.

Lemma mark_apply_parameters_is_sound:
  forall xs k c,
  mark (apply_parameters xs k c) = redexes_apply_parameters xs k (mark c).
Proof.
  induction xs; simpl; intros.
  - reflexivity.
  - rewrite mark_subst_is_sound.
    f_equal.
    apply IHxs.
Qed.

Inductive compatible: relation redexes :=
  | compatible_type:
    compatible redexes_type redexes_type
  | compatible_prop:
    compatible redexes_prop redexes_prop
  | compatible_base:
    compatible redexes_base redexes_base
  | compatible_void:
    compatible redexes_void redexes_void
  | compatible_bound:
    forall n,
    compatible (redexes_bound n) (redexes_bound n)
  | compatible_negation:
    forall ts,
    compatible (redexes_negation ts) (redexes_negation ts)
  | compatible_jump:
    forall r1 r2 f xs,
    compatible (redexes_jump r1 f xs) (redexes_jump r2 f xs)
  | compatible_bind:
    forall b1 b2 ts c1 c2,
    compatible b1 b2 ->
    compatible c1 c2 ->
    compatible (redexes_bind b1 ts c1) (redexes_bind b2 ts c2).

Global Hint Constructors compatible: cps.

Goal
  forall b c,
  compatible b c <-> unmark b = unmark c.
Proof.
  split; intros.
  - induction H; simpl; congruence.
  - generalize dependent c.
    induction b;
    intros;
    destruct c;
    try discriminate;
    dependent destruction H;
    constructor; auto.
Qed.

Lemma compatible_refl:
  forall e,
  compatible e e.
Proof.
  induction e; auto with cps.
Qed.

Global Hint Resolve compatible_refl: cps.

Lemma compatible_sym:
  forall a b,
  compatible a b -> compatible b a.
Proof.
  induction 1; auto with cps.
Qed.

Global Hint Resolve compatible_sym: cps.

Lemma compatible_trans:
  forall a b,
  compatible a b ->
  forall c,
  compatible b c -> compatible a c.
Proof.
  induction 1; inversion_clear 1; auto with cps.
Qed.

Global Hint Resolve compatible_trans: cps.

Lemma compatible_lift:
  forall a b,
  compatible a b ->
  forall i k,
  compatible (redexes_lift i k a) (redexes_lift i k b).
Proof.
  induction 1; simpl; auto with cps.
Qed.

Lemma compatible_subst:
  forall a b,
  compatible a b ->
  forall y k,
  compatible (redexes_subst y k a) (redexes_subst y k b).
Proof.
  induction 1; simpl; auto with cps.
Qed.

Lemma compatible_apply_parameters:
  forall ys k a b,
  compatible a b ->
  compatible (redexes_apply_parameters ys k a)
    (redexes_apply_parameters ys k b).
Proof.
  induction ys; simpl; intros.
  - assumption.
  - apply compatible_subst.
    apply IHys.
    assumption.
Qed.

Definition residuals_env: Set :=
  list (option (nat * redexes)).

Global Hint Unfold residuals_env: cps.

(* TODO: I might use skip in the machine semantics file as well. *)

Local Notation skip n k xs :=
  (insert (repeat None n) k xs).

Inductive residuals: residuals_env -> redexes -> redexes -> redexes -> Prop :=
  | residuals_type:
    forall g,
    residuals g redexes_type redexes_type redexes_type
  | residuals_prop:
    forall g,
    residuals g redexes_prop redexes_prop redexes_prop
  | residuals_base:
    forall g,
    residuals g redexes_base redexes_base redexes_base
  | residuals_void:
    forall g,
    residuals g redexes_void redexes_void redexes_void
  | residuals_bound:
    forall g n,
    residuals g (redexes_bound n) (redexes_bound n) (redexes_bound n)
  | residuals_negation:
    forall g ts,
    residuals g
      (redexes_negation ts)
      (redexes_negation ts)
      (redexes_negation ts)
  | residuals_jump:
    forall g r k xs,
    residuals g
      (redexes_jump r k xs)
      (redexes_jump false k xs)
      (redexes_jump r k xs)
  | residuals_mark:
    forall g r k xs c,
    item (Some (length xs, c)) g k ->
    residuals g
      (redexes_jump r (bound k) xs)
      (redexes_jump true (bound k) xs)
      (redexes_apply_parameters xs 0 (redexes_lift (S k) (length xs) c))
  | residuals_bind:
    forall g b1 b2 b3 ts c1 c2 c3,
    residuals (Some (length ts, c3) :: g) b1 b2 b3 ->
    residuals (skip (length ts) 0 g) c1 c2 c3 ->
    residuals g
      (redexes_bind b1 ts c1)
      (redexes_bind b2 ts c2)
      (redexes_bind b3 ts c3).

Global Hint Constructors residuals: cps.

Lemma residuals_term:
  forall c g,
  residuals g (mark c) (mark c) (mark c).
Proof.
  induction c; eauto with cps.
Qed.

Lemma residuals_is_unique:
  forall a g b c1,
  residuals g a b c1 ->
  forall c2,
  residuals g a b c2 -> c1 = c2.
Proof.
  induction a; simpl; intros.
  - dependent destruction H.
    dependent destruction H0.
    reflexivity.
  - dependent destruction H.
    dependent destruction H0.
    reflexivity.
  - dependent destruction H.
    dependent destruction H0.
    reflexivity.
  - dependent destruction H.
    dependent destruction H0.
    reflexivity.
  - dependent destruction H.
    dependent destruction H0.
    reflexivity.
  - dependent destruction H.
    dependent destruction H0.
    reflexivity.
  - dependent destruction H.
    + dependent destruction H0.
      reflexivity.
    + dependent destruction H0.
      eapply item_unique in H; eauto.
      dependent destruction H.
      reflexivity.
  - dependent destruction H.
    dependent destruction H1.
    assert (c3 = c4).
    + eapply IHa2; eauto.
    + dependent destruction H1.
      f_equal; eapply IHa1; eauto.
Qed.

Lemma residuals_apply_parameters:
  forall xs g c1 c2 c3,
  residuals (skip (length xs) 0 g) c1 c2 c3 ->
  residuals g (redexes_apply_parameters xs 0 c1)
              (redexes_apply_parameters xs 0 c2)
              (redexes_apply_parameters xs 0 c3).
Proof.
  admit.
Admitted.

Lemma compatible_residuals:
  forall g a b c,
  residuals g a b c ->
  compatible a b.
Proof.
  induction 1; auto with cps.
Qed.

Global Hint Resolve compatible_residuals: cps.

Inductive sanity: residuals_env -> residuals_env -> residuals_env -> Prop :=
  | sanity_nil:
    sanity nil nil nil
  | sanity_cons:
    forall a r rs p ps q qs,
    sanity rs ps qs ->
    residuals (skip a 0 qs) r p q ->
    sanity (Some (a, r) :: rs) (Some (a, p) :: ps) (Some (a, q) :: qs)
  | sanity_none:
    forall rs ps qs,
    sanity rs ps qs ->
    sanity (None :: rs) (None :: ps) (None :: qs).

Local Hint Constructors sanity: cps.

Lemma sanity_skip:
  forall a rs ps qs,
  sanity rs ps qs ->
  sanity (skip a 0 rs) (skip a 0 ps) (skip a 0 qs).
Proof.
  unfold skip.
  induction a; simpl; intros.
  - assumption.
  - auto with cps.
Qed.

Local Hint Resolve sanity_skip: cps.

(* -------------------------------------------------------------------------- *)

Fixpoint drop {T} (n: nat) (xs: list T) :=
  match n, xs with
  | 0, _ => xs
  | _, [] => []
  | S n', _ :: xs' => drop n' xs'
  end.

(* -------------------------------------------------------------------------- *)

Lemma residuals_sanity:
  forall k a b g,
  item (Some (a, b)) g k ->
  forall c h,
  item (Some (a, c)) h k ->
  forall q,
  sanity g h q ->
  exists2 d,
  residuals (skip a 0 (drop (S k) q)) b c d & item (Some (a, d)) q k.
Proof.
  induction k; intros.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    simpl; exists q.
    + assumption.
    + constructor.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    + edestruct IHk with (b := b) (c := c) as (d, ?, ?); eauto with cps.
    + edestruct IHk with (b := b) (c := c) as (d, ?, ?); eauto with cps.
Qed.

Lemma foobar:
  forall g h q,
  sanity g h q ->
  forall xs k b1 b2,
  item (Some (length xs, b1)) g k ->
  item (Some (length xs, b2)) h k ->
  forall c,
  residuals q
       (redexes_apply_parameters xs 0
          (redexes_lift (S k) (length xs) b1))
       (redexes_apply_parameters xs 0
          (redexes_lift (S k) (length xs) b2)) c ->
  exists2 b3,
    c = redexes_apply_parameters xs 0 (redexes_lift (S k) (length xs) b3) &
    item (Some (length xs, b3)) q k.
Proof.
  admit.
Admitted.

Lemma cube:
  forall g a r b,
  residuals g a r b ->
  forall h p c,
  residuals h a p c ->
  forall i rp,
  residuals i r p rp ->
  forall j pr,
  residuals j p r pr ->
  forall q d,
  residuals q b pr d ->
  sanity g j q ->
  sanity h i q ->
  residuals q c rp d.
Proof.
  induction 1; inversion_clear 1; intros.
  (* Case: (type, type). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (prop, prop). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (base, base). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (void, void). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (bound, bound). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (negation, negation). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (jump, jump). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (jump, mark). *)
  - dependent destruction H.
    dependent destruction H1.
    dependent destruction H2.
    eapply residuals_sanity in H4 as (c2', ?, ?); eauto.
    assert (c2' = c2); subst.
    + eapply item_unique in H1; eauto.
      now dependent destruction H1.
    + apply residuals_apply_parameters.
      admit.
  (* Case: (mark, jump). *)
  - dependent destruction H0.
    dependent destruction H1.
    eapply foobar in H2 as (b3, ?, ?).
    + subst.
      now constructor.
    + exact H3.
    + assumption.
    + assumption.
  (* Case: (mark, mark). *)
  - dependent destruction H0.
    dependent destruction H2.
    eapply foobar in H3 as (c4, ?, ?).
    + subst.
      apply residuals_apply_parameters.
      eapply residuals_sanity in H5 as (c4', ?, ?); eauto.
      assert (c4' = c4); subst.
      * eapply item_unique in H6; eauto.
        now dependent destruction H6.
      * admit.
    + exact H4.
    + assumption.
    + assumption.
  (* Case: (bind, bind). *)
  - dependent destruction H1.
    dependent destruction H4.
    dependent destruction H5.
    (* A bit of a hard search in here, but straightforward in paper by using our
       inductive hypotheses! *)
    eauto 11 with cps.
Admitted.

Lemma residuals_compatible:
  forall g a r b,
  residuals g a r b ->
  forall p,
  compatible a p ->
  exists pr,
  (* Not the same g, but compatible with it! *)
  residuals g p r pr.
Proof.
  induction 1; intros.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H0.
    eauto with cps.
  - dependent destruction H1.
    admit.
Admitted.

Global Hint Resolve residuals_compatible: cps.

Inductive paving_result b c r p: Prop :=
  | paving_result_mk
    (pr: redexes)
    (rp: redexes)
    (d: redexes)
    (H1: residuals [] p r pr)
    (H2: residuals [] r p rp)
    (H3: residuals [] b pr d)
    (H4: residuals [] c rp d).

Theorem paving:
  forall a r b,
  residuals [] a r b ->
  forall p c,
  residuals [] a p c ->
  paving_result b c r p.
Proof.
  intros.
  assert (exists pr, residuals [] p r pr) as (pr, ?); eauto with cps.
  assert (exists rp, residuals [] r p rp) as (rp, ?); eauto with cps.
  assert (exists d, residuals [] b pr d) as (d, ?).
  admit.
  apply paving_result_mk with pr rp d.
  - assumption.
  - assumption.
  - assumption.
  - apply cube with [] a r b [] p [] [] pr; auto with cps.
Admitted.

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

Fixpoint redexes_count r: nat :=
  match r with
  | redexes_jump true f xs =>
    1
  | redexes_bind b ts c =>
    redexes_count b + redexes_count c
  | _ =>
    0
  end.

Lemma redexes_count_mark:
  forall c,
  redexes_count (mark c) = 0.
Proof.
  induction c; simpl; lia.
Qed.

Lemma residuals_tail:
  forall g b r c,
  residuals g b r c ->
  forall h,
  residuals (g ++ h) b r c.
Proof.
  induction 1; simpl; intros.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
    apply item_insert_tail.
    assumption.
  - constructor.
    + apply IHresiduals1.
    + rewrite <- insert_app_assoc by lia.
      apply IHresiduals2.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive redexes_context: Set :=
  | redexes_context_hole
  | redexes_context_left
      (b: redexes_context) (ts: list pseudoterm) (c: redexes)
  | redexes_context_right
      (b: redexes) (ts: list pseudoterm) (c: redexes_context).

Fixpoint apply_redexes_context h e: redexes :=
  match h with
  | redexes_context_hole =>
    e
  | redexes_context_left b ts c =>
    redexes_bind (apply_redexes_context b e) ts c
  | redexes_context_right b ts c =>
    redexes_bind b ts (apply_redexes_context c e)
  end.

Coercion apply_redexes_context: redexes_context >-> Funclass.

Fixpoint mark_context h: redexes_context :=
  match h with
  | context_hole =>
    redexes_context_hole
  | context_left b ts c =>
    redexes_context_left (mark_context b) ts (mark c)
  | context_right b ts c =>
    redexes_context_right (mark b) ts (mark_context c)
  end.

Lemma mark_context_is_sound:
  forall h e,
  mark_context h (mark e) = mark (h e).
Proof.
  induction h; simpl; congruence.
Qed.

Inductive redexes_same_path: relation redexes_context :=
  | redexes_same_path_hole:
    redexes_same_path redexes_context_hole redexes_context_hole
  | redexes_same_path_left:
    forall h r ts1 ts2 c1 c2,
    redexes_same_path h r ->
    length ts1 = length ts2 ->
    redexes_same_path
      (redexes_context_left h ts1 c1)
      (redexes_context_left r ts2 c2)
  | redexes_same_path_right:
    forall b1 b2 ts1 ts2 h r,
    redexes_same_path h r ->
    length ts1 = length ts2 ->
    redexes_same_path
      (redexes_context_right b1 ts1 h)
      (redexes_context_right b2 ts2 r).

Global Hint Constructors redexes_same_path: cps.

Fixpoint redexes_context_bvars h: nat :=
  match h with
  | redexes_context_hole =>
    0
  | redexes_context_left b _ _ =>
    S (redexes_context_bvars b)
  | redexes_context_right _ ts c =>
    redexes_context_bvars c + length ts
  end.

Notation RAP xs k c :=
  (redexes_apply_parameters xs 0 (redexes_lift (S k) (length xs) c)).

(* -------------------------------------------------------------------------- *)

Inductive subset: relation redexes :=
  | subset_type:
    subset redexes_type redexes_type
  | subset_prop:
    subset redexes_prop redexes_prop
  | subset_base:
    subset redexes_base redexes_base
  | subset_void:
    subset redexes_void redexes_void
  | subset_bound:
    forall n,
    subset (redexes_bound n) (redexes_bound n)
  | subset_negation:
    forall xs,
    subset (redexes_negation xs) (redexes_negation xs)
  | subset_jump:
    forall k xs,
    subset (redexes_jump false k xs) (redexes_jump false k xs)
  | subset_mark:
    forall r k xs,
    subset (redexes_jump r k xs) (redexes_jump true k xs)
  | subset_bind:
    forall b1 b2 ts c1 c2,
    subset b1 b2 ->
    subset c1 c2 ->
    subset (redexes_bind b1 ts c1) (redexes_bind b2 ts c2).

Lemma partial_development:
  forall g r s x,
  residuals g r s x ->
  forall t,
  subset t s ->
  forall h y,
  residuals h r t y ->
  forall i z,
  residuals i s t z ->
  sanity h i g ->
  residuals g y z x.
Proof.
  induction 1; intros.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  - dependent destruction H0.
    rename r into r1, r0 into r2.
    dependent destruction H1.
    + dependent destruction H2.
      constructor.
      assumption.
    + dependent destruction H2.
      rename g0 into h, g1 into i.
      rename c into c3, c0 into c1, c1 into c2.
      admit.
  - dependent destruction H1.
    dependent destruction H2.
    dependent destruction H3.
    rename g0 into h, g1 into i.
    (* Nice automation in here! *)
    constructor; eauto with cps.
Admitted.

(* -------------------------------------------------------------------------- *)

Fixpoint redexes_weight (g: list (option nat)) (r: redexes): nat :=
  match r with
  | redexes_jump true (bound k) xs =>
    match nth k g None with
    | Some n => 1 + n
    | None => 0
    end
  | redexes_bind b ts c =>
    let n := redexes_weight (skip (length ts) 0 g) c in
    redexes_weight (Some n :: g) b + n
  | _ =>
    0
  end.

(* Contracting a redex, any redex, should reduce the count! *)

Goal
  forall h k xs ts c g,
  length xs = length ts ->
  k = redexes_context_bvars h ->
  redexes_weight g (redexes_bind (h (RAP xs k c)) ts c) <
    redexes_weight g (redexes_bind (h (redexes_jump true k xs)) ts c).
Proof.
  intros; simpl.
  remember (redexes_weight (skip (length ts) 0 g) c) as n.
  apply Nat.add_lt_mono_r.
  rename g into g'.
  remember (Some n :: g') as g.
  assert (k >= redexes_context_bvars h) by lia.
  assert (item (Some n) g (k - redexes_context_bvars h) /\
          g' = drop (1 + (k - redexes_context_bvars h)) g) as (?, ?).
  - rewrite <- H0, Heqg.
    replace (k - k) with 0; try lia.
    split; auto with cps.
  - clear H0 Heqg.
    generalize dependent g.
    induction h; intros.
    + rewrite Nat.sub_0_r in H2, H3.
      (* simpl.
      erewrite nth_item; eauto; simpl.
      assert (g' = drop (S k) g).
      * destruct g; auto.
      * clear H1 H2 H3.
        rewrite H0 in Heqn; clear H0.
        (* Well, this should be true! Beware of high-order terms, though! *)
        admit. *)
      admit.
    + (* simpl.
      apply Nat.add_lt_mono_r.
      simpl in H1; destruct k; try lia.
      apply IHh.
      * lia.
      * replace (S k - redexes_context_bvars h) with
          (S (k - redexes_context_bvars h)); try lia.
        constructor; auto.
      * (* Ok, fair enough... *)
        simpl in H2.
        admit. *)
      admit.
    + admit.
Admitted.

Inductive partial_reduction: relation redexes :=
  | partial_reduction_mk:
    forall r s t,
    redexes_count t > 0 ->
    subset t r ->
    residuals [] r t s ->
    partial_reduction r s.

Lemma partial_reduction_reduces_weight:
  forall r s,
  partial_reduction r s ->
  forall g,
  redexes_weight g s < redexes_weight g r.
Proof.
  intros until 1.
  dependent destruction H.
  induction H1; intros h.
  - exfalso.
    inversion H.
  - exfalso.
    inversion H.
  - exfalso.
    inversion H.
  - exfalso.
    inversion H.
  - exfalso.
    inversion H.
  - exfalso.
    inversion H.
  - exfalso.
    inversion H.
  - admit.
  - simpl in H |- *.
    admit.
Admitted.

Theorem finite_development:
  forall r,
  SN partial_reduction r.
Proof.
  intros.
  remember (redexes_weight [] r) as n.
  generalize dependent r.
  induction n using lt_wf_ind; intros.
  (* For any partial reduction, we reduce the weight. *)
  constructor; intros s ?.
  apply H with (redexes_weight [] s); subst; auto.
  now apply partial_reduction_reduces_weight.
Qed.
