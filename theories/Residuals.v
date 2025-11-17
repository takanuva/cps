(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.

Import ListNotations.

(** ** Residuals *)

Inductive redexes: Set :=
  | redexes_bound (n: nat)
  | redexes_type (x: type_tag) (ts: list pseudoterm)
  | redexes_jump (r: bool) (f: pseudoterm) (xs: list pseudoterm)
  | redexes_bind (b: redexes) (ts: list pseudoterm) (c: redexes).

Fixpoint mark (e: pseudoterm): redexes :=
  match e with
  | bound n =>
    redexes_bound n
  | type x ts =>
    redexes_type x ts
  | jump f xs =>
    redexes_jump false f xs
  | bind b ts c =>
    redexes_bind (mark b) ts (mark c)
  end.

Fixpoint unmark (e: redexes): pseudoterm :=
  match e with
  | redexes_bound n =>
    n
  | redexes_type x ts =>
    type x ts
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

Lemma mark_is_injective:
  forall a b,
  mark a = mark b ->
  a = b.
Proof.
  induction a; intros.
  - destruct b; simpl in H; now inversion H.
  - destruct b; simpl in H; now inversion H.
  - destruct b; simpl in H; now inversion H.
  - destruct b; simpl in H; inversion H.
    f_equal; auto.
Qed.

Global Hint Resolve mark_is_injective: cps.

Fixpoint redexes_traverse f k e: redexes :=
  match e with
  | redexes_bound n =>
    mark (f k n)
  | redexes_jump r x xs =>
    redexes_jump r (traverse f k x) (map (traverse f k) xs)
  | redexes_bind b ts c =>
    redexes_bind
      (redexes_traverse f (S k) b)
      (traverse_list (traverse f) k ts)
      (redexes_traverse f (k + length ts) c)
  | _ =>
    mark (traverse f k (unmark e))
  end.

Global Instance redexes_dbTraverse: dbTraverse redexes pseudoterm :=
  redexes_traverse.

Global Instance redexes_dbTraverseLaws: dbTraverseLaws redexes pseudoterm.
Proof.
  split; unfold Substitution.traverse; intros.
  - generalize dependent k.
    induction x; intros; simpl.
    + now rewrite H.
    + f_equal.
      induction ts; auto.
      simpl; f_equal; auto.
      rewrite traverse_type_length.
      now apply traverse_ids.
    + f_equal.
      * now apply traverse_ids.
      * induction xs; auto.
        simpl; f_equal; auto.
        now apply traverse_ids.
    + f_equal; auto.
      induction ts; auto.
      simpl; f_equal; auto.
      rewrite traverse_list_length.
      now apply traverse_ids.
  - apply mark_is_injective.
    apply (H k (redexes_bound n)).
  - generalize dependent j.
    generalize dependent k.
    induction x; intros; simpl.
    + f_equal.
      apply (H 0).
    + f_equal.
      induction ts; auto.
      simpl; f_equal; auto.
      repeat rewrite traverse_type_length.
      apply traverse_ext; intros.
      now do 2 rewrite Nat.add_assoc.
    + f_equal.
      * now apply traverse_ext.
      * induction xs; auto.
        simpl; f_equal; auto.
        now apply traverse_ext.
    + f_equal.
      * apply IHx1; intros.
        replace (l + S k) with (S l + k) by lia.
        replace (l + S j) with (S l + j) by lia.
        apply H.
      * induction ts; auto.
        simpl; f_equal; auto.
        repeat rewrite traverse_list_length.
        apply traverse_ext; intros.
        now do 2 rewrite Nat.add_assoc.
      * apply IHx2; intros.
        replace (l + (k + length ts)) with (l + length ts + k) by lia.
        replace (l + (j + length ts)) with (l + length ts + j) by lia.
        apply H.
  - generalize dependent k.
    induction x; intros; simpl.
    + generalize (g k n) as x; intros.
      generalize dependent k.
      induction x; simpl; intros; auto.
      now rewrite IHx1, IHx2.
    + f_equal.
      induction ts; auto.
      simpl; repeat rewrite traverse_type_length.
      f_equal; auto.
      apply traverse_fun.
    + f_equal.
      * apply traverse_fun.
      * induction xs; auto.
        simpl; f_equal; auto.
        apply traverse_fun.
    + rewrite traverse_list_length.
      f_equal; auto.
      induction ts; auto.
      simpl; f_equal; auto.
      repeat rewrite traverse_list_length.
      apply traverse_fun.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma redexes_bound_var_equality_stuff:
  forall s n,
  inst s (redexes_bound n) = mark (inst s (bound n)).
Proof.
  auto.
Qed.

Lemma inst_distributes_over_redexes_type:
  forall s x ts,
  inst s (redexes_type x ts) = redexes_type x (traverse_type x s 0 ts).
Proof.
  auto.
Qed.

Lemma inst_distributes_over_redexes_jump:
  forall s r x xs,
  inst s (redexes_jump r x xs) = redexes_jump r (s 0 x) (smap s 0 xs).
Proof.
  auto.
Qed.

Lemma inst_distributes_over_redexes_bind:
  forall s b ts c,
  inst s (redexes_bind b ts c) =
    redexes_bind (s 1 b) (bsmap s 0 ts) (s (length ts) c).
Proof.
  auto.
Qed.

Global Hint Rewrite redexes_bound_var_equality_stuff using sigma_solver: sigma.
Global Hint Rewrite inst_distributes_over_redexes_type using sigma_solver:
  sigma.
Global Hint Rewrite inst_distributes_over_redexes_jump using sigma_solver:
  sigma.
Global Hint Rewrite inst_distributes_over_redexes_bind using sigma_solver:
  sigma.

(* -------------------------------------------------------------------------- *)

Lemma mark_inst_is_sound:
  forall c s,
  mark (inst s c) = inst s (mark c).
Proof.
  induction c; intros.
  - simpl.
    now sigma.
  - reflexivity.
  - reflexivity.
  - simpl; sigma.
    now rewrite <- IHc1, <- IHc2.
Qed.

Lemma mark_lift_is_sound:
  forall c i k,
  mark (lift i k c) = lift i k (mark c).
Proof.
  intros.
  sigma.
  apply mark_inst_is_sound.
Qed.

Lemma mark_subst_is_sound:
  forall c x k,
  mark (subst x k c) = subst x k (mark c).
Proof.
  intros.
  sigma.
  apply mark_inst_is_sound.
Qed.

Lemma mark_apply_parameters_is_sound:
  forall xs k c,
  mark (apply_parameters xs k c) = apply_parameters xs k (mark c).
Proof.
  intros.
  sigma.
  apply mark_inst_is_sound.
Qed.

Inductive compatible: relation redexes :=
  | compatible_bound:
    forall n,
    compatible (redexes_bound n) (redexes_bound n)
  | compatible_type:
    forall x ts,
    compatible (redexes_type x ts) (redexes_type x ts)
  | compatible_jump:
    forall r1 r2 f xs,
    compatible (redexes_jump r1 f xs) (redexes_jump r2 f xs)
  | compatible_bind:
    forall b1 b2 ts c1 c2,
    compatible b1 b2 ->
    compatible c1 c2 ->
    compatible (redexes_bind b1 ts c1) (redexes_bind b2 ts c2).

Global Hint Constructors compatible: cps.

Local Goal
  forall b c,
  compatible b c <-> unmark b = unmark c.
Proof.
  split; intros.
  - induction H; simpl; congruence.
  - generalize dependent c.
    (* We probably could make a better proof here... *)
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

Lemma compatible_inst:
  forall a b,
  compatible a b ->
  forall s,
  compatible (inst s a) (inst s b).
Proof.
  induction 1; simpl; auto with cps; intros.
  - sigma; constructor.
  - sigma; now constructor.
Qed.

Lemma compatible_lift:
  forall a b,
  compatible a b ->
  forall i k,
  compatible (lift i k a) (lift i k b).
Proof.
  intros.
  sigma.
  now apply compatible_inst.
Qed.

Lemma compatible_subst:
  forall a b,
  compatible a b ->
  forall y k,
  compatible (subst y k a) (subst y k b).
Proof.
  intros.
  sigma.
  now apply compatible_inst.
Qed.

Lemma compatible_apply_parameters:
  forall ys k a b,
  compatible a b ->
  compatible (apply_parameters ys k a) (apply_parameters ys k b).
Proof.
  intros.
  sigma.
  now apply compatible_inst.
Qed.

Definition residuals_env: Set :=
  list (option (nat * redexes)).

Global Hint Unfold residuals_env: cps.

Local Notation blank n :=
  (repeat None n).

Inductive residuals: residuals_env -> redexes -> redexes -> redexes -> Prop :=
  | residuals_bound:
    forall g n,
    residuals g (redexes_bound n) (redexes_bound n) (redexes_bound n)
  | residuals_type:
    forall g x ts,
    residuals g
      (redexes_type x ts)
      (redexes_type x ts)
      (redexes_type x ts)
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
      (apply_parameters xs 0 (lift (S k) (length xs) c))
  | residuals_bind:
    forall g b1 b2 b3 ts c1 c2 c3,
    residuals (Some (length ts, c3) :: g) b1 b2 b3 ->
    residuals (blank (length ts) ++ g) c1 c2 c3 ->
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
    + dependent destruction H0.
      reflexivity.
    + dependent destruction H0.
      eapply item_unique in H; eauto.
      dependent destruction H.
      reflexivity.
  - dependent destruction H.
    dependent destruction H1.
    assert (c3 = c4); subst.
    + eapply IHa2; eauto.
    + f_equal.
      eapply IHa1; eauto.
Qed.

Global Hint Resolve residuals_is_unique: cps.

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
    residuals (blank a ++ qs) r p q ->
    sanity (Some (a, r) :: rs) (Some (a, p) :: ps) (Some (a, q) :: qs)
  | sanity_none:
    forall rs ps qs,
    sanity rs ps qs ->
    sanity (None :: rs) (None :: ps) (None :: qs).

Global Hint Constructors sanity: cps.

Lemma sanity_skip:
  forall a rs ps qs,
  sanity rs ps qs ->
  sanity (blank a ++ rs) (blank a ++ ps) (blank a ++ qs).
Proof.
  induction a; simpl; intros.
  - assumption.
  - auto with cps.
Qed.

Global Hint Resolve sanity_skip: cps.

(* -------------------------------------------------------------------------- *)

Fixpoint drop {T} (n: nat) (xs: list T) :=
  match n, xs with
  | 0, _ => xs
  | _, [] => []
  | S n', _ :: xs' => drop n' xs'
  end.

(* -------------------------------------------------------------------------- *)

Lemma residuals_sanity:
  forall k g h q,
  sanity g h q ->
  forall a b,
  item (Some (a, b)) g k ->
  forall c,
  item (Some (a, c)) h k ->
  exists2 d,
  residuals (blank a ++ (drop (S k) q)) b c d & item (Some (a, d)) q k.
Proof.
  induction k; intros.
  - dependent destruction H0.
    dependent destruction H1.
    dependent destruction H.
    simpl; exists q.
    + assumption.
    + constructor.
  - dependent destruction H0.
    dependent destruction H1.
    dependent destruction H.
    + edestruct IHk with (b := b) (c := c) as (d, ?, ?); eauto with cps.
    + edestruct IHk with (b := b) (c := c) as (d, ?, ?); eauto with cps.
Qed.

Local Lemma residuals_env_item_aux:
  forall a1 a2 b c k (g: residuals_env),
  item (Some (a1, b)) g k ->
  item (Some (a2, c)) g k ->
  b = c.
Proof.
  intros.
  assert (Some (a1, b) = Some (a2, c)).
  - eapply item_unique; eauto.
  - now dependent destruction H1.
Qed.

Local Hint Resolve residuals_env_item_aux: cps.

(* -------------------------------------------------------------------------- *)

Lemma redexes_apply_parameters_distributes_over_jump:
  forall ys k r x xs,
  apply_parameters ys k (redexes_jump r x xs) =
  redexes_jump r (apply_parameters ys k x)
    (map (apply_parameters ys k) xs).
Proof.
  intros.
  now sigma.
Qed.

Lemma redexes_apply_parameters_distributes_over_bind:
  forall ys k b ts c,
  apply_parameters ys k (redexes_bind b ts c) =
    redexes_bind (apply_parameters ys (S k) b)
      (traverse_list (apply_parameters ys) k ts)
      (apply_parameters ys (k + length ts) c).
Proof.
  intros.
  sigma; do 3 f_equal.
  (* TODO: could we please check where have we inverted this bit? *)
  lia.
Qed.

Lemma redexes_apply_parameters_distributes_over_itself:
  forall b xs ys k,
  apply_parameters xs k (apply_parameters ys 0 b) =
    apply_parameters (map (apply_parameters xs k) ys) 0
      (apply_parameters xs (length ys + k) b).
Proof.
  intros.
  unfold apply_parameters.
  sigma.
  replace (map (subst_app xs subst_ids k) ys) with
    (smap (subst_app xs subst_ids) k ys) by auto.
  sigma; repeat f_equal; lia.
Qed.

Local Lemma technical1:
  forall {T} k a g h,
  insert (blank a) k g h ->
  forall t n,
  item (@Some T t) h n ->
  k <= n ->
  a + k <= n.
Proof.
  intros until 1.
  dependent induction H; intros.
  - clear H0; rewrite Nat.add_0_r.
    generalize dependent n.
    induction a; simpl; intros.
    + lia.
    + dependent destruction H.
      specialize (IHa n H).
      lia.
  - destruct n0 as [| m ]; try lia.
    dependent destruction H0.
    assert (a + n <= m).
    + eapply IHinsert; eauto.
      lia.
    + lia.
Qed.

Lemma residuals_apply_parameters:
  forall h c1 c2 c3,
  residuals h c1 c2 c3 ->
  forall xs k g,
  insert (blank (length xs)) k g h ->
  residuals g (apply_parameters xs k c1)
    (apply_parameters xs k c2) (apply_parameters xs k c3).
Proof.
  induction 1; intros.
  - sigma.
    apply residuals_term.
  - sigma.
    constructor.
  - sigma.
    constructor.
  - rename xs0 into ys, k into n, k0 into k, g into h, g0 into g.
    do 2 rewrite redexes_apply_parameters_distributes_over_jump.
    (* For this case to work we have to make sure the substitution on the marked
       jump results in a variable again, otherwise there won't be a constructor
       for this. This is the case: our hypothesis guarantees that the jump isn't
       performed to one of the parameters, i.e., it's not performed on one of
       the variables that we are substituting in here. So, two cases: either
       it was already bound from the start, or we bound it during the induction
       process. *)
    destruct (le_gt_dec k n).
    + (* If it was already bound, it means it can't be replaced now. *)
      assert (length ys + k <= n).
      * eapply technical1; eauto.
      * rewrite apply_parameters_bound_gt by assumption.
        (* We have to adjust the term a bit. *)
        rewrite redexes_apply_parameters_distributes_over_itself.
        (* TODO: fix me. *)
        replace (apply_parameters ys (length xs + k) (lift (S n)
          (length xs) c)) with (lift (S (n - length ys))
            (length (map (apply_parameters ys k) xs)) c) by admit.
        (* Now we can make the residual by performing this redex. *)
        constructor.
        (* We already have this item! *)
        rewrite map_length.
        eapply item_insert_ge_rev; eauto; try lia.
        rewrite repeat_length.
        now replace (length ys + (n - length ys)) with n by lia.
    + (* The jump is to a newly bound variable, we can just reproduce it. *)
      rewrite apply_parameters_bound_lt by assumption.
      (* Adjust the term a bit... *)
      rewrite redexes_apply_parameters_distributes_over_itself.
      admit.
  - repeat rewrite redexes_apply_parameters_distributes_over_bind.
    admit.
Admitted.

Lemma residuals_lift:
  forall k i g c1 c2 c3,
  residuals (blank k ++ drop i g) c1 c2 c3 ->
  residuals (blank k ++ g) (lift i k c1) (lift i k c2) (lift i k c3).
Proof.
  admit.
Admitted.

(* -------------------------------------------------------------------------- *)

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
  (* Case: (bound, bound). *)
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H1.
    constructor.
  (* Case: (type, type). *)
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
    assert (c2' = c2) by eauto with cps; subst.
    (* This is a cool case! You might wanna read the comments in the following
       auxiliary lemma as it's tricky in the higher-order de Bruijn version. *)
    eapply residuals_apply_parameters with (h := blank (length xs) ++ g2).
    + apply residuals_lift.
      assumption.
    + constructor.
  (* Case: (mark, jump). *)
  - dependent destruction H0.
    dependent destruction H1.
    (* Follows the same reasoning as above to conclude that d must respect the
       structure, allowing a redex to be performed. *)
    eapply residuals_sanity in H3 as (c2, ?, ?); eauto.
    apply residuals_lift in H1.
    eapply residuals_apply_parameters with (k := 0) (g := q) (xs := xs) in H1.
    + replace d with (apply_parameters xs 0 (lift (S k) (length xs) c2)).
      * now constructor.
      * eapply residuals_is_unique; eauto.
    + constructor.
  (* Case: (mark, mark). *)
  - dependent destruction H0.
    dependent destruction H2.
    (* Hah, in here we have to mix the two cases above! We find out d, then we
       go and show that we arrive at it as well by using our sanity lemmas. *)
    eapply residuals_sanity in H4 as (c4, ?, ?); eauto.
    apply residuals_lift in H4.
    eapply residuals_apply_parameters with (k := 0) (g := q) (xs := xs) in H4.
    + replace d with (apply_parameters xs 0 (lift (S k) (length xs) c4)).
      * (* Sigh... TODO: refactor me, please? *)
        eapply residuals_sanity in H5 as (c4', ?, ?); eauto.
        assert (c4' = c4) by eauto with cps; subst.
        eapply residuals_apply_parameters with (h := blank (length xs) ++ q).
        apply residuals_lift.
        assumption.
        constructor.
      * eapply residuals_is_unique; eauto.
    + constructor.
  (* Case: (bind, bind). *)
  - (* After case analysis, we just have to use the inductive hypotheses to show
       that the reductions will happen on both sides of a bind. *)
    dependent destruction H1.
    dependent destruction H4.
    dependent destruction H5.
    (* A bit of a hard search in here, but straightforward in paper. *)
    eauto 11 with cps.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive compatible_env: relation (option (nat * redexes)) :=
  | compatible_env_some:
    forall r s n,
    compatible r s ->
    compatible_env (Some (n, r)) (Some (n, s))
  | compatible_env_none:
    compatible_env None None.

Lemma compatible_env_inversion:
  forall a b k g,
  item (Some (a, b)) g k ->
  forall h,
  Forall2 compatible_env g h ->
  exists2 c,
  item (Some (a, c)) h k & compatible b c.
Proof.
  induction k; simpl; intros.
  - dependent destruction H.
    dependent destruction H0.
    dependent destruction H.
    exists s.
    + constructor.
    + assumption.
  - dependent destruction H.
    dependent destruction H0.
    edestruct IHk.
    + eassumption.
    + eassumption.
    + exists x.
      * constructor.
        assumption.
      * assumption.
Qed.

Lemma compatible_env_refl:
  forall g,
  Forall2 compatible_env g g.
Proof.
  induction g; simpl; intros.
  - constructor.
  - constructor.
    + destruct a.
      * destruct p.
        constructor.
        apply compatible_refl.
      * constructor.
    + assumption.
Qed.

Lemma compatible_env_sym:
  forall g h,
  Forall2 compatible_env g h ->
  Forall2 compatible_env h g.
Proof.
  induction 1; simpl; intros.
  - constructor.
  - constructor; auto.
    dependent destruction H.
    + constructor.
      now apply compatible_sym.
    + constructor.
Qed.

Lemma compatible_env_skip:
  forall g h,
  Forall2 compatible_env g h ->
  forall n,
  Forall2 compatible_env (blank n ++ g) (blank n ++ h).
Proof.
  induction n; simpl; intros.
  - assumption.
  - constructor.
    + constructor.
    + assumption.
Qed.

Lemma compatible_residuals_result:
  forall g r b1 c1,
  residuals g b1 r c1 ->
  forall h,
  Forall2 compatible_env g h ->
  forall b2 c2,
  residuals h b2 r c2 ->
  compatible c1 c2.
Proof.
  induction 1; inversion_clear 2.
  - constructor.
  - constructor.
  - constructor.
  - eapply compatible_env_inversion in H0 as (d, ?, ?); eauto.
    assert (c0 = d) by eauto with cps; subst.
    apply compatible_apply_parameters.
    apply compatible_lift.
    assumption.
  - assert (compatible c3 c6).
    + eapply IHresiduals2.
      * apply compatible_env_skip.
        eassumption.
      * eassumption.
    + assert (compatible b3 b6).
      * eapply IHresiduals1; eauto.
        constructor; auto.
        now constructor.
      * constructor; auto.
Qed.

Local Hint Resolve compatible_residuals_result: cps.

Definition regular: redexes -> Prop :=
  fun r =>
    exists a b,
    residuals [] a r b.

Global Hint Unfold regular: cps.

Lemma residuals_compatible:
  forall r,
  regular r ->
  forall p,
  compatible r p ->
  exists pr,
  residuals [] p r pr.
Proof.
  intros.
  (* We gotta generalize our induction a bit. *)
  destruct H as (a, (b, ?)).
  cut (Forall2 compatible_env [] []); eauto with cps.
  generalize dependent H.
  generalize (@nil (option (nat * redexes))) at 3 4 as h.
  generalize (@nil (option (nat * redexes))) as g.
  intros until 1.
  generalize dependent h.
  generalize dependent p.
  (* There we go; now we can proceed. *)
  induction H; intros.
  - dependent destruction H0.
    eauto with cps.
  - dependent destruction H0.
    eauto with cps.
  - dependent destruction H0.
    eauto with cps.
  - dependent destruction H0.
    eapply compatible_env_inversion in H1 as (d, ?, ?); eauto.
    eexists.
    constructor.
    eassumption.
  - dependent destruction H1.
    edestruct IHresiduals2 as (c5, ?).
    + eassumption.
    + apply compatible_env_skip.
      eassumption.
    + edestruct IHresiduals1 as (b5, ?).
      * eassumption.
      * constructor; eauto.
        constructor.
        eapply compatible_residuals_result; eauto.
        apply compatible_env_skip.
        assumption.
      * eexists.
        constructor; eauto.
Qed.

Global Hint Resolve residuals_compatible: cps.

Local Lemma generalized_regularity_preservation:
  forall g a b c,
  residuals g a b c ->
  forall h r s,
  residuals h r a s ->
  forall q,
  sanity g g q ->
  exists d, residuals q c c d.
Proof.
  induction 1; intros.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - (* Did a mark this redex? *)
    dependent destruction H.
    + (* It didn't, so we don't have to do anything now. *)
      eauto with cps.
    + (* It did, so we'll repeat it now. *)
      rename g0 into h, k0 into n, r0 into r.
      (* Ok, we need an additional hypothesis... *)
      admit.
  - (* Here we have contracted the redex, so it doesn't matter if it was marked
       in a or not. *)
    clear H0.
    edestruct residuals_sanity as (d, ?, ?); eauto.
    apply residuals_lift in H0.
    eapply residuals_apply_parameters in H0.
    + eexists.
      eassumption.
    + constructor.
  - (* Use the inductive hypotheses to construct the resulting term. *)
    dependent destruction H1.
    rename g0 into h, b0 into b4, c0 into c4.
    edestruct IHresiduals2 as (c6, ?).
    + eassumption.
    + apply sanity_skip.
      eassumption.
    + edestruct IHresiduals1 as (b6, ?).
      * eassumption.
      * constructor; eauto.
      * (* There we go! *)
        eauto with cps.
Admitted.

(* TODO: join with the above...? *)

Lemma regularity_preservation:
  forall a,
  regular a ->
  forall b c,
  residuals [] a b c ->
  regular c.
Proof.
  intros.
  exists c.
  destruct H as (r, (s, ?)).
  eapply generalized_regularity_preservation with (a := a); eauto with cps.
Qed.

Global Hint Resolve regularity_preservation: cps.

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
  (* Since both a\r and a\p are defined, these are all compatible. As such, we
     also know that r\p and p\r must be defined. *)
  assert (exists pr, residuals [] p r pr) as (pr, ?) by eauto 9 with cps.
  assert (exists rp, residuals [] r p rp) as (rp, ?) by eauto 9 with cps.
  (* As both r\p and p\r are defined, we know that both must be regular (in the
     sense of Huet): they only contain marks in valid places. Then, as both a\r
     and p\r reduce only the redexes that are marked in r, they are compatible
     and so (a\r)\(p\r) must be defined as well. *)
  assert (exists d, residuals [] b pr d) as (d, ?) by eauto 7 with cps.
  (* Thus we can create the desired result. *)
  apply paving_result_mk with pr rp d.
  - assumption.
  - assumption.
  - assumption.
  - (* The last item, (a\p)\(r\p), should also be defined and, by the cube lemma
       it must be the same as (a\r)\(p\r) as expected. *)
    apply cube with [] a r b [] p [] [] pr; auto with cps.
Qed.

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

Global Hint Resolve redexes_count_mark: cps.

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
    apply item_insert_tail.
    assumption.
  - constructor.
    + apply IHresiduals1.
    + rewrite app_assoc.
      apply IHresiduals2.
Qed.

Lemma residuals_zero_marks:
  forall g r s t,
  residuals g r s t ->
  redexes_count s = 0 ->
  r = t.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - f_equal.
    + now rewrite IHresiduals1 by lia.
    + now rewrite IHresiduals2 by lia.
Qed.

Global Hint Resolve residuals_zero_marks: cps.

Lemma residuals_unmarked_preserve_no_marks:
  forall r s t,
  residuals [] r s t ->
  redexes_count r = 0 ->
  redexes_count t = 0.
Proof.
  admit.
Admitted.

Global Hint Resolve residuals_unmarked_preserve_no_marks: cps.

Lemma mark_unmark_is_sound:
  forall r,
  redexes_count r = 0 ->
  r = mark (unmark r).
Proof.
  induction r; simpl; intros.
  - reflexivity.
  - reflexivity.
  - now destruct r.
  - f_equal.
    + apply IHr1; lia.
    + apply IHr2; lia.
Qed.

Global Hint Resolve mark_unmark_is_sound: cps.

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

Notation RAP xs k c := (apply_parameters xs 0 (lift (S k) (length xs) c)).

(* -------------------------------------------------------------------------- *)

Inductive subset: relation redexes :=
  | subset_bound:
    forall n,
    subset (redexes_bound n) (redexes_bound n)
  | subset_type:
    forall x ts,
    subset (redexes_type x ts) (redexes_type x ts)
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

Global Hint Constructors subset: cps.

Lemma subset_residuals_zero_marks:
  forall g r s t,
  residuals g r s t ->
  redexes_count t = 0 ->
  subset r s.
Proof.
  induction 1; simpl; intros.
  - constructor.
  - constructor.
  - destruct r.
    + discriminate.
    + constructor.
  - constructor.
  - constructor.
    + apply IHresiduals1.
      lia.
    + apply IHresiduals2.
      lia.
Qed.

Global Hint Resolve subset_residuals_zero_marks: cps.

Lemma compatible_subset:
  forall r s,
  subset r s ->
  compatible r s.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve compatible_subset: cps.

Local Lemma generalized_regular_subset:
  forall s r,
  subset s r ->
  forall g a b,
  residuals g a r b ->
  forall h,
  exists c, residuals h a s c.
Proof.
  induction 1; intros.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    eauto with cps.
  - dependent destruction H.
    destruct r.
    + eexists.
      constructor.
      (* We clearly need another hypothesis. *)
      admit.
    + eexists.
      constructor.
  - dependent destruction H1.
    edestruct IHsubset2 as (c5, ?); eauto.
    edestruct IHsubset1 as (b5, ?); eauto.
    eexists; eauto with cps.
Admitted.

Lemma regular_subset:
  forall r,
  regular r ->
  forall s,
  subset s r ->
  regular s.
Proof.
  destruct 1 as (a, (b, ?)); intros.
  exists a.
  eapply generalized_regular_subset; eauto.
Qed.

Global Hint Resolve regular_subset: cps.

Lemma partial_development:
  forall t s,
  subset t s ->
  forall g1 r rs,
  residuals g1 r s rs ->
  forall g2 rt,
  residuals g2 r t rt ->
  forall g3 st,
  residuals g3 s t st ->
  sanity g2 g3 g1 ->
  residuals g1 rt st rs.
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
    + dependent destruction H1.
      now constructor.
    + dependent destruction H1.
      edestruct residuals_sanity as (c', ?, ?); eauto.
      assert (c' = c) by eauto with cps; subst.
      eapply residuals_apply_parameters.
      * apply residuals_lift.
        eassumption.
      * constructor.
  - dependent destruction H1.
    dependent destruction H2.
    dependent destruction H3.
    (* Nice automation in here! *)
    constructor; eauto with cps.
Qed.

(* -------------------------------------------------------------------------- *)

Fixpoint redexes_weight (g: list (option nat)) (r: redexes): nat :=
  match r with
  | redexes_jump true (bound k) xs =>
    match nth k g None with
    | Some n => 1 + n
    | None => 0
    end
  | redexes_bind b ts c =>
    let n := redexes_weight (blank (length ts) ++ g) c in
    redexes_weight (Some n :: g) b + n
  | _ =>
    0
  end.

Inductive redexes_weight_count: residuals_env -> list (option nat) -> Prop :=
  | redexes_weight_count_nil:
    redexes_weight_count [] []
  | redexes_weight_count_cons:
    forall g h a c,
    redexes_weight_count g h ->
    redexes_weight_count (Some (a, c) :: g)
      (Some (redexes_weight (blank a ++ h) c) :: h)
  | redexes_weight_count_none:
    forall g h,
    redexes_weight_count g h ->
    redexes_weight_count (None :: g) (None :: h).

Local Hint Constructors redexes_weight_count: cps.

Lemma redexes_weight_count_skip:
  forall g h,
  redexes_weight_count g h ->
  forall a,
  redexes_weight_count (blank a ++ g) (blank a ++ h).
Proof.
  induction a; simpl; auto with cps.
Qed.

Local Hint Resolve redexes_weight_count_skip: cps.

Lemma redexes_weight_count_inversion:
  forall k a c g,
  item (Some (a, c)) g k ->
  forall h,
  redexes_weight_count g h ->
  exists2 n,
  item (Some n) h k & n = redexes_weight (blank a ++ drop (S k) h) c.
Proof.
  intros until 1.
  dependent induction H; intros.
  - dependent destruction H.
    eexists; eauto with cps.
  - dependent destruction H0.
    + edestruct IHitem.
      * eassumption.
      * eexists; auto.
        constructor.
        now subst.
    + edestruct IHitem.
      * eassumption.
      * eexists; auto.
        constructor.
        now subst.
Qed.

Lemma development_reduces_weight:
  forall t r,
  subset t r ->
  forall g s,
  residuals g r t s ->
  redexes_count t > 0 ->
  forall h,
  redexes_weight_count g h ->
  redexes_weight h s < redexes_weight h r.
Proof.
  induction 1; intros.
  - inversion H0.
  - inversion H0.
  - inversion H0.
  - destruct r.
    + dependent destruction H.
      clear H0; rename k0 into k.
      eapply redexes_weight_count_inversion in H1 as (n, ?, ?); eauto.
      simpl; erewrite nth_item; eauto; simpl.
      (* Clearly we're dropping by 1 in here. *)
      admit.
    + inversion H0.
  - dependent destruction H1.
    destruct (le_gt_dec (redexes_count b1) 0);
    destruct (le_gt_dec (redexes_count c1) 0);
    simpl.
    + exfalso; simpl in H2.
      lia.
    + assert (b4 = b2) by admit; subst.
      set (q := blank (length ts) ++ h).
      set (v1 := Some (redexes_weight q c4) :: h).
      set (v2 := Some (redexes_weight q c2) :: h).
      assert (redexes_weight v1 b2 <= redexes_weight v2 b2) by admit.
      assert (redexes_weight q c4 < redexes_weight q c2) by eauto with cps.
      lia.
    + assert (c4 = c2) by admit; subst.
      set (q := blank (length ts) ++ h).
      set (v := Some (redexes_weight q c2) :: h).
      assert (redexes_weight v b4 < redexes_weight v b2) by eauto with cps.
      lia.
    + set (q := blank (length ts) ++ h).
      assert (redexes_weight q c4 < redexes_weight q c2) by eauto with cps.
      set (v1 := Some (redexes_weight q c4) :: h).
      set (v2 := Some (redexes_weight q c2) :: h).
      assert (redexes_weight v1 b4 < redexes_weight v2 b2) by admit.
      lia.
Admitted.

(* TODO: use this in the partial_development lemma above...? ALSO... TODO: we
   need to be more strict with the names. Technically, development reduces all
   the redexes, partial development reduces some (this definition!) and full
   development reduces all the possible ones. *)

Inductive development: relation redexes :=
  | development_mk:
    forall r s t,
    redexes_count t > 0 ->
    subset t r ->
    residuals [] r t s ->
    development r s.

Theorem finite_development:
  forall r,
  SN development r.
Proof.
  intros.
  remember (redexes_weight [] r) as n.
  generalize dependent r.
  induction n using lt_wf_ind; intros.
  (* For any partial development, we strictly reduce the weight. *)
  constructor; intros s ?.
  apply H with (redexes_weight [] s); subst.
  - destruct H0.
    apply development_reduces_weight with t []; auto with cps.
  - reflexivity.
Qed.
