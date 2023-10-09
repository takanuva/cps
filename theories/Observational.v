(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Confluence.
Require Import Local.Factorization.
Require Import Local.Structural.

(** ** Observational theory *)

Inductive converges: pseudoterm -> nat -> Prop :=
  | converges_jump:
    forall k xs,
    converges (jump (bound k) xs) k
  | converges_bind:
    forall b ts c k,
    converges b (S k) -> converges (bind b ts c) k.

Global Hint Constructors converges: cps.

Definition weakly_converges a n: Prop :=
  comp star converges a n.

Global Hint Unfold weakly_converges: cps.

Lemma convergence_is_unique:
  forall e n,
  converges e n ->
  forall m,
  converges e m -> n = m.
Proof.
  induction 1; intros.
  (* Case: converges_jump. *)
  - inversion H; auto.
  (* Case: converges_bind. *)
  - dependent destruction H0.
    firstorder.
Qed.

Lemma converges_inv:
  forall P: pseudoterm -> nat -> Prop,
  forall f1: (forall h xs n, static h -> P (h (jump (n + #h) xs)) n),
  forall e n,
  converges e n -> P e n.
Proof.
  intros.
  assert (exists2 h, static h & exists xs, e = h (jump (n + #h) xs)).
  - clear f1.
    induction H.
    + exists context_hole; auto with cps.
      exists xs; rewrite Nat.add_comm; simpl.
      reflexivity.
    + destruct IHconverges as (h, ?, (xs, ?)).
      exists (context_left h ts c); auto with cps.
      exists xs; rewrite Nat.add_comm; simpl.
      dependent destruction H1.
      do 4 f_equal; lia.
  - destruct H0 as (h, ?, (xs, ?)).
    dependent destruction H1.
    apply f1; auto.
Qed.

(* TODO: rename the following lemma. *)

Lemma converges_context_inversion:
  forall h,
  static h ->
  forall k xs n,
  converges (h (jump (bound k) xs)) n ->
  n = k - #h.
Proof.
  induction 1; simpl; intros.
  - dependent destruction H.
    lia.
  - dependent destruction H0.
    rename k0 into n.
    assert (S n = k - #h).
    + eapply IHstatic; eauto.
    + lia.
Qed.

Lemma converges_jump_inversion:
  forall (h: context) xs k,
  converges (h (jump #h xs)) k ->
  k > 0 ->
  nonstatic h.
Proof.
  unfold nonstatic, not; intros.
  assert (k = #h - #h).
  - eapply converges_context_inversion; eauto.
  - lia.
Qed.

(* Note here that the converse is not necessarily true: a term in head normal
   form might unfortunately still be stuck. *)

Lemma convergence_implies_head_normal_form:
  forall c k,
  converges c k -> normal head c.
Proof.
  induction 1.
  - inversion 1.
    destruct r; try discriminate.
  - intros d ?.
    dependent destruction H0.
    destruct H1; simpl in x.
    + dependent destruction x.
      apply converges_jump_inversion in H.
      * contradiction.
      * lia.
    + rename h0 into r.
      dependent destruction x.
      eapply IHconverges.
      constructor; auto.
Qed.

Lemma converges_is_preserved_by_subst:
  forall c k p y,
  converges c (p + S k) ->
  converges (subst y p c) (p + k).
Proof.
  intros.
  dependent induction H.
  - rewrite subst_distributes_over_jump.
    rewrite subst_bound_gt; try lia.
    rewrite Nat.add_comm; simpl.
    rewrite Nat.add_comm; constructor.
  - rewrite subst_distributes_over_bind.
    constructor.
    replace (S (p + k)) with (S p + k); try lia.
    apply IHconverges; lia.
Qed.

Lemma converges_is_preserved_by_step:
  forall a b,
  [a => b] ->
  forall n,
  converges a n -> converges b n.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    constructor.
    assert (nonstatic h).
    + eapply converges_jump_inversion; eauto.
      lia.
    + generalize dependent k.
      generalize #h.
      induction H1 using nonstatic_ind; simpl; intros.
      * dependent destruction H0.
        constructor; auto.
      * dependent destruction H0.
        constructor; auto.
  - dependent destruction H0.
    apply converges_is_preserved_by_subst with (p := 0).
    assumption.
  - dependent destruction H0.
    constructor; auto.
  - dependent destruction H0.
    constructor; auto.
Qed.

Global Hint Resolve converges_is_preserved_by_step: cps.

Lemma converges_is_preserved_by_star:
  forall a b,
  [a =>* b] ->
  forall n,
  converges a n -> converges b n.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve converges_is_preserved_by_star: cps.

Lemma weakly_converges_is_preserved_by_conv:
  forall a b,
  [a <=> b] ->
  forall n,
  weakly_converges a n -> weakly_converges b n.
Proof.
  destruct 2 as (c, ?, ?).
  assert [c <=> b].
  - eauto with cps.
  - destruct step_is_church_rosser with c b as (d, ?, ?); auto.
    exists d; auto.
    apply converges_is_preserved_by_star with c; auto.
Qed.

Lemma weakly_convergence_is_a_function:
  forall e n,
  weakly_converges e n ->
  forall m,
  weakly_converges e m -> n = m.
Proof.
  intros.
  destruct H as (a, ?, ?).
  destruct H0 as (b, ?, ?).
  destruct step_is_confluent with e a b as (c, ?, ?); auto.
  assert (converges c n); eauto with cps.
  assert (converges c m); eauto with cps.
  apply convergence_is_unique with c; auto.
Qed.

Lemma converges_lift:
  forall e n,
  converges e n ->
  forall i k (m: nat),
  lift i k n = m ->
  converges (lift i k e) m.
Proof.
  induction 1; intros.
  - rename k0 into p.
    rewrite lift_distributes_over_jump.
    rewrite H.
    constructor.
  - rename k0 into p.
    rewrite lift_distributes_over_bind.
    constructor.
    apply IHconverges.
    destruct (le_gt_dec p k).
    + rewrite lift_bound_ge in H0; auto.
      rewrite lift_bound_ge; try lia.
      dependent destruction H0.
      f_equal; lia.
    + rewrite lift_bound_lt in H0; auto.
      rewrite lift_bound_lt; try lia.
      dependent destruction H0.
      f_equal; lia.
Qed.

Lemma converges_subst:
  forall e n,
  converges e n ->
  forall y k (m: nat),
  subst y k n = m ->
  converges (subst y k e) m.
Proof.
  induction 1; intros.
  - rename k0 into p.
    rewrite subst_distributes_over_jump.
    rewrite H.
    constructor.
  - rename k0 into p.
    rewrite subst_distributes_over_bind.
    constructor.
    apply IHconverges.
    destruct (lt_eq_lt_dec p k) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_gt in H0; auto.
      rewrite subst_bound_gt; try lia.
      dependent destruction H0.
      f_equal; lia.
    + rewrite subst_bound_eq in H0; auto.
      rewrite subst_bound_eq; try lia.
      destruct y; try discriminate.
      rewrite lift_bound_ge in H0; try lia.
      rewrite lift_bound_ge; try lia.
      dependent destruction H0.
      f_equal; lia.
    + rewrite subst_bound_lt in H0; auto.
      rewrite subst_bound_lt; try lia.
      dependent destruction H0.
      f_equal; lia.
Qed.

Lemma converges_unlift:
  forall i k e n,
  converges (lift i k e) n ->
  exists2 m,
  converges e m & bound n = lift i k m.
Proof.
  intros.
  dependent induction H.
  - destruct e; try discriminate.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in x; auto.
        inversion x.
      * rewrite lift_bound_lt in x; auto.
        inversion x.
    + rewrite lift_distributes_over_jump in x.
      dependent destruction x.
      destruct e; try discriminate.
      exists n; auto with cps.
  - destruct e; try discriminate.
    + exfalso.
      destruct (le_gt_dec k n).
      * rewrite lift_bound_ge in x; auto.
        inversion x.
      * rewrite lift_bound_lt in x; auto.
        inversion x.
    + rewrite lift_distributes_over_bind in x.
      dependent destruction x.
      edestruct IHconverges; eauto.
      destruct x.
      * exfalso.
        rewrite lift_bound_lt in H1; try lia.
        discriminate.
      * exists x; auto with cps.
        (* TODO: fix this proof, please. *)
        destruct (le_gt_dec k x).
        rewrite lift_bound_ge in H1 |- *; try lia.
        dependent destruction H1; f_equal; lia.
        rewrite lift_bound_lt in H1 |- *; try lia.
        congruence.
Qed.

(** ** Observational relations *)

(* We'd like to show that defining weak convergence by using either head or full
   reduction coincide; this will allow us to further extend Merro's results:
   enabling full reduction won't change the observable behavior of terms, since
   the observational relations introduced by either of the reduction relations
   will also coincide. Of course, one of the sides is trivial.

   This proof seems way more trickier than I thought... it will probably require
   a notion of standard reduction sequences, in which we only allow jumps to be
   performed to unchanged commands (i.e., leftmost first, instead of rightmost
   first as it's done in the parallel reduction lemmas). If this is complete
   w.r.t. star, such that forall a =>* b there's a standard sequence from a to
   b, then it'll reach the correct head position using only head steps. *)

Local Lemma subst_backwards_preserves_convergence_gc:
  forall c y k p,
  not_free p c ->
  converges (subst y p c) (p + k) ->
  converges c (p + S k).
Proof.
  intros.
  dependent induction H0.
  - destruct c; try discriminate.
    + exfalso.
      dependent destruction H.
      destruct (le_gt_dec n0 n).
      * rewrite subst_bound_gt in x; try lia.
        discriminate.
      * rewrite subst_bound_lt in x; try lia.
        discriminate.
    + rewrite subst_distributes_over_jump in x.
      dependent destruction x.
      dependent destruction H.
      destruct c; try discriminate.
      dependent destruction H.
      destruct (le_gt_dec n n0).
      * rewrite subst_bound_gt in x; try lia.
        dependent destruction x.
        replace n0 with (n + S k); try lia.
        constructor.
      * exfalso.
        rewrite subst_bound_lt in x; try lia.
        dependent destruction x.
        lia.
  - destruct c; try discriminate.
    + exfalso.
      dependent destruction H.
      destruct (le_gt_dec n0 n).
      * rewrite subst_bound_gt in x; try lia.
        discriminate.
      * rewrite subst_bound_lt in x; try lia.
        discriminate.
    + rewrite subst_distributes_over_bind in x.
      dependent destruction x.
      dependent destruction H.
      constructor.
      rewrite <- plus_Sn_m.
      eapply IHconverges; eauto.
Qed.

(* Just a quick (legacy) check: an eta step also conserves convergence. *)

Goal
  forall h k xs y,
  static h ->
  forall c j p,
  k <> bound (p + #h) ->
  c = h (jump k xs) ->
  converges (subst y p c) (p + j) ->
  converges c (p + S j).
Proof.
  induction 1; intros.
  - rewrite Nat.add_comm in H.
    simpl in H, H0.
    dependent destruction H0.
    rewrite subst_distributes_over_jump in H1.
    dependent destruction H1.
    destruct k; try discriminate.
    (* H is an equality between terms! *)
    assert (n <> p); eauto.
    destruct (le_gt_dec p n).
    + rewrite subst_bound_gt in x; try lia.
      dependent destruction x.
      replace n with (p + S j); try lia.
      constructor.
    + exfalso.
      rewrite subst_bound_lt in x; try lia.
      dependent destruction x.
      lia.
  - simpl in H0, H1.
    destruct c0; try discriminate.
    dependent destruction H1.
    rewrite subst_distributes_over_bind in H2.
    dependent destruction H2.
    constructor.
    rewrite <- plus_Sn_m.
    apply IHstatic.
    + replace (S p + #h) with (p + S #h); try lia.
      assumption.
    + reflexivity.
    + assumption.
Qed.

Lemma inner_backwards_preserves_convergence:
  forall a b,
  inner a b ->
  forall k,
  converges b k -> converges a k.
Proof.
  induction 1.
  - clear H0; generalize #h; intros.
    dependent destruction H0; constructor.
    dependent induction H0.
    + exfalso.
      destruct h; try discriminate.
      apply H; auto with cps.
    + destruct h.
      * exfalso.
        apply H; auto with cps.
      * dependent destruction x; simpl.
        constructor.
        eapply IHconverges; eauto.
        intro; apply H.
        constructor; auto.
      * dependent destruction x; simpl.
        constructor; auto.
  - intros.
    constructor.
    eapply subst_backwards_preserves_convergence_gc with (p := 0).
    + assumption.
    + eassumption.
  - intros.
    dependent destruction H0.
    constructor; auto.
  - intros.
    dependent destruction H0.
    constructor; auto.
Qed.

Lemma rt_inner_backwards_preserves_convergence:
  forall a b,
  rt(inner) a b ->
  forall k,
  converges b k -> converges a k.
Proof.
  induction 1; intros.
  - eapply inner_backwards_preserves_convergence; eauto.
  - assumption.
  - firstorder.
Qed.

Theorem weak_convergence_characterization:
  forall a k,
  weakly_converges a k <-> comp rt(head) converges a k.
Proof.
  split; intros.
  - destruct H as (c, ?, ?).
    apply factorization in H.
    destruct H as (b, ?, ?).
    exists b; auto.
    apply rt_inner_backwards_preserves_convergence with c; auto.
  - destruct H as (b, ?, ?).
    exists b; auto.
    clear H0.
    induction H; eauto with cps.
Qed.

(** ** Barbed relations *)

Notation barb := (barbed_congruence head converges apply_context).

Notation "[ a ~~ b ]" := (barb a b)
  (at level 0, a, b at level 200): type_scope.

Lemma barb_refl:
  forall e,
  [e ~~ e].
Proof.
  intros.
  apply barbed_congruence_refl.
Qed.

Global Hint Resolve barb_refl: cps.

Lemma barb_sym:
  forall a b,
  [a ~~ b] -> [b ~~ a].
Proof.
  intros.
  apply barbed_congruence_sym; auto.
Qed.

Global Hint Resolve barb_sym: cps.

Lemma barb_trans:
  forall a b c,
  [a ~~ b] -> [b ~~ c] -> [a ~~ c].
Proof.
  intros.
  eapply barbed_congruence_trans; eauto.
Qed.

Global Hint Resolve barb_trans: cps.

Lemma barb_bind_left:
  LEFT barb.
Proof.
  unfold LEFT; intros.
  set (r := context_left context_hole ts c).
  replace (bind b1 ts c) with (r b1); auto.
  replace (bind b2 ts c) with (r b2); auto.
  intro; do 2 rewrite <- compose_context_is_sound.
  apply H.
Qed.

Global Hint Resolve barb_bind_left: cps.

Lemma barb_bind_right:
  RIGHT barb.
Proof.
  unfold RIGHT; intros.
  set (r := context_right b ts context_hole).
  replace (bind b ts c1) with (r c1); auto.
  replace (bind b ts c2) with (r c2); auto.
  intro; do 2 rewrite <- compose_context_is_sound.
  apply H.
Qed.

Global Hint Resolve barb_bind_right: cps.

Lemma barb_lift:
  forall a b,
  [a ~~ b] ->
  forall i k,
  [lift i k a ~~ lift i k b].
Proof.
  (* There's no reason this shouldn't be true, and we even checked that this is
     true for sema. But this seems to be overly complex to prove, so I'll get
     back to this later on! *)
  admit.
Admitted.

Global Instance barb_is_a_congruence: Congruence barb.
Proof.
  split.
  - split.
    + exact barb_refl.
    + exact barb_sym.
    + exact barb_trans.
  - exact barb_bind_left.
  - exact barb_bind_right.
Defined.

(* If R and R-1 are barbed simulations, so is the equivalence closure of R.
   This might be useful in showing that sema is a barbed bisimulation by tracing
   its individual axioms. *)

Goal
  forall R,
  (* TODO: generalize this. *)
  barbed_simulation step converges R ->
  barbed_simulation step converges (transp R) ->
  barbed_simulation step converges rst(R).
Proof.
  split.
  - do 3 intro.
    assert ((forall c, [a =>* c] -> exists2 d, [b =>* d] & rst(R) c d)
         /\ (forall c, [b =>* c] -> exists2 d, [a =>* d] & rst(R) c d)).
    + induction H1; split; intros.
      * destruct H.
        eapply multistep_reduction_closed with (S := R) in H2 as (d, ?, ?);
          eauto.
        exists d; auto with cps.
      * destruct H0.
        eapply multistep_reduction_closed with (S := transp R) in H2
          as (d, ?, ?); eauto.
        exists d; auto with cps.
      * eauto with cps.
      * eauto with cps.
      * firstorder.
      * firstorder.
      * destruct IHclos_refl_sym_trans1.
        destruct IHclos_refl_sym_trans2.
        destruct H2 with c as (d, ?, ?); auto.
        destruct H4 with d as (e, ?, ?); auto.
        exists e; eauto with cps.
      * destruct IHclos_refl_sym_trans1.
        destruct IHclos_refl_sym_trans2.
        destruct H5 with c as (d, ?, ?); auto.
        destruct H3 with d as (e, ?, ?); auto.
        exists e; eauto with cps.
    + destruct H2.
      induction H1; intros.
      * eauto with cps.
      * eauto with cps.
      * eauto with cps.
      * eauto with cps.
  - do 4 intro.
    assert ((weakly_converges a n -> weakly_converges b n)
         /\ (weakly_converges b n -> weakly_converges a n)).
    + induction H1; split; intros.
      * destruct H.
        destruct H2 as (z, ?, ?).
        eapply multistep_reduction_closed in H1; eauto.
        destruct H1 as (w, ?, ?).
        apply H3 in H5.
        destruct H5 with n as (k, ?, ?); auto.
        exists k; eauto with cps.
      * destruct H0.
        destruct H2 as (z, ?, ?).
        assert (transp R y x); eauto.
        eapply multistep_reduction_closed in H5; eauto.
        destruct H5 as (w, ?, ?).
        apply H3 in H6.
        destruct H6 with n as (k, ?, ?); auto.
        exists k; eauto with cps.
      * assumption.
      * assumption.
      * firstorder.
      * firstorder.
      * firstorder.
      * firstorder.
    + destruct H2.
      induction H1; intros.
      * unfold weakly_converges in H2, H3.
        eauto with cps.
      * apply H2; eexists; eauto with cps.
      * apply H2; eexists; eauto with cps.
      * destruct H2 as (w, ?, ?); eexists; eauto with cps.
Qed.

Theorem barb_sema:
  forall a b,
  [a == b] -> [a ~~ b].
Proof.
  admit.
Admitted.

Global Hint Resolve barb_sema: cps.

Corollary barb_conv:
  forall a b,
  [a <=> b] -> [a ~~ b].
Proof.
  intros.
  apply barb_sema.
  apply sema_conv.
  assumption.
Qed.

Global Hint Resolve barb_conv: cps.

(* TODO: please, properly show that barbed congruence and the observational
   congruence coincide, as shown by Merro. *)

Lemma barb_weak_convergence:
  forall b c,
  [b ~~ c] ->
  forall k,
  weakly_converges b k <-> weakly_converges c k.
Proof.
  intros.
  edestruct barbed_bisimilarity_implies_observational_equivalence with (l := k).
  - specialize (H context_hole).
    eassumption.
  - simpl in H0, H1.
    split; intros.
    + apply weak_convergence_characterization in H2.
      destruct H0; auto.
      exists x; auto with cps.
    + apply weak_convergence_characterization in H2.
      destruct H1; auto.
      exists x; auto with cps.
Qed.

(* -------------------------------------------------------------------------- *)

(* As shown by Merro, the CPS-calculus validates the corresponding of the omega
   rule in the lambda calculus: any two diverging terms are observationally
   equivalent. *)

Definition diverges (c: pseudoterm): Prop :=
  ~WN head c.

Lemma diverges_head:
  forall c,
  diverges c ->
  forall b,
  head b c -> diverges b.
Proof.
  admit.
Admitted.

Lemma diverges_rt_head:
  forall c,
  diverges c ->
  forall b,
  rt(head) b c -> diverges b.
Proof.
  intros.
  apply clos_rt_rt1n_iff in H0.
  induction H0.
  - assumption.
  - apply diverges_head with y; auto.
Qed.

(* From Merro's paper, proposition 5.1.(1). *)

Lemma diverges_lift:
  forall b,
  diverges b ->
  forall i k,
  diverges (lift i k b).
Proof.
  admit.
Admitted.

Lemma diverges_subst:
  forall b,
  diverges b ->
  forall y k,
  diverges (subst y k b).
Proof.
  admit.
Admitted.

Lemma diverges_apply_parameters:
  forall b,
  diverges b ->
  forall ys k,
  diverges (apply_parameters ys k b).
Proof.
  intros until ys; generalize dependent b.
  induction ys; simpl; intros.
  - assumption.
  - apply IHys.
    apply diverges_subst.
    assumption.
Qed.

(* From Merro's paper, proposition 5.1.(2). *)

Lemma diverges_static_context:
  forall h,
  static h ->
  forall b,
  diverges b -> diverges (h b).
Proof.
  admit.
Admitted.

(* From Merro's paper, proposition 5.1.(3). *)

Lemma diverges_from_jump:
  forall c,
  diverges c ->
  forall b,
  weakly_converges b 0 ->
  forall ts,
  diverges (bind b ts c).
Proof.
  intros.
  apply weak_convergence_characterization in H0.
  destruct H0 as (x, ?, ?).
  assert (rt(head) (bind b ts c) (bind x ts c)) by admit.
  assert (exists2 h, static h & exists xs, x = h (jump #h xs))
    as (h, ?, (xs, ?)) by admit.
  subst.
  eapply diverges_rt_head.
  - apply diverges_static_context with (h := context_left h ts c).
    + auto with cps.
    + apply diverges_apply_parameters.
      apply diverges_lift.
      eassumption.
  - eapply rt_trans.
    + eassumption.
    + apply rt_step; simpl.
      (* Aww crap... TODO: fix this, please!!! *)
      assert (LONGJMP head) by apply head_longjmp.
      unfold LONGJMP in H4.
      specialize H4 with (r := context_hole); simpl in H4.
      apply H4; auto with cps.
      (* Huh... this might NOT be the case... it is in Merro's work, but here
         terms can also get stuck... we don't know if it has the right arity! *)
      admit.
Admitted.

Theorem omega_law:
  forall b c,
  diverges b ->
  diverges c ->
  [b ~~ c].
Proof.
  intros.
  (* TODO: automate this conversion... *)
  exists (observational_equivalence head converges).
  - apply observational_equivalence_is_a_barbed_bisimulation.
    + (* Well, this is obviously the case, since it is deterministic. Didn't add
       this proof yet though... *)
      admit.
    + (* TODO: move to a proper lemma? *)
      clear H H0 b c h.
      intros b c ? k ?.
      eauto with cps.
  - split; intros.
    + clear H0; generalize dependent c.
      admit.
    + clear H; generalize dependent b.
      admit.
Admitted.
