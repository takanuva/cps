(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Confluence.
Require Import Local.Factorization.
Require Import Local.Structural.
Require Import Local.Shrinking.

Import ListNotations.

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

Notation cps_terminates c :=
  (exists k, weakly_converges c k).

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

Lemma free_converges:
  forall b k,
  converges b k ->
  free k b.
Proof.
  induction 1; intros.
  - intros ?H.
    dependent destruction H.
    dependent destruction H.
    contradiction.
  - intros ?H; apply IHconverges.
    dependent destruction H0.
    assumption.
Qed.

Lemma converges_lift:
  forall e n,
  converges e n ->
  forall i k m,
  lift i k (bound n) = bound m ->
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
  forall y k m,
  subst y k (bound n) = bound m ->
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
  converges e m & bound n = lift i k (bound m).
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

Lemma gc_backwards_preserves_convergence:
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

Lemma smol_backwards_preserves_convergence:
  forall a b,
  smol a b ->
  forall k,
  converges b k -> converges a k.
Proof.
  induction 1; intros.
  - constructor.
    eapply gc_backwards_preserves_convergence with (p := 0).
    + assumption.
    + eassumption.
  - dependent destruction H0.
    constructor; auto.
  - dependent destruction H0.
    constructor; auto.
Qed.

Lemma rt_smol_backwards_preserves_convergence:
  forall a b,
  rt(smol) a b ->
  forall k,
  converges b k -> converges a k.
Proof.
  induction 1; intros.
  - eapply smol_backwards_preserves_convergence; eauto.
  - assumption.
  - firstorder.
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
    apply star_characterization in H.
    apply shrinking_may_be_postponed in H as (d, ?, ?).
    + apply factorization in H as (b, ?, ?).
      exists b; auto.
      apply rt_inner_backwards_preserves_convergence with d; auto.
      eapply rt_smol_backwards_preserves_convergence with c; auto.
    + apply smol_is_shrinking.
  - destruct H as (b, ?, ?).
    exists b; auto.
    clear H0.
    induction H; eauto with cps.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma cps_terminates_implies_sn_head:
  forall b,
  cps_terminates b -> SN head b.
Proof.
  intros.
  destruct H as (k, ?).
  apply weak_convergence_characterization in H.
  destruct H as (c, ?, ?).
  apply clos_rt_rt1n_iff in H.
  induction H.
  - constructor; intros.
    exfalso.
    apply convergence_implies_head_normal_form in H0.
    firstorder.
  - constructor; intros w ?.
    assert (w = y).
    + eapply head_is_a_function; eauto.
    + subst.
      apply IHclos_refl_trans_1n.
      assumption.
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

Corollary barb_head:
  forall a b,
  head a b -> [a ~~ b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve barb_head: cps.

Corollary barb_beta:
  forall a b,
  beta a b -> [a ~~ b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve barb_beta: cps.

Corollary barb_step:
  forall a b,
  [a => b] -> [a ~~ b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve barb_step: cps.

Corollary barb_star:
  forall a b,
  [a =>* b] -> [a ~~ b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve barb_star: cps.

Corollary barb_conv:
  forall a b,
  [a <=> b] -> [a ~~ b].
Proof.
  eauto with cps.
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

(* TODO: define this relation. On the translation files I've called it eval. I
   also do use it above somewhere. *)

Lemma barb_eval:
  forall b c,
  [b ~~ c] ->
  forall k,
  comp rt(head) converges b k <-> comp rt(head) converges c k.
Proof.
  split; intros.
  - destruct H0 as (b', ?, ?).
    assert (weakly_converges b' k) by eauto with cps.
    apply barb_weak_convergence with c b' k in H2.
    + now apply weak_convergence_characterization.
    + transitivity b; auto with cps.
  - destruct H0 as (c', ?, ?).
    assert (weakly_converges c' k) by eauto with cps.
    apply barb_weak_convergence with b c' k in H2.
    + now apply weak_convergence_characterization.
    + transitivity c; auto with cps.
Qed.

(* TODO: this is a bit dissonant from the two above lemmas; check it please? *)

Lemma cps_terminates_barb:
  forall b,
  cps_terminates b ->
  forall c,
  [b ~~ c] ->
  cps_terminates c.
Proof.
  intros.
  destruct H as (k, ?).
  exists k.
  now apply barb_weak_convergence with b.
Qed.

(* -------------------------------------------------------------------------- *)

(* As shown by Merro, the CPS-calculus validates the corresponding of the omega
   rule in the lambda calculus: any two diverging terms are observationally
   equivalent. *)

Definition diverges (c: pseudoterm): Prop :=
  ~cps_terminates c.

(* The term k<k> { k<k> = k<k> } is akin to the omega combinator in the lambda
   calculus, i.e., it will have a single redex and will reduce to itself. Thus
   it will trivially diverge. *)

Definition omega: pseudoterm :=
  bind (jump 0 [bound 0]) [void] (jump 0 [bound 0]).

Lemma omega_reduces_to_itself:
  head omega omega.
Proof.
  unfold omega at 1.
  set (b := jump 0 [bound 0]).
  replace (bind b [void] b) with (context_hole (bind (context_hole b) [void] b))
    by auto.
  apply head_longjmp; auto with cps.
Qed.

Lemma omega_diverges:
  diverges omega.
Proof.
  intros ?.
  (* The proof, of course, follows by assuming that it halts and deriving a
     contradiction. As we're assuming that it terminates, it follows that head
     reduction will be strongly normalizing. *)
  apply cps_terminates_implies_sn_head in H.
  (* We proceed by induction on the reduction length, as we always have a head
     redex in here: omega reduces to itself. *)
  remember omega as b.
  induction H using SN_ind; subst.
  apply H2 with omega; clear H2.
  - apply t_step.
    apply omega_reduces_to_itself.
  - reflexivity.
Qed.

Lemma diverges_step:
  forall c,
  diverges c ->
  forall b,
  step b c -> diverges b.
Proof.
  intros c ? b ? ?.
  apply H; clear H.
  destruct H1 as (k, ?).
  apply barb_step in H0.
  exists k.
  now apply barb_weak_convergence with b.
Qed.

Lemma diverges_beta:
  forall c,
  diverges c ->
  forall b,
  beta b c -> diverges b.
Proof.
  intros.
  apply diverges_step with c; auto with cps.
Qed.

Lemma diverges_head:
  forall c,
  diverges c ->
  forall b,
  head b c -> diverges b.
Proof.
  intros.
  apply diverges_beta with c; auto with cps.
Qed.

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
  intros b ? i k ?.
  apply H; clear H.
  admit.
Admitted.

Lemma diverges_subst:
  forall b,
  diverges b ->
  forall y k,
  diverges (subst y k b).
Proof.
  intros b ? y k ?.
  apply H; clear H.
  admit.
Admitted.

Lemma diverges_apply_parameters:
  forall b,
  diverges b ->
  forall ys k,
  diverges (apply_parameters ys k b).
Proof.
  admit.
Admitted.

(* From Merro's paper, proposition 5.1.(2). *)

Lemma diverges_static_context:
  forall h,
  static h ->
  forall b,
  diverges b -> diverges (h b).
Proof.
  intros h ? b ? ?.
  apply H0; clear H0.
  (* Clearly, when h b reduces, this will happen either in b alone, which we can
     reproduce, or it will something from h (or, of course, it will halt at the
     same point as b itself exactly). This means that the reduction path for b
     will be exactly a prefix of the path for h b. As h b terminates, we will
     follow by induction on the reduction length for head reduction. *)
  assert (SN head (h b)) by now apply cps_terminates_implies_sn_head.
  remember (h b) as x.
  generalize dependent b.
  induction H0 using SN_ind; intros; subst.
  (* Do we still have a head redex in b alone? *)
  destruct head_is_decidable with b as [ ?H | (c, ?H) ].
  - (* If we don't, and since h b doesn't get stuck, this means that b alone
       isn't stuck either, and it has to converge to some continuation. We have
       now to properly find which one it is. *)
    clear H2 H0.
    (* We can remember, of course, that divergence is a syntactic property and
       is thus decidable. Either b converges to some k, or it doesn't converge
       at all, which is an absurd. *)
    admit.
  - (* If we have a head redex in b, we'll reduce the same redex at h b, and we
       can keep going by the inductive hypothesis. *)
    destruct H2 with (h c) c as (k, (c', ?, ?)).
    + apply t_step.
      now apply head_static_context.
    + assert [h b ~~ h c] by admit.
      now apply cps_terminates_barb with (h b).
    + reflexivity.
    + exists k, c'; auto.
      apply star_trans with c; auto with cps.
Admitted.

(* From Merro's paper, proposition 5.1.(3). *)

Lemma diverges_from_jump:
  forall c,
  diverges c ->
  forall h,
  static h ->
  forall b xs,
  (* A bit more restrict than Merro's version! *)
  rt(head) b (h (jump #h xs)) ->
  forall ts,
  length xs = length ts -> diverges (bind b ts c).
Proof.
  intros.
  apply diverges_rt_head with (bind (h (apply_parameters xs 0
    (lift (S #h) (length ts) c))) ts c).
  - (* I don't really wanna type the term, but I know what happens to it. *)
    apply diverges_static_context with (h := context_left h ts c);
      auto with cps.
    apply diverges_apply_parameters.
    apply diverges_lift.
    assumption.
  - simpl; apply rt_trans with (bind (h (jump #h xs)) ts c).
    + apply rt_head_bind_left.
      assumption.
    + apply rt_step.
      (* Sigh... TODO: fix this, please! The definition for (LONGJMP) sucks! *)
      assert (LONGJMP head) by apply head_longjmp.
      unfold LONGJMP in H3.
      specialize H3 with (r := context_hole); simpl in H3.
      apply H3; auto with cps.
Qed.

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
    + (* TODO: move to a proper lemma? We *do* use this in the machine semantics
         file in order to show equivalence of observational equalities... *)
      clear H H0 b c h.
      intros b c ? k ?.
      eauto with cps.
  - split; intros.
    + clear H0; generalize dependent c.
      admit.
    + clear H; generalize dependent b.
      admit.
Admitted.
