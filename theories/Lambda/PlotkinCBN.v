(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.Reduction.
Require Import Local.Factorization.
Require Import Local.Observational.
(* TODO: are we using this one...? *)
Require Import Local.Conservation.
Require Import Local.Shrinking.
Require Import Local.TypeSystem.
Require Import Local.Normalization.
Require Export Local.Lambda.Calculus.

Import ListNotations.

Module CPS := Local.Syntax.

(* TODO: move this comment somewhere else.

   The definitions of call by name and call by value reductions are standard;
   as of this development, they were taken from Plotkin's paper.

   Note: if the CPS-calculus properly simulates CBN/CBV reduction, then, by the
   factorization lemma, it's possible to show that we'll reach the desired value
   only by using head redutions! They are enough to simulate the results.

   The CPS translations are given in Thielecke's dissertation, and are based on
   those of Plotkin's paper as well. We note that both translations receive the
   returning continuation as a parameter, but the translation will always set
   this to be the most recently bound continuation, i.e., the de Bruijn index 0,
   so this parameter is taken implictly in our setting. *)

Inductive cbn: relation term :=
  | cbn_beta:
    forall t b x,
    cbn
      (application (abstraction t b) x)
      (subst x 0 b)
  | cbn_app1:
    forall f1 f2 x,
    cbn f1 f2 ->
    cbn (application f1 x) (application f2 x)
  | cbn_app2:
    (* This rule is hardly ever considered, probably because it's only necessary
       for open terms, but it was used in Plotkin's paper, so we'll add it here
       as well. *)
    forall (f: nat) x1 x2,
    cbn x1 x2 ->
    cbn (application f x1) (application f x2).

Local Hint Constructors cbn: cps.

Lemma full_characterization:
  same_relation full (compatible cbn).
Proof.
  split; induction 1.
  - do 2 constructor.
  - now constructor 2.
  - now constructor 3.
  - now constructor 4.
  - induction H.
    + constructor.
    + now constructor 3.
    + now constructor 4.
  - now constructor 2.
  - now constructor 3.
  - now constructor 4.
Qed.

Lemma full_cbn:
  inclusion cbn full.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma cbn_whr:
  inclusion whr cbn.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
Qed.

Lemma cbn_implies_nonvalue:
  forall a b,
  cbn a b -> ~value a.
Proof.
  induction 1; inversion 1.
Qed.

Lemma cbn_is_a_function:
  forall a b1,
  cbn a b1 ->
  forall b2,
  cbn a b2 -> b1 = b2.
Proof.
  induction 1; intros.
  - dependent destruction H.
    + reflexivity.
    + exfalso.
      inversion H.
  - dependent destruction H0.
    + exfalso.
      inversion H.
    + f_equal; auto.
    + exfalso.
      inversion H.
  - dependent destruction H0.
    + exfalso.
      inversion H0.
    + f_equal; auto.
Qed.

Lemma cbn_is_decidable:
  forall e,
  { normal cbn e } + { exists f, cbn e f }.
Proof.
  induction e; simpl.
  - left.
    inversion 1.
  - left.
    inversion 1.
  - destruct e1.
    + clear IHe1.
      destruct IHe2.
      * left.
        (* TODO: damn OCD... *)
        inversion_clear 1; [ easy | firstorder ].
      * right.
        destruct e as (x, ?).
        exists (application n x).
        now constructor 3.
    + right; eexists.
      constructor.
    + destruct IHe1.
      * left; intros x ?.
        dependent destruction H.
        firstorder.
      * right.
        destruct e as (x, ?).
        eexists; eauto with cps.
    + left; inversion_clear 1.
      inversion H0.
    + left; inversion_clear 1.
      inversion H0.
    + left; inversion_clear 1.
      inversion H0.
    + left; inversion_clear 1.
      inversion H0.
    + left; inversion_clear 1.
      inversion H0.
  - left; inversion 1.
  - left; inversion 1.
  - left; inversion 1.
  - left; inversion 1.
  - left; inversion 1.
Qed.

Lemma cbn_whr_iff:
  forall e,
  closed e ->
  forall f,
  cbn e f <-> whr e f.
Proof.
  split; induction 1.
  - constructor.
  - constructor.
    apply IHcbn.
    apply closed_application_left with x.
    assumption.
  - exfalso.
    specialize (H f).
    dependent destruction H.
    dependent destruction H.
    contradiction.
  - constructor.
  - constructor.
    apply IHwhr.
    apply closed_application_left with x.
    assumption.
Qed.

Lemma closed_normal_cbn_implies_value:
  forall e,
  closed e ->
  normal cbn e ->
  value e.
Proof.
  intros.
  destruct value_dec with e as [ ?H | ?H ].
  - assumption.
  - exfalso.
    induction e.
    + apply H1.
      constructor.
    + apply H1.
      constructor.
    + clear IHe2 H1.
      destruct e1.
      * specialize (H n).
        dependent destruction H.
        dependent destruction H.
        contradiction.
      * eapply H0.
        constructor.
      * apply IHe1.
        (* TODO: refactor me, please... *)
        intro.
        specialize (H n).
        dependent destruction H.
        assumption.
        intros x ?.
        eapply H0.
        constructor.
        eassumption.
        inversion 1.
      * (* TODO: not true yet, as we can't reduce inside a pair. *)
        admit.
      * admit.
      * admit.
      * admit.
      * admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
Admitted.

(* TODO: fix typing on the following! *)

Local Notation VAR n :=
  (* [x] = x<k> *)
  (jump (S n) [CPS.bound 0]).

Local Notation ABS b t1 t2 :=
  (* [\x.e] = k<f> { f<x, k> = [e] } *)
  (bind (jump 1 [CPS.bound 0]) [t1; t2] b).

Local Notation APP b c t1 t2 :=
  (* [e f] = [e] { k<f> = f<v, k> { v<k> = [f] } } *)
  (bind b [t1] (bind (jump 1 [CPS.bound 2; CPS.bound 0]) [t2] c)).

(* TODO: these lifts should be moved from source to target! *)

Inductive cbn_cps: term -> pseudoterm -> Prop :=
  | cbn_cps_bound:
    forall n: nat,
    cbn_cps n (VAR n)
  | cbn_cps_abstraction:
    forall t e b,
    cbn_cps (lift 1 1 e) b ->
    cbn_cps (abstraction t e) (ABS b void void)
  | cbn_cps_application:
    forall f x b c,
    cbn_cps (lift 1 0 f) b ->
    cbn_cps (lift 2 0 x) c ->
    cbn_cps (application f x) (APP b c void void).

Local Hint Constructors cbn_cps: cps.

Lemma cbn_cps_is_a_function:
  forall e c1,
  cbn_cps e c1 ->
  forall c2,
  cbn_cps e c2 -> c1 = c2.
Proof.
  induction 1; intros.
  - dependent destruction H.
    reflexivity.
  - dependent destruction H0.
    f_equal; auto.
  - dependent destruction H1.
    f_equal; auto.
    f_equal; auto.
Qed.

Local Hint Resolve cbn_cps_is_a_function: cps.

Lemma cbn_cps_lift:
  forall e c,
  cbn_cps e c ->
  forall i k,
  cbn_cps (lift i k e) (lift i (S k) c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k n).
    + sigma.
      replace (k + (i + n) - k) with (i + n) by lia.
      constructor.
    + sigma.
      constructor.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    replace (lift i k (abstraction t e)) with
      (abstraction t (lift i (S k) e)) by now sigma.
    constructor.
    rewrite lift_lift_permutation; try lia.
    replace (k + 2) with (2 + k); simpl; try lia.
    apply IHcbn_cps; lia.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    replace (lift i k (application f x)) with
      (application (lift i k f) (lift i k x)) by now sigma.
    constructor.
    + rewrite lift_lift_permutation; try lia.
      apply IHcbn_cps1; lia.
    + rewrite lift_lift_permutation; try lia.
      replace (k + 1 + 1) with (2 + k); try lia.
      apply IHcbn_cps2; lia.
Qed.

Local Hint Resolve cbn_cps_lift: cps.

Lemma cbn_cps_is_total:
  forall e,
  exists c,
  cbn_cps e c.
Proof.
  induction e.
  - eauto with cps.
  - destruct IHe as (c, ?).
    eauto with cps.
  - destruct IHe1 as (b, ?).
    destruct IHe2 as (c, ?).
    eauto with cps.
  (* TODO: not yet true, we didn't define the CPS translations for pairs and
     thunks. *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Local Hint Resolve cbn_cps_is_total: cps.

Lemma cbn_cps_lift_inversion:
  forall i k e b,
  cbn_cps (lift i k e) b ->
  exists2 c,
  cbn_cps e c & b = lift i (S k) c.
Proof.
  intros.
  assert (exists c, cbn_cps e c) as (c, ?).
  - eauto with cps.
  - eauto with cps.
Qed.

Local Hint Resolve cbn_cps_lift_inversion: cps.

Lemma cbn_cps_not_free:
  forall e c,
  cbn_cps e c ->
  forall n,
  not_free n e <-> CPS.not_free (S n) c.
Proof.
  induction 1; split; intros.
  - dependent destruction H.
    rename n0 into m.
    constructor.
    + constructor; lia.
    + do 2 constructor; lia.
  - dependent destruction H.
    dependent destruction H.
    rename n0 into m.
    constructor; lia.
  - constructor; simpl.
    + constructor.
      * constructor; lia.
      * do 2 constructor; lia.
    + repeat constructor.
    + dependent destruction H0.
      apply IHcbn_cps; try lia.
      replace (S n) with (n + 1) in H0; try lia.
      apply not_free_lift with (k := 1) in H0.
      replace (n + 1 + 1) with (2 + n) in H0; try lia.
      assumption.
  - constructor.
    dependent destruction H0.
    simpl in H0_0.
    apply IHcbn_cps in H0_0; auto.
    replace (S (S n)) with (n + 1 + 1) in H0_0; try lia.
    apply not_free_lift in H0_0.
    replace (n + 1) with (1 + n) in H0_0; try lia.
    assumption.
  - dependent destruction H1.
    constructor; simpl.
    + apply IHcbn_cps1; auto.
      replace (S n) with (n + 1 + 0); try lia.
      apply not_free_lift.
      rewrite Nat.add_comm.
      assumption.
    + repeat constructor.
    + repeat (try constructor; try lia).
      simpl; eapply IHcbn_cps2; auto.
      replace (S (S n)) with (n + 2 + 0); try lia.
      apply not_free_lift.
      rewrite Nat.add_comm.
      assumption.
  - dependent destruction H1.
    dependent destruction H1_0.
    simpl in H2, H1_0_2.
    constructor.
    + apply IHcbn_cps1 in H1_; auto.
      replace (S n) with (n + 1 + 0) in H1_; try lia.
      apply not_free_lift in H1_.
      rewrite Nat.add_comm in H1_.
      assumption.
    + apply IHcbn_cps2 in H1_0_2; auto.
      replace (S (S n)) with (n + 2 + 0) in H1_0_2; try lia.
      apply not_free_lift in H1_0_2.
      rewrite Nat.add_comm in H1_0_2.
      assumption.
Qed.

(* -------------------------------------------------------------------------- *)

(*
  From Amadio's class notes, we know that head reduction can't directly simulate
  beta reduction, though it's still computationally adequate. It should be the
  case that extended reduction will be able to properly simulate beta reduction.

  For the call-by-name translation:

    1) [x]    = x<k>
    2) [\x.M] = k<f> { f<x, k> = [M] }
    3) [M N]  = [M] { k<f> = f<v, k> { v<k> = [N] } }

  For a lambda term of the form [(\x.a) b], we will have:

    k<f>
    { f<x, k> =
        [a] }
    { k<f> =
        f<v, k>
        { v<k> =
            [b] } }

  We immediately can apply a two linear head redexes:

    [a]
    { x<k> =
        [b] }

  Though the exact induction statement may be awkward, as we have to apply these
  simplifications first and keep building the way, we will proceed by induction
  now on the number of free occurrences of x in a:

    Base: if we don't have x free in a, we don't have x free in [a]. Thus, we
    can apply a garbage collection step and get [a] alone, as expected.

    Step: if there's a x in a, then a can be rewritten as C[x]. Then, due to the
    composability of the translation, we will have:

      D[x<k>]
      { x<k> =
        [b] }

    We would want to show that we can mimick a single substitution, thus, we
    will compare (\x.C[x]) b to (\x.C[b]) b. Thus, we want the above to reduce
    to:

      D[[b]]
      { x<k> =
        [b] }

    Which we can do in one (CTXJMP) step. Qed.

  We note that eta reduction is not sound in here, because this translation is
  tailored for the weak beta reduction used in programming languages. We know
  that eta is not sound in it, because \x.O x has a weak head normal form while
  O does not in the empty context (where O is the omega combinator). Similarly,
  for a variable y, \x.y x and y can be taken apart in the context C = (\y.[]) O
  if y is free (or similar context if it is bound). The remaining case is that
  when we have an abstraction, but then a beta step can be applied and eta is
  not really necessary anymore. We can prove that the translation also doesn't
  validate eta, same as the source language doesn't.

*)

(* -------------------------------------------------------------------------- *)

(* TODO: move me above. *)

Local Notation SUBST b1 b2 :=
  (bind (switch_bindings 0 b1) [void] (lift 1 1 b2)).

Local Lemma cbn_linear_jump_inversion:
  forall (h: context) k b,
  cbn_cps (h (k + context_bvars h)) b ->
  exists2 r: Context.context,
  b = r (jump (1 + k + #r) [CPS.bound 0]) &
    forall e c,
    cbn_cps e c ->
    cbn_cps (h (lift (context_bvars h) 0 e)) (r (lift #r 1 c)).
Proof.
  intros h.
  remember (context_depth h) as n.
  generalize dependent h.
  induction n using lt_wf_ind; intros; subst.
  destruct h.
  - dependent destruction H0.
    exists Context.context_hole; intros.
    + now simpl.
    + simpl.
      rewrite lift_zero_e_equals_e.
      rewrite Metatheory.lift_zero_e_equals_e.
      assumption.
  - dependent destruction H0.
    rewrite context_lift_is_sound in H0.
    edestruct H with (h := context_lift 1 1 h)
      (m := context_depth (context_lift 1 1 h)) as (r, ?, ?); intros.
    + rewrite context_lift_depth.
      simpl; lia.
    + reflexivity.
    + rewrite context_lift_bvars.
      (* TODO: we need a "sigma in" tactic!!! *)
      rewrite_strat topdown (hints sigma) in H0; simpl in H0.
      replace (context_bvars h + 1 + S (k + S (context_bvars h) -
        (context_bvars h + 1))) with (2 + k + context_bvars h) in H0 by lia.
      eassumption.
    + subst.
      eexists (Context.context_right _ _ r); simpl; intros.
      * f_equal; simpl; do 3 f_equal.
        lia.
      * constructor.
        rewrite context_lift_is_sound.
        rewrite lift_lift_simplification by lia.
        rewrite context_lift_bvars in H2.
        apply cbn_cps_lift with (i := 2) (k := 0) in H1.
        specialize (H2 _ _ H1).
        rewrite lift_lift_simplification in H2 by lia.
        rewrite Metatheory.lift_lift_simplification in H2 by lia.
        rewrite Nat.add_comm in H2.
        assumption.
  - dependent destruction H0.
    rewrite context_lift_is_sound in H0_.
    edestruct H with (h := context_lift 1 0 h)
      (m := context_depth (context_lift 1 0 h)) as (r, ?, ?).
    + rewrite context_lift_depth.
      simpl; lia.
    + reflexivity.
    + rewrite Nat.add_0_r in H0_.
      rewrite context_lift_bvars.
      (* TODO: we need a "sigma in" tactic!!! *)
      rewrite_strat topdown (hints sigma) in H0_; simpl in H0_.
      replace (context_bvars h + S (k + context_bvars h - context_bvars h)) with
        (1 + k + context_bvars h) in H0_ by lia.
      eassumption.
    + subst.
      eexists (Context.context_left r _ _); simpl; intros.
      * f_equal; simpl; do 3 f_equal.
        lia.
      * constructor; auto.
        rewrite context_lift_is_sound.
        rewrite lift_lift_simplification by lia.
        rewrite context_lift_bvars in H1.
        apply cbn_cps_lift with (i := 1) (k := 0) in H0.
        specialize (H1 _ _ H0).
        rewrite lift_lift_simplification in H1 by lia.
        rewrite Metatheory.lift_lift_simplification in H1 by lia.
        rewrite Nat.add_comm in H1.
        rewrite Nat.add_comm with (n := #r) in H1.
        assumption.
  - dependent destruction H0.
    rewrite context_lift_is_sound in H0_0.
    edestruct H with (h := context_lift 2 0 h)
      (m := context_depth (context_lift 2 0 h)) as (r, ?, ?).
    + rewrite context_lift_depth.
      simpl; lia.
    + reflexivity.
    + rewrite Nat.add_0_r in H0_0.
      rewrite context_lift_bvars.
      (* TODO: we need a "sigma in" tactic!!! *)
      rewrite_strat topdown (hints sigma) in H0_0; simpl in H0_0.
      replace (context_bvars h + S (S (k + context_bvars h - context_bvars h)))
        with (2 + k + context_bvars h) in H0_0 by lia.
      eassumption.
    + subst.
      eexists (Context.context_right _ _ (Context.context_right _ _ r)); simpl;
        intros.
      * do 2 f_equal; simpl; do 3 f_equal.
        lia.
      * constructor; auto.
        rewrite context_lift_is_sound.
        rewrite lift_lift_simplification by lia.
        rewrite context_lift_bvars in H1.
        apply cbn_cps_lift with (i := 2) (k := 0) in H0.
        specialize (H1 _ _ H0).
        rewrite lift_lift_simplification in H1 by lia.
        rewrite Metatheory.lift_lift_simplification in H1 by lia.
        rewrite Nat.add_comm in H1.
        rewrite Nat.add_comm with (n := #r) in H1.
        simpl length.
        replace (#r + 1 + 1) with (2 + #r) by lia.
        assumption.
  - simpl in H0.
    inversion H0.
  - simpl in H0.
    inversion H0.
  - simpl in H0.
    inversion H0.
  - simpl in H0.
    inversion H0.
  - simpl in H0.
    inversion H0.
  - simpl in H0.
    inversion H0.
Qed.

Local Lemma technical1:
  forall (b: pseudoterm) n k,
  subst (subst (CPS.bound 1) n (CPS.bound 0)) k
    (lift (2 + n) (1 + k) b) =
  subst (CPS.bound 1) (k + n) (lift (2 + n) (1 + k) b).
Proof.
  (* TODO: sigma CAN'T solve this one! Figure out why! *)
  induction b using pseudoterm_deepind; intros.
  (* Case: bound. *)
  - rename n0 into m.
    destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + rewrite Metatheory.lift_bound_ge by lia.
      rewrite Metatheory.subst_bound_gt by lia.
      rewrite Metatheory.subst_bound_gt by lia.
      reflexivity.
    + rewrite Metatheory.lift_bound_lt by lia.
      rewrite Metatheory.subst_bound_eq by lia.
      destruct m.
      * rewrite Metatheory.subst_bound_eq by lia.
        rewrite Metatheory.lift_bound_ge by lia.
        rewrite Metatheory.subst_bound_eq by lia.
        reflexivity.
      * rewrite Metatheory.subst_bound_lt by lia.
        rewrite Metatheory.subst_bound_lt by lia.
        rewrite Metatheory.lift_bound_ge by lia.
        rewrite Nat.add_comm.
        reflexivity.
    + rewrite Metatheory.lift_bound_lt by lia.
      rewrite Metatheory.subst_bound_lt by lia.
      rewrite Metatheory.subst_bound_lt by lia.
      reflexivity.
  (* Case: type. *)
  - rewrite lift_distributes_over_type.
    do 2 rewrite subst_distributes_over_type.
    f_equal.
    induction H; simpl.
    + reflexivity.
    + f_equal; auto.
      repeat rewrite traverse_type_length.
      replace (type_binder x (length l) + S k) with
        (S (type_binder x (length l) + k)) by lia.
      rewrite H; f_equal.
      now rewrite Nat.add_assoc.
  (* Case: jump. *)
  - rewrite lift_distributes_over_jump.
    do 2 rewrite subst_distributes_over_jump.
    f_equal.
    + apply IHb.
    + clear IHb.
      induction H; simpl.
      * reflexivity.
      * f_equal; eauto.
  (* Case: bind. *)
  - rewrite lift_distributes_over_bind.
    do 2 rewrite subst_distributes_over_bind.
    f_equal.
    + apply IHb1.
    + clear IHb1 IHb2.
      induction H; simpl.
      * reflexivity.
      * repeat rewrite traverse_list_length.
        f_equal; auto.
        replace (length l + S k) with (S (length l + k)) by lia.
        rewrite H; f_equal.
        now rewrite Nat.add_assoc.
    + repeat rewrite traverse_list_length.
      rewrite IHb2; f_equal.
      lia.
Qed.

Lemma cbn_simulates_substitution:
  forall e b1,
  cbn_cps e b1 ->
  forall x b2,
  cbn_cps x b2 ->
  forall c,
  cbn_cps (subst x 0 e) c ->
  [SUBST b1 b2 =>* c].
Proof.
  intros e.
  (* To simulate the substitution step of a redex, we perform induction on the
     number of occurrences of the variable in the term. *)
  destruct free_count_is_decidable with e 0 as (k, ?).
  generalize dependent e.
  induction k; intros.
  (* Case: zero. *)
  - (* Our term has the form [b1] { x<k> = [b2] }, where x doesn't appear free
       in [b1]. Thus we just have to apply a single garbage collection step and
       we're left with b1, which is our goal. *)
    apply not_free_count_zero_iff in H.
    replace c with (remove_binding 0 (switch_bindings 0 b1)).
    + apply star_step.
      apply step_gc.
      apply cbn_cps_not_free with e b1 0 in H; auto.
      (* Clearly... *)
      admit.
    + assert (exists f, e = lift 1 0 f) as (f, ?) by admit; subst.
      rewrite subst_lift_simplification in H2 by lia.
      rewrite lift_zero_e_equals_e in H2.
      apply cbn_cps_lift_inversion in H0 as (b, ?, ?); subst.
      assert (b = c) by eauto with cps; subst.
      unfold remove_binding.
      rewrite switch_bindings_characterization.
      now sigma.
  (* Case: succ. *)
  - (* If our term is [b1] { x<k> = [b2] }, with x appearing free in b1, then it
       means there is a context C such that the term is [C[x]] { x<k> = [b2] },
       thus we have [C][x<k>] { ... }, which can perform a single jump leading
       to [C][b2] { ... }. Since the CPS translation is compositional, we can
       proceed by induction with C[b2], which has one less occurrence of x. *)
    edestruct free_usage as (h, ?); eauto with arith; subst.
    rewrite Nat.add_0_r in H, H0, H2.
    assert (exists b1', cbn_cps (h (lift (1 + context_bvars h) 0 x)) b1')
      as (b1', ?) by eauto with cps.
    apply star_trans with (SUBST b1' b2).
    + (* We can apply the linear substitution of the x variable. *)
      edestruct cbn_linear_jump_inversion with (k := 0) as (r, ?, ?); eauto.
      (* According to the inversion, b1 is on the form [C][x<k>]. *)
      simpl in H4; subst.
      (* Also, we can show that b1' contains the expanded term b2. *)
      apply cbn_cps_lift with (i := 1) (k := 0) in H1.
      specialize (H5 _ _ H1).
      rewrite lift_lift_simplification in H5 by lia.
      rewrite Metatheory.lift_lift_simplification in H5 by lia.
      rewrite Nat.add_comm in H5.
      replace b1' with (r (lift (#r + 1) 1 b2)) by eauto with cps.
      (* Now it's just a matter to show that the hygiene conditions guarantee
         that our jump can happen safely. Again, just de Bruijn gimmick! *)
      do 2 rewrite context_switch_bindings_is_sound.
      rewrite Nat.add_0_r.
      rewrite switch_bindings_distributes_over_jump.
      evar (j: pseudoterm).
      evar (b2': pseudoterm).
      replace (switch_bindings #r (CPS.bound (S #r))) with ?j; [
        replace (switch_bindings #r (lift (#r + 1) 1 b2)) with ?b2' |].
      * apply star_ctxjmp.
        reflexivity.
      * simpl.
        rewrite context_switch_bindings_bvars.
        repeat rewrite switch_bindings_characterization.
        rewrite Metatheory.lift_lift_simplification by lia.
        rewrite Metatheory.lift_lift_simplification by lia.
        rewrite Metatheory.lift_bound_lt by lia.
        (* Same term! *)
        replace (S #r + 1) with (2 + #r) by lia.
        replace (1 + (#r + 1)) with (2 + #r) by lia.
        rewrite apply_parameters_cons.
        rewrite apply_parameters_nil.
        apply technical1.
      * rewrite context_switch_bindings_bvars.
        rewrite switch_bindings_characterization.
        rewrite Metatheory.lift_bound_lt by lia.
        rewrite Metatheory.subst_bound_gt by lia.
        reflexivity.
    + (* We have applied the necessary jump for that variable occurrence; we now
         follow by induction by decreasing the number of occurrences. *)
      eapply IHk; eauto.
      * apply free_count_linear_substitution.
        assumption.
      * replace (subst x 0 (h (lift (1 + context_bvars h) 0 x))) with
          (subst x 0 (h (context_bvars h))); auto.
        apply subst_linear_substitution.
Admitted.

Lemma cbn_simulates_beta:
  forall t e x b c,
  cbn_cps (application (abstraction t e) x) b ->
  cbn_cps (subst x 0 e) c ->
  comp t(head) star b c.
Proof.
  intros.
  dependent destruction H.
  replace (lift 1 0 (abstraction t e)) with
    (abstraction t (lift 1 1 e)) in H by now sigma.
  dependent destruction H.
  rewrite lift_lift_simplification in H; auto.
  apply cbn_cps_lift_inversion in H as (b1, ?, ?).
  apply cbn_cps_lift_inversion in H0 as (b2, ?, ?).
  subst; simpl.
  (* At this point, our term stands as:

       k<f> { f<x, k> = [b1] } { k<f> = f<v, k> { v<k> = [b2] } }

     We'll perform two head redexes and two garbage collection steps, resulting
     in the following term:

       [b1] { x<k> = [b2] }

     At this point, we'll proceed to show that the substitution holds. In the
     de Bruijn setting, we notice that [b1] and [b2] both have their variables
     adjusted and got a fresh variable at the closest position. To make up for
     this transformation, [b1] has the closest two variables switched (so 0 is
     the x and 1 is the current continuation), and [b2] has a fresh variable at
     position 1 (the current continuation for [b1]). *)
  admit.
Admitted.

(* TODO: move me! *)

Lemma t_head_bind_left:
  LEFT t(head).
Proof.
  induction 1; eauto with cps.
Qed.

(* TODO: move me! *)

Lemma head_lift:
  forall b c,
  head b c ->
  forall i k,
  head (lift i k b) (lift i k c).
Proof.
  admit.
Admitted.

(* TODO: move me! *)

Lemma t_head_lift:
  forall b c,
  t(head) b c ->
  forall i k,
  t(head) (lift i k b) (lift i k c).
Proof.
  induction 1; intros.
  - apply t_step.
    now apply head_lift.
  - now apply t_trans with (lift i k y).
Qed.

(* TODO: move me! *)

Lemma star_t_head:
  inclusion t(head) star.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve star_t_head: cps.

Lemma cbn_simulates_cbn:
  forall e,
  closed e ->
  forall f,
  cbn e f ->
  forall b c,
  cbn_cps e b ->
  cbn_cps f c ->
  comp t(head) rt(step) b c.
Proof.
  intros until 2.
  apply cbn_whr_iff in H0; auto.
  induction H0; intros.
  - rename b into e, b0 into b.
    now apply cbn_simulates_beta with t e x.
  - dependent destruction H1.
    dependent destruction H2.
    assert (c0 = c); eauto 2 with cps.
    clear H1_0 H2_0; subst.
    apply cbn_cps_lift_inversion in H1_ as (c1, ?, ?).
    apply cbn_cps_lift_inversion in H2_ as (c3, ?, ?).
    subst.
    destruct IHwhr with c1 c3 as (c2, ?, ?); auto.
    + intro.
      specialize (H n).
      now dependent destruction H.
    + eexists.
      * apply t_head_bind_left.
        apply t_head_lift.
        eassumption.
      * apply star_bind_left.
        now apply star_lift.
Qed.

Lemma cbn_simulation:
  forall e f,
  full e f ->
  forall b c,
  cbn_cps e b ->
  cbn_cps f c ->
  [b =>* c].
Proof.
  induction 1; intros.
  (* Case: full_beta. *)
  - rename b into e, b0 into b.
    destruct cbn_simulates_beta with t e x b c as (d, ?, ?).
    + assumption.
    + assumption.
    + apply star_trans with d.
      * now apply star_t_head.
      * assumption.
  (* Case: full_abs. *)
  - dependent destruction H0.
    dependent destruction H1.
    apply cbn_cps_lift_inversion in H0 as (c1, ?, ?).
    apply cbn_cps_lift_inversion in H1 as (c2, ?, ?).
    specialize IHfull with c1 c2; subst.
    apply star_bind_right.
    apply star_lift.
    now apply IHfull.
  (* Case: full_app1. *)
  - dependent destruction H0.
    dependent destruction H1.
    assert (c0 = c); eauto 2 with cps.
    clear H0_0 H1_0; subst.
    apply cbn_cps_lift_inversion in H0_ as (c1, ?, ?).
    apply cbn_cps_lift_inversion in H1_ as (c2, ?, ?).
    specialize IHfull with c1 c2; subst.
    apply star_bind_left.
    apply star_lift.
    now apply IHfull.
  (* Case: full_app2. *)
  - dependent destruction H0.
    dependent destruction H1.
    assert (b0 = b); eauto 2 with cps.
    clear H0_ H1_; subst.
    apply cbn_cps_lift_inversion in H0_0 as (b1, ?, ?).
    apply cbn_cps_lift_inversion in H1_0 as (b2, ?, ?).
    specialize IHfull with b1 b2; subst.
    apply star_bind_right.
    apply star_bind_right.
    apply star_lift.
    now apply IHfull.
Qed.

Lemma termination_nonvalue:
  forall e,
  ~value e ->
  whnf e ->
  forall c,
  cbn_cps e c ->
  exists2 k,
  converges c (1 + k) & free k e.
Proof.
  induction e; intros.
  - exfalso.
    apply H.
    constructor.
  - exfalso.
    apply H.
    constructor.
  - destruct e1.
    + exists n.
      * dependent destruction H1.
        dependent destruction H1_.
        do 2 constructor.
      * intro.
        dependent destruction H2.
        dependent destruction H2_.
        contradiction.
    + exfalso.
      eapply H0.
      constructor.
    + clear IHe2.
      dependent destruction H1.
      edestruct cbn_cps_lift_inversion with (b := b); eauto.
      subst; rename x into b.
      edestruct IHe1.
      * inversion 1.
      * eapply whnf_application_left.
        eassumption.
      * eassumption.
      * (* TODO: please refactor me. *)
        rename x into k; exists k.
        constructor.
        eapply converges_lift.
        eassumption.
        rewrite lift_bound_ge; try lia.
        constructor; lia.
        intro; apply H3.
        dependent destruction H4.
        assumption.
    + dependent destruction H1.
      inversion H1_.
    + dependent destruction H1.
      inversion H1_.
    + dependent destruction H1.
      inversion H1_.
    + dependent destruction H1.
      inversion H1_.
    + dependent destruction H1.
      inversion H1_.
  - inversion H1.
  - inversion H1.
  - inversion H1.
  - inversion H1.
  - inversion H1.
Qed.

Lemma termination:
  forall e,
  normal cbn e ->
  forall c,
  cbn_cps e c ->
  exists k,
  converges c k.
Proof.
  intros.
  destruct value_dec with e as [ ?H | ?H ].
  (* Case: e is a value. *)
  - destruct H1.
    + (* If this is a free variable, we converge to it. *)
      dependent destruction H0.
      exists (S n).
      constructor.
    + (* If this is an abstraction, we converge to the fresh k. *)
      dependent destruction H0.
      eexists 0.
      do 2 constructor.
    + inversion H0.
    + inversion H0.
  (* Case: e is not a value. *)
  - destruct termination_nonvalue with e c.
    + assumption.
    + intros f ?.
      apply H with f.
      apply cbn_whr.
      assumption.
    + assumption.
    + exists (1 + x).
      assumption.
Qed.

Lemma normal_form_preservation:
  forall e,
  normal full e ->
  forall c,
  cbn_cps e c ->
  normal step c.
Proof.
  admit.
Admitted.

(* -------------------------------------------------------------------------- *)

Definition cbn_terminates (e: term): Prop :=
  exists2 v,
  value v & rt(cbn) e v.

Lemma sn_cbn_terminates:
  forall e,
  cbn_terminates e -> SN cbn e.
Proof.
  intros.
  destruct H as (v, ?, ?).
  apply clos_rt_rt1n in H0.
  induction H0.
  - rename x into e.
    constructor; intros f ?.
    exfalso.
    eapply cbn_implies_nonvalue with e f; auto.
  - clear H1.
    constructor; intros w ?.
    assert (y = w).
    + apply cbn_is_a_function with x; auto.
    + subst; firstorder.
Qed.

Lemma adequacy_only_if:
  forall e,
  closed e ->
  forall c,
  cbn_cps e c ->
  cbn_terminates e ->
  cps_terminates c.
Proof.
  intros.
  generalize dependent c.
  apply sn_cbn_terminates in H1.
  induction H1 using SN_ind.
  destruct cbn_is_decidable with x; intros.
  - rename x into e; clear H1 H2.
    destruct termination with e c as (k, ?).
    + assumption.
    + assumption.
    + exists k, c; auto with cps.
  - rename c into b.
    destruct e as (y, ?).
    assert (exists c, cbn_cps y c) as (c, ?); eauto with cps.
    assert [b =>* c].
    + apply cbn_simulation with x y; auto.
      apply full_cbn; auto.
    + destruct H2 with y c as (k, ?).
      * apply t_step.
        assumption.
      * (* Reduction can't introduce free variables! *)
        admit.
      * assumption.
      * destruct H6 as (d, ?, ?).
        exists k, d; eauto with cps.
Admitted.

Lemma adequacy_if:
  forall e,
  closed e ->
  forall b,
  cbn_cps e b ->
  cps_terminates b ->
  cbn_terminates e.
Proof.
  intros.
  (* We proceed by induction on the number of head steps until normal form. *)
  apply cps_terminates_implies_sn_head in H1.
  assert (exists2 c, [b =>* c] & cbn_cps e c) as (c, ?, ?) by eauto with cps.
  clear H0.
  generalize dependent c.
  generalize dependent e.
  induction H1 using SN_ind; intros.
  (* Do we still have a redex? *)
  destruct cbn_is_decidable with e as [ ?H | (f, ?H) ].
  - (* No more redexes, so we are done. *)
    exists e; eauto with cps.
    now apply closed_normal_cbn_implies_value.
  - rename x into b.
    assert (exists d, cbn_cps f d) as (d, ?) by eauto with cps.
    assert (comp t(head) star c d) as (x, ?, ?) by
      now apply cbn_simulates_cbn with e f.
    (* Ok, here's the catch! By H1, we know that a head step has to change what
       is in head position of a term. We can check that b =>* d and apply the
       factorization lemma. Since inner reduction can't ever change the head of
       a term, then this means that, in this case, head reduction is essential
       and in order to go from b to d we can indeed start with a positive number
       of head steps. *)
    assert [b =>* d] by eauto with cps.
    apply star_characterization in H8.
    apply shrinking_may_be_postponed in H8 as (z, ?, ?).
    + apply factorization in H8 as (y, ?, ?).
      apply rt_characterization in H8.
      destruct H8.
      * edestruct H2 with y f d as (g, ?, ?).
        (* TODO: refactor, please... *)
        assumption.
        (* Sure, from H and H4, reduction can't introduce free variables. *)
        admit.
        (* Clearly, from H9 and H10. *)
        admit.
        assumption.
        (* Now we can terminate! *)
        exists g; eauto with cps.
      * exfalso.
        (* Ok, H6 implies that b and d have different heads, and from H9 and H10
           we have that they are the same. So we have a contradiction here. *)
        admit.
    + exact smol_is_shrinking.
Admitted.

Theorem adequacy:
  forall e,
  closed e ->
  forall c,
  cbn_cps e c ->
  cbn_terminates e <-> cps_terminates c.
Proof.
  split; intros.
  - apply adequacy_only_if with e; auto.
  - apply adequacy_if with c; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma cbn_cps_is_compositional:
  forall b1 b2 e1 e2,
  cbn_cps e1 b1 ->
  cbn_cps e2 b2 ->
  [b1 ~~ b2] ->
  forall (h: context) c1 c2,
  cbn_cps (h e1) c1 ->
  cbn_cps (h e2) c2 ->
  [c1 ~~ c2].
Proof.
  induction h; simpl; intros.
  - assert (b1 = c1); eauto 2 with cps.
    assert (b2 = c2); eauto 2 with cps.
    subst; assumption.
  - dependent destruction H2.
    dependent destruction H3.
    apply cbn_cps_lift_inversion in H2 as (d1, ?, ?).
    apply cbn_cps_lift_inversion in H3 as (d2, ?, ?).
    subst.
    apply barb_bind_right.
    apply barb_lift.
    apply IHh; auto.
  - dependent destruction H2.
    dependent destruction H3.
    assert (c0 = c); eauto 2 with cps.
    subst; clear H2_0 H3_0.
    apply cbn_cps_lift_inversion in H2_ as (d1, ?, ?).
    apply cbn_cps_lift_inversion in H3_ as (d2, ?, ?).
    subst.
    apply barb_bind_left.
    apply barb_lift.
    apply IHh; auto.
  - dependent destruction H2.
    dependent destruction H3.
    assert (b0 = b); eauto 2 with cps.
    subst; clear H2_ H3_.
    apply cbn_cps_lift_inversion in H2_0 as (d1, ?, ?).
    apply cbn_cps_lift_inversion in H3_0 as (d2, ?, ?).
    subst.
    apply barb_bind_right.
    apply barb_bind_right.
    apply barb_lift.
    apply IHh; auto.
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - inversion H2.
  - inversion H2.
Qed.

Local Hint Resolve cbn_cps_is_compositional: cps.

Definition cbn_equivalent e f: Prop :=
  forall h: context,
  closed (h e) ->
  closed (h f) ->
  cbn_terminates (h e) <-> cbn_terminates (h f).

Corollary denotational_soundness:
  forall e b,
  cbn_cps e b ->
  forall f c,
  cbn_cps f c ->
  [b ~~ c] -> cbn_equivalent e f.
Proof.
  split; intros.
  - assert (exists b', cbn_cps (h e) b') as (b', ?); auto with cps.
    assert (exists c', cbn_cps (h f) c') as (c', ?); auto with cps.
    apply adequacy with c'.
    + assumption.
    + assumption.
    + apply adequacy with (h e) b' in H4.
      * assert [b' ~~ c']; eauto 2 with cps.
        apply cps_terminates_barb with b'; auto.
      * assumption.
      * assumption.
  - assert (exists b', cbn_cps (h e) b') as (b', ?); auto with cps.
    assert (exists c', cbn_cps (h f) c') as (c', ?); auto with cps.
    apply adequacy with b'.
    + assumption.
    + assumption.
    + apply adequacy with (h f) c' in H4.
      * assert [b' ~~ c']; eauto 2 with cps.
        apply cps_terminates_barb with c'; auto with cps.
      * assumption.
      * assumption.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma cbn_cps_subterm_wn:
  forall e b,
  cbn_cps e b ->
  forall f,
  subterm f e ->
  forall c,
  cbn_cps f c ->
  WN beta b -> WN beta c.
Proof.
  intros.
  (* This is perhaps not the best approach, computationally speaking, as we rely
     a lot on uniform normalization, and there are certainly more efficient ways
     to compute this, but still... it's a somewhat simple way to prove it. *)
  apply uniform_normalization in H2.
  destruct H0.
  (* Case: inside abstraction. *)
  - dependent destruction H.
    apply cbn_cps_lift_inversion in H.
    destruct H; subst; rename b0 into e.
    assert (x = c); eauto with cps; subst.
    apply uniform_normalization.
    eapply SN_preimage with (f := fun c => bind _ _ (lift 1 2 c));
    eauto; intros.
    apply beta_bind_right.
    apply beta_lift.
    assumption.
  (* Case: inside left hand side of application. *)
  - dependent destruction H.
    apply cbn_cps_lift_inversion in H.
    destruct H; subst; rename x0 into b.
    assert (c0 = b); eauto with cps; subst.
    apply uniform_normalization.
    eapply SN_preimage with (f := fun b => bind (lift 1 1 b) _ _);
    eauto; intros.
    apply beta_bind_left.
    apply beta_lift.
    assumption.
  (* Case: inside right hand side of application. *)
  - dependent destruction H.
    apply cbn_cps_lift_inversion in H0.
    destruct H0; subst; rename x0 into c.
    assert (c0 = c); eauto with cps; subst.
    apply uniform_normalization.
    eapply SN_preimage with (f := fun c => bind _ _ (bind _ _ (lift 2 1 c)));
    eauto; intros.
    apply beta_bind_right.
    apply beta_bind_right.
    apply beta_lift.
    assumption.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
Qed.

Lemma foo:
  forall y x,
  t(subterm) y x ->
  forall z,
  t(full) y z ->
  exists2 w, t(full) x w & t(subterm) z w.
Proof.
  intros.
  eapply transitive_closure_preserves_diagram; eauto with cps.
  destruct 1; eauto with cps.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma bar:
  forall e,
  SN full e ->
  SN (union full (transp subterm)) e.
Proof.
  induction 1 using SN_ind.
  induction subterm_is_well_founded with x.
  clear H0.
  assert (forall y : term,
     subterm y x ->
     SN full y ->
     SN (union full (transp subterm)) y).
  - intros.
    apply H1; clear H1; auto; intros.
    rename y0 into z.
    assert (exists2 w, t(full) x w & subterm z w) as (w, ?, ?).
    + edestruct foo; eauto with cps.
      admit.
    + specialize (H2 w H4).
      destruct H2.
      apply H2; right.
      assumption.
  - clear H1.
    constructor; destruct 1.
    + apply H2; auto with cps.
    + apply H0; auto with cps.
      admit.
Admitted.

Lemma lambda_sn_implies_beta_normal_form:
  forall e,
  SN full e ->
  forall b,
  cbn_cps e b -> WN beta b.
Proof.
  induction 1 using SN_ind; intros.
  destruct x.
  - clear H2.
    dependent destruction H0.
    eexists.
    + eauto with cps.
    + inversion 1.
  - dependent destruction H0.
    apply cbn_cps_lift_inversion in H0 as (c, ?, ?); subst.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Theorem preservation_of_strong_normalization:
  forall e,
  SN full e ->
  forall b,
  cbn_cps e b -> SN step b.
Proof.
  intros.
  apply SN_subset with (union beta smol).
  - apply step_characterization.
  - apply shrinking_preserves_strong_normalization.
    + apply smol_is_shrinking.
    + apply uniform_normalization.
      apply lambda_sn_implies_beta_normal_form with e; auto.
Qed.

(* -------------------------------------------------------------------------- *)

Fixpoint cbn_type (t: type): pseudoterm :=
  match t with
  | base =>
    negation [CPS.base]
  | arrow t s =>
    negation [negation [cbn_type s; negation [cbn_type t]]]
  end.

Definition cbn_env (g: env): list pseudoterm :=
  map (fun t => CPS.negation [cbn_type t]) g.

Fixpoint cbn_type_alt (t: type): pseudoterm :=
  match t with
  | base =>
    CPS.base
  | arrow t s =>
    negation [negation [cbn_type_alt s]; negation [negation [cbn_type_alt t]]]
  end.

Definition cbn_env_alt (g: env): list pseudoterm :=
  map (fun t => CPS.negation [CPS.negation [cbn_type_alt t]]) g.

Goal
  forall g,
  cbn_env g = cbn_env_alt g.
Proof.
  induction g; simpl.
  - reflexivity.
  - f_equal.
    + clear IHg g; do 2 f_equal.
      induction a; simpl.
      * reflexivity.
      * rewrite IHa1, IHa2.
        reflexivity.
    + assumption.
Qed.

Lemma cbn_type_association:
  forall t g n,
  item t g n ->
  item (CPS.negation [cbn_type t]) (cbn_env g) n.
Proof.
  induction 1; simpl; intros.
  - constructor.
  - now constructor.
Qed.

Lemma simple_cbn_type:
  forall t,
  simple (cbn_type t).
Proof.
  induction t; simpl.
  - repeat constructor.
  - now repeat constructor.
Qed.

Global Hint Resolve simple_cbn_type: cps.

Lemma valid_env_cbn_env:
  forall g,
  valid_env (cbn_env g).
Proof.
  induction g; simpl.
  - constructor.
  - repeat constructor; auto with cps.
Qed.

Global Hint Resolve valid_env_cbn_env: cps.

Section TypePreservation.

  Local Notation N ts :=
    (negation ts).

  Local Notation DN ts :=
    (N [N ts]).

  (* To avoid complications while dealing with both untyped and typed terms, as
     we have defined the CPS translation as a function into terms without the
     proper type annotations, we will simply assume that a term that is untyped,
     i.e., in which the binders are marked with void instead of a proper type,
     can be typed if we add the type annotations required. TODO: how could we
     properly fix this...? *)

  Hypothesis ignore_void_typing:
    forall g b ts c,
    TypeSystem.typing g (bind b ts c) void ->
    TypeSystem.typing g (bind b (repeat void (length ts)) c) void.

  Theorem cbn_type_preservation:
    forall g e t,
    typing g e t ->
    forall c,
    cbn_cps e c ->
    TypeSystem.typing (cbn_type t :: cbn_env g) c void.
  Proof.
    induction 1; simpl; intros.
    (* Case: bound var. *)
    - dependent destruction H0.
      apply cbn_type_association in H.
      constructor 2 with [cbn_type t].
      + constructor.
        * auto with cps.
        * now constructor.
      + repeat constructor; auto with cps.
    (* Case: abstraction. *)
    - dependent destruction H0.
      apply cbn_cps_lift_inversion in H0 as (c, ?, ?); subst.
      apply ignore_void_typing with (ts := [cbn_type s; N [cbn_type t]]).
      constructor; simpl.
      + constructor 2 with [N [cbn_type s; N [cbn_type t]]].
        * repeat constructor; auto with cps.
        * repeat constructor; auto with cps.
      + eapply typing_lift with (us := [DN [cbn_type s; N [cbn_type t]]]).
        * now apply IHtyping.
        * repeat constructor; auto with cps.
        * repeat constructor.
    (* Case: application. *)
    - dependent destruction H1.
      apply cbn_cps_lift_inversion in H1_ as (b', ?, ?); subst.
      apply cbn_cps_lift_inversion in H1_0 as (c', ?, ?); subst.
      rename b' into b, c' into c.
      apply ignore_void_typing with (ts := [N [cbn_type s; N [cbn_type t]]]).
      constructor; simpl.
      + eapply typing_lift with (us := [cbn_type s]).
        * now apply IHtyping1.
        * auto with cps.
        * repeat constructor.
      + apply ignore_void_typing with (ts := [cbn_type t]).
        constructor; simpl.
        * repeat econstructor; auto with cps.
        * eapply typing_lift with
            (us := [N [cbn_type s; N [cbn_type t]]; cbn_type s]).
          (* TODO: refactor me, will you? *)
          now apply IHtyping2.
          repeat constructor; auto with cps.
          repeat constructor.
  Qed.

  Corollary cbn_strong_normalization:
    forall g e t,
    typing g e t ->
    SN full e.
  Proof.
    intros.
    assert (exists b, cbn_cps e b) as (b, ?) by eauto with cps.
    apply cbn_type_preservation with (c := b) in H; auto.
    apply strong_normalization in H.
    generalize dependent e.
    induction H using SN_ind; intros.
    constructor; intros f ?.
    assert (exists c, cbn_cps f c) as (c, ?) by eauto with cps.
    apply H2 with c.
    - (* TODO: Oops, simulation shouldn't be reflexive! *)
      assert [x =>* c].
      * now apply cbn_simulation with e f.
      * apply rt_characterization in H4.
        destruct H4; auto.
        (* Can't happen! *)
        admit.
    - assumption.
  Admitted.

End TypePreservation.
