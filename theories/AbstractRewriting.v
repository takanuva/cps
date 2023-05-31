(******************************************************************************)
(*   Copyright (c) 2019--2022 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Set Implicit Arguments.
Require Import Arith.
Require Import Equality.
Require Export Relations.
Require Import Local.Prelude.

(** ** Relations *)

Notation "'r(' R )" := (clos_refl _ R)
  (format "'r(' R )"): type_scope.

Notation "'t(' R )" := (clos_trans _ R)
  (format "'t(' R )"): type_scope.

Notation "'rt(' R )" := (clos_refl_trans _ R)
  (format "'rt(' R )"): type_scope.

Notation "'rst(' R )" := (clos_refl_sym_trans _ R)
  (format "'rst(' R )"): type_scope.

Global Hint Constructors clos_refl: cps.
Global Hint Constructors clos_trans: cps.
Global Hint Constructors clos_refl_trans: cps.
Global Hint Constructors clos_refl_sym_trans: cps.

Arguments transp {A}.

Global Hint Unfold transp: cps.

Arguments union {A}.

Global Hint Unfold union: cps.

Arguments same_relation {A}.

Global Hint Unfold same_relation: cps.

Arguments inclusion {A}.

Global Hint Unfold inclusion: cps.

Arguments reflexive {A}.

Global Hint Unfold reflexive: cps.

Arguments symmetric {A}.

Global Hint Unfold symmetric: cps.

Arguments transitive {A}.

Global Hint Unfold transitive: cps.

Arguments equivalence {A}.

Global Hint Resolve equiv_refl: cps.
Global Hint Resolve equiv_sym: cps.
Global Hint Resolve equiv_trans: cps.
Global Hint Constructors equivalence: cps.

(* Generalize the idea of a square commutation diagram. *)

Definition diagram {A B C D} (R: A -> B -> Prop)
                             (S: A -> C -> Prop)
                             (T: B -> D -> Prop)
                             (U: C -> D -> Prop): Prop :=
  forall x y,
  R x y ->
  forall z,
  S x z ->
  exists2 w,
  T y w & U z w.

Global Hint Unfold diagram: cps.

(* Relations R and S commute with each other. *)

Definition commutes {T} (R: relation T) (S: relation T): Prop :=
  diagram R S S R.

Global Hint Unfold commutes: cps.

(* Relation R commutes with itself. *)

Definition diamond {T} (R: relation T): Prop :=
  commutes R R.

Global Hint Unfold diamond: cps.

(* Relation composition. *)

Definition comp {A} {B} {C} R S: A -> C -> Prop :=
  fun a c =>
    exists2 b: B,
    R a b & S b c.

Global Hint Unfold comp: cps.

Section Relations.

  Variable T: Type.
  Variable R: relation T.

  Lemma clos_t_clos_rt:
    inclusion t(R) rt(R).
  Proof.
    induction 1; eauto with cps.
  Qed.

  Hint Resolve clos_t_clos_rt: cps.

  Lemma rt_characterization:
    same_relation rt(R) r(t(R)).
  Proof.
    split; intros x y ?.
    - induction H.
      + eauto with cps.
      + eauto with cps.
      + destruct IHclos_refl_trans1;
        destruct IHclos_refl_trans2;
        eauto with cps.
    - destruct H; eauto with cps.
  Qed.

  Lemma t_characterization:
    same_relation t(R) (comp R rt(R)).
  Proof.
    split; intros x y ?.
    - apply clos_trans_t1n_iff in H.
      destruct H.
      + exists y; auto with cps.
      + apply clos_trans_t1n_iff in H0.
        exists y; auto.
        apply clos_t_clos_rt; auto.
    - destruct H as (w, ?, ?).
      apply rt_characterization in H0.
      destruct H0; eauto with cps.
  Qed.

  Lemma r_and_t_closures_commute:
    same_relation r(t(R)) t(r(R)).
  Proof.
    split; intros x y ?.
    - destruct H.
      + induction H; eauto with cps.
      + auto with cps.
    - induction H.
      + destruct H; auto with cps.
      + destruct IHclos_trans1; destruct IHclos_trans2; eauto with cps.
  Qed.

  Lemma rt_unequal_implies_t:
    forall a b,
    a <> b ->
    rt(R) a b -> t(R) a b.
  Proof.
    intros.
    apply rt_characterization in H0.
    destruct H0.
    - assumption.
    - exfalso.
      contradiction.
  Qed.

  Inductive clos_trans_cnt: nat -> relation T :=
    | tc_step x y:
      R x y -> clos_trans_cnt 1 x y
    | tc_trans x y z n m:
      clos_trans_cnt n x y ->
      clos_trans_cnt m y z ->
      clos_trans_cnt (n + m) x z.

  (*
  Inductive clos_trans_1n_cnt: nat -> relation T :=
    | t1nc_step x y:
      R x y ->
      clos_trans_1n_cnt 1 x y
    | t1nc_trans x y z n:
      R x y ->
      clos_trans_1n_cnt n y z ->
      clos_trans_1n_cnt (S n) x z.

  Inductive clos_trans_n1_cnt: nat -> relation T :=
    | tn1c_step x y:
      R x y ->
      clos_trans_n1_cnt 1 x y
    | tn1c_trans x y z n:
      R y z ->
      clos_trans_n1_cnt n x y ->
      clos_trans_n1_cnt (S n) x z.
  *)

  Lemma clos_trans_trans_cnt_iff:
    forall a b,
    t(R) a b <-> (exists n, clos_trans_cnt n a b).
  Proof.
    split; intros.
    - induction H.
      + exists 1.
        constructor; auto.
      + destruct IHclos_trans1 as (n, ?H).
        destruct IHclos_trans2 as (m, ?H).
        exists (n + m).
        econstructor 2; eauto.
    - destruct H.
      induction H.
      + constructor; auto.
      + econstructor 2; eauto.
  Qed.

  (*
  Lemma clos_t1n_trans_cnt:
    forall n x y,
    clos_trans_1n_cnt n x y -> clos_trans_cnt n x y.
  Proof.
    induction 1.
    - constructor; auto.
    - replace (S n) with (1 + n); auto.
      econstructor 2.
      + constructor; eauto.
      + assumption.
  Qed.

  Lemma clos_trans_t1n_cnt:
    forall n x y,
    clos_trans_cnt n x y -> clos_trans_1n_cnt n x y.
  Proof.
    induction 1.
    - constructor; auto.
    - clear H H0.
      generalize dependent m.
      induction IHclos_trans_cnt1; intros.
      + econstructor 2; eauto.
      + replace (S n + m) with (1 + (n + m)); auto.
        econstructor 2; eauto.
  Qed.

  Lemma clos_trans_t1n_cnt_iff:
    forall n x y,
    clos_trans_cnt n x y <-> clos_trans_1n_cnt n x y.
  Proof.
    split.
    - apply clos_trans_t1n_cnt.
    - apply clos_t1n_trans_cnt.
  Qed.

  Lemma clos_tn1_trans_cnt:
    forall n x y,
    clos_trans_n1_cnt n x y -> clos_trans_cnt n x y.
  Proof.
    induction 1.
    - constructor; auto.
    - replace (S n) with (1 + n); auto.
      replace (1 + n) with (n + 1); auto with arith.
      econstructor 2.
      + eassumption.
      + constructor; auto.
  Qed.

  Lemma clos_trans_tn1_cnt:
    forall n x y,
    clos_trans_cnt n x y -> clos_trans_n1_cnt n x y.
  Proof.
    induction 1.
    - constructor; auto.
    - clear H H0.
      generalize dependent n.
      induction IHclos_trans_cnt2; intros.
      + rewrite Nat.add_comm.
        econstructor 2; eauto.
      + rename n0 into m.
        replace (m + S n) with (1 + (m + n)); auto with arith.
        econstructor 2; eauto.
  Qed.

  Lemma clos_trans_tn1_cnt_iff:
    forall n x y,
    clos_trans_cnt n x y <-> clos_trans_n1_cnt n x y.
  Proof.
    split.
    - apply clos_trans_tn1_cnt.
    - apply clos_tn1_trans_cnt.
  Qed.

  Goal
    forall P: nat -> T -> T -> Prop,
    (forall x y, R x y -> P 1 x y) ->
    (forall x y z n,
       R x y -> clos_trans_cnt n y z -> P n y z -> P (S n) x z) ->
    forall n x y,
    clos_trans_cnt n x y -> P n x y.
  Proof.
    intros.
    apply clos_trans_t1n_cnt_iff in H1.
    induction H1.
    - apply H.
      assumption.
    - eapply H0.
      + eassumption.
      + apply clos_trans_t1n_cnt_iff in H2.
        assumption.
      + assumption.
  Qed.

  Goal
    forall P : nat -> T -> T -> Prop,
    (forall x y, R x y -> P 1 x y) ->
    (forall x y z n,
       R y z -> clos_trans_cnt n x y -> P n x y -> P (S n) x z) ->
    forall n x y,
    clos_trans_cnt n x y -> P n x y.
  Proof.
    intros.
    apply clos_trans_tn1_cnt_iff in H1.
    induction H1.
    - apply H.
      assumption.
    - eapply H0.
      + eassumption.
      + apply clos_trans_tn1_cnt_iff in H2.
        assumption.
      + assumption.
  Qed.
  *)

End Relations.

Section Confluency.

  Lemma generalized_strip_lemma:
    forall A: Type,
    forall B: Type,
    forall R: A -> B -> Prop,
    forall S: A -> A -> Prop,
    forall P: B -> B -> Prop,
    forall Q: A -> B -> Prop,
    (* Q is a subset of R. *)
    (forall x y, Q x y -> R x y) ->
    diagram R S P Q -> diagram R t(S) t(P) Q.
  Proof.
    intros; intros x y ? z ?.
    generalize dependent y.
    induction H2.
    (* Case: step. *)
    - rename y into z; intros y ?.
      destruct H0 with x y z as (w, ?, ?); auto.
      exists w; auto with cps.
    (* Case: trans. *)
    - intros w ?.
      destruct IHclos_trans1 with w as (v, ?, ?); auto.
      destruct IHclos_trans2 with v as (u, ?, ?); auto.
      exists u; eauto with cps.
  Qed.

  Variable T: Type.

  Lemma strip_lemma:
    forall R: relation T,
    forall S: relation T,
    commutes R S -> commutes R t(S).
  Proof.
    intros.
    apply generalized_strip_lemma; auto with cps.
  Qed.

  Lemma transitive_closure_preserves_diagram:
    forall R: relation T,
    forall S: relation T,
    forall P: relation T,
    forall Q: relation T,
    inclusion t(P) t(S) ->
    inclusion Q R ->
    diagram R S P Q -> diagram t(R) t(S) t(P) t(Q).
  Proof.
    induction 4; intros.
    (* Case: step. *)
    - edestruct generalized_strip_lemma as (w, ?, ?).
      + exact H0.
      + exact H1.
      + eassumption.
      + eassumption.
      + exists w; auto with cps.
    (* Case: trans. *)
    - rename z0 into w.
      destruct IHclos_trans1 with w as (v, ?, ?); auto.
      destruct IHclos_trans2 with v as (u, ?, ?); auto.
      exists u; eauto with cps.
  Qed.

  Lemma transitive_closure_preserves_commutation:
    forall R: relation T,
    forall S: relation T,
    commutes R S -> commutes t(R) t(S).
  Proof.
    intros.
    apply transitive_closure_preserves_diagram; auto with cps.
  Qed.

  Lemma reflexive_closure_preserves_diagram:
    forall R: relation T,
    forall S: relation T,
    forall P: relation T,
    forall Q: relation T,
    inclusion S P ->
    inclusion R Q ->
    diagram R S P Q -> diagram r(R) r(S) r(P) r(Q).
  Proof.
    intros; intros x y ? z ?.
    destruct H2; destruct H3.
    - rename y0 into z.
      destruct H1 with x y z as (w, ?, ?); auto.
      exists w; auto with cps.
    - exists y; auto with cps.
    - exists y; auto with cps.
    - exists x; auto with cps.
  Qed.

  Lemma reflexive_closure_preserves_commutation:
    forall R: relation T,
    forall S: relation T,
    commutes R S -> commutes r(R) r(S).
  Proof.
    intros.
    apply reflexive_closure_preserves_diagram; auto with cps.
  Qed.

  Variable R: relation T.

  Definition confluent: Prop :=
    diamond rt(R).

  Definition church_rosser: Prop :=
    forall x y,
    rst(R) x y ->
    exists2 z,
    rt(R) x z & rt(R) y z.

  Lemma confluence_implies_church_rosser:
    confluent -> church_rosser.
  Proof.
    induction 2.
    (* Case: step. *)
    - exists y; auto with cps.
    (* Case: refl. *)
    - exists x; auto with cps.
    (* Case: sym. *)
    - destruct IHclos_refl_sym_trans as (z, ?, ?).
      exists z; auto.
    (* Case: trans. *)
    - destruct IHclos_refl_sym_trans1 as (w, ?, ?).
      destruct IHclos_refl_sym_trans2 as (v, ?, ?).
      destruct H with y w v as (u, ?, ?); auto with cps.
      exists u; eauto with cps.
  Qed.

End Confluency.

Section HindleyRosen.

  Variable T: Type.

  Variable R: relation T.
  Variable S: relation T.

  Hypothesis R_is_confluent: confluent R.
  Hypothesis S_is_confluent: confluent S.
  Hypothesis R_and_S_commute: commutes rt(R) rt(S).

  Local Lemma rt_union_characterization:
    same_relation rt(union R S) rt(union rt(R) rt(S)).
  Proof.
    split; induction 1.
    - destruct H; auto with cps.
    - auto with cps.
    - eauto with cps.
    - destruct H.
      + induction H; eauto with cps.
      + induction H; eauto with cps.
    - eauto with cps.
    - eauto with cps.
  Qed.

  Lemma hindley_rosen:
    confluent (union R S).
  Proof.
    (* The proof follows by diagram chasing. *)
    assert (diamond (union rt(R) rt(S))).
    - intros x y ? z ?.
      destruct H; destruct H0.
      + destruct R_is_confluent with x y z as (w, ?, ?); auto.
        exists w; auto with cps.
      + destruct R_and_S_commute with x y z as (w, ?, ?); auto.
        exists w; auto with cps.
      + destruct R_and_S_commute with x z y as (w, ?, ?); auto.
        exists w; auto with cps.
      + destruct S_is_confluent with x y z as (w, ?, ?); auto.
        exists w; auto with cps.
    - apply transitive_closure_preserves_commutation in H.
      apply reflexive_closure_preserves_commutation in H.
      intros x y ? z ?.
      destruct H with x y z as (w, ?, ?).
      + apply rt_characterization.
        apply rt_union_characterization.
        assumption.
      + apply rt_characterization.
        apply rt_union_characterization.
        assumption.
      + exists w.
        * apply rt_union_characterization.
          apply rt_characterization.
          assumption.
        * apply rt_union_characterization.
          apply rt_characterization.
          assumption.
  Qed.

  (* TODO: check if this is the correct name. *)

  Definition strong_commutation: Prop :=
    forall x y,
    R x y ->
    forall z,
    S x z ->
    exists2 w,
    rt(S) y w & r(R) z w.

  Hypothesis strongly_commutes: strong_commutation.

  Local Lemma strong_strip_lemma:
    commutes r(R) rt(S).
  Proof.
    intros x y ? z ?.
    generalize dependent y.
    apply clos_rt_rt1n_iff in H0.
    induction H0; intros.
    - destruct H.
      + exists y; auto with cps.
      + exists x; auto with cps.
    - rename y0 into w.
      destruct H1.
      + rename y0 into w.
        destruct strongly_commutes with x w y as (u, ?, ?); auto.
        destruct IHclos_refl_trans_1n with u as (v, ?, ?); auto.
        exists v; eauto with cps.
      + destruct IHclos_refl_trans_1n with y as (w, ?, ?); auto with cps.
        exists w; eauto with cps.
  Qed.

  Lemma strong_commutation_implies_commutation:
    commutes rt(R) rt(S).
  Proof.
    intros until 1.
    apply clos_rt_rt1n_iff in H.
    induction H; intros.
    - exists z; auto with cps.
    - rename z0 into w.
      destruct strong_strip_lemma with x y w as (u, ?, ?); eauto with cps.
      destruct IHclos_refl_trans_1n with u as (v, ?, ?); auto.
      exists v; destruct H3; eauto with cps.
  Qed.

End HindleyRosen.

(*

(* TODO: review me, please. This might be a nice way to generalize the proof
   for tidying reductions! Of course I've already seem variants of the lemma
   written like this, using an indexed family instead of a single relation. *)

Section Test.

  Variable T: Type.
  Variable L: Type.
  Variable X: L -> relation T.

  Hypothesis foo:
    forall l1 l2,
    (* We don't really care which order! *)
    strong_commutation (X l1) (X l2) \/
      strong_commutation (X l2) (X l1).

  (* TODO: move me, please? *)

  Lemma commutes_sym:
    forall R S,
    @commutes T R S -> @commutes T S R.
  Proof.
    intros R S ? x y ? z ?.
    destruct H with x z y as (w, ?, ?); auto.
    exists w; auto.
  Qed.

  Lemma bar:
    forall l1 l2,
    commutes rt(X l1) rt(X l2).
  Proof.
    intros.
    destruct foo with l1 l2.
    - apply strong_commutation_implies_commutation.
      assumption.
    - apply commutes_sym.
      apply strong_commutation_implies_commutation.
      assumption.
  Qed.

  Goal
    forall l,
    confluent (X l).
  Proof.
    intros.
    apply bar.
  Qed.

  Definition Y: relation T :=
    fun a b =>
      exists l, X l a b.

  Definition Z: relation T :=
    fun a b =>
      exists l, rt(X l) a b.

  Local Hint Unfold Y: cps.
  Local Hint Unfold Z: cps.

  Lemma baz:
    diamond Z.
  Proof.
    intros x y (l1, ?) z (l2, ?).
    destruct bar with l1 l2 x y z as (w, ?, ?); eauto.
    exists w; eauto with cps.
  Qed.

  Lemma aaa:
    same_relation r(t(Z)) rt(Y).
  Proof.
    split; intros x y ?.
    - destruct H.
      + induction H; eauto with cps.
        destruct H as (l, ?).
        induction H; eauto with cps.
      + auto with cps.
    - induction H.
      + destruct H as (l, ?).
        eauto 6 with cps.
      + eauto with cps.
      + destruct IHclos_refl_trans1;
        destruct IHclos_refl_trans2;
        eauto with cps.
  Qed.

  Lemma qux:
    confluent Y.
  Proof.
    assert (diamond r(t(Z))).
    - destruct 1; destruct 1; eauto with cps.
      rename y0 into z.
      edestruct transitive_closure_preserves_diagram as (w, ?, ?).
      + intros a b ?.
        exact H1.
      + intros a b ?.
        exact H1.
      + exact baz.
      + exact H.
      + exact H0.
      + eauto with cps.
    - intros x y ? z ?.
      destruct H with x y z as (w, ?, ?).
      + apply aaa; auto.
      + apply aaa; auto.
      + exists w.
        * apply aaa; auto.
        * apply aaa; auto.
  Qed.

End Test.

*)

Section Normalization.

  Variable T: Type.

  Definition SN (R: relation T) :=
    (Acc (transp R)).

  Variable R: relation T.

  Definition normal a: Prop :=
    forall b, ~R a b.

  Definition WN a: Prop :=
    exists2 b, rt(R) a b & normal b.

  Lemma SN_preimage:
    forall f,
    (forall a b, R a b -> R (f a) (f b)) ->
    forall e,
    SN R (f e) -> SN R e.
  Proof.
    intros.
    (* The dependent induction tactic seems to generalize variables... *)
    remember (f e) as x.
    generalize dependent e.
    induction H0; intros.
    constructor; intros.
    eapply H1; eauto.
    rewrite Heqx.
    apply H.
    assumption.
  Qed.

  Lemma SN_R_t_R:
    forall e,
    SN R e <-> SN t(R) e.
  Proof.
    split; induction 1.
    - clear H.
      constructor; intros.
      induction H.
      + apply H0.
        assumption.
      + apply IHclos_trans2; intros.
        apply IHclos_trans1; auto with cps.
    - clear H.
      constructor; intros.
      apply H0.
      auto with cps.
  Qed.

  Lemma SN_subset:
    forall S,
    inclusion S R ->
    forall e,
    SN R e -> SN S e.
  Proof.
    intros.
    induction H0.
    constructor; intros.
    fold (SN R) in H0; fold (SN S).
    unfold transp in H0, H1, H2.
    apply H1.
    apply H.
    assumption.
  Qed.

End Normalization.

Section ListNormalization.

  Variable T: Type.
  Variable R: relation T.

  Inductive step_in_list: relation (list T) :=
    | step_in_env_car:
      forall g t u,
      R t u -> step_in_list (t :: g) (u :: g)
    | step_in_env_cdr:
      forall g h t,
      step_in_list g h -> step_in_list (t :: g) (t :: h).

  (* Still not sure we'll be needing this, but just in case... *)

  Lemma step_in_list_is_well_founded:
    forall xs,
    Forall (SN R) xs ->
    SN step_in_list xs.
  Proof.
    induction xs; intros.
    (* Case: nil. *)
    - constructor; intros.
      exfalso.
      inversion H0.
    (* Case: cons. *)
    - dependent destruction H.
      apply IHxs in H0; clear IHxs.
      induction H; clear H.
      induction H0.
      constructor; intros.
      unfold transp in H2.
      dependent destruction H2.
      + apply H1.
        assumption.
      + apply H0; intros.
        * assumption.
        * eapply H1; eauto.
          constructor.
          assumption.
  Qed.

End ListNormalization.

Section Newman.

  Variable T: Type.

  Variable R: relation T.

  Definition locally_confluent: Prop :=
    diagram R R rt(R) rt(R).

  Hypothesis local_confluence: locally_confluent.
  Hypothesis normalizing: forall x, SN R x.

  Lemma newman:
    confluent R.
  Proof.
    intro x.
    induction (normalizing x); clear H.
    intros y ? z ?.
    apply rt_characterization in H.
    apply rt_characterization in H1.
    destruct H; destruct H1.
    - rename y into w, y0 into v.
      apply t_characterization in H.
      apply t_characterization in H1.
      destruct H as (y, ?, ?).
      destruct H1 as (z, ?, ?).
      (*
        Simple diagram chasing, which proceeds as follows:

          x ------ z ------ v  In here, assuming there are at least one step
          |        |        |  in each direction, we take the first steps to
          |        |        |  be y and z, but we want to close the diagram
          |        |        |  between w and v. We first take u by using the
          y ------ u        |  local confluence hypothesis, then we find t by
          |        |        |  using our inductive hypothesis (on the step from
          |        |        |  x to y), then we proceed to find s again using
          |        |        |  our inductive hypothesis (but on the step from x
          w ------ t ------ s  to z this time).
      *)
      destruct local_confluence with x y z as (u, ?, ?); auto.
      edestruct H0 with y u w as (t, ?, ?); eauto.
      edestruct H0 with z t v as (s, ?, ?); eauto with cps.
    - exists y; auto with cps.
      clear H0.
      induction H; eauto with cps.
    - exists y; auto with cps.
      clear H0.
      induction H; eauto with cps.
    - exists x; auto with cps.
  Qed.

End Newman.

Section ObservationalRelations.

  Variable T: Type.
  Variable L: Type.
  Variable C: Type.

  Variable R: relation T.
  Variable P: T -> L -> Prop.

  Hypothesis apply: C -> T -> T.

  Definition observational_equivalence a b: Prop :=
    forall l,
    comp rt(R) P a l <-> comp rt(R) P b l.

  Definition observational_congruence a b: Prop :=
    forall h,
    observational_equivalence (apply h a) (apply h b).

  Lemma observational_equivalence_refl:
    reflexive observational_equivalence.
  Proof.
    firstorder.
  Qed.

  Lemma observational_equivalence_sym:
    symmetric observational_equivalence.
  Proof.
    firstorder.
  Qed.

  Lemma observational_equivalence_trans:
    transitive observational_equivalence.
  Proof.
    split; intros.
    - apply H0; apply H; auto.
    - apply H; apply H0; auto.
  Qed.

  Lemma observational_congruence_refl:
    reflexive observational_congruence.
  Proof.
    intros x h.
    apply observational_equivalence_refl.
  Qed.

  Lemma observational_congruence_sym:
    symmetric observational_congruence.
  Proof.
    intros x y ? h.
    apply observational_equivalence_sym; auto.
  Qed.

  Lemma observational_congruence_trans:
    transitive observational_congruence.
  Proof.
    intros x y z ? ? h.
    eapply observational_equivalence_trans; eauto.
  Qed.

End ObservationalRelations.

(* TODO: move this one. It might be useful, specially for reasoning about extra
   reductions on the call-by-value calculus. *)

Goal
  forall T L,
  forall R S: relation T,
  forall P: T -> L -> Prop,
  inclusion R S ->
  inclusion S (observational_equivalence R P) ->
  same_relation (observational_equivalence R P) (observational_equivalence S P).
Proof.
  intros.
  assert (inclusion rt(S) (observational_equivalence R P)).
  - do 3 intro.
    induction H1.
    + apply H0.
      assumption.
    + apply observational_equivalence_refl.
    + apply observational_equivalence_trans with y; auto.
  - clear H0.
    split; split; intro.
    + destruct H2 as (x', ?, ?).
      assert (comp rt(R) P x' l); eauto with cps.
      apply H1 in H2.
      apply H2 in H4.
      apply H0 in H4.
      destruct H4 as (y', ?, ?).
      exists y'; auto.
      clear H0 H2 H5.
      induction H4; eauto with cps.
    + destruct H2 as (y', ?, ?).
      assert (comp rt(R) P y' l); eauto with cps.
      apply H1 in H2.
      apply H2 in H4.
      apply H0 in H4.
      destruct H4 as (x', ?, ?).
      exists x'; auto.
      clear H0 H2 H5.
      induction H4; eauto with cps.
    + assert (comp rt(S) P x l).
      * destruct H2 as (x', ?, ?).
        exists x'; auto.
        clear H0 H3.
        induction H2; eauto with cps.
      * apply H0 in H3.
        destruct H3 as (y', ?, ?).
        apply H1 in H3.
        apply H3.
        exists y'; auto with cps.
    + assert (comp rt(S) P y l).
      * destruct H2 as (y', ?, ?).
        exists y'; auto.
        clear H0 H3.
        induction H2; eauto with cps.
      * apply H0 in H3.
        destruct H3 as (x', ?, ?).
        apply H1 in H3.
        apply H3.
        exists x'; auto with cps.
Qed.

Section BarbedRelations.

  Variable T: Type.
  Variable L: Type.
  Variable C: Type.

  Variable R: relation T.
  Variable P: T -> L -> Prop.

  Hypothesis apply: C -> T -> T.

  (* Set-theoretic definition of barbed relations. *)

  Definition reduction_closed (S: relation T): Prop :=
    forall a b,
    S a b ->
    forall c,
    R a c ->
    exists2 d,
    rt(R) b d & S c d.

  Definition barb_preserving (S: relation T): Prop :=
    forall a b,
    S a b ->
    forall n,
    P a n -> comp rt(R) P b n.

  Definition barbed_simulation (S: relation T): Prop :=
    reduction_closed S /\ barb_preserving S.

  Definition barbed_bisimulation (S: relation T): Prop :=
    barbed_simulation S /\ barbed_simulation (transp S).

  Definition barbed_bisimilarity a b: Prop :=
    exists2 S, barbed_bisimulation S & S a b.

  Definition barbed_congruence a b: Prop :=
    forall h,
    barbed_bisimilarity (apply h a) (apply h b).

  Lemma symmetric_barbed_simulation_is_bisimulation:
    forall S,
    barbed_simulation S ->
    symmetric S ->
    barbed_bisimulation S.
  Proof.
    intros; split.
    - assumption.
    - destruct H; split.
      + unfold reduction_closed, transp; intros.
        destruct H with a b c; firstorder.
      + unfold barb_preserving, transp; intros.
        firstorder.
  Qed.

  (* TODO: we could fix the type of this definition. *)

  Lemma multistep_reduction_closed:
    forall S,
    reduction_closed S ->
    forall a b,
    S a b ->
    forall c,
    rt(R) a c ->
    exists2 d,
    rt(R) b d & S c d.
  Proof.
    intros.
    generalize b H0; clear b H0.
    induction H1; simpl; intros.
    - eapply H; eauto.
    - exists b; auto with cps.
    - destruct IHclos_refl_trans1 with b as (w, ?, ?); auto.
      destruct IHclos_refl_trans2 with w as (v, ?, ?); auto.
      exists v; eauto with cps.
  Qed.

  Lemma barbed_bisimilarity_refl:
    reflexive barbed_bisimilarity.
  Proof.
    (* We can show that identity is a barbed bisimulation. *)
    exists eq.
    - apply symmetric_barbed_simulation_is_bisimulation.
      + split; do 5 intro.
        * destruct H; eauto with cps.
        * destruct H; eauto with cps.
      + firstorder.
    - reflexivity.
  Qed.

  Lemma barbed_bisimilarity_sym:
    symmetric barbed_bisimilarity.
  Proof.
    (* Since there's a bisimulation S, its inverse is one as well. *)
    destruct 1 as (S, (?, ?), ?).
    exists (transp S); auto.
    firstorder.
  Qed.

  Lemma barbed_bisimilarity_trans:
    transitive barbed_bisimilarity.
  Proof.
    (* Given S1 and S2 that are bisimulations, so is (S1; S2). *)
    destruct 1 as (S1, (?, ?), ?).
    destruct 1 as (S2, (?, ?), ?).
    exists (comp S1 S2).
    - clear x y z H1 H4.
      split; split; do 5 intro.
      + destruct H1 as (d, ?, ?).
        destruct H as (?, _).
        destruct H2 as (?, _).
        destruct H with a d c as (x, ?, ?); auto.
        edestruct multistep_reduction_closed as (y, ?, ?); eauto.
        exists y; auto.
        exists x; auto.
      + destruct H1 as (d, ?, ?).
        destruct H as (_, ?).
        destruct H2 as (?, ?).
        destruct H with a d n as (x, ?, ?); auto.
        edestruct multistep_reduction_closed as (y, ?, ?); eauto.
        destruct H6 with x y n as (z, ?, ?); auto.
        exists z; eauto with cps.
      + destruct H1 as (d, ?, ?).
        destruct H0 as (?, _).
        destruct H3 as (?, _).
        destruct H3 with a d c as (x, ?, ?); auto.
        edestruct multistep_reduction_closed with (S := transp S1) as (y, ?, ?);
          eauto.
        exists y; auto.
        exists x; auto.
      + destruct H1 as (d, ?, ?).
        destruct H0 as (?, ?).
        destruct H3 as (_, ?).
        destruct H3 with a d n as (x, ?, ?); auto.
        edestruct multistep_reduction_closed with (S := transp S1) as (y, ?, ?);
          eauto.
        destruct H6 with x y n as (z, ?, ?); auto.
        exists z; eauto with cps.
    - exists y; auto.
  Qed.

  Lemma barbed_bisimilarity_is_a_bisimulation:
    barbed_bisimulation barbed_bisimilarity.
  Proof.
    apply symmetric_barbed_simulation_is_bisimulation.
    - split; do 5 intro.
      + destruct H as (S, ((?, ?), ?), ?).
        destruct H with a b c as (d, ?, ?); auto.
        firstorder.
      + destruct H as (S, ((?, ?), ?), ?).
        firstorder.
    - apply barbed_bisimilarity_sym.
  Qed.

  Lemma barbed_congruence_refl:
    reflexive barbed_congruence.
  Proof.
    intros x h.
    apply barbed_bisimilarity_refl.
  Qed.

  Lemma barbed_congruence_sym:
    symmetric barbed_congruence.
  Proof.
    intros x y ? h.
    apply barbed_bisimilarity_sym; auto.
  Qed.

  Lemma barbed_congruence_trans:
    transitive barbed_congruence.
  Proof.
    intros x y z ? ? h.
    eapply barbed_bisimilarity_trans; eauto.
  Qed.

  Goal
    inclusion barbed_bisimilarity (observational_equivalence R P).
  Proof.
    intros x y ?H l; split; intros.
    - destruct H as (S, ((?, ?), _), ?).
      destruct H0 as (z, ?, ?).
      destruct multistep_reduction_closed with S x y z as (w, ?, ?); auto.
      destruct H1 with z w l as (v, ?, ?); auto.
      exists v; eauto with cps.
    - destruct H as (S, (_, (?, ?)), ?).
      destruct H0 as (z, ?, ?).
      destruct multistep_reduction_closed with (transp S) y x z as (w, ?, ?);
        auto.
      destruct H1 with z w l as (v, ?, ?); auto.
      exists v; eauto with cps.
  Qed.

  Goal
    confluent R ->
    barb_preserving rt(R) ->
    barbed_bisimulation (observational_equivalence R P).
  Proof.
    unfold inclusion; intros.
    apply symmetric_barbed_simulation_is_bisimulation.
    - split; do 5 intro.
      + exists b; auto with cps.
        split; intro.
        * apply H1.
          destruct H3.
          destruct H with a x c as (y, ?, ?); eauto with cps.
        * apply H1 in H3.
          destruct H3 as (x, ?, ?).
          destruct H with a x c as (y, ?, ?); eauto with cps.
          destruct H0 with x y l as (w, ?, ?); eauto.
          exists w; eauto with cps.
      + apply H1.
        eauto with cps.
    - apply observational_equivalence_sym.
  Qed.

End BarbedRelations.

Section WeakBisimulation.

  Variable T: Type.
  Variable L: Type.

  Variable R: L -> relation T.

  Variable tau: L.

  Hypothesis is_tau_dec: forall l, { l = tau } + { l <> tau }.

  Definition weak_transition (l: L): relation T :=
    if is_tau_dec l then
      rt(R tau)
    else
      comp rt(R tau) (R l).

  Definition simulation (S: relation T): Prop :=
    forall a b,
    S a b ->
    forall c l,
    R l a c ->
    exists2 d,
    weak_transition l b d & S c d.

  Definition bisimulation (S: relation T): Prop :=
    simulation S /\ simulation (transp S).

  Definition bisimilarity a b: Prop :=
    exists2 S, bisimulation S & S a b.

  Lemma weak_transition_immediate:
    forall l,
    inclusion (R l) (weak_transition l).
  Proof.
    intros l a b ?H.
    unfold weak_transition.
    destruct is_tau_dec with l.
    - destruct e; auto with cps.
    - exists a; auto with cps.
  Qed.

  Lemma symmetric_simulation_is_bisimulation:
    forall S,
    simulation S ->
    symmetric S ->
    bisimulation S.
  Proof.
    split.
    - assumption.
    - do 6 intro.
      destruct H with a b c l as (d, ?, ?); auto.
      exists d; firstorder.
  Qed.

  Lemma weak_transition_silent:
    forall l,
    l = tau ->
    weak_transition l = rt(R tau).
  Proof.
    unfold weak_transition; intros.
    destruct is_tau_dec with l.
    - reflexivity.
    - firstorder.
  Qed.

  Lemma weak_transition_nonsilent:
    forall l,
    l <> tau ->
    weak_transition l = comp rt(R tau) (R l).
  Proof.
    intros.
    unfold weak_transition.
    destruct is_tau_dec with l.
    - firstorder.
    - reflexivity.
  Qed.

  Lemma weak_transition_closed:
    forall S,
    simulation S ->
    forall a b,
    S a b ->
    forall c l,
    weak_transition l a c ->
    exists2 d,
    weak_transition l b d & S c d.
  Proof.
    intros until l.
    assert (forall c, rt(R tau) a c ->
      exists2 d, rt(R tau) b d & S c d).
    - clear c; intros.
      generalize dependent b.
      induction H1; intros.
      + destruct H with x b y tau as (z, ?, ?); auto.
        rewrite weak_transition_silent in H2; auto.
        exists z; eauto.
      + exists b; auto with cps.
      + edestruct IHclos_refl_trans1 as (w, ?, ?); eauto.
        edestruct IHclos_refl_trans2 as (v, ?, ?); eauto.
        exists v; eauto with cps.
    - unfold weak_transition.
      destruct is_tau_dec with l; intros.
      + eapply H1; eauto.
      + destruct H2 as (d, ?, ?).
        edestruct H1 as (x, ?, ?); eauto.
        destruct H with d x c l as (y, ?, ?); eauto.
        rewrite weak_transition_nonsilent in H6; auto.
        destruct H6 as (z, ?, ?).
        exists y; auto.
        exists z; eauto with cps.
  Qed.

  Lemma bisimilarity_refl:
    reflexive bisimilarity.
  Proof.
    (* Same reasoning as for reflexivity on the barbed bisimilarity above. *)
    exists eq; auto.
    split; do 6 intro.
    - destruct H.
      exists c; auto.
      apply weak_transition_immediate; auto.
    - destruct H.
      exists c; auto with cps.
      apply weak_transition_immediate; auto.
  Qed.

  Lemma bisimilarity_sym:
    symmetric bisimilarity.
  Proof.
    (* Same reasoning as for symmetry on the barbed bisimilarity above. *)
    destruct 1 as (S, ?, ?).
    exists (transp S); auto.
    firstorder.
  Qed.

  Lemma bisimilarity_trans:
    transitive bisimilarity.
  Proof.
    (* Same reasoning as for transitivity on the barbed bisimilarity above. *)
    destruct 1 as (S1, (?, ?), ?).
    destruct 1 as (S2, (?, ?), ?).
    exists (comp S1 S2).
    - split; do 6 intro.
      + destruct H5 as (d, ?, ?).
        destruct H with a d c l as (w, ?, ?); auto.
        destruct weak_transition_closed with S2 d b w l as (v, ?, ?); auto.
        exists v; auto.
        exists w; auto.
      + destruct H5 as (d, ?, ?).
        destruct H3 with a d c l as (w, ?, ?); auto.
        destruct weak_transition_closed with (transp S1) d b w l as (v, ?, ?);
          auto.
        exists v; auto.
        exists w; auto.
    - exists y; auto.
  Qed.

  Lemma bisimilarity_is_a_bisimulation:
    bisimulation bisimilarity.
  Proof.
    apply symmetric_simulation_is_bisimulation.
    - do 6 intro.
      destruct H as (S, (?, ?), ?).
      destruct H with a b c l as (d, ?, ?); auto.
      exists d; auto.
      firstorder.
    - apply bisimilarity_sym.
  Qed.

End WeakBisimulation.

Section StrongBisimulation.

  Variable T: Type.
  Variable L: Type.

  Variable R: L -> relation T.

  Definition strong_simulation (S: relation T): Prop :=
    forall a b,
    S a b ->
    forall c l,
    R l a c ->
    exists2 d,
    R l b d & S c d.

  Goal
    forall S,
    strong_simulation S <-> (forall l, commutes (R l) S).
  Proof.
    split; intros.
    - intros x y ? z ?.
      destruct H with x z y l as (w, ?, ?); auto.
      exists w; auto.
    - intros x y ? z l ?.
      destruct H with l x z y as (w, ?, ?); auto.
      exists w; auto.
  Qed.

  Definition strong_bisimulation (S: relation T): Prop :=
    strong_simulation S /\ strong_simulation (transp S).

  (* TODO: take a look at the definitions below. *)

  Variable l: L.
  Variable S: relation T.

  Hypothesis S_is_bisim: strong_bisimulation S.

  Goal
    forall a1 b1,
    rst(S) a1 b1 ->
    (exists a2, R l a1 a2) <-> (exists b2, R l b1 b2).
  Proof.
    induction 1.
    - split; intros.
      + destruct H0 as (a2, ?H).
        destruct S_is_bisim.
        edestruct H1; eauto.
      + destruct H0 as (b2, ?H).
        destruct S_is_bisim.
        edestruct H2; eauto.
    - firstorder.
    - firstorder.
    - firstorder.
  Qed.

  Goal
    forall x y,
    S x y ->
    forall n z,
    clos_trans_cnt (R l) n x z ->
    exists2 w,
    clos_trans_cnt (R l) n y w & S z w.
  Proof.
    intros.
    generalize dependent y.
    induction H0; intros.
    - rename y0 into y, y into z.
      destruct S_is_bisim as ((w, ?, ?), _).
      + eassumption.
      + eassumption.
      + exists w; auto.
        constructor; auto.
    - rename y0 into a.
      edestruct IHclos_trans_cnt1 as (b, ?, ?); eauto.
      edestruct IHclos_trans_cnt2 as (w, ?, ?); eauto.
      exists w; auto.
      econstructor 2; eauto.
  Qed.

  Goal
    forall x y,
    S x y ->
    SN (R l) x <-> SN (R l) y.
  Proof.
    split; intros.
    - generalize dependent y.
      induction H0; intros.
      constructor; intros w ?H.
      fold (SN (R l)) in H |- *.
      unfold transp in H, H0, H2.
      destruct S_is_bisim as (_, (a, ?, ?)).
      + eassumption.
      + eassumption.
      + eapply H0; eauto.
    - generalize dependent x.
      induction H0; intros.
      constructor; intros w ?H.
      fold (SN (R l)) in H |- *.
      unfold transp in H, H0, H2.
      destruct S_is_bisim as ((a, ?, ?), _).
      + eassumption.
      + eassumption.
      + eapply H0; eauto.
  Qed.

End StrongBisimulation.

Section Postponement.

  Variable T: Type.
  Variable L: Type.

  Variable R: L -> relation T.
  Variable S: relation T.

  Definition postpones: Prop :=
    forall l,
    diagram (R l) (transp S) rt(transp S) r(R l).

  Hypothesis local_postponement: postpones.

  Local Lemma postponement_diagram:
    forall l,
    diagram rt(R l) rt(transp S) rt(transp S) rt(R l).
  Proof.
    intros.
    assert (diagram (R l) t(transp S) rt(transp S) r(R l)).
    - intros x y ? z ?.
      apply r_step in H.
      generalize dependent y.
      induction H0.
      + intros z ?.
        destruct H0.
        * rename y0 into z.
          eapply local_postponement; eauto.
        * exists y; auto with cps.
      + intros w ?.
        edestruct IHclos_trans1 as (v, ?, ?); eauto.
        edestruct IHclos_trans2 as (u, ?, ?); eauto.
        exists u; eauto with cps.
    - induction 1.
      + intros z ?.
        apply rt_characterization in H1.
        destruct H1.
        * rename y0 into z.
          destruct H with x y z as (w, ?, ?); eauto.
          exists w; destruct H3; eauto with cps.
        * exists y; eauto with cps.
      + intros z ?.
        exists z; eauto with cps.
      + intros w ?.
        destruct IHclos_refl_trans1 with w as (v, ?, ?); auto.
        destruct IHclos_refl_trans2 with v as (u, ?, ?); auto.
        exists u; eauto with cps.
  Qed.

  Lemma postponement:
    forall l,
    inclusion (comp rt(S) rt(R l)) (comp rt(R l) rt(S)).
  Proof.
    intros l x z (y, ?, ?).
    destruct postponement_diagram with l y z x as (w, ?, ?).
    - assumption.
    - clear H0 z.
      induction H; eauto with cps.
    - exists w; auto.
      clear H H0 H2 x y.
      induction H1; eauto with cps.
  Qed.

  (* TODO: this might be useful. I hope I'll remember about this if I come to
     need it. I gotta be fast, the deadline is approaching. *)

  Goal
    let X := fun a b => exists l, R l a b in
    diagram rt(X) rt(transp S) rt(transp S) rt(X).
  Proof.
    simpl; induction 1; intros.
    - destruct H as (l, ?).
      destruct postponement_diagram with l x y z as (w, ?, ?); eauto with cps.
      exists w.
      + assumption.
      + clear H H0 H1 x y.
        induction H2; eauto with cps.
    - exists z; eauto with cps.
    - rename z0 into w.
      edestruct IHclos_refl_trans1 as (v, ?, ?); eauto.
      edestruct IHclos_refl_trans2 as (u, ?, ?); eauto.
      exists u; eauto with cps.
  Qed.

  Lemma bisimulation_implies_postponement:
    strong_bisimulation R S -> postpones.
  Proof.
    intros (_, ?) l x y ? z ?.
    destruct H with x z y l as (w, ?, ?); auto.
    exists w; auto with cps.
  Qed.

End Postponement.

Section Modulo.

  Variable T: Type.

  Variable R: relation T.
  Variable S: relation T.

  Definition modulo: relation T :=
    fun a d =>
      exists b c,
      S a b /\ R b c /\ S c d.

  Hint Unfold modulo: cps.

  Hypothesis S_is_equiv: equivalence S.
  Hypothesis S_is_bisimulation: strong_bisimulation (fun _: unit => R) S.

  (* TODO: rewrite the following lemmas to use the postponement code above! *)

  Lemma modulo_bisimulation_postponement:
    same_relation t(modulo) (comp t(R) S).
  Proof.
    destruct S_is_equiv.
    split; intros x y ?.
    - apply clos_trans_tn1_iff in H.
      induction H.
      + destruct H as (b, (c, (?, (?, ?)))).
        destruct S_is_bisimulation as (_, (d, ?, ?)).
        * exact H.
        * easy.
        * exact H0.
        * exists d; eauto with cps.
      + apply clos_trans_tn1_iff in H0.
        destruct IHclos_trans_n1 as (a, ?, ?).
        destruct H as (b, (c, (?, (?, ?)))).
        destruct S_is_bisimulation as (_, (d, ?, ?)).
        * apply equiv_trans with y; eauto.
        * easy.
        * eassumption.
        * exists d; eauto with cps.
    - destruct H as (z, ?, ?).
      generalize dependent y.
      apply clos_trans_tn1_iff in H.
      induction H; intros.
      + rename y0 into z.
        apply t_step.
        exists x, y; eauto.
      + rename y0 into w.
        apply clos_trans_tn1_iff in H0.
        apply t_trans with y.
        * eauto with cps.
        * apply t_step.
          exists y, z; eauto.
  Qed.

  Lemma modulo_bisimulation_diamond:
    diamond R -> diamond modulo.
  Proof.
    destruct S_is_equiv.
    intros ? x y ? z ?.
    unfold transp in H1 |- *.
    destruct H0 as (a, (b, (?, (?, ?)))).
    destruct H1 as (c, (d, (?, (?, ?)))).
    destruct S_is_bisimulation as (_, (e, ?, ?)).
    - exact H0.
    - easy.
    - exact H2.
    - destruct S_is_bisimulation as (_, (f, ?, ?)).
      + exact H1.
      + easy.
      + exact H4.
      + destruct H with x e f as (g, ?, ?); eauto.
        exists g; do 2 eexists; eauto.
  Qed.

  Lemma modulo_bisimulation_transitive_diamond:
    diamond t(R) -> diamond t(modulo).
  Proof.
    intros ? x y ? z ?.
    destruct S_is_equiv.
    apply modulo_bisimulation_postponement in H0.
    apply modulo_bisimulation_postponement in H1.
    destruct H0 as (y', ?, ?).
    destruct H1 as (z', ?, ?).
    destruct H with x y' z' as (w, ?, ?); auto.
    exists w.
    - clear H0 H1 H3 H5.
      apply clos_trans_t1n_iff in H4.
      destruct H4.
      + apply t_step.
        exists y', y0; eauto.
      + apply clos_trans_t1n_iff in H4.
        apply t_trans with y0.
        * apply t_step.
          exists y', y0; eauto.
        * apply modulo_bisimulation_postponement.
          exists z0; eauto.
    - clear H0 H1 H2 H4.
      apply clos_trans_t1n_iff in H5.
      destruct H5.
      + apply t_step.
        exists z', y0; eauto.
      + apply clos_trans_t1n_iff in H5.
        apply t_trans with y0.
        * apply t_step.
          exists z', y0; eauto.
        * apply modulo_bisimulation_postponement.
          exists z0; eauto.
  Qed.

  Lemma modulo_bisimulation_strong_normalization:
    forall e,
    SN R e -> SN modulo e.
  Proof.
    intros x ?.
    destruct S_is_equiv.
    (* We need to generalize the induction a bit... *)
    assert (exists2 y, S x y & SN R y) as (y, ?, ?); eauto.
    apply SN_R_t_R in H1.
    apply SN_R_t_R.
    clear H; generalize dependent x.
    (* There we go, now we can proceed. *)
    induction H1.
    clear H; intros x' ?.
    constructor; intros y' ?.
    fold (SN t(modulo)).
    unfold transp in H.
    assert (t(modulo) x y').
    - apply clos_trans_t1n_iff in H.
      destruct H.
      + apply t_step.
        destruct H as (a, (b, (?, (?, ?)))).
        exists a, b; eauto.
      + apply clos_trans_t1n_iff in H2.
        apply t_trans with y.
        * apply t_step.
          destruct H as (a, (b, (?, (?, ?)))).
          exists a, b; eauto.
        * assumption.
    - apply modulo_bisimulation_postponement in H2.
      destruct H2 as (y, ?, ?).
      eapply H0; eauto.
  Qed.

End Modulo.
