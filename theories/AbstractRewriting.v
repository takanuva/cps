(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Set Implicit Arguments.
Require Import Equality.
Require Export Relations.
Require Import Local.Prelude.

(** ** Relations *)

Notation "'t(' R )" := (clos_trans _ R)
  (format "'t(' R )"): type_scope.

Notation "'rt(' R )" := (clos_refl_trans _ R)
  (format "'rt(' R )"): type_scope.

Notation "'rst(' R )" := (clos_refl_sym_trans _ R)
  (format "'rst(' R )"): type_scope.

Global Hint Constructors clos_trans: cps.
Global Hint Constructors clos_refl_trans: cps.
Global Hint Constructors clos_refl_sym_trans: cps.

Arguments transp {A}.

Global Hint Unfold transp: cps.

Arguments commut {A}.

Global Hint Unfold commut: cps.

Arguments same_relation {A}.

Global Hint Unfold same_relation: cps.

Arguments reflexive {A}.

Global Hint Unfold reflexive: cps.

Arguments symmetric {A}.

Global Hint Unfold symmetric: cps.

Arguments transitive {A}.

Global Hint Unfold transitive: cps.

Definition diamond {T} (R: relation T): Prop :=
  commut R (transp R).

Global Hint Unfold diamond: cps.

Definition comp {A} {B} {C} R S: A -> C -> Prop :=
  fun a c =>
    exists2 b: B,
    R a b & S b c.

Global Hint Unfold comp: cps.

Section Confluency.

  Variable T: Type.
  Variable R: relation T.

  Definition confluent: Prop :=
    diamond rt(R).

  Definition church_rosser: Prop :=
    forall x y,
    rst(R) x y ->
    exists2 z,
    rt(R) x z & rt(R) y z.

  Lemma strip_lemma:
    diamond R -> commut t(R) (transp R).
  Proof.
    induction 2; intros.
    (* Case: step. *)
    - destruct H with y x z as (w, ?, ?); auto.
      exists w; auto with cps.
    (* Case: trans. *)
    - rename z0 into w.
      destruct IHclos_trans1 with w as (v, ?, ?); auto.
      destruct IHclos_trans2 with v as (u, ?, ?); auto.
      exists u; eauto with cps.
  Qed.

  Lemma transitive_closure_preserves_diamond:
    diamond R -> diamond t(R).
  Proof.
    induction 2; intros.
    (* Case: step. *)
    - destruct strip_lemma with z x y as (w, ?, ?); auto.
      exists w; auto with cps.
    (* Case: tran. *)
    - rename z0 into w.
      destruct IHclos_trans1 with w as (v, ?, ?); auto.
      destruct IHclos_trans2 with v as (u, ?, ?); auto.
      exists u; eauto with cps.
  Qed.

  Lemma confluence_implies_church_rosser:
    confluent -> church_rosser.
  Proof.
    induction 2.
    (* Case: step. *)
    - exists y; auto with cps.
    (* Case: refl. *)
    - exists x; auto with cps.
    (* Case: symm. *)
    - destruct IHclos_refl_sym_trans as (z, ?, ?).
      exists z; auto.
    (* Case: tran. *)
    - destruct IHclos_refl_sym_trans1 as (w, ?, ?).
      destruct IHclos_refl_sym_trans2 as (v, ?, ?).
      destruct H with w y v as (u, ?, ?); auto with cps.
      exists u; eauto with cps.
  Qed.

End Confluency.

Section Normalization.

  Variable T: Type.
  Variable R: relation T.

  Definition normal a: Prop :=
    forall b, ~R a b.

  Definition WN a: Prop :=
    exists2 b, rt(R) a b & normal b.

  Definition SN :=
    (Acc (transp R)).

  Lemma SN_preimage:
    forall f,
    (forall a b, R a b -> R (f a) (f b)) ->
    forall e,
    Acc R (f e) -> Acc R e.
  Proof.
    intros.
    (* There seems to be a bug in the dependent induction tactic... *)
    remember (f e) as x.
    generalize dependent e.
    induction H0; intros.
    constructor; intros.
    eapply H1; eauto.
    rewrite Heqx.
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
    - constructor; intros.
      exfalso.
      inversion H0.
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

  Definition barbed_bisimilarity: relation T :=
    fun a b =>
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
    - do 3 intro.
      destruct H as (S, (?, ?), ?).
      exists (transp S); firstorder.
  Qed.

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
    exists (transp S).
    - split; auto.
    - assumption.
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
    - firstorder.
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

End BarbedRelations.
