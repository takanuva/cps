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
    (* Case: trans. *)
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
    (* Case: sym. *)
    - destruct IHclos_refl_sym_trans as (z, ?, ?).
      exists z; auto.
    (* Case: trans. *)
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

End BarbedRelations.

Section Bisimulation.

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
    forall l a b,
    R l a b -> weak_transition l a b.
  Proof.
    intros.
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

End Bisimulation.
