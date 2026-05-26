(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Program.
Require Import Morphisms.
Require Import Local.Setoid.
Require Import Local.Universe.

Section IZF.

  Context `{Universe}.

  Definition V: Set :=
    w U T.

  Local Notation setof :=
    (sup U T).

  Definition idx (x: V): U :=
    match x with
    | sup _ _ A f => A
    end.

  Definition elts (x: V): T (idx x) -> V :=
    match x return T (idx x) -> V with
    | sup _ _ A f => f
    end.

  Definition V_class: Type :=
    V -> Prop.

  Fixpoint V_equiv (x: V) (y: V): Prop :=
    match x, y with
    | sup _ _ A f, sup _ _ B g =>
      (forall a: T A, exists b: T B, V_equiv (f a) (g b)) /\
        (forall b: T B, exists a: T A, V_equiv (f a) (g b))
    end.

  Lemma V_equiv_refl:
    forall x,
    V_equiv x x.
  Proof.
    induction x as [A f]; split; intros.
    - now exists a.
    - now exists b.
  Qed.

  Lemma V_equiv_sym:
    forall x y,
    V_equiv x y -> V_equiv y x.
  Proof.
    induction x as [A f]; destruct y as (B, g); split; intros.
    - destruct H1 as (_, ?H).
      destruct (H1 a) as (b, ?H).
      exists b.
      now apply H0.
    - destruct H1 as (?H, _).
      destruct (H1 b) as (a, ?H).
      exists a.
      now apply H0.
  Qed.

  Lemma V_equiv_trans:
    forall x y z,
    V_equiv x y -> V_equiv y z -> V_equiv x z.
  Proof.
    induction x as [A f]; destruct y as (B, g), z as (C, h); split; intros.
    - destruct H1 as (?H, _).
      destruct H2 as (?H, _).
      destruct (H1 a) as (b, ?H).
      destruct (H2 b) as (c, ?H).
      exists c.
      now apply H0 with (g b).
    - destruct H1 as (_, ?H).
      destruct H2 as (_, ?H).
      destruct (H2 b) as (a, ?H).
      destruct (H1 a) as (c, ?H).
      exists c.
      now apply H0 with (g a).
  Qed.

  Definition V_in (x: V) (y: V): Prop :=
    match y with
    | sup _ _ A f => exists a: T A, V_equiv x (f a)
    end.

  Definition V_setoid: SmallSetoid := {|
    setoid_carrier := V;
    setoid_equiv := V_equiv;
    setoid_refl := V_equiv_refl;
    setoid_sym := V_equiv_sym;
    setoid_trans := V_equiv_trans
  |}.

  Global Canonical Structure V_setoid.

  Global Instance V_in_is_proper:
    Proper (setoid_equiv ==> setoid_equiv ==> iff) V_in.
  Proof.
    split; intros.
    - destruct x0 as (A, f), y0 as (B, g); simpl in H2 |- *.
      destruct H2 as (a, ?H).
      destruct H1 as (?H, _).
      destruct (H1 a) as (b, ?H).
      exists b.
      rewrite <- H0, H2.
      assumption.
    - destruct x0 as (A, f), y0 as (B, g); simpl in H2 |- *.
      destruct H2 as (b, ?H).
      destruct H1 as (_, ?H).
      destruct (H1 b) as (a, ?H).
      exists a.
      rewrite H0, H3.
      assumption.
  Qed.

  Theorem V_extensionality_ax:
    forall x y,
    (forall z, V_in z x <-> V_in z y) ->
    x == y.
  Proof.
    intros.
    destruct x as (A, f), y as (B, g); split; intros.
    - simpl in H0.
      destruct (H0 (f a)) as (?H, _).
      apply H1.
      now exists a.
    - simpl in H0.
      destruct (H0 (g b)) as (_, ?H).
      destruct H1 as (a, ?H).
      + now exists b.
      + now exists a.
  Qed.

  (* TODO: improve how we do casts... *)

  Import EqNotations.

  Local Definition cast {T: Set} {U: Set} (H: T = U) (x: T): U :=
    rew dependent H in x.

  Definition V_pair (x: V) (y: V): V :=
    setof (FIN 2) (fun n: T (FIN 2) =>
      if proj1_sig (cast (T_FIN 2) n) then x else y).

  Definition V_pair_fst:
    forall x y,
    V_in x (V_pair x y).
  Proof.
    intros; simpl.
    generalize (T (FIN 2)) (T_FIN 2); intros.
    subst; simpl.
    unshelve eexists (exist 0 _); simpl.
    - lia.
    - reflexivity.
  Qed.

  Definition V_pair_snd:
    forall x y,
    V_in y (V_pair x y).
  Proof.
    intros; simpl.
    generalize (T (FIN 2)) (T_FIN 2); intros.
    subst; simpl.
    unshelve eexists (exist 1 _); simpl.
    - lia.
    - reflexivity.
  Qed.

  Theorem V_pairing_ax:
    forall x y w,
    V_in w (V_pair x y) <-> (w == x \/ w == y).
  Proof.
    split; intros.
    - destruct H0 as (n, ?H).
      generalize dependent n.
      generalize (T (FIN 2)) (T_FIN 2); intros.
      subst; simpl.
      destruct n as (n, ?H).
      simpl in *.
      destruct n.
      + now left.
      + now right.
    - destruct H0; simpl.
      + generalize (T (FIN 2)) (T_FIN 2); intros.
        subst; unshelve eexists (exist 0 _); simpl.
        * simpl; lia.
        * assumption.
      + generalize (T (FIN 2)) (T_FIN 2); intros.
        subst; unshelve eexists (exist 1 _); simpl.
        * simpl; lia.
        * assumption.
  Qed.

  Global Instance V_pair_is_proper:
    Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) V_pair.
  Proof.
    repeat intro; split; intros.
    - exists a; generalize dependent a.
      generalize (T (FIN 2)) (T_FIN 2); intros.
      subst; simpl.
      destruct a as (n, ?H); simpl.
      destruct n.
      + assumption.
      + assumption.
    - exists b; generalize dependent b.
      generalize (T (FIN 2)) (T_FIN 2); intros.
      subst; simpl.
      destruct b as (n, ?H); simpl.
      destruct n.
      + assumption.
      + assumption.
  Qed.

  Definition V_union (x: V): V :=
    match x with
    | sup _ _ A f =>
      setof (SIGMA A (fun a => idx (f a)))
        (fun p =>
          let (y, z) := cast (T_SIGMA A _) p in elts (f y) z)
    end.

  Theorem V_union_ax:
    forall a z,
    V_in z (V_union a) <-> (exists2 b, V_in z b & V_in b a).
  Proof.
    split; intros.
    - destruct a as (A, f); simpl in *.
      destruct H0.
      generalize dependent x.
      generalize (T (SIGMA A (fun a : T A => idx (f a))))
        (T_SIGMA A (fun a : T A => idx (f a))); intros.
      subst; simpl in *.
      destruct x as (x, ?H).
      exists (f x).
      + remember (f x) as y.
        destruct y; simpl in *.
        now exists H1.
      + now exists x.
    - destruct H0 as (b, ?H, ?H).
      destruct a as (A, f); simpl in *.
      generalize (T (SIGMA A (fun a : T A => idx (f a))))
        (T_SIGMA A (fun a : T A => idx (f a))); intros.
      subst; simpl in *.
      destruct H1.
      rewrite H1 in H0; clear H1.
      remember (f x) as y.
      destruct y; simpl in *.
      destruct H0.
      unshelve eexists.
      + exists x.
        rewrite <- Heqy; simpl.
        assumption.
      + simpl.
        rewrite <- Heqy; simpl.
        assumption.
  Qed.

  Global Instance V_union_is_proper:
    Proper (setoid_equiv ==> setoid_equiv) V_union.
  Proof.
    repeat intro.
    destruct x as (A, f), y as (B, g); split; intros.
    - generalize dependent a.
      generalize (T (SIGMA A (fun a : T A => idx (f a))))
        (T_SIGMA A (fun a : T A => idx (f a))); intros.
      subst; simpl.
      generalize (T (SIGMA B (fun a : T B => idx (g a))))
        (T_SIGMA B (fun a : T B => idx (g a))); intros.
      subst; simpl.
      destruct H0 as (?H, _).
      destruct a as (a, ?H).
      specialize (H0 a) as (b, ?H).
      remember (f a) as y.
      remember (g b) as z.
      destruct y, z; simpl in H0, H1.
      destruct H0 as (?H, _).
      destruct (H0 H1) as (c, ?H).
      unshelve eexists.
      + exists b; simpl.
        rewrite <- Heqz; simpl.
        assumption.
      + simpl.
        rewrite <- Heqz; simpl.
        assumption.
    - generalize dependent b.
      generalize (T (SIGMA B (fun a : T B => idx (g a))))
        (T_SIGMA B (fun a : T B => idx (g a))); intros.
      subst; simpl.
      generalize (T (SIGMA A (fun a : T A => idx (f a))))
        (T_SIGMA A (fun a : T A => idx (f a))); intros.
      subst; simpl.
      destruct H0 as (_, ?H).
      destruct b as (b, ?H).
      specialize (H0 b) as (a, ?H).
      remember (g b) as y.
      remember (f a) as z.
      destruct y, z; simpl in H0, H1.
      destruct H0 as (_, ?H).
      destruct (H0 H1) as (c, ?H).
      unshelve eexists.
      + exists a; simpl.
        rewrite <- Heqz; simpl.
        assumption.
      + simpl.
        rewrite <- Heqz; simpl.
        assumption.
  Qed.

  Definition V_separation (x: V) (P: V -> U): V :=
    match x with
    | sup _ _ A f =>
      setof (SIGMA A (fun a: T A => P (f a)))
        (fun p =>
          let (a, _) := cast (T_SIGMA A _) p in f a)
    end.

  Theorem V_separation_ax:
    forall x P z,
    V_in z (V_separation x P) <->
      (V_in z x /\ exists2 z', z == z' & inhabited (T (P z'))).
  Proof.
    admit.
  Admitted.

  (* ---------------------------------------------------------------------- *)

  Definition V_singleton (x: V): V :=
    V_pair x x.

  (* Kuratowski's pairs. *)

  Definition V_couple (x: V) (y: V): V :=
    V_pair (V_singleton x) (V_pair x y).

  Definition V_cartesian (x: V) (y: V): V :=
    match x, y with
    | sup _ _ A f, sup _ _ B g =>
      setof (SIGMA A (const B)) (fun p =>
        let (z, w) := cast (T_SIGMA A (const B)) p in
        V_couple (f z) (g w))
    end.

  Definition V_subset (x: V) (y: V): Prop :=
    forall z: V,
    V_in z x -> V_in z y.

  Definition V_relation (x: V) (y: V): V_class :=
    fun z => V_subset z (V_cartesian x y).

End IZF.
