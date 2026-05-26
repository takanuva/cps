(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Program.
Require Import Equality.
Require Import FunctionalExtensionality.
Require Import Local.InductionRecursion.
Require Import Local.Setoid.
Require Import Local.Category.

Import EqNotations.
Import ListNotations.
Set Universe Polymorphism.
Set Primitive Projections.

Arguments projT1 {A} {P}.
Arguments projT2 {A} {P}.
Arguments exist {A} {P}.
Arguments existT {A} {P}.

(* ... *)

Section Family.

  Universe u0.

  Local Notation constructor :=
    (forall X: Type@{u0}, (X -> Type@{u0}) -> Type@{u0}).

  Variable A: Set.
  Variable B: A -> Type@{u0}.
  Variable C: list constructor.

  Local Notation ctor_index :=
    { n: nat | n < length C }.

  Local Program Definition GET_CTOR (n: ctor_index) :=
    match nth_error C n with
    | Some ctor => ctor
    | None => False_rect _ _
    end.

  Next Obligation.
    eapply nth_error_Some.
    - eassumption.
    - auto.
  Qed.

  Variant branch: Set :=
    | U_idx
    | U_lift
    | U_ctor.

  Definition TARSKI: @Sig Type@{u0} :=
    sigma branch (fun b: branch =>
      match b with
      | U_idx =>
        iota (A: Type@{u0})
      | U_lift =>
        sigma A (fun a: A =>
          iota (B a))
      | U_ctor =>
        sigma ctor_index (fun n =>
          delta unit (fun Ta: unit -> Type@{u0} =>
            delta (Ta tt) (fun Tb: Ta tt -> Type@{u0} =>
              iota (GET_CTOR n (Ta tt) Tb))))
      end).

  Local Definition IND: Type :=
    E TARSKI (total (muE TARSKI)) projT1.

  Local Definition REC: IND -> Type@{u0} :=
    F TARSKI (total (muE TARSKI)) projT1.

  Local Definition embed (x: IND): total (muE TARSKI) :=
    existT (REC x) (inE TARSKI (exist x eq_refl)).

  Local Definition IDX': IND :=
    existT U_idx tt.

  Local Definition LIFT' (a: A): IND :=
    existT U_lift
      (existT a tt).

  Local Definition CTOR' (n: ctor_index) (a: IND) (b: REC a -> IND): IND :=
    existT U_ctor
      (existT n
        (existT (fun _ => embed a)
          (existT (fun x => embed (b x))
            tt))).

  Inductive canonical: IND -> Type :=
    | canonical_idx:
      canonical IDX'
    | canonical_lift:
      forall a: A,
      canonical (LIFT' a)
    | canonical_ctor:
      forall n: ctor_index,
      forall a: IND,
      forall b: REC a -> IND,
      forall ok_a: canonical a,
      forall ok_b: (forall x, canonical (b x)),
      canonical (CTOR' n a b).

  Unset Elimination Schemes.

  Inductive CODE: Set :=
    | shrink (x: IND) (ok: canonical x).

  Set Elimination Schemes.

  Definition get_branch (c: CODE): branch :=
    let (x, ok) := c in projT1 x.

  Definition get_inner:
    forall c: CODE,
    forall H: U_lift = get_branch c,
    A.
  Proof.
    intros.
    destruct c.
    now destruct ok.
  Defined.

  Definition get_index:
    forall c: CODE,
    forall H: U_ctor = get_branch c,
    ctor_index.
  Proof.
    intros.
    destruct c.
    now destruct ok.
  Defined.

  Definition valid_type (c: CODE) (T: Type@{u0}): Type :=
    forall a H, c = shrink a H -> T = REC a.

  Definition left_child:
    forall c: CODE,
    U_ctor = get_branch c ->
    CODE.
  Proof.
    intros.
    destruct c.
    destruct ok.
    - exfalso.
      simpl in H.
      inversion H.
    - exfalso.
      simpl in H.
      inversion H.
    - exact (shrink a ok).
  Defined.

  Definition right_child:
    forall c: CODE,
    forall H: U_ctor = get_branch c,
    forall T: Type@{u0},
    forall X: valid_type (left_child c H) T,
    T -> CODE.
  Proof.
    intros.
    destruct c.
    destruct ok; try easy.
    simpl in *.
    set (y := rew dependent X a ok eq_refl in X0).
    exact (shrink (b y) (ok_b y)).
  Defined.

  Inductive subterm: CODE -> CODE -> Prop :=
    | subterm_ctor_left:
      forall c H,
      subterm (left_child c H) c
    | subterm_ctor_right:
      forall c H T X x,
      subterm (right_child c H T X x) c.

  Lemma subterm_acc:
    forall c: CODE,
    Acc subterm c.
  Proof.
    intros.
    destruct c.
    induction ok.
    - constructor; intros.
      inversion H; easy.
    - constructor; intros.
      inversion H; easy.
    - constructor; intros.
      inversion_clear H0.
      + simpl in *.
        assumption.
      + simpl in *.
        apply H.
  Defined.

  Lemma CODE_prim_rect:
    forall P: CODE -> Type,
    forall f1: P (shrink IDX' canonical_idx),
    forall f2: (forall a: A, P (shrink (LIFT' a) (canonical_lift a))),
    forall f3: (forall x: CODE,
                forall H: U_ctor = get_branch x,
                P (left_child x H) ->
                (forall T X y, P (right_child x H T X y)) ->
                P x),
    forall x: CODE,
    P x.
  Proof.
    intros.
    assert (Acc subterm x) by now apply subterm_acc.
    induction H; clear H.
    remember (get_branch x) as b.
    destruct b.
    - enough (x = shrink IDX' canonical_idx).
      + rewrite H.
        apply f1.
      + destruct x.
        now destruct ok.
    - set (a := get_inner x Heqb).
      enough (x = shrink (LIFT' a) (canonical_lift a)).
      + rewrite H.
        apply f2.
      + destruct x.
        now destruct ok.
    - apply f3 with Heqb.
      + apply X.
        constructor.
      + intros.
        apply X.
        constructor.
  Qed.

  Local Notation GOAL c :=
    { x: IND & canonical x & valid_type c (REC x) }.

  Definition get_ind {c: CODE} (x: GOAL c): IND :=
    let (a, ok_a, H) := x in a.

  Definition get_canonical {c: CODE} (x: GOAL c): canonical (get_ind x) :=
    let (a, ok_a, H) return canonical (get_ind x) := x in ok_a.

  Definition rebuild:
    forall x: CODE,
    GOAL x.
  Proof.
    intros.
    induction x using CODE_prim_rect.
    - exists IDX'; repeat intro.
      + constructor.
      + apply (f_equal get_branch) in H0.
        now destruct H.
    - exists (LIFT' a); repeat intro.
      + constructor.
      + pose proof H0.
        apply (f_equal get_branch) in H1; simpl in H1.
        destruct H; try easy.
        inversion H0; subst.
        reflexivity.
    - destruct IHx as (a, ok_a, ?H).
      specialize (X (REC a) H0).
      exists (CTOR' (get_index x H) a (fun y => get_ind (X y))); repeat intro.
      + constructor; intros.
        * assumption.
        * apply get_canonical.
      + subst.
        destruct H1; try easy; simpl in *; clear H.
        remember (H0 a0 H1 eq_refl) as f.
        clear H0 Heqf; rename a0 into a'.
        change (REC (CTOR' ?n ?a ?b)) with
          (GET_CTOR n (REC a) (fun y => REC (b y))); simpl.
        destruct f; f_equal.
        extensionality y.
        destruct (X y); simpl.
        eapply v; reflexivity.
  Qed.

  Definition TYPE (c: CODE): Type@{u0} :=
    REC (get_ind (rebuild c)).

  Lemma TYPE_shrink:
    forall a ok,
    TYPE (shrink a ok) = REC a.
  Proof.
    intros.
    unfold TYPE.
    destruct rebuild; simpl.
    eapply v; reflexivity.
  Qed.

  Local Definition IDX: CODE :=
    shrink IDX' canonical_idx.

  Local Lemma TYPE_IDX:
    TYPE IDX = A.
  Proof.
    unfold TYPE.
    destruct (rebuild IDX); simpl.
    specialize (v _ _ eq_refl).
    now rewrite v.
  Qed.

  Local Definition LIFT (a: A): CODE :=
    shrink (LIFT' a) (canonical_lift a).

  Local Lemma TYPE_LIFT:
    forall a,
    TYPE (LIFT a) = B a.
  Proof.
    intros.
    unfold TYPE.
    destruct (rebuild (LIFT a)); simpl.
    specialize (v _ _ eq_refl).
    now rewrite v.
  Qed.

  Local Definition CTOR (n: ctor_index) (a: CODE) (b: TYPE a -> CODE): CODE :=
    let a' := rebuild a in
    let b' y := rebuild (b y) in
    shrink (CTOR' n (get_ind a') (fun y => get_ind (b' y)))
      (canonical_ctor n _ _ (get_canonical a') (fun y => get_canonical (b' y))).

  Lemma TYPE_CTOR:
    forall n a b,
    TYPE (CTOR n a b) = GET_CTOR n (TYPE a) (fun x => TYPE (b x)).
  Proof.
    intros.
    unfold TYPE.
    destruct (rebuild (CTOR n a b)); simpl.
    specialize (v _ _ eq_refl).
    now rewrite v.
  Qed.

End Family.

Arguments IDX {A} {B} {C}.
Arguments LIFT {A} {B} {C}.
Arguments CTOR {A} {B} {C}.
Arguments TYPE {A} {B} {C}.

Section Preliminaries.

  Definition finite (n: nat): Set :=
    { m: nat | m < n }.

  Definition pi (A: Type) (B: A -> Type): Type :=
    forall x: A, B x.

  Definition sigma (A: Type) (B: A -> Type): Type :=
    @sigT A B.

  Cumulative Inductive w (A: Type) (B: A -> Type): Type :=
    | sup (a: A) (f: B a -> w A B): w A B.

  Cumulative CoInductive m (A: Type) (B: A -> Type): Type := inf {
    seed: A;
    step: B seed -> m A B
  }.

End Preliminaries.

Structure universe: Type := {
  U: Set;
  T: U -> Set;
  NAT: U;
  T_NAT: T NAT = nat;
  FIN: nat -> U;
  T_FIN: forall n, T (FIN n) = finite n;
  PI: forall a: U, (T a -> U) -> U;
  T_PI: forall a b, T (PI a b) = (forall x: T a, T (b x));
  SIGMA: forall a: U, (T a -> U) -> U;
  T_SIGMA: forall a b, T (SIGMA a b) = { x: T a & T (b x) };
  W: forall a: U, (T a -> U) -> U;
  T_W: forall a b, T (W a b) = w (T a) (fun x => T (b x));
  M: forall a: U, (T a -> U) -> U;
  T_M: forall a b, T (M a b) = m (T a) (fun x => T (b x))
}.

Arguments T {u}.
Arguments T_FIN {u}.
Arguments T_PI {u}.
Arguments T_SIGMA {u}.
Arguments T_W {u}.
Arguments T_M {u}.

Local Notation ctors :=
  [pi; sigma; w; m].

Program Definition u0: universe := {|
  U := CODE nat finite ctors;
  T := TYPE;
  NAT := IDX;
  FIN := LIFT;
  PI := CTOR 0;
  SIGMA := CTOR 1;
  W := CTOR 2;
  M := CTOR 3
|}.

Next Obligation of u0.
  apply TYPE_IDX.
Qed.

Next Obligation of u0.
  apply TYPE_LIFT.
Qed.

Next Obligation of u0.
  apply TYPE_CTOR.
Qed.

Next Obligation of u0.
  apply TYPE_CTOR.
Qed.

Next Obligation of u0.
  apply TYPE_CTOR.
Qed.

Next Obligation of u0.
  apply TYPE_CTOR.
Qed.

Program Definition next_universe (u: universe): universe := {|
  U := CODE (U u) (@T u) ctors;
  T := TYPE;
  NAT := LIFT (NAT u);
  FIN n := LIFT (FIN u n);
  PI := CTOR 0;
  SIGMA := CTOR 1;
  W := CTOR 2;
  M := CTOR 3
|}.

Next Obligation of next_universe.
  rewrite TYPE_LIFT.
  apply T_NAT.
Qed.

Next Obligation of next_universe.
  rewrite TYPE_LIFT.
  apply T_FIN.
Qed.

Next Obligation of next_universe.
  apply TYPE_CTOR.
Qed.

Next Obligation of next_universe.
  apply TYPE_CTOR.
Qed.

Next Obligation of next_universe.
  apply TYPE_CTOR.
Qed.

Next Obligation of next_universe.
  apply TYPE_CTOR.
Qed.

Fixpoint un (i: nat): universe :=
  match i with
  | 0 => u0
  | S j => next_universe (un j)
  end.

Program Definition uw: universe := {|
  U := CODE { i: nat & U (un i) } (fun p => T (projT2 p)) ctors;
  T := TYPE;
  NAT := LIFT (existT 0 (NAT u0));
  FIN n := LIFT (existT 0 (FIN u0 n));
  PI := CTOR 0;
  SIGMA := CTOR 1;
  W := CTOR 2;
  M := CTOR 3
|}.

Next Obligation of uw.
  rewrite TYPE_LIFT; simpl.
  apply TYPE_IDX.
Qed.

Next Obligation of uw.
  rewrite TYPE_LIFT; simpl.
  apply TYPE_LIFT.
Qed.

Next Obligation of uw.
  apply TYPE_CTOR.
Qed.

Next Obligation of uw.
  apply TYPE_CTOR.
Qed.

Next Obligation of uw.
  apply TYPE_CTOR.
Qed.

Next Obligation of uw.
  apply TYPE_CTOR.
Qed.

Program Definition us: universe := {|
  U := CODE nat finite ((fun A B => CODE A B ctors) :: ctors);
  T := TYPE;
  NAT := IDX;
  FIN := LIFT;
  PI := CTOR 1;
  SIGMA := CTOR 2;
  W := CTOR 3;
  M := CTOR 4
|}.

Next Obligation of us.
  apply TYPE_IDX.
Qed.

Next Obligation of us.
  apply TYPE_LIFT.
Qed.

Next Obligation of us.
  apply TYPE_CTOR.
Qed.

Next Obligation of us.
  apply TYPE_CTOR.
Qed.

Next Obligation of us.
  apply TYPE_CTOR.
Qed.

Next Obligation of us.
  apply TYPE_CTOR.
Qed.
