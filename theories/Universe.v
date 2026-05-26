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

  Local Notation TYPE := (Type@{u0}).

  Local Notation constructor :=
    (forall X: TYPE, (X -> TYPE) -> TYPE).

  Variable A: Set.
  Variable B: A -> TYPE.
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

  Definition TARSKI: @Sig TYPE :=
    sigma branch (fun b: branch =>
      match b with
      | U_idx =>
        iota (A: TYPE)
      | U_lift =>
        sigma A (fun a: A =>
          iota (B a))
      | U_ctor =>
        sigma ctor_index (fun n =>
          delta unit (fun Ta: unit -> TYPE =>
            delta (Ta tt) (fun Tb: Ta tt -> TYPE =>
              iota (GET_CTOR n (Ta tt) Tb))))
      end).

  Local Definition IND: Type :=
    E TARSKI (total (muE TARSKI)) projT1.

  Local Definition REC: IND -> TYPE :=
    F TARSKI (total (muE TARSKI)) projT1.

  Local Definition embed (x: IND): total (muE TARSKI) :=
    existT (REC x) (inE TARSKI (exist x eq_refl)).

  Definition IDX': IND :=
    existT U_idx tt.

  Definition LIFT' (a: A): IND :=
    existT U_lift
      (existT a tt).

  Definition CTOR' (n: ctor_index) (a: IND) (b: REC a -> IND): IND :=
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

  Definition valid_type (c: CODE) (T: TYPE): Type :=
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
    forall T: TYPE,
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

  (* Definition T (c: CODE): TYPE :=
    REC (get_ind (rebuild c)).

  Lemma T_shrink:
    forall a ok,
    T (shrink a ok) = REC a.
  Proof.
    intros.
    unfold T.
    destruct rebuild; simpl.
    eapply v; reflexivity.
  Qed. *)

  (*
  Definition IDX: CODE :=
    shrink IDX' canonical_idx.

  Lemma T_IDX:
    T IDX = A.
  Proof.
    unfold T.
    destruct (rebuild IDX); simpl.
    specialize (v _ _ eq_refl).
    now rewrite v.
  Qed.

  Definition LIFT (a: A): CODE :=
    shrink (LIFT' a) (canonical_lift a).

  Lemma T_LIFT:
    forall a,
    T (LIFT a) = B a.
  Proof.
    intros.
    unfold T.
    destruct (rebuild (LIFT a)); simpl.
    specialize (v _ _ eq_refl).
    now rewrite v.
  Qed.

  Definition CTOR (n: ctor_index) (a: CODE) (b: T a -> CODE): CODE :=
    let a' := rebuild a in
    let b' y := rebuild (b y) in
    shrink (CTOR' n (get_ind a') (fun y => get_ind (b' y)))
      (canonical_ctor n _ _ (get_canonical a') (fun y => get_canonical (b' y))).

  Lemma T_CTOR:
    forall n a b,
    T (CTOR n a b) = GET_CTOR n (T a) (fun x => T (b x)).
  Proof.
    intros.
    unfold T.
    destruct (rebuild (CTOR n a b)); simpl.
    specialize (v _ _ eq_refl).
    now rewrite v.
  Qed.
  *)

End Family.

Definition finite (n: nat): Set :=
  { m: nat | m < n }.

Cumulative Inductive w (A: Type) (B: A -> Type): Type :=
  | sup (a: A) (f: B a -> w A B): w A B.

(*
  Cumulative CoInductive m (A: Type) (B: A -> Type): Type := inf {
    seed: A;
    step: B seed -> m A B
  }.
*)

Class Universe: Type := {
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
  T_W: forall a b, T (W a b) = w (T a) (fun x => T (b x))
}.
