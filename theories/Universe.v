(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Program.
Require Import Equality.
Require Import Local.InductionRecursion.
Require Import Local.Setoid.
Require Import Local.Category.

Import ListNotations.
Set Universe Polymorphism.
Set Primitive Projections.

(* This file will have a version of my technique for encoding Tarski universes
   in Coq, as shown in https://github.com/takanuva/tarski-rocq, but this time
   using setoids to avoid the need for functional extensionality. Of course I
   would prefer to avoid uniqueness of identity proofs as well, but most of my
   codebase in this repository uses it already... so why bother? Sorry.

   We also construct an enhanced version; instead of abstracting the universes
   over some family of types, we also abstract them over types constructors, so
   that we may also build Palmgren's notion of a superuniverse and we may have
   codes for D-sets within the universes (for the proof of strong normalization
   for the dependent type theory). *)

Section Family.

  Monomorphic Universe u.

  Local Notation TYPE := (Type@{u}).

  Variable A: Set.
  Variable B: A -> TYPE.
  Variable C: list (forall (X: TYPE), (X -> TYPE) -> TYPE).

  Variant branch: Set :=
    | U_idx
    | U_lift
    | U_ctor.

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

  Arguments projT1 {A} {P}.
  Arguments projT2 {A} {P}.
  Arguments exist {A} {P}.
  Arguments existT {A} {P}.

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

  Structure valid_type (c: CODE) (T: TYPE): Type := witness {
    cast:
      forall a H, c = shrink a H -> T -> REC a
  }.

  Arguments cast {c} {T} v {a} {H}.

  Definition right_child:
    forall c: CODE,
    forall H: U_ctor = get_branch c,
    forall T: TYPE,
    forall X: valid_type (left_child c H) T,
    forall x: T,
    CODE.
  Proof.
    intros.
    destruct c.
    destruct ok; try easy.
    simpl in *.
    set (y := cast X eq_refl x).
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
      + simpl.
        assumption.
      + simpl in X |- *.
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

  (*

  Local Notation GOAL c :=
    { x: IND & canonical x & forall a H, c = shrink a H -> x == a }.

  Definition get_ind {c: CODE} (x: GOAL c): IND :=
    let (a, ok_a, H) := x in a.

  Definition get_canonical {c: CODE} (x: GOAL c): canonical (get_ind x) :=
    let (a, ok_a, H) return canonical (get_ind x) := x in ok_a.

  (* The main component: from any code, we can rebuild its elements, while
     recursively also keeping track that the constructor is injective. *)

  Definition rebuild:
    forall x: CODE,
    GOAL x.
  Proof.

  *)

End Family.
