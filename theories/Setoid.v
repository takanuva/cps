(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
Require Import Program.
Require Import Relations.
Require Import Morphisms.

Set Primitive Projections.
Set Universe Polymorphism.

(* In this project, we'll need to formalize some categorical notions.

   In general, category theory is agnostic in respect to the foundation used to
   build it. As we are working within Coq's type theory, and our use case needs
   a lot of reasoning on sets, we instead start by defining setoids. We will of
   course take advantage a lot of Coq's generalized rewriting mechanisms. The
   idea is to simulate quotient types, which are not available, constructively.

   A setoid is just a carrier type equipped with an equivalence relation that
   represents the desired notion of equality within this type. We define here
   carrier as a reversible coercion (so that we may identify the carrier set
   with the setoid itself), and setoid_equiv as an instance proving that the
   packed relation is indeed an equivalence relation over the carrier type. *)

Cumulative Structure Setoid: Type := {
  setoid_carrier :> Type;
  setoid_equiv: setoid_carrier -> setoid_carrier -> Prop;
  setoid_refl:
    forall x,
    setoid_equiv x x;
  setoid_sym:
    forall x y,
    setoid_equiv x y -> setoid_equiv y x;
  setoid_trans:
    forall x y z,
    setoid_equiv x y -> setoid_equiv y z -> setoid_equiv x z
}.

Arguments setoid_equiv {s}.
Arguments setoid_refl {s}.
Arguments setoid_sym {s}.
Arguments setoid_trans {s}.

SubClass SmallSetoid: Type@{Set+1} := Setoid@{Set}.

Global Instance setoid_equiv_equivalence:
  forall S,
  RelationClasses.Equivalence (@setoid_equiv S).
Proof.
  split.
  - exact setoid_refl.
  - exact setoid_sym.
  - exact setoid_trans.
Defined.

Notation "x == y" := (setoid_equiv x y)
  (at level 70, no associativity): type_scope.

(* TODO: will we use this? *)

Ltac setoidify :=
  repeat progress match goal with
  | H: ?R ?x ?y |- _ =>
    change R with (@setoid_equiv _) in H
  | |- context C [?R ?x ?y] =>
    change (R x y) with (@setoid_equiv _ x y)
  end.

(* TODO: review comment block...

   We define a notion of setoid maps (a structure-preserving function over two
   total setoids) as a type-theoretic function over the two carrier sets, along
   with a proof that this is a proper morphism, preserving the structure. I.e.,
   for setoids S and T, if x: S and y: S such that x == y, a morphism f: S ~> T
   will guarantee that f x == f y. Notice the coercion for the packed function,
   which is given for convenience. *)

Structure SetoidMap (S: Setoid) (T: Setoid): Type := {
  setoid_map: S -> T;
  cong: forall x y, x == y -> setoid_map x == setoid_map y
}.

Arguments cong {S} {T} s {x} {y}.

(* ... *)

Definition setoid_map' {S} {T} (f: SetoidMap S T): S -> T :=
  setoid_map S T f.

Global Coercion setoid_map': SetoidMap >-> Funclass.

Global Notation "'map' p .. q => e" :=
  {| setoid_map p := (.. {| setoid_map q := e |} ..) |}
  (at level 200, p binder, q binder, e at level 200, only parsing).

Global Program Definition setoid_map_setoid S T: Setoid := {|
  setoid_carrier := SetoidMap S T;
  setoid_equiv f g := forall x, f x == g x
|}.

Next Obligation of setoid_map_setoid.
  reflexivity.
Qed.

Next Obligation of setoid_map_setoid.
  now symmetry.
Qed.

Next Obligation of setoid_map_setoid.
  rename x0 into w.
  now transitivity (y w).
Qed.

Global Canonical Structure setoid_map_setoid.

Global Notation "S ~> T" := (setoid_map_setoid S T)
  (at level 99, T at level 200, right associativity).

Global Instance setoid_fun_proper:
  forall S T,
  Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) (@setoid_map' S T).
Proof.
  repeat intro.
  rename x into f, y into g, x0 into x, y0 into y.
  transitivity (g x).
  - apply H.
  - now apply cong.
Qed.

(* ... *)

Structure PartialSetoid: Type := {
  partial_carrier: Type;
  partial_equiv: partial_carrier -> partial_carrier -> Prop;
  partial_sym:
    forall x y,
    partial_equiv x y -> partial_equiv y x;
  partial_trans:
    forall x y z,
    partial_equiv x y -> partial_equiv y z -> partial_equiv x z
}.

Arguments partial_equiv {p}.
Arguments partial_sym {p}.
Arguments partial_trans {p}.

Global Instance partial_equiv_per:
  forall S,
  RelationClasses.PER (@partial_equiv S).
Proof.
  split.
  - exact partial_sym.
  - exact partial_trans.
Defined.

Definition partial_inclusion (S: Setoid): PartialSetoid := {|
  partial_carrier := setoid_carrier S;
  partial_equiv := setoid_equiv;
  partial_sym := setoid_sym;
  partial_trans := setoid_trans
|}.

Global Canonical Structure partial_inclusion.

Global Coercion partial_inclusion: Setoid >-> PartialSetoid.

(* ... *)

Definition Domain (P: PartialSetoid): Type :=
  { wit: partial_carrier P | partial_equiv wit wit }.

Definition domain_equiv {P: PartialSetoid} (x: Domain P) (y: Domain P): Prop :=
  partial_equiv (`x) (`y).

Definition self_relation {P: PartialSetoid} (x: Domain P): domain_equiv x x :=
  proj2_sig x.

Program Definition domain_setoid (P: PartialSetoid): Setoid := {|
  setoid_carrier := Domain P;
  setoid_equiv := @domain_equiv P
|}.

Next Obligation.
  apply self_relation.
Qed.

Next Obligation.
  now apply partial_sym.
Qed.

Next Obligation.
  now apply partial_trans with (`y).
Qed.

Global Canonical Structure domain_setoid.
