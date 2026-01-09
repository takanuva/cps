(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
Require Import Program.
Require Import Relations.
Require Import Morphisms.

Set Primitive Projections.

Polymorphic Class Setoid: Type := {
  carrier: Type;
  equiv: relation carrier;
  setoid_equiv: Equivalence equiv
}.

Add Printing Let Setoid.

Global Coercion carrier: Setoid >-> Sortclass.

Global Existing Instance setoid_equiv.

Notation "x == y" := (equiv x y)
  (at level 70, no associativity): type_scope.

Notation "x =/= y" := (complement equiv x y)
  (at level 70, no associativity): type_scope.

Polymorphic Class SetoidFunction (S: Setoid) (T: Setoid): Type := {
  function: S -> T;
  function_respectful:
    Proper (equiv ==> equiv) function
}.

Global Coercion function: SetoidFunction >-> Funclass.

Global Existing Instance function_respectful.

Infix "~>" := SetoidFunction (at level 90, right associativity).

Polymorphic Class Category: Type := {
  obj: Type;
  hom: obj -> obj -> Setoid;
  id {x}: hom x x;
  post {x y z}: hom x y -> hom y z -> hom x z;
  post_respectful {x y z}:
    Proper (equiv ==> equiv ==> equiv) (@post x y z);
  post_id_left {x y}:
    forall f: hom x y,
    post id f == f;
  post_id_right {x y}:
    forall f: hom x y,
    post f id == f;
  post_assoc {x y z w}:
    forall f: hom x y,
    forall g: hom y z,
    forall h: hom z w,
    post f (post g h) == post (post f g) h
}.

Add Printing Let Category.

Global Coercion obj: Category >-> Sortclass.

Global Coercion hom: Category >-> Funclass.

Global Existing Instance post_respectful.

Global Polymorphic Program Instance SetCategory: Category := {
  obj := Set;
  hom T U := {|
    carrier := T -> U;
    equiv f g := forall x, f x = g x
  |};
  id {T} x := x;
  post {T U V} f g x := g (f x)
}.

Next Obligation of SetCategory.
  split; repeat intro.
  - reflexivity.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Next Obligation of SetCategory.
  repeat intro.
  now rewrite H, H0.
Qed.

Global Polymorphic Program Instance SetoidCategory: Category := {
  obj := Setoid;
  hom T U := {|
    carrier := T ~> U;
    equiv f g := forall x, f x == g x
  |};
  id {T} := {|
    function x := x
  |};
  post {T U V} f g := {|
    function x := g (f x)
  |}
}.

Next Obligation of SetoidCategory.
  split; repeat intro.
  - reflexivity.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Next Obligation of SetoidCategory.
  firstorder.
Qed.

Next Obligation of SetoidCategory.
  repeat intro.
  now rewrite H.
Qed.

Next Obligation of SetoidCategory.
  repeat intro; simpl.
  now rewrite H, H0.
Qed.

Next Obligation of SetoidCategory.
  reflexivity.
Qed.

Next Obligation of SetoidCategory.
  reflexivity.
Qed.

Next Obligation of SetoidCategory.
  reflexivity.
Qed.
