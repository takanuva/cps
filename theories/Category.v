(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
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

Existing Instance setoid_equiv.

Notation "x == y" := (equiv x y)
  (at level 70, no associativity): type_scope.

Notation "x =/= y" := (complement equiv x y)
  (at level 70, no associativity): type_scope.

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

Existing Instance post_respectful.
