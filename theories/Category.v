(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
Require Import Program.
Require Import Relations.
Require Import Morphisms.

Set Primitive Projections.

Polymorphic Structure Setoid: Type := {
  carrier :> Type;
  equiv: relation carrier;
  setoid_equiv :: Equivalence equiv
}.

Add Printing Let Setoid.

Arguments equiv {s}.

Notation "x == y" := (equiv x y)
  (at level 70, no associativity): type_scope.

Notation "x =/= y" := (complement equiv x y)
  (at level 70, no associativity): type_scope.

Polymorphic Structure SetoidMorphism (S: Setoid) (T: Setoid): Type := {
  setoid_fun: S -> T;
  setoid_fun_respectful:
    Proper (equiv ==> equiv) setoid_fun
}.

Global Coercion setoid_fun: SetoidMorphism >-> Funclass.

Global Existing Instance setoid_fun_respectful.

Infix "~>" := SetoidMorphism (at level 90, right associativity).

Polymorphic Structure Category: Type := {
  obj :> Type;
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

Global Existing Instance post_respectful.

Global Coercion hom: Category >-> Funclass.

Arguments id {c x}.
Arguments post {c x y z}.
Arguments post_respectful {c x y z}.
Arguments post_id_left {c x y}.
Arguments post_id_right {c x y}.
Arguments post_assoc {c x y z w}.

Definition SmallCategory: Type := Category@{Set Set}.

Global Typeclasses Transparent SmallCategory.

Polymorphic Program Definition opposite (C: Category): Category := {|
  obj := C;
  hom := flip C;
  id x := id;
  post x y z := flip post
|}.

Obligation 1 of opposite.
  repeat intro.
  now apply post_respectful.
Qed.

Obligation 2 of opposite.
  apply post_id_right.
Qed.

Obligation 3 of opposite.
  apply post_id_left.
Qed.

Obligation 4 of opposite.
  symmetry.
  apply post_assoc.
Qed.

Polymorphic Structure Functor (C: Category) (D: Category): Type := {
  mapping :> C -> D;
  fmap {x y}: C x y -> D (mapping x) (mapping y);
  fmap_respectful {x y}:
    Proper (equiv ==> equiv) (@fmap x y);
  fmap_id {x}:
    @fmap x x (@id C x) == (@id D (mapping x));
  fmap_comp {x y z}:
    forall f: C x y,
    forall g: C y z,
    fmap (post f g) == post (fmap f) (fmap g)
}.

Global Existing Instance fmap_respectful.

Arguments mapping {C D} F: rename.
Arguments fmap {C D} F {x y}: rename.

(* -------------------------------------------------------------------------- *)

Polymorphic Definition funext_eq T U: relation (T -> U) :=
  fun f g => forall x, f x = g x.

Global Polymorphic Program Definition FunctionSetoid T U: Setoid := {|
  carrier := T -> U;
  equiv := funext_eq T U
|}.

Obligation 1 of FunctionSetoid.
  split; repeat intro.
  - reflexivity.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Global Canonical Structure FunctionSetoid.

Global Program Definition SetCategory: Category := {|
  obj := Set;
  hom T U := T -> U;
  id T x := x;
  post T U V f g x := g (f x)
|}.

Obligation 1 of SetCategory.
  repeat intro.
  now rewrite H, H0.
Qed.

Obligation 2 of SetCategory.
  repeat intro.
  reflexivity.
Qed.

Obligation 3 of SetCategory.
  repeat intro.
  reflexivity.
Qed.

Obligation 4 of SetCategory.
  repeat intro.
  reflexivity.
Qed.

Global Canonical Structure SetCategory.

Global Polymorphic Program Definition MorphismSetoid S T: Setoid := {|
  carrier := S ~> T;
  equiv f g := forall x, f x == g x
|}.

Obligation 1 of MorphismSetoid.
  split; repeat intro.
  - reflexivity.
  - now rewrite H.
  - now rewrite H, H0.
Qed.

Global Canonical Structure MorphismSetoid.

Global Program Definition SetoidCategory: Category := {|
  obj := Setoid;
  hom T U := T ~> U;
  (* TODO: can we coerce those from regular functions...? *)
  id T := {|
    setoid_fun x := x
  |};
  post T U V f g := {|
    setoid_fun x := g (f x)
  |}
|}.

Obligation 1 of SetoidCategory.
  firstorder.
Qed.

Obligation 2 of SetoidCategory.
  repeat intro.
  now rewrite H.
Qed.

Obligation 3 of SetoidCategory.
  repeat intro; simpl.
  now rewrite H, H0.
Qed.

Obligation 4 of SetoidCategory.
  reflexivity.
Qed.

Obligation 5 of SetoidCategory.
  reflexivity.
Qed.

Obligation 6 of SetoidCategory.
  reflexivity.
Qed.

(* TODO: fix this warning. *)
Global Canonical Structure SetoidCategory.

(* -------------------------------------------------------------------------- *)

Polymorphic Definition Presheaf (C: Category): Type :=
  Functor (opposite C) Setoid.

Polymorphic Section Restriction.

  Variable C: Category.
  Variable X: C.
  Variable Y: C.
  Variable F: C Y X.
  Variable G: Presheaf C.

  Polymorphic Definition restrict: G X -> G Y :=
    fmap G F.

End Restriction.

Arguments restrict {C X Y} F {G}.
