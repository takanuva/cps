(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Relations.
Require Import Morphisms.

Set Primitive Projections.

Polymorphic Definition structure: Type := Type -> Type.

Polymorphic Record packed {S: structure}: Type := pack_carrier {
  carrier :> Type;
  structure_def: S carrier
}.

Global Coercion packed: structure >-> Sortclass.

Global Canonical Structure structure_search :=
  fun (T: Set) {S: structure} `{H: S T} => pack_carrier S T H.

Polymorphic Inductive Setoid: structure :=
  | Setoid_mk:
    forall C: Type,
    forall R: relation C,
    Equivalence R -> Setoid C.

Existing Class Setoid.
Add Printing Let Setoid.

Definition setoid_def: forall S: Setoid, Setoid S :=
  structure_def.

Existing Instance setoid_def.

Definition equiv {T} `{S: Setoid T}: relation T :=
  match S in Setoid X return relation X with
  | Setoid_mk _ R _ => R
  end.

Notation "x == y" := (equiv x y)
  (at level 70, no associativity): type_scope.

Notation "x =/= y" := (complement equiv x y)
  (at level 70, no associativity): type_scope.

Instance setoid_equiv: forall {T} (S: Setoid T), Equivalence (@equiv T S).
Proof.
  intros.
  destruct S as (C, R, H).
  assumption.
Qed.

Polymorphic Inductive Category: structure :=
  | Category_mk:
    forall obj: Type,
    forall arr: obj -> obj -> Setoid,
    forall id: (forall {X: obj}, arr X X),
    forall postcomp: (forall {X Y Z}, arr X Y -> arr Y Z -> arr X Z),
    (forall {x y z},
       Proper (equiv ==> equiv ==> equiv) (@postcomp x y z)) ->
    (forall {x y} (f: arr x y),
       postcomp id f == f) ->
    (forall {x y} (f: arr x y),
       postcomp f id == f) ->
    (forall {x y z w} (f: arr x y) (g: arr y z) (h: arr z w),
       postcomp f (postcomp g h) == postcomp (postcomp f g) h) ->
    Category obj.

Existing Class Category.
Add Printing Let Category.
