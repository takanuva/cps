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

Polymorphic Inductive Category: structure :=
  | Category_mk:
    forall O: Type,
    forall A: O -> O -> Setoid,
    Category O.

Existing Class Category.
