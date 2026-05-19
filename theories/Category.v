(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
Require Import Program.
Require Import Relations.
Require Import Morphisms.
Require Import Local.Setoid.

Set Primitive Projections.
Set Universe Polymorphism.

(* We take an almost standard definition for categories, by giving the desired
   structure over (1) a type of objects, and (2) a family of setoids for sorting
   morphisms. This definition also uses a postcomposition operator instead of
   the more usual regular composition operator, though of course both are easily
   equivalent (for every f and g, post f g = comp g f). We recall that this will
   form a setoid-enriched category, also called an E-category.

   For convenience, we identify the category with the type of objects and the
   family of morphisms. *)

Structure Category: Type := {
  obj :> Type;
  hom: obj -> obj -> Setoid;
  id {x}: hom x x;
  post {x y z}: hom x y ~> hom y z ~> hom x z;
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

Global Coercion hom: Category >-> Funclass.

Arguments id {c x}.
Arguments post {c x y z}.
Arguments post_id_left {c x y}.
Arguments post_id_right {c x y}.
Arguments post_assoc {c x y z w}.

(* We use universe polymorphism in order to more easily tackle size issues. But
   for convenience, we also define a notion of small category, which is just a
   category where both the type of objects and the (carrier type of the) setoid
   are small (thus live in Set). *)

SubClass SmallCategory: Type@{Set+1} := Category@{Set Set}.

(* We define the opposite category construction, which takes a category C and
   build a new category C^op (here opposite C) by taking as the type of objects
   the same one from C, but inverting all the morphism; i.e., f is a morphism
   from X to Y in C if and only if it is a morphism from Y to X in C^op. All the
   laws in the structure are derivable. *)

Program Definition opposite (C: Category): Category := {|
  obj := C;
  (* TODO: can we change this to flip C? Gotta add some machinery then! *)
  hom X Y := C Y X;
  id X := id;
  post X Y Z := map f g => post g f
|}.

Next Obligation of opposite.
  now rewrite H.
Qed.

Next Obligation of opposite.
  now rewrite H.
Qed.

Next Obligation of opposite.
  apply post_id_right.
Qed.

Next Obligation of opposite.
  apply post_id_left.
Qed.

Next Obligation of opposite.
  symmetry.
  apply post_assoc.
Qed.

Global Program Example set_category: Category := {|
  obj := Set;
  hom T U := T -> U;
  id T := fun x => x;
  post T U V := map f g => fun x => g (f x)
|}.

Next Obligation of set_category.
  repeat intro; simpl.
  now rewrite H.
Qed.

Next Obligation of set_category.
  repeat intro; simpl.
  now rewrite H.
Qed.

Next Obligation of set_category.
  repeat intro; simpl.
  reflexivity.
Qed.

Next Obligation of set_category.
  repeat intro; simpl.
  reflexivity.
Qed.

Next Obligation of set_category.
  repeat intro; simpl.
  reflexivity.
Qed.

Global Canonical Structure set_category.

(* ... *)

Global Program Definition partial_category: Category := {|
  obj := PartialSetoid;
  hom P Q := Domain P ~> Domain Q;
  id T := map x => x;
  post T U V := map f g x => g (f x)
|}.

Next Obligation of partial_category.
  now rewrite H.
Qed.

Next Obligation of partial_category.
  now rewrite H.
Qed.

Next Obligation of partial_category.
  reflexivity.
Qed.

Next Obligation of partial_category.
  reflexivity.
Qed.

Next Obligation of partial_category.
  reflexivity.
Qed.

(* TODO: fix this warning! *)

Global Canonical Structure partial_category.

(* ... *)

Section Isomorphism.

  Variable C: Category.

  Structure Isomorphism (X: C) (Y: C) (iso_to: C X Y): Type := isomorphism_mk {
    iso_from: C Y X;
    iso_to_from: post iso_to iso_from == id;
    iso_from_to: post iso_from iso_to == id;
  }.

  Definition iso_to (X: C) (Y: C) (f: C X Y) (i: Isomorphism X Y f): C X Y :=
    f.

  Definition iso_rev:
    forall X Y f i,
    Isomorphism Y X (iso_from X Y f i).
  Proof.
    intros.
    destruct i as (g, ?H, ?H); simpl.
    now apply isomorphism_mk with f.
  Qed.

  Definition isomorphism (X: C) (Y: C): Prop :=
    exists f: C X Y, inhabited (Isomorphism X Y f).

  Global Instance isomorphism_equiv: Equivalence isomorphism.
  Proof.
    split; repeat intro.
    - exists id; constructor.
      apply isomorphism_mk with id.
      + now rewrite post_id_left.
      + now rewrite post_id_left.
    - destruct H as (f, (?X)).
      exists (iso_from x y f X).
      constructor.
      apply iso_rev.
    - destruct H as (f1, (?H)).
      destruct H0 as (f2, (H0)).
      destruct H as (g1, ?H, ?H).
      destruct H0 as (g2, ?H, ?H).
      exists (post f1 f2); constructor.
      apply isomorphism_mk with (post g2 g1).
      + rewrite <- post_assoc.
        rewrite post_assoc with (f := f2).
        rewrite H0.
        rewrite post_id_left.
        assumption.
      + rewrite <- post_assoc.
        rewrite post_assoc with (f := g1).
        rewrite H1.
        rewrite post_id_left.
        assumption.
  Qed.

End Isomorphism.

Arguments Isomorphism {C}.
Arguments isomorphism {C}.
Arguments iso_to {C} {X} {Y}.
Arguments iso_from {C} {X} {Y}.
Arguments iso_to_from {C} {X} {Y}.
Arguments iso_from_to {C} {X} {Y}.
Arguments iso_rev {C} {X} {Y}.

(* ... *)

(* As usual, we define functors from categories C and D as structure-preserving
   morphisms. So we keep to functions: one for converting objects from C to D,
   and one for converting morphisms from C to D, which respects the categorical
   structure. *)

Structure Functor (C: Category) (D: Category): Type := {
  mapping :> C -> D;
  fmap {x y}: C x y ~> D (mapping x) (mapping y);
  fmap_id {x}:
    @fmap x x (@id C x) == (@id D (mapping x));
  fmap_comp {x y z}:
    forall f: C x y,
    forall g: C y z,
    fmap (post f g) == post (fmap f) (fmap g)
}.

Arguments mapping {C D} F: rename.
Arguments fmap {C D} F {x y}: rename.
  
(* ... *)

Section NaturalTransformation.

  Variable C: Category.
  Variable D: Category.

  Variable F: Functor C D.
  Variable G: Functor C D.

  Structure NaturalTransformation: Type := {
    transformation: forall X, D (F X) (G X);
    transformation_naturality X Y f:
      post (fmap F f) (transformation Y) == post (transformation X) (fmap G f)
  }.

  Definition transformation' (A: NaturalTransformation) (X: C): D (F X) (G X) :=
    transformation A X.

  Definition transformation_equiv A B: Prop :=
    forall X: C, transformation' A X == transformation' B X.

  Program Definition transformation_setoid: Setoid := {|
    setoid_carrier := NaturalTransformation;
    setoid_equiv := transformation_equiv
  |}.

  Next Obligation of transformation_setoid.
    intro.
    reflexivity.
  Qed.

  Next Obligation of transformation_setoid.
    intro.
    now symmetry.
  Qed.

  Next Obligation of transformation_setoid.
    intro.
    now transitivity (transformation y X).
  Qed.

  Global Canonical Structure transformation_setoid.

End NaturalTransformation.

Arguments NaturalTransformation {C} {D}.
Arguments transformation_equiv {C} {D} {F} {G}.
Arguments transformation_setoid {C} {D}.
Arguments transformation {C} {D} {F} {G}.
Arguments transformation' {C} {D} {F} {G}.

Global Coercion transformation': NaturalTransformation >-> Funclass.

Definition naturality {C D F G} (A: @NaturalTransformation C D F G) X Y f:
  post (fmap F f) (A Y) == post (A X) (fmap G f) :=
  transformation_naturality C D F G A X Y f.

Global Instance transformation_proper:
  forall C D F G,
  Proper (setoid_equiv ==> forall_relation (fun X => setoid_equiv))
    (@transformation' C D F G).
Proof.
  repeat intro.
  apply H.
Qed.

(* ... *)

Section FunctorCategory.

  Variable C: Category.
  Variable D: Category.

  Global Program Definition functor_category: Category := {|
    obj := Functor C D;
    hom F G := NaturalTransformation F G;
    id F :=
      {| transformation X := @id D (F X) |};
    post F G H := map A B =>
      {| transformation X :=
        post (A X) (B X)
      |}
  |}.

  Next Obligation of functor_category.
    rewrite post_id_right.
    rewrite post_id_left.
    reflexivity.
  Qed.

  Next Obligation of functor_category.
    rewrite post_assoc.
    rewrite naturality.
    rewrite <- post_assoc.
    rewrite naturality.
    rewrite post_assoc.
    reflexivity.
  Qed.

  Next Obligation of functor_category.
    repeat intro; simpl.
    now rewrite H0.
  Qed.

  Next Obligation of functor_category.
    repeat intro; simpl.
    now rewrite H0.
  Qed.

  Next Obligation of functor_category.
    repeat intro; simpl.
    apply post_id_left.
  Qed.

  Next Obligation of functor_category.
    repeat intro; simpl.
    apply post_id_right.
  Qed.

  Next Obligation of functor_category.
    repeat intro; simpl.
    apply post_assoc.
  Qed.

  Global Canonical Structure functor_category.

End FunctorCategory.

(* TODO: review comment block.

   There are some distinct but equivalent definitions for presheafs; we take,
   perhaps, the most common one (or close enough to it): that a presheaf on C is
   a functor from C^op to the category of setoids. The usual definition goes to
   the category of sets instead, of course, so what we define is technically a
   "setoid-valued presheaf in C". *)

Definition Presheaf (C: Category): Type :=
  Functor (opposite C) PartialSetoid.

(* For convenience, we also treat presheafs as if defined by restricting maps;
   a presheaf G in C will have, for every object X of C, a setoid G X, and also
   a restriction operation: for every morphism C Y X, the presheaf will map from
   G X into G Y, thus restricting the basic elements used within the set. *)

Section Restriction.

  Variable C: Category.
  Variable X: C.
  Variable Y: C.
  Variable F: C Y X.
  (* TODO: should we generalize to any category D instead of Setoid? *)
  Variable G: Presheaf C.

  Definition restrict: Domain (G X) ~> Domain (G Y) :=
    fmap G F.

End Restriction.

Arguments restrict {C X Y} F {G}.

Lemma restrict_id:
  forall C: Category,
  forall G: Presheaf C,
  forall X: C,
  forall S: Domain (G X),
  restrict id S == S.
Proof.
  intros; unfold restrict.
  (* TODO: I'd like to have rewrite fmap_id in here! :( *)
  assert (fmap G id (y := X) == id) by apply fmap_id.
  now rewrite H.
Qed.

(* ... *)

(* Section Yoneda.

  Variable C: Category.

  (* TODO: should this be an example...? Will we be using this? *)

  Program Definition Yoneda: Functor C (Presheaf C) := {|
    mapping X := {|
      mapping Y := C Y X;
      fmap Y Z := {|
        setoid_map f := {|
          setoid_map g := post (f: C Z Y) (g: C Y X)
        |}
      |}
    |};
    fmap Y Z := {|
      setoid_map f := {|
        transformation X := {|
          setoid_map g := post (g: C X Y) (f: C Y Z)
        |}
      |}
    |}
  |}.

  Obligation 1 of Yoneda.
    repeat intro.
    now rewrite H.
  Qed.

  Obligation 2 of Yoneda.
    repeat intro; simpl.
    now rewrite H.
  Qed.

  Obligation 3 of Yoneda.
    now rewrite post_id_left.
  Qed.

  Obligation 4 of Yoneda.
    now rewrite post_assoc.
  Qed.

  Obligation 5 of Yoneda.
    repeat intro.
    now rewrite H.
  Qed.

  Obligation 6 of Yoneda.
    now rewrite post_assoc.
  Qed.

  Obligation 7 of Yoneda.
    repeat intro; simpl.
    now rewrite H.
  Qed.

  Obligation 8 of Yoneda.
    now rewrite post_id_right.
  Qed.

  Obligation 9 of Yoneda.
    now rewrite post_assoc.
  Qed.

End Yoneda. *)

(* ... *)

Structure Terminal (C: Category): Type := {
  terminal: C;
  terminal_hom X: C X terminal;
  terminal_unique:
    forall X: C,
    forall f: C X terminal,
    f == terminal_hom X
}.

Global Arguments terminal {C}.
Global Arguments terminal_hom {C} t {X}.

Global Coercion terminal: Terminal >-> obj.
Global Coercion terminal_hom: Terminal >-> Funclass.

(* -------------------------------------------------------------------------- *)

(* We define the notion of a category with families, which forms a model of
   basic dependent type theory. This is a category C, such that:

   - we call the objects of C contexts (environments), and they model such;
   - we call the morphisms of C substitutions, and they model such;
   - an empty context, which is a terminal object of C;
   - ...

   TODO: properly document this, specially the relationship to explicit
   substitution and to the sigma-calculus, which is quite evident!
*)

Structure CwF := {
  (* ... *)
  cwf_cat: Category;
  (* ... *)
  cwf_env :=
    obj cwf_cat;
  (* ... *)
  cwf_sub: cwf_cat -> cwf_cat -> Setoid :=
    hom cwf_cat;
  (* ... *)
  cwf_empty: Terminal cwf_cat;
  (* ... *)
  cwf_ty: cwf_env -> Setoid;
  cwf_tsub {G D}:
    cwf_sub D G ~> cwf_ty G ~> cwf_ty D;
  (* ... *)
  cwf_el G: SetoidFamily (cwf_ty G);
  cwf_esub {G D A}:
    forall s: cwf_sub D G,
    cwf_el G A ~> cwf_el D (cwf_tsub s A);
  (* ... *)
  cwf_transp {G A B} (H: A == B) :=
    setoid_transport (cwf_el G) H;
  (* ... *)
  cwf_u {G}: nat -> cwf_ty G;
  cwf_t {G n}:
    forall X: cwf_el G (cwf_u n),
    cwf_ty G;
  cwf_lift {G n l}:
    forall H: n < l,
    forall X: cwf_el G (cwf_u n),
    cwf_el G (cwf_u l);
  (* ... *)
  cwf_ucoh {G n l}:
    forall H: n < l,
    forall X: cwf_el G (cwf_u n),
    cwf_t (cwf_lift H X) == cwf_t X
}.

(*

(* TODO: temporary...! *)
Coercion Domain: PartialSetoid >-> Sortclass.

Coercion domain_cast: partial_path >-> Funclass.

Structure CwF: Type := {
  (* TODO: can we enforce that this is small? Check later! *)
  cwf_cat: Category;
  cwf_env := obj cwf_cat;
  cwf_sub := hom cwf_cat;
  cwf_empty: Terminal cwf_cat;
  (* ... *)
  cwf_ty: cwf_env -> PartialSetoid;
  cwf_tsub {G D}:
    cwf_sub D G -> cwf_ty G -> cwf_ty D;
  (* ... *)
  cwf_el G: cwf_ty G ~> PartialSetoid;
  cwf_esub {G D A}:
    forall s: cwf_sub D G,
    cwf_el G A -> cwf_el D (cwf_tsub s A);
  cwf_transp {G A B} (H: A == B) :=
    cong (cwf_el G) H;
  (* ... *)
  cwf_ext G: cwf_ty G -> cwf_env;
  cwf_cons {G D}:
    forall s: cwf_sub D G,
    forall A: cwf_ty G,
    cwf_el D (cwf_tsub s A) ->
    cwf_sub D (cwf_ext G A);
  cwf_proj {G A}:
    cwf_sub (cwf_ext G A) G;
  cwf_zero {G A}:
    cwf_el (cwf_ext G A) (cwf_tsub cwf_proj A);
  (* ... *)
  cwf_tsub_respectful {G D}:
    Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) (@cwf_tsub G D);
  cwf_tsub_id {G}:
    forall {A: cwf_ty G},
    cwf_tsub id A == A;
  cwf_tsub_comp {G D E}:
    forall {s: cwf_sub D G},
    forall {r: cwf_sub E D},
    forall {A: cwf_ty G},
    cwf_tsub r (cwf_tsub s A) == cwf_tsub (post r s) A;
  (* TODO: we need to check that esub is respectful, but that is a form of
     heterogeneous equality; figure it out how to do that later, please? *)
  (* TODO: cwf_esub_id, same reason... *)
  (* TODO: cwf_esub_comp, same reason... *)
  (* TODO: should cwf_ext be respectful? Cause it doesn't make much sense that
     there would be an isomorphism between the resulting contexts afterwards, as
     morphisms are meant to be substitutions! *)
  (* TODO: show that snoc, proj and zero need to be respectful. *)
  (* TODO: law for p o (a, s) = s *)
  (* TODO: law for q[a, s] = a *)
  (* TODO: law for (a, s) o r = (a[r], s o r) *)
  (* TODO: law for (q, p) = id *)
  (* TODO: do we need eta? I.e., (q[s], p o s) = s? This derives the above... *)
  (* ... *)
  (* Given e: El(G, A), we take (e/) = (e[id], id) : G -> (G, A). This is just
     the subst/slash substitution built out of cons and identity. *)
  cwf_slash {G A} (e: cwf_el G A) :=
    cwf_cons id A (cwf_esub id e);
  (* Given a substitution s: D -> G, we want to lift it into another scope by
     defining up s = (0, (s o proj)) : (D, A[s]) -> (G, A). *)
  cwf_up {G D A} (s: cwf_sub D G) :=
    cwf_cons (post cwf_proj s) A (cwf_transp cwf_tsub_comp cwf_zero)
}.

*)
