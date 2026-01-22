(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
Require Import Program.
Require Import Relations.
Require Import Morphisms.

Set Primitive Projections.

(* In general, category theory is agnostic in respect to the foundation used to
   build it. As we are working within Coq's type theory, and our use case needs
   a lot of reasoning on sets, we instead start by defining setoids. We will of
   course take advantage a lot of Coq's generalized rewriting mechanisms. The
   idea is to simulate quotient types, which are not available, constructively.

   A setoid is just a carrier type equipped with an equivalence relation that
   represents the desired notion of equality within this type. We define here
   carrier as a reversible coercion (so that we may identify the carrier set
   with the setoid itself), and setoid_equiv as an instance proving that the
   packed relation is indeed an equivalence relation over the carrier type. *)

Polymorphic Structure Setoid: Type := {
  carrier :> Type;
  equiv: relation carrier;
  setoid_equiv: Equivalence equiv
}.

Add Printing Let Setoid.

Arguments equiv {s}.

Global Existing Instance setoid_equiv.

Notation "x == y" := (equiv x y)
  (at level 70, no associativity): type_scope.

Notation "x =/= y" := (complement equiv x y)
  (at level 70, no associativity): type_scope.

(* We define a notion of setoid morphisms (a structure-preserving function over
   two setoids) as a type-theoretic function over the two carrier sets, along
   with a proof that this is a proper morphism, preserving the structure. I.e.,
   for setoids S and T, if x: S and y: S such that x == y, a morphism f: S ~> T
   will guarantee that f x == f y. Notice the coercion for the packed function,
   which is given for convenience. *)

Polymorphic Structure SetoidMorphism (S: Setoid) (T: Setoid): Type := {
  setoid_fun: S -> T;
  setoid_fun_respectful:
    Proper (equiv ==> equiv) setoid_fun
}.

Global Coercion setoid_fun: SetoidMorphism >-> Funclass.

Global Existing Instance setoid_fun_respectful.

Infix "~>" := SetoidMorphism (at level 90, right associativity).

(* We take an almost standard definition for categories, by giving the desired
   structure over (1) a type of objects, and (2) a family of setoids for sorting
   morphisms. This definition also uses a postcomposition operator instead of
   the more usual regular composition operator, though of course both are easily
   equivalent (for every f and g, post f g = comp g f).

   For convenience, we identify the category with the type of objects and the
   family of morphisms. *)

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

(* We use universe polymorphism in order to more easily tackle size issues. But
   for convenience, we also define a notion of small category, which is just a
   category where both the type of objects and the (carrier type of the) setoid
   are small (thus live in Set).

   TODO: can we force this definition to live in Type 0...? *)

SubClass SmallCategory: Type := Category@{Set Set}.

(* We define the opposite category construction, which takes a category C and
   build a new category C^op (here opposite C) by taking as the type of objects
   the same one from C, but inverting all the morphism; i.e., f is a morphism
   from X to Y in C if and only if it is a morphism from Y to X in C^op. All the
   laws in the structure are derivable. *)

Polymorphic Program Definition opposite (C: Category): Category := {|
  obj := C;
  hom X Y := C Y X;
  id x := id;
  post x y z f g := post g f
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

(* We define, as a test and an example, a category of sets and functions (which
   we will not be using in favor of setoids, of course). As morphisms, we define
   the desired notion of equivalence for functions as extensional equality (so
   that we would not need to take that as an axiom, since it's not derivable in
   Coq's type theory anyway). First we define a canonical setoid for functions,
   and then proceed to build the canonical category for sets. *)

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

Global Program Example SetCategory: Category := {|
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

(* We now do a similar thing and define a category of setoids and setoid
   morphisms as previously defined. So first make a canonical definition to set
   the desired notion of equality of morphisms (which is similar to functional
   extensionality!), and then proceed to build the canonical category. *)

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

(* TODO: fix this warning! *)

Global Canonical Structure SetoidCategory.

(* As usual, we define functors from categories C and D as structure-preserving
   morphisms. So we keep to functions: one for converting objects from C to D,
   and one for converting morphisms from C to D, which respects the categorical
   structure. *)

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

(* ... *)

Polymorphic Section NaturalTransformation.

  Variable C: Category.
  Variable D: Category.

  Variable F: Functor C D.
  Variable G: Functor C D.

  Polymorphic Structure NaturalTransformation: Type := {
    transformation: forall X: C, D (F X) (G X);
    naturality X Y f:
      post (fmap F f) (transformation Y) == post (transformation X) (fmap G f)
  }.

  Polymorphic Program Definition NaturalTransformationSetoid: Setoid := {|
    carrier := NaturalTransformation;
    equiv A B :=
      forall X: C,
      transformation A X == transformation B X
  |}.

  Obligation 1 of NaturalTransformationSetoid.
    split; repeat intro.
    - reflexivity.
    - now symmetry.
    - now transitivity (transformation y X).
  Qed.

  (* TODO: fix this warning! *)

  Global Canonical Structure NaturalTransformationSetoid.

End NaturalTransformation.

Arguments NaturalTransformation {C} {D}.
Arguments NaturalTransformationSetoid {C} {D}.
Arguments transformation {C} {D} {F} {G}.
Arguments naturality {C} {D} {F} {G}.

Global Coercion transformation: NaturalTransformation >-> Funclass.

(* ... *)

Polymorphic Section FunctorCategory.

  Variable C: Category.
  Variable D: Category.

  Global Polymorphic Program Definition FunctorCategory: Category := {|
    obj := Functor C D;
    hom F G := NaturalTransformation F G;
    id F :=
      (* TODO: can we use just id here...? *)
      {| transformation X := @id D (F X) |};
    post F G H A B :=
      {| transformation X := post (transformation A X) (transformation B X) |}
  |}.

  Obligation 1 of FunctorCategory.
    rewrite post_id_right.
    rewrite post_id_left.
    reflexivity.
  Qed.

  Obligation 2 of FunctorCategory.
    rewrite post_assoc.
    rewrite naturality.
    rewrite <- post_assoc.
    rewrite naturality.
    rewrite post_assoc.
    reflexivity.
  Qed.

  Obligation 3 of FunctorCategory.
    repeat intro; simpl.
    now rewrite H, H0.
  Qed.

  Obligation 4 of FunctorCategory.
    now rewrite post_id_left.
  Qed.

  Obligation 5 of FunctorCategory.
    now rewrite post_id_right.
  Qed.

  Obligation 6 of FunctorCategory.
    now rewrite post_assoc.
  Qed.

  Global Canonical Structure FunctorCategory.

End FunctorCategory.

(* There are some distinct but equivalent definitions for presheafs; we take,
   perhaps, the most common one (or close enough to it): that a presheaf on C is
   a functor from C^op to the category of setoids. The usual definition goes to
   the category of sets instead, of course, so what we define is technically a
   "setoid-valued presheaf in C". *)

Polymorphic Definition Presheaf (C: Category): Type :=
  Functor (opposite C) Setoid.

(* For convenience, we also treat presheafs as if defined by restricting maps;
   a presheaf G in C will have, for every object X of C, a setoid G X, and also
   a restriction operation: for every morphism C Y X, the presheaf will map from
   G X into G Y, thus restricting the basic elements used within the set. *)

Polymorphic Section Restriction.

  Variable C: Category.
  Variable X: C.
  Variable Y: C.
  Variable F: C Y X.
  (* TODO: should we generalize to any category D instead of Setoid? *)
  Variable G: Presheaf C.

  Polymorphic Definition restrict: G X ~> G Y :=
    fmap G F.

End Restriction.

Arguments restrict {C X Y} F {G}.

Polymorphic Lemma restrict_id:
  forall C: Category,
  forall G: Presheaf C,
  forall X: C,
  forall S: G X,
  restrict id S == S.
Proof.
  intros; unfold restrict.
  (* TODO: I'd like to have rewrite fmap_id in here! *)
  assert (fmap G id (y := X) == id) by apply fmap_id.
  simpl in H.
  now rewrite H.
Qed.

(* ... *)

Polymorphic Section Yoneda.

  Variable C: Category.

  (* TODO: should this be an example...? *)

  Polymorphic Program Definition Yoneda: Functor C (Presheaf C) := {|
    mapping X := {|
      mapping Y := C Y X;
      fmap Y Z f := {|
        setoid_fun g := post (f: C Z Y) (g: C Y X)
      |}
    |};
    fmap Y Z f := {|
      transformation X := {|
        setoid_fun g := post (g: C X Y) (f: C Y Z)
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

End Yoneda.

(* ... *)

Polymorphic Structure Terminal (C: Category): Type := {
  terminal: C;
  terminal_hom X: C X terminal;
  terminal_unique:
    forall X: C,
    forall f: C X terminal,
    f == terminal_hom X
}.

Global Coercion terminal: Terminal >-> obj.
Global Coercion terminal_hom: Terminal >-> Funclass.

(* We define the notion of a category with family, which forms a model of basic
   dependent type theory. This is a small category C, such that:

   - we call the objects of C contexts, and they model such;
   - we call the morphisms of C substitutions, and they model such;
   - an empty context, which is a terminal object of C;
   - ...

   TODO: properly document this, specially the relationship to explicit
   substitution and to the sigma-calculus, which is quite evident.
*)

Polymorphic Structure CwF: Type := {
  (* We start with a category of contexts and substitutions, such that it has
     a terminal object, which represents the empty context. TODO: do we want it
     to be small? *)
  cwf_cat: Category;
  cwf_empty: Terminal cwf_cat;
  (* ... *)
  cwf_type: cwf_cat -> Setoid;
  cwf_ctxext G: cwf_type G -> cwf_cat;
  cwf_tsubst {D G}:
    cwf_cat D G -> cwf_type G -> cwf_type D;
  (* TODO: tsubst composition law. *)
  (* TODO: tsubst identity law. *)
  (* ... *)
  cwf_elem: forall G: cwf_cat, cwf_type G -> Setoid;
  cwf_esubst {D G A}:
    forall s: cwf_cat D G,
    cwf_elem G A -> cwf_elem D (cwf_tsubst s A);
  (* TODO: esubst composition law. *)
  (* TODO: esubst identity law. *)
  (* ... *)
  cwf_snoc {D G A}:
    forall s: cwf_cat D G,
    cwf_elem D (cwf_tsubst s A) -> cwf_cat D (cwf_ctxext G A);
  cwf_proj {G}:
    forall A: cwf_type G,
    cwf_cat (cwf_ctxext G A) G;
  cwf_zero {G}:
    forall A: cwf_type G,
    cwf_elem (cwf_ctxext G A) (cwf_tsubst (cwf_proj A) A)
  (* TODO: laws on proj and zero. *)
}.

Global Coercion cwf_cat: CwF >-> Category.

(* -------------------------------------------------------------------------- *)

(* Should be (cwf_snoc C id a), with proper coercions... *)

(* Fail Check forall {C G A} (a: cwf_elem C G A), cwf_snoc C id a.

Axiom cwf_subst:
  forall {M G A} (a: cwf_elem M G A),
  cwf_cat M G (cwf_ctxext M G A). *)

(* Thus if B in Type(G.A) and a in Elem(G, A), we have B[a] in Type(G).

   If b in Elem[G.A, B], we have b[a] in Elem(G, B[a]). *)

(* We define, for s in D -> G and A in Type(G), our uplifting operation as
   (s p, q), of course, in D.sA -> G.A. *)

(* Variable M: CwF.

Variable D: obj (cwf_cat M).
Variable G: obj (cwf_cat M).

Variable s: hom (cwf_cat M) D G.

Variable A: cwf_type M G.

Definition sA: cwf_type M D := (cwf_tsubst M s A).

Definition p: cwf_cat M (cwf_ctxext M D sA) D :=
  cwf_proj M (cwf_tsubst M s A).

Definition ps: cwf_cat M (cwf_ctxext M D sA) G :=
  post p s.

Check cwf_zero M A.

Definition q := cast (cwf_zero M sA).

Check cwf_snoc M ps q.
*)

(* Check cwf_tsubst.

Require Import Equality.

Lemma foo:
  forall M G A B,
  A == B ->
  cwf_elem M G A = cwf_elem M G B.
Proof.
  admit.
Admitted.

Local Lemma cast:
  forall {M D G E},
  forall {r: hom (cwf_cat M) D G} {s: hom (cwf_cat M) G E},
  forall {A},
  cwf_elem M D (cwf_tsubst M r (cwf_tsubst M s A)) ->
  cwf_elem M D (cwf_tsubst M (post r s) A).
Proof.
  intros.
  erewrite foo.
  - exact X.
  - admit.
Admitted.

Section Uplift.

  Variable M: CwF.

  Variable D: obj (cwf_cat M).
  Variable G: obj (cwf_cat M).
  Variable A: cwf_type M G.
  Variable s: hom (cwf_cat M) D G.

  Polymorphic Definition cwf_uplift:
    hom (cwf_cat M) (cwf_ctxext M D (cwf_tsubst M s A)) (cwf_ctxext M G A) :=
    (* up(s) = (q, (p; s)). *)
    let sA := (cwf_tsubst M s A) in
    cwf_snoc M (post (cwf_proj M sA) s) (cast (cwf_zero M sA)).

End Uplift.

Arguments cwf_uplift M {D} {G} {A}. *)

(* -------------------------------------------------------------------------- *)

(* Polymorphic Section Universes.

  Variable C: CwF.

  Polymorphic Structure CwF'U: Type := {
    cwf_universe G: nat -> cwf_type C G;
    cwf_el G n:
      cwf_elem C G (cwf_universe G n) ->
      cwf_type C G;
    cwf_foo G n m:
      n <= m ->
      cwf_elem C G (cwf_universe G n) ->
      cwf_elem C G (cwf_universe G m);
    cwf_bar G n m:
      forall H: n <= m,
      forall X: cwf_elem C G (cwf_universe G n),
      (* TODO: not an equality... an isomorphism? *)
      cwf_el G m (cwf_foo G n m H X) = cwf_el G n X
  }.

End Universes. *)
