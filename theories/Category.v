(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
Require Import Program.
Require Import Relations.
Require Import Morphisms.

Set Primitive Projections.
Set Universe Polymorphism.

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

Structure Setoid: Type := {
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

(* TODO: review comment block...

   We define a notion of setoid maps (a structure-preserving function over two
   total setoids) as a type-theoretic function over the two carrier sets, along
   with a proof that this is a proper morphism, preserving the structure. I.e.,
   for setoids S and T, if x: S and y: S such that x == y, a morphism f: S ~> T
   will guarantee that f x == f y. Notice the coercion for the packed function,
   which is given for convenience. *)

Structure SetoidMap (S: Setoid) (T: Setoid): Type := {
  setoid_map: S -> T;
  setoid_map_coherence:
    forall x y, x == y -> setoid_map x == setoid_map y
}.

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
  Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) (@setoid_map S T).
Proof.
  repeat intro.
  rename x into f, y into g, x0 into x, y0 into y.
  transitivity (setoid_map S T g x).
  - apply H.
  - now apply setoid_map_coherence.
Qed.

(* ... *)

Structure PartialSetoid: Type := {
  partial_carrier :> Type;
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

Structure Domain (P: PartialSetoid): Type := relate {
  wit: P;
  self_relation: partial_equiv wit wit
}.

Arguments wit {P}.

Definition domain_equiv {P: PartialSetoid} (x: Domain P) (y: Domain P): Prop :=
  partial_equiv (wit x) (wit y).

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
  now apply partial_trans with (wit y).
Qed.

Global Canonical Structure domain_setoid.

(* We take an almost standard definition for categories, by giving the desired
   structure over (1) a type of objects, and (2) a family of setoids for sorting
   morphisms. This definition also uses a postcomposition operator instead of
   the more usual regular composition operator, though of course both are easily
   equivalent (for every f and g, post f g = comp g f). We recall that this will
   form a setoid-enriched category, also called an E-category.

   For convenience, we identify the category with the type of objects and the
   family of morphisms. *)

Definition Morphism := PartialSetoid.

Definition HomSetoid (f: Morphism): Setoid :=
  domain_setoid (f :> PartialSetoid).

Global Coercion HomSetoid: Morphism >-> Setoid.

Structure Category: Type := {
  obj :> Type;
  hom: obj -> obj -> Morphism;
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

(* We define, as a test and an example, a category of sets and functions (which
   we will not be using in favor of setoids, of course). As morphisms, we define
   the desired notion of equivalence for functions as extensional equality (so
   that we would not need to take that as an axiom, since it's not derivable in
   Coq's type theory anyway). First we define a canonical setoid for dependent
   functions, as a generalization, and then we proceed to build the canonical
   category for sets. *)

Definition funext_eq T U: relation (forall t: T, U t) :=
  fun f g => forall x, f x = g x.

Global Program Definition function_setoid T U: Setoid := {|
  setoid_carrier := forall t: T, U t;
  setoid_equiv := funext_eq T U
|}.

Next Obligation.
  repeat intro.
  reflexivity.
Qed.

Next Obligation.
  repeat intro.
  now rewrite H.
Qed.

Next Obligation.
  repeat intro.
  now rewrite H, H0.
Qed.

Global Canonical Structure function_setoid.

Global Program Example set_category: Category := {|
  obj := Set;
  hom T U := (T -> U) :> Setoid;
  id T := {| wit x := x |};
  (* TODO: I would very much like to generalize this notation and add implicits
     casts to the domain... I'd like to write something like:

      [morphism f g x => g (f x)]

     Can we figure it out a way to do that once we have some time? *)
  post T U V := map f g => {| wit x := wit g (wit f x) |}
|}.

Next Obligation of set_category.
  repeat intro.
  reflexivity.
Qed.

Next Obligation of set_category.
  repeat intro.
  reflexivity.
Qed.

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
  hom P Q := (Domain P ~> Domain Q) :> Setoid;
  (* TODO: c'mon, these are too ugly! We gotta improve the notation and add some
     nice coercions in here... *)
  id T := {| wit := map x => x |};
  post T U V := map f g => {| wit := map x => wit g (wit f x) |}
|}.

Next Obligation of partial_category.
  reflexivity.
Qed.

Next Obligation of partial_category.
  now rewrite H.
Qed.

Next Obligation of partial_category.
  reflexivity.
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

(* Section Isomorphism.

  Variable C: Category.

  Structure Isomorphism (X: C) (Y: C): Type := isomorphism_mk {
    iso_to: C X Y;
    iso_from: C Y X;
    iso_to_from: post iso_to iso_from == id;
    iso_from_to: post iso_from iso_to == id;
  }.

  Definition isomorphism (X: C) (Y: C): Prop :=
    inhabited (Isomorphism X Y).

  Global Instance IsomorphismEquiv: Equivalence isomorphism.
  Proof.
    split; repeat intro.
    - constructor.
      apply isomorphism_mk with id id.
      + now rewrite post_id_left.
      + now rewrite post_id_left.
    - destruct H.
      destruct X as (f, g, ?H, ?H).
      constructor.
      apply isomorphism_mk with g f.
      + assumption.
      + assumption.
    - destruct H, H0.
      destruct X as (f1, g1, ?H, ?H).
      destruct X0 as (f2, g2, ?H, ?H).
      constructor.
      apply isomorphism_mk with (post f1 f2) (post g2 g1).
      + rewrite <- post_assoc.
        rewrite post_assoc with (f := f2).
        rewrite H1.
        rewrite post_id_left.
        assumption.
      + rewrite <- post_assoc.
        rewrite post_assoc with (f := g1).
        rewrite H0.
        rewrite post_id_left.
        assumption.
  Qed.

End Isomorphism.

Arguments Isomorphism {C}.
Arguments isomorphism {C}.
Arguments iso_to {C} {X} {Y}.
Arguments iso_from {C} {X} {Y}.
Arguments iso_to_from {C} {X} {Y}.
Arguments iso_from_to {C} {X} {Y}. *)

(* ... *)

Structure partial_path (P: PartialSetoid) (Q: PartialSetoid): Prop := {
  partial_path_eq:
    partial_carrier P = partial_carrier Q;
  partial_transp (p: P) :=
    match partial_path_eq in (_ = T) return T with
    | eq_refl => p
    end :> Q;
  partial_reclassify:
    forall x y,
    partial_equiv x y <-> partial_equiv (partial_transp x) (partial_transp y)
}.

Arguments partial_path_eq {P} {Q}.
Arguments partial_transp {P} {Q}.
Arguments partial_reclassify {P} {Q}.

Program Definition domain_cast {P} {Q} H (p: Domain P): Domain Q :=
  {| wit := partial_transp H (wit p) |}.

Next Obligation.
  destruct p as (w, ?H); simpl in *.
  destruct H as (?H, ?H, ?H); simpl in *.
  destruct P as (P, ?H, ?H, ?H); simpl in *.
  destruct Q as (Q, ?H, ?H, ?H); simpl in *.
  subst; apply H2.
  assumption.
Qed.

(* ... *)

Global Program Definition partial_setoid: Setoid := {|
  setoid_carrier := PartialSetoid;
  setoid_equiv := partial_path
|}.

Next Obligation.
  rename x into P.
  exists eq_refl; split; intros.
  - assumption.
  - assumption.
Qed.

Next Obligation.
  destruct H as (?H, ?H, ?H); simpl in *.
  destruct x as (P, PR, ?H, ?H); simpl in *.
  destruct y as (Q, QR, ?H, ?H); simpl in *.
  exists (symmetry H); simpl in *; intros.
  subst; simpl; split; intro.
  - now apply H1.
  - now apply H1.
Qed.

Next Obligation.
  destruct H as (?H, ?H, ?H); simpl in *.
  destruct H0 as (?H, ?H, ?H); simpl in *.
  destruct x as (P, PQ, ?H, ?H); simpl in *.
  destruct y as (Q, QR, ?H, ?H); simpl in *.
  destruct z as (R, RR, ?H, ?H); simpl in *.
  exists (transitivity H H0); simpl in *; intros.
  subst; simpl; split; intro.
  - now apply H4, H2.
  - now apply H2, H4.
Qed.

Global Canonical Structure partial_setoid.

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
    transformation: forall X: C, D (F X) (G X);
    naturality X Y f:
      post (fmap F f) (transformation Y) == post (transformation X) (fmap G f)
  }.

  Program Definition transformation_setoid: Setoid := {|
    setoid_carrier := NaturalTransformation;
    setoid_equiv A B :=
      forall X: C, transformation A X == transformation B X
  |}.

  Next Obligation of transformation_setoid.
    reflexivity.
  Qed.

  Next Obligation of transformation_setoid.
    now symmetry.
  Qed.

  Next Obligation of transformation_setoid.
    now transitivity (transformation y X).
  Qed.

  (* TODO: fix this warning! *)

  Global Canonical Structure transformation_setoid.

End NaturalTransformation.

Arguments NaturalTransformation {C} {D}.
Arguments transformation_setoid {C} {D}.
Arguments transformation {C} {D} {F} {G}.
Arguments naturality {C} {D} {F} {G}.

Global Coercion transformation: NaturalTransformation >-> Funclass.

(* ... *)

Section FunctorCategory.

  Variable C: Category.
  Variable D: Category.

  Global Program Definition functor_category: Category := {|
    obj := Functor C D;
    hom F G := NaturalTransformation F G :> Setoid;
    id F :=
      (* TODO: can we use just id here...? Sigh... *)
      {| wit :=
        {| transformation X := @id D (F X) |}
      |};
    post F G H := map A B =>
      {| wit :=
        {| transformation X :=
          post (wit A X) (wit B X)
        |}
      |}
  |}.

  Next Obligation of functor_category.
    rewrite post_id_right.
    rewrite post_id_left.
    reflexivity.
  Qed.

  Next Obligation of functor_category.
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
    reflexivity.
  Qed.

  Next Obligation of functor_category.
    now rewrite H0.
  Qed.

  Next Obligation of functor_category.
    now rewrite H0.
  Qed.

  Next Obligation of functor_category.
    apply post_id_left.
  Qed.

  Next Obligation of functor_category.
    apply post_id_right.
  Qed.

  Next Obligation of functor_category.
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

  Definition restrict: (G X: Morphism) ~> (G Y: Morphism) :=
    wit (fmap G F).

End Restriction.

Arguments restrict {C X Y} F {G}.

Lemma restrict_id:
  forall C: Category,
  forall G: Presheaf C,
  forall X: C,
  forall S: (G X: Morphism),
  restrict id S == S.
Proof.
  intros; unfold restrict.
  (* TODO: I'd like to have rewrite fmap_id in here! *)
  assert (fmap G id (y := X) == id) by apply fmap_id.
  simpl in H.
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

Global Coercion terminal: Terminal >-> obj.
Global Coercion terminal_hom: Terminal >-> Funclass.

(* We define the notion of a category with families, which forms a model of
   basic dependent type theory. This is a category C, such that:

   - we call the objects of C contexts (environments), and they model such;
   - we call the morphisms of C substitutions, and they model such;
   - an empty context, which is a terminal object of C;
   - ...

   TODO: properly document this, specially the relationship to explicit
   substitution and to the sigma-calculus, which is quite evident!
*)

Structure CwF: Type := {
  (* TODO: can we enforce that it is small? Check later! *)
  cwf_cat: Category;
  cwf_env := obj cwf_cat;
  cwf_sub := hom cwf_cat;
  cwf_empty: Terminal cwf_cat;
  (* ... *)
  cwf_ty: cwf_env -> Setoid;
  cwf_tsub {G D}:
    cwf_sub D G -> cwf_ty G -> cwf_ty D;
  (* ... *)
  cwf_el G: cwf_ty G ~> PartialSetoid;
  cwf_esub {G D A}:
    forall s: cwf_sub D G,
    cwf_el G A -> cwf_el D (cwf_tsub s A);
  (* ... *)
  cwf_ext G: cwf_ty G -> cwf_env;
  cwf_snoc {G D}:
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
    forall A: cwf_ty G,
    cwf_tsub id A == A;
  cwf_tsub_comp {G D E}:
    forall s: cwf_sub D G,
    forall r: cwf_sub E D,
    forall A: cwf_ty G,
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
}.

Global Coercion cwf_cat: CwF >-> Category.

(* -------------------------------------------------------------------------- *)

(* Given e: El(G, A), we take (e/) = (e[id], id) : G -> (G, A). This is just the
   subst/slash substitution built out of cons and identity. *)

Program Definition cwf_slash M {G} {A} e: cwf_sub M G (cwf_ext M G A) :=
  cwf_snoc M id A (cwf_esub M id e).

(* Given a substitution s: D -> G, we want to lift it into another scope by
   defining up s = (0, (proj; s)), which is a morphism (D, A[s]) -> (G, A).
   TODO: there's some bookkeeping here! *)

Program Definition cwf_up (M: CwF) {G} {D}
  (s: cwf_sub M D G)
  (A: cwf_ty M G): M (cwf_ext M D (cwf_tsub M s A)) (cwf_ext M G A) :=
  cwf_snoc M (post (cwf_proj M) s) A _.

Next Obligation of cwf_up.
  pose proof (@cwf_zero M D (cwf_tsub M s A)).
  (* What now? Zero could return different data for different types on some
     models... we only know there's a non-constructive isomorphism so far... *)
  admit.
Admitted.
