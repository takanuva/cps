(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Category.
Require Import Local.Substitution.
Require Import Local.Combinators.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
(* Require Import Local.Constructions.Inversion. *)

Set Universe Polymorphism.
Set Primitive Projections.

Inductive dset: Type@{Set+1} :=
  | dset_mk:
    forall T: Set,
    forall R: CL -> T -> Prop,
    (forall x1 x2 y, x1 == x2 -> R x2 y -> R x1 y) ->
    (forall y, exists x, R x y) ->
    dset
  | delta_unit:
    dset
  | delta_dset:
    dset.

Definition dset_carrier (G: dset): Type :=
  match G with
  | dset_mk T R _ _ => T
  | delta_unit => unit
  | delta_dset => dset
  end.

Local Coercion dset_carrier: dset >-> Sortclass.

Definition dset_realization (G: dset): CL -> G -> Prop :=
  match G with
  | dset_mk T R _ _ => R
  (* For the following, return the universal relation. *)
  | delta_unit => fun _ _ => True
  | delta_dset => fun _ _ => True
  end.

Local Coercion dset_realization: dset >-> Funclass.

Lemma dset_respectful:
  forall x1 x2,
  x1 == x2 ->
  forall (G: dset) y,
  G x2 y -> G x1 y.
Proof.
  simpl; intros.
  destruct G.
  + now apply r with x2.
  + trivial.
  + trivial.
Qed.

Lemma dset_surjective (G: dset) (y: G): exists x, G x y.
Proof.
  destruct G.
  - apply e.
  - exists I; simpl.
    trivial.
  - exists I; simpl.
    trivial.
Qed.

Structure dmap (G: dset) (D: G -> dset) := {
  dmap_fun: forall g: G, D g;
  dmap_wit: CL;
  dmap_preserves:
    forall y g,
    G y g -> D g (app dmap_wit y) (dmap_fun g)
}.

Global Arguments dmap_fun {G} {D}.
Global Arguments dmap_wit {G} {D}.

Local Coercion dmap_fun: dmap >-> Funclass.

(* TODO: should dmaps carry setoids...? We'll find out later! *)
Definition dmap_equiv {G D}: dmap G D -> dmap G D -> Prop :=
  funext_equiv.

Program Definition dmap_setoid G D: Setoid := {|
  setoid_carrier := dmap G D;
  setoid_equiv := dmap_equiv
|}.

Next Obligation of dmap_setoid.
  repeat intro.
  reflexivity.
Qed.

Next Obligation of dmap_setoid.
  repeat intro.
  now rewrite H.
Qed.

Next Obligation of dmap_setoid.
  repeat intro.
  now rewrite H, H0.
Qed.

Global Canonical Structure dmap_setoid.

Program Definition dset_category: Category := {|
  obj := dset;
  hom G D := dmap G (fun _ => D);
  id G := {|
    dmap_fun x := x;
    dmap_wit := I
  |};
  post G D E := map f g => {|
    dmap_fun x := g (f x);
    dmap_wit := B (dmap_wit g) (dmap_wit f)
  |}
|}.

Next Obligation of dset_category.
  apply dset_respectful with y.
  - apply conv_I.
  - assumption.
Qed.

Next Obligation of dset_category.
  rename g0 into x.
  apply dset_respectful with (dmap_wit g (dmap_wit f y)).
  - apply conv_B.
  - now apply g, f.
Qed.

Next Obligation of dset_category.
  repeat intro; simpl.
  now rewrite H.
Qed.

Next Obligation of dset_category.
  repeat intro; simpl.
  now rewrite H.
Qed.

Next Obligation of dset_category.
  repeat intro; simpl.
  reflexivity.
Qed.

Next Obligation of dset_category.
  repeat intro; simpl.
  reflexivity.
Qed.

Next Obligation of dset_category.
  repeat intro; simpl.
  reflexivity.
Qed.

Definition dset_family_equiv (G: dset): (G -> dset) -> (G -> dset) -> Prop :=
  funext_equiv.

Program Definition dset_family (G: dset): Setoid := {|
  setoid_carrier := G -> dset;
  setoid_equiv := dset_family_equiv G
|}.

Next Obligation of dset_family.
  reflexivity.
Qed.

Next Obligation of dset_family.
  now symmetry.
Qed.

Next Obligation of dset_family.
  now transitivity y.
Qed.

(* TODO: move me! *)
Import EqNotations.

Program Definition dset_model: CwF := {|
  cwf_cat := dset_category;
  cwf_empty := {|
    terminal := delta_unit;
    terminal_hom X := {|
      dmap_fun x := ();
      dmap_wit := I
    |}
  |};
  cwf_ty := dset_family;
  cwf_el (G: dset) := {|
    setoid_family (T: dset_family G) :=
      dmap_setoid G T;
    setoid_transport T U H := {|
      setoid_map E := {|
        dmap_fun (X: G) :=
          rew [dset_carrier] H X in E X;
        dmap_wit := dmap_wit E
      |}
    |}
  |};
  cwf_u (G: dset) (n: nat) (g: G) :=
    delta_dset;
  cwf_t (G: dset) (n: nat) U :=
    dmap_fun U;
  cwf_lift (G: dset) n l (H: n < l) U :=
    U
|}.

Next Obligation of dset_model.
  repeat intro; simpl.
  now destruct (f x).
Qed.

Next Obligation of dset_model.
  destruct (H g); simpl.
  now apply dmap_preserves.
Qed.

Next Obligation of dset_model.
  repeat intro; simpl.
  destruct (H x0); simpl.
  apply H0.
Qed.

Next Obligation of dset_model.
  (* Some rewriting gimmicks here! *)
  repeat intro; simpl.
  generalize (H2 x1) as Y.
  generalize (H1 x1) as X.
  clear H1 H2; intros.
  dependent destruction X; simpl.
  dependent destruction Y; simpl.
  reflexivity.
Qed.

Next Obligation of dset_model.
  repeat intro; simpl.
  generalize (H x1) as X; intros.
  dependent destruction X; simpl.
  reflexivity.
Qed.

Next Obligation of dset_model.
  repeat intro; simpl.
  generalize (H3 x1) as Z.
  generalize (H2 x1) as Y.
  generalize (H1 x1) as X.
  intros.
  dependent destruction X; simpl.
  dependent destruction Y; simpl.
  dependent destruction Z; simpl.
  reflexivity.
Qed.

Next Obligation of dset_model.
  repeat intro.
  reflexivity.
Qed.

Next Obligation of dset_model.
  repeat intro.
  reflexivity.
Qed.

(* Section Elements.

  Variable C: Category.
  Variable G: Functor (opposite C) dset_category.

  Structure elem: Type := elem_mk {
    elem_obj: opposite C;
    elem_set: G elem_obj
  }.

  Record elem_hom (x: elem) (y: elem): Type := elem_hom_mk {
    elem_hom_morphism: opposite C (elem_obj x) (elem_obj y);
    elem_hom_coherence: elem_set y = fmap G elem_hom_morphism (elem_set x)
  }.

  Local Coercion elem_hom_morphism: elem_hom >-> setoid_carrier.

  Program Definition elem_hom_setoid e f: Setoid := {|
    setoid_carrier := elem_hom e f;
    (* We use the D-set morphism definition of equality for the inner map! *)
    setoid_equiv := setoid_equiv
  |}.

  Next Obligation.
    reflexivity.
  Qed.

  Next Obligation.
    now symmetry.
  Qed.

  Next Obligation.
    now transitivity (elem_hom_morphism e f y).
  Qed.

  Local Canonical Structure elem_hom_setoid.

  Program Definition elements_category: Category := {|
    obj := elem;
    hom e f := elem_hom e f;
    id x := elem_hom_mk x x id _;
    post x y z := map f g => elem_hom_mk x z (post f g) _
  |}.

  Next Obligation of elements_category.
    destruct x as (X, Y); simpl.
    (* It's invisible, but beware! *)
    pose proof fmap_id _ _ G Y.
    now symmetry.
  Qed.

  Next Obligation of elements_category.
    destruct f as (X, ?H); simpl.
    destruct g as (Y, ?H); simpl.
    rewrite H0, H.
    (* Again... *)
    pose proof fmap_comp _ _ G X Y.
    now symmetry.
  Qed.

  Next Obligation of elements_category.
    now rewrite H.
  Qed.

  Next Obligation of elements_category.
    now rewrite H.
  Qed.

  Next Obligation of elements_category.
    apply post_id_right.
  Qed.

  Next Obligation of elements_category.
    apply post_id_left.
  Qed.

  Next Obligation of elements_category.
    symmetry.
    apply post_assoc.
  Qed.

End Elements.

Section DPresheaf.

  Variable C: SmallCategory.

  Definition dpresheaf := Functor (opposite C) dset_category.

  Program Definition dpresheaf_model := {|
    cwf_cat := dpresheaf;
    cwf_empty := {|
      terminal := {|
        mapping (X: C) := delta_unit;
        fmap (X: C) (Y: C) :=
          map (f: C Y X) => {|
            dmap_fun (g: delta_unit) := ();
            dmap_wit := I
          |}
      |};
      terminal_hom (F: dpresheaf) := {|
        transformation (X: C) := {|
          dmap_fun (g: F X) := ();
          dmap_wit := I
        |}
      |};
    |};
    cwf_ty (G: dpresheaf) := {|
      partial_carrier := Functor
        (opposite (elements_category C G)) dset_category;
      (* Hmmmm... *)
      partial_equiv := eq
    |};
    cwf_el (G: dpresheaf) :=
      map A => {|
        partial_carrier :=
          (* forall X: C,
          let Ax D := (`A) (elem_mk _ _ X D) in
          partial_carrier (cwf_el dset_model (G X) Ax); *)
          @NaturalTransformation _ _ ({|
        mapping X := delta_unit;
        fmap X Y :=
          map f => {|
            dmap_fun (g: delta_unit) := ();
            dmap_wit := I
          |}
      |}: Functor _ dset_category) (`A);
        partial_equiv := transformation_equiv
      |}
  |}.

  Next Obligation of dpresheaf_model.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of dpresheaf_model.
    repeat intro; simpl.
    now destruct x0.
  Qed.

  Next Obligation of dpresheaf_model.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of dpresheaf_model.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of dpresheaf_model.
    repeat intro; simpl.
    now destruct (f X0 x).
  Qed.

  (* ... *)

  Next Obligation of dpresheaf_model.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of dpresheaf_model.
    repeat intro; simpl.
    now destruct x0.
  Qed.

  Next Obligation of dpresheaf_model.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of dpresheaf_model.
    now symmetry.
  Qed.

  Next Obligation of dpresheaf_model.
    now transitivity y.
  Qed.

  Admit Obligations.

End DPresheaf. *)

(* TODO: backup code, remove later!

(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------------- *)

(* Given some partial combinatory algebra D, which in here we specialize for the
   plain SK combinatory logic, a D-set is a pair (G, R) such that:
   - G is a type that represents a context (the carrier type);
   - R is a relation between D and G that specifies whether an element x of D
     realizes the context g in G;
   - R is respectful of D's inner structure, so x R g <-> y R g when x == y;
   - R is surjective, such that for every g in G, there is at least one x in D
     such that x R g. *)

Polymorphic Record Dset: Type := {
  Dset_carrier :> Type;
  Dset_realization:
    CL -> Dset_carrier -> Prop;
  Dset_respectful:
    forall x1 x2,
    x1 == x2 ->
    forall y, (* Note that conv is symmetric! *)
    Dset_realization x2 y -> Dset_realization x1 y;
  Dset_surjective:
    forall y: Dset_carrier,
    exists x: CL,
    Dset_realization x y
}.

(* We associate the Dset object to the realization relation for convenience. *)

Local Coercion Dset_realization: Dset >-> Funclass.

(* We define an operation to lift an arbitrary type into a D-set by taking the
   full relation as it's realization (thus we don't care about the computational
   content); i.e., any element x realizes contexts. *)

Polymorphic Program Definition Delta (A: Type): Dset := {|
  Dset_carrier := A;
  Dset_realization x y := True
|}.

Next Obligation of Delta.
  (* Any combinator is ok; we merely need to show that some exist. We pick I. *)
  exists I; trivial.
Qed.

(* A mapping between D-set D and D-indexed family of D-sets G, called D-map, is
   a function f between their carrier types such that there is some combinator x
   where, for any element d of D, and for any realizer y such y realizes d in D,
   then x y realizes f d in G d. We call those D-maps here; Streicher calls them
   D-functions or realizable morphisms. *)

Polymorphic Record Dmap (D: Dset) (G: D -> Dset): Type := {
  Dmap_fun: forall d: D, G d;
  (* TODO: does the element x have to be relevant...? *)
  Dmap_preserve: exists x, forall y d, D y d -> G d (app x y) (Dmap_fun d)
}.

Local Coercion Dmap_fun: Dmap >-> Funclass.

(* Two Dmaps are the same iff their inner mappings are extensionally equal. *)

Definition Dmap_eq: forall {X Y}, relation (Dmap X Y) :=
  fun X Y M N => forall x, M x = N x.

(* This, of course, forms a setoid. *)

Polymorphic Program Definition DmapSetoid {X Y}: Setoid := {|
  setoid_carrier := Dmap X Y;
  setoid_equiv := Dmap_eq
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

Global Canonical Structure DmapSetoid.

(* We will often want maps from D-sets into simple D-sets rather than into D-set
   families, so we add an abbreviation for these. *)

Polymorphic Definition Dmap' (D: Dset) (G: Dset) := Dmap D (const G).

(* We may consider the identity Dmap on Dsets, using the identity function. *)

Polymorphic Program Definition Dmap'_id (X: Dset): Dmap' X X := {|
  Dmap_fun x := x
|}.

Obligation 1 of Dmap'_id.
  exists I; intros.
  apply Dset_respectful with y.
  - apply conv_I.
  - assumption.
Qed.

(* Of course, we may compose D-maps using composition of their functions, which
   respects the proper conditions. *)

Polymorphic Program Definition Dmap'_post {X Y Z} (M: Dmap' X Y) (N: Dmap' Y Z):
  Dmap' X Z :=
{|
  Dmap_fun x := N (M x)
|}.

Obligation 1 of Dmap'_post.
  destruct M as (g, (y, ?H)).
  destruct N as (f, (x, ?H)).
  exists (B x y); intros; simpl.
  rename y0 into z.
  apply Dset_respectful with (x (y z)).
  - apply conv_B.
  - now apply H0, H.
Qed.

(* As required, D-sets and D-maps form a category. *)

Polymorphic Program Definition DsetCategory: Category := {|
  obj := Dset;
  hom := Dmap';
  id := Dmap'_id;
  post X Y Z := map f g => Dmap'_post f g
|}.

Next Obligation of DsetCategory.
  repeat intro; simpl.
  now rewrite H.
Qed.

Next Obligation of DsetCategory.
  repeat intro; simpl.
  now rewrite H.
Qed.

Next Obligation of DsetCategory.
  repeat intro; simpl.
  reflexivity.
Qed.

Next Obligation of DsetCategory.
  repeat intro; simpl.
  reflexivity.
Qed.

Next Obligation of DsetCategory.
  repeat intro; simpl.
  reflexivity.
Qed.

Local Canonical Structure DsetCategory.

(* -------------------------------------------------------------------------- *)

Section DsetModel.

  (*
  Program Definition DsetModel: CwF := {|
    cwf_cat := Dset;
    cwf_empty := {|
      terminal := Delta ();
      terminal_hom (X: Dset) := {|
        Dmap_fun (g: X) := ();
      |}
    |};
    cwf_ty G := partial_inclusion (G -> Dset);
    cwf_tsub G D (s: Dmap' D G) (A: G -> Dset | _) (d: D) :=
      A (s d);
    cwf_el G := map A => partial_inclusion (Dmap G A);
    cwf_esub G D (A: G -> Dset | _) (s: Dmap' D G) (e: Dmap G A | _) := {|
      Dmap_fun (d: D) := (`e) (s d)
    |};
    cwf_ext G (A: G -> Dset | _) := {|
      Dset_carrier := { g: G & A g };
      Dset_realization (x: CL) p :=
        let (g, e) := p in G (x K) g /\ A g (x F) e
    |};
    (* TODO: make a general definition for Dset pairs! *)
    cwf_cons G D (s: Dmap' D G) (A: G -> Dset | _) e := {|
      Dmap_fun d := existT _ (s d) ((`e) d)
    |};
    (* First projection. *)
    cwf_proj G (A: G -> Dset | _) := {|
      Dmap_fun p := let (g, e) := p in g
    |};
    (* Second projection. *)
    cwf_zero G (A: G -> Dset | _) := {|
      (* The program mode will make the conversion for us! *)
      Dmap_fun p := _ (* let (g, e) := p in _ e *)
    |}
  |}.

  Next Obligation of DsetModel.
    exists I; intros.
    trivial.
  Qed.

  Next Obligation of DsetModel.
    repeat intro; simpl.
    remember (f x) as u.
    now destruct u.
  Qed.

  Next Obligation of DsetModel.
    repeat intro.
    reflexivity.
  Qed.

  Next Obligation of DsetModel.
    (* Hm, ok, this might not hold yet... *)
    admit.
  Admitted.

  Next Obligation of DsetModel.
    destruct e as (e, (x, ?H)); simpl in *.
    destruct s as (s, (y, ?H)); simpl in *.
    unfold Dmap_eq in H; simpl in *.
    exists (B x y); intros.
    rename y0 into z.
    apply Dset_respectful with (x (y z)).
    - apply conv_B.
    - now apply H1, H2.
  Qed.

  Next Obligation of DsetModel.
    repeat intro; simpl in *.
    reflexivity.
  Qed.

  Next Obligation of DsetModel.
    split.
    - apply Dset_respectful with (x2 K).
      + now rewrite H.
      + assumption.
    - apply Dset_respectful with (x2 F).
      + now rewrite H.
      + assumption.
  Qed.

  Next Obligation of DsetModel.
    rename y into g, X into e.
    destruct Dset_surjective with G g as (x, ?H).
    destruct Dset_surjective with (A g) e as (y, ?H).
    exists (P x y); split.
    - apply Dset_respectful with x.
      + rewrite conv_P.
        rewrite conv_K.
        reflexivity.
      + assumption.
    - apply Dset_respectful with y.
      + rewrite conv_P.
        rewrite conv_F.
        reflexivity.
      + assumption.
  Qed.

  Next Obligation of DsetModel.
    destruct (Dmap_preserve _ _ s) as (x, ?).
    destruct (Dmap_preserve _ _ (`e)) as (y, ?).
    (* Careful inspection: this term is enough! *)
    exists (C (P x y)); intros z ? ?; split.
    - specialize (H0 _ _ H2).
      unfold const in H.
      apply Dset_respectful with (x z).
      + rewrite conv_C.
        rewrite conv_P.
        rewrite conv_K.
        reflexivity.
      + assumption.
    - specialize (H1 _ _ H2).
      apply Dset_respectful with (y z).
      + rewrite conv_C.
        rewrite conv_P.
        rewrite conv_F.
        reflexivity.
      + assumption.
  Qed.

  Next Obligation of DsetModel.
    exists (C I K); intros.
    destruct d as (g, e).
    unfold const.
    apply Dset_respectful with (y K).
    - rewrite conv_C.
      rewrite conv_I.
      reflexivity.
    - destruct H0.
      assumption.
  Qed.

  Next Obligation of DsetModel.
    exists (C I F); intros.
    destruct d as (g, e); simpl.
    apply Dset_respectful with (y F).
    - rewrite conv_C.
      rewrite conv_I.
      reflexivity.
    - destruct H0.
      simpl in H1.
      assumption.
  Qed.

  Next Obligation of DsetModel.
    repeat intro; simpl in *.
    reflexivity.
  Qed.

  Next Obligation of DsetModel.
    repeat intro; simpl.
    now rewrite H, H0.
  Qed.

  Next Obligation of DsetModel.
    repeat intro.
    reflexivity.
  Qed.

  Next Obligation of DsetModel.
    repeat intro.
    reflexivity.
  Qed.
  *)

End DsetModel.

Section Dpresheaf.

  (* TODO: make C polymorphic, turn this into an actual presheaf... *)

  Variable C: Category.

  Local Definition Dpresheaf: Type := Functor (opposite C) Dset.

  (*
  Structure TY (G: Dpresheaf) := {
    TY_fun: forall X: C, cwf_ty DsetModel (G X);
    TY_restriction X Y: forall f: opposite C X Y,
                        cwf_el DsetModel (G X)
                          (cwf_tsub DsetModel (fmap G f) (TY_fun Y));
  }.

  Program Definition foobar X f g (H: f == g) (x: Dmap X f): Dmap X g := {|
    Dmap_fun d := _ (Dmap_fun _ _ x d)
  |}.

  Next Obligation.
    compute in H.
    rewrite <- H.
    assumption.
  Defined.

  Next Obligation.
    compute in H |- *.
    destruct x as (m, (x, ?H)).
    exists x; intros.
    rewrite <- H.
    apply H0.
    assumption.
  Defined. *)

  (* Goal
    forall G: Dpresheaf,
    forall T: TY G,
    forall X: C,
    (Dmap (G X) (fun x => TY_fun _ T X (fmap G id x)): Setoid) ==
    (Dmap (G X) (fun x => TY_fun _ T X x): Setoid).
  Proof.
    intros; simpl.
    constructor.
    eexists.
    Unshelve.
    3: {
      simpl; econstructor.
      Unshelve.
      2: {
        intro.
        simpl in *.
        assert (forall d, fmap G id (y := d) == id) by apply fmap_id.
        apply foobar with (f := fun x => TY_fun _ T X (fmap G id x)).
        - simpl; intro.
          simpl in H.
          rewrite H.
          reflexivity.
        - assumption.
      }
      repeat intro; simpl.
      compute.
      simpl in H.
      unfold Dmap_eq in H.
      rewrite H.
      reflexivity.
    }
    3: {
      simpl; econstructor.
      Unshelve.
      2: {
        intro.
        simpl in *.
        assert (forall d, fmap G id (y := d) == id) by apply fmap_id.
        apply foobar with (f := fun x => TY_fun _ T X x).
        - simpl; intro.
          simpl in H.
          rewrite H.
          reflexivity.
        - assumption.
      }
      compute.
      repeat intro; simpl.
      now rewrite H.
    }
    - compute; intros.
      destruct x as (f, ?H); simpl.
      destruct G as (a, b, ?H, ?H).
      compute in *.
      destruct (H0 X x0).
      reflexivity.
    - compute; intros.
      destruct x as (f, ?H); simpl.
      destruct G as (a, b, ?H, ?H).
      compute in *.
      destruct (H0 X x0).
      reflexivity.
  Qed. *)

  (*

  Axiom TY_EQ: forall G, relation (TY G).

  Local Program Definition TY_setoid (G: Dpresheaf) := {|
    partial_carrier := TY G;
    (* TODO: obviously, fix equivalence... *)
    partial_equiv := TY_EQ G
  |}.

  Next Obligation.
    admit.
  Admitted.

  Next Obligation.
    admit.
  Admitted.

  *)

  (* Program Definition DpresheafModel: CwF := {|
    cwf_cat := Dpresheaf;
    cwf_empty := {|
      terminal := {|
        mapping (X: opposite C) :=
          terminal _ (cwf_empty DsetModel);
        fmap (X: opposite C) (Y: opposite C) := {|
          setoid_map (f: opposite C X Y) := {|
            Dmap_fun (Z: Delta ()) := Z
          |}
        |}
      |};
      terminal_hom (X: Dpresheaf) := {|
        transformation (Y: opposite C) :=
          terminal_hom Dset (cwf_empty DsetModel) (X Y)
      |}
    |};
    cwf_ty (G: Dpresheaf) := TY_setoid G;
    cwf_tsub (G: Dpresheaf) (D: Dpresheaf) (s: NaturalTransformation D G)
      (A: TY G | _) := {|
      TY_fun (X: C) :=
        cwf_tsub DsetModel (s X) (TY_fun G A X);
      TY_restriction (X: C) (Y: C) (f: opposite C X Y) :=
        _
    |};
    (* ... *)
    cwf_el (G: Dpresheaf) := map (A: TY G | _) =>
        partial_inclusion (forall X: C, cwf_el DsetModel (G X) (TY_fun G A X));
        (* TODO: there's a coherence condition here... I think! *)
    cwf_esub (G: Dpresheaf) (D: Dpresheaf) (A: _)
      (s: NaturalTransformation D G) e :=
      (* TODO: is there a cast happening here...? *)
      fun (X: C) => cwf_esub DsetModel (s X) (e X);
    cwf_ext G (A: TY G | _) := {|
      mapping (X: C) := cwf_ext DsetModel (G X) (TY_fun G A X);
      fmap (X: C) (Y: C) := {|
        setoid_map (f: opposite C X Y) := {|
          Dmap_fun (p: { x: G X & TY_fun G A X x }) := _
        |}
      |}
    |};
    cwf_cons G D (s: NaturalTransformation D G) (A: _) e := {|
      transformation (X: C) := _
    |};
    cwf_proj G (A: _) := {|
      transformation (X: C) := _
    |};
    cwf_zero G (A: _) := _
  |}.

  Next Obligation of DpresheafModel.
    exists I; intros.
    assumption.
  Qed.

  Next Obligation of DpresheafModel.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    repeat intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    repeat intro; simpl.
    rename X0 into Y.
    remember (f Y x) as u.
    now destruct u.
  Qed.

  Next Obligation of DpresheafModel.
    set (e := cwf_esub DsetModel (s X) (TY_restriction G A X Y f)).
    destruct s as (s, ?H); simpl in *.
    destruct A as (Af, Ar); simpl in *.
    destruct e as ((e, ?H), _).
    clear H.
    assert (forall d: D X, (` (Af Y)) (s Y (fmap D f d))) as g; intros.
    - clear H1.
      specialize (e d); simpl.
      unfold Dmap_eq, Dmap'_post in H0; simpl in H0.
      now rewrite H0.
    - enough (exists (x: CL), forall y d, D X y d ->
                (` (Af Y)) (s Y (fmap D f d)) (x y) (g d)).
      + now exists {|
          Dmap_fun := g;
          Dmap_preserve := H
        |}.
      + destruct H1 as (x, ?H).
        exists x; intros.
        specialize (H0 X Y f d).
        specialize (H y d H1).
        unfold Dmap'_post in H0; simpl in H0.
        (* Hmm...? *)
        admit.
  Admitted.

  Next Obligation of DpresheafModel.
    repeat intro.
    admit.
  Admitted.

  Next Obligation of DpresheafModel.
    admit.
  Admitted.

  Next Obligation of DpresheafModel.
    repeat intro.
    reflexivity.
  Qed.

  Next Obligation of DpresheafModel.
    rename p into x, X0 into D.
    destruct A as (Af, Ar); simpl in *.
    clear H.
    specialize (Ar X Y f).
    destruct Ar as (g, _); simpl in *.
    exists (fmap G f x).
    apply g.
  Qed.

  Next Obligation of DpresheafModel.
    admit.
  Admitted.

  Admit Obligations. *)

End Dpresheaf.

(* TODO: move these definitions to the [Category.v] file. *)

(* Section Elements.

  Variable C: Category.

  (* TODO: use any kind of presheaf! *)

  Variable G: Dpresheaf C.

  (* The category of elements of G, a presheaf over C, has, as objects, pairs
     of an object X of C and an element r of the set G(X). Then, for every
     morphism f in C from Y to X, and for every element r of G(X), it has a
     morphism from (X, r) to (Y, G(f)(r)); i.e., the morphisms are technically
     pairs of an inner morphism in C^op and a proof about the relation between
     the respective sets (in the second projection). *)

  Record elem: Type := elem_mk {
    elem_obj: opposite C;
    elem_set: G elem_obj
  }.

  Record elem_hom (x: elem) (y: elem): Type := elem_hom_mk {
    elem_hom_morphism: opposite C (elem_obj x) (elem_obj y);
    elem_hom_coherence: elem_set y = fmap G elem_hom_morphism (elem_set x)
  }.

  Local Coercion elem_hom_morphism: elem_hom >-> setoid_carrier.

  Program Definition ElemHomSetoid e f: Setoid := {|
    setoid_carrier := elem_hom e f;
    (* We use the D-set morphism definition of equality for the inner map. *)
    setoid_equiv := setoid_equiv
  |}.

  Next Obligation.
    reflexivity.
  Qed.

  Next Obligation.
    now symmetry.
  Qed.

  Next Obligation.
    now transitivity (elem_hom_morphism e f y).
  Qed.

  Local Canonical Structure ElemHomSetoid.

  Program Definition ElementsCategory: Category := {|
    obj := elem;
    hom e f := elem_hom e f;
    id x := elem_hom_mk x x id _;
    post x y z f g := elem_hom_mk x z (post f g) _
  |}.

  Next Obligation.
    rewrite (fmap_id _ _ G); simpl.
    reflexivity.
  Qed.

  Next Obligation.
    destruct x as (x, r).
    destruct y as (y, s).
    destruct z as (z, t).
    destruct f as (f, ?H); simpl in *.
    destruct g as (g, ?H); simpl in *.
    change (post g f) with (post (c := opposite C) f g).
    rewrite (fmap_comp _ _ G); simpl.
    subst; reflexivity.
  Qed.

  Next Obligation.
    repeat intro; simpl.
    now rewrite H, H0.
  Qed.

  Next Obligation.
    now rewrite post_id_right.
  Qed.

  Next Obligation.
    now rewrite post_id_left.
  Qed.

  Next Obligation.
    now rewrite post_assoc.
  Qed.

End Elements. *)

*)
