(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
Require Import Program.
Require Import Relations.
Require Import Morphisms.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

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

Structure Domain (P: PartialSetoid): Type := {
  domain: partial_carrier P;
  self_relation: partial_equiv domain domain
}.

Global Arguments domain {P}.
Global Arguments self_relation {P}.

Definition domain_equiv {P: PartialSetoid} (x: Domain P) (y: Domain P): Prop :=
  partial_equiv (domain x) (domain y).

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
  now apply partial_trans with (domain y).
Qed.

Global Canonical Structure domain_setoid.

Definition funext_equiv {T U} (f g: forall t: T, U t): Prop :=
  forall x, f x = g x.

Global Program Definition function_setoid T U: Setoid := {|
  setoid_carrier := forall t: T, U t;
  setoid_equiv := funext_equiv
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

(*
Structure partial_path (P: PartialSetoid) (Q: PartialSetoid): Prop := {
  partial_path_eq:
    partial_carrier P = partial_carrier Q;
  partial_transp (p: partial_carrier P) :=
    (match partial_path_eq in (_ = T) return T with
    | eq_refl => p
    end): partial_carrier Q;
  partial_reclassify:
    forall x y,
    partial_equiv x y <-> partial_equiv (partial_transp x) (partial_transp y)
}.

Arguments partial_path_eq {P} {Q}.
Arguments partial_transp {P} {Q}.
Arguments partial_reclassify {P} {Q}.

Program Definition domain_cast {P} {Q} H (p: Domain P): Domain Q :=
  partial_transp H p.

Next Obligation.
  destruct p as (w, ?H); simpl in *.
  destruct H as (?H, ?H, ?H); simpl in *.
  destruct P as (P, ?H, ?H, ?H); simpl in *.
  destruct Q as (Q, ?H, ?H, ?H); simpl in *.
  subst; now apply H2.
Qed.

(* ... *)

Global Program Definition partial_setoid: Setoid := {|
  setoid_carrier := PartialSetoid;
  setoid_equiv := partial_path
|}.

Next Obligation.
  rename x into P.
  now exists eq_refl.
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
*)

Program Definition setoid_map_id {S}: S ~> S := {|
  setoid_map x := x
|}.

Program Definition setoid_map_post {S T U} (f: S ~> T) (g: T ~> U): S ~> U := {|
  setoid_map x := g (f x)
|}.

Next Obligation of setoid_map_post.
  now rewrite H.
Qed.

(* TODO: we can surely simplify this if Setoid is itself a setoid, right...?

   NOTE: if the family is constant (i.e., it doesn't use S), this is really
   just a setoid map! Cool! *)

Structure is_family (S: Setoid) (f: S -> Setoid): Type := {
  setoid_transport:
    forall x y, x == y -> f x ~> f y;
  setoid_transport_irr:
    forall x y H1 H2,
    setoid_transport x y H1 == setoid_transport x y H2;
  setoid_transport_id:
    forall x H,
    setoid_transport x x H == setoid_map_id;
  setoid_transport_post:
    forall x y z H1 H2 H3,
    setoid_map_post (setoid_transport x y H1) (setoid_transport y z H2) ==
      setoid_transport x z H3
}.

Structure SetoidFamily (S: Setoid): Type := family {
  setoid_family: S -> Setoid;
  setoid_family_prf :> is_family S setoid_family
}.

Global Coercion setoid_family: SetoidFamily >-> Funclass.

Global Arguments setoid_transport {S} {f} i {x} {y}.

Lemma setoid_transport_comp:
  forall {S: Setoid},
  forall F: SetoidFamily S,
  forall {x: S},
  forall {y: S},
  forall {z: S},
  forall H1: y == z,
  forall H2: x == y,
  forall {w: F x},
  setoid_transport F H1 (setoid_transport F H2 w) ==
    setoid_transport F (setoid_trans _ _ _ H2 H1) w.
Proof.
  intros.
  (* A small (definitional) rewrite to make things work... *)
  change (setoid_transport F H1 (setoid_transport F H2 w)) with
    (setoid_map_post (setoid_transport F H2) (setoid_transport F H1) w).
  (* There we go. *)
  apply setoid_transport_post.
Qed.

(* -------------------------------------------------------------------------- *)

Section Constructors.

  Local Notation Family := SetoidFamily.

  Variable S: Setoid.
  Variable F: Family S.

  Local Definition sigma_carrier: Type :=
    { x: S & F x }.

  Local Definition sigma_equiv (p: sigma_carrier) (q: sigma_carrier): Prop :=
    exists H: projT1 p == projT1 q,
    setoid_transport F H (projT2 p) == (projT2 q).

  Program Definition sigma_setoid: Setoid := {|
    setoid_carrier := sigma_carrier;
    setoid_equiv := sigma_equiv
  |}.

  Next Obligation of sigma_setoid.
    destruct x as (x, x').
    exists (setoid_refl x); simpl.
    rewrite setoid_transport_id.
    reflexivity.
  Qed.

  Next Obligation of sigma_setoid.
    destruct x as (x, x').
    destruct y as (y, y').
    destruct H as (?H, ?H); simpl in *.
    exists (setoid_sym x y H); simpl.
    rewrite <- H0.
    rewrite setoid_transport_comp.
    rewrite setoid_transport_id.
    reflexivity.
  Qed.

  Next Obligation of sigma_setoid.
    destruct x as (x, x').
    destruct y as (y, y').
    destruct z as (z, z').
    destruct H as (?H, ?H).
    destruct H0 as (?H, ?H).
    simpl in *.
    exists (setoid_trans x y z H H0); simpl.
    rewrite <- H2, <- H1.
    rewrite setoid_transport_comp.
    reflexivity.
  Qed.

  Local Definition pi_carrier: Type :=
    { f: forall x: S, F x | forall x y H, setoid_transport F H (f x) == f y }.

  Local Definition pi_equiv (f: pi_carrier) (g: pi_carrier): Prop :=
    forall x, proj1_sig f x == proj1_sig g x.

  Program Definition pi_setoid: Setoid := {|
    setoid_carrier := pi_carrier;
    setoid_equiv := pi_equiv
  |}.

  Next Obligation of pi_setoid.
    destruct x as (f, ?H); simpl in *.
    intro; simpl.
    reflexivity.
  Qed.

  Next Obligation of pi_setoid.
    destruct x as (f, ?H); simpl in *.
    destruct y as (g, ?H); simpl in *.
    intro; simpl.
    symmetry; apply H.
  Qed.

  Next Obligation of pi_setoid.
    destruct x as (f, ?H); simpl in *.
    destruct y as (g, ?H); simpl in *.
    destruct z as (h, ?H); simpl in *.
    intro; simpl.
    transitivity (g x).
    - apply H.
    - apply H0.
  Qed.

End Constructors.
