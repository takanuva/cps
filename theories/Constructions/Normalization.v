(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Local.Prelude.
Require Import Local.Category.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Inversion.
Require Local.Constructions.TermModel.
Require Local.Constructions.DPresheafModel.

Import ListNotations.

(* -------------------------------------------------------------------------- *)

(* Quick and dirty trial to actually prove strong normalization by using the
   proof given by Szumi Xie in their master's thesis, along with Coquand's paper
   on the matter. Just cause it's fun! *)

Section Normalization.

  Variable M: CwF.

  Local Notation Env := (cwf_env M).
  Local Notation Sub := (cwf_sub M).
  Local Notation Ty := (cwf_ty M).

  Local Notation Tsub := (cwf_tsub M).

  Local Notation Nil := (cwf_empty M).
  Local Notation Ext := (cwf_ext M).

  Local Notation P := (cwf_proj M _).

  (*

  Local Notation UP := (cwf_uplift M).

  (* Following both Coquand and Xie, a telescope is defined inductively as:
     - () is telescope;
     - if X is a telescope and A is a TYPE <X>, then (X.A) is a telescope;

     Along with a recursive interpretation function <->, where:
     - <()> is NIL;
     - <X.A> is SNOC <X> A.

     As noted by Coquand, we may have <X> == <Y> without X = Y. These will be
     the objects of the category. Our morphisms are syntactic objects which
     represeting weakening, namely as:
     - () is a morphism from () to ();
     - if f is a morphism from X to Y, shift f is a morphism from X.A to Y;
     - if f is a morphism from X to Y, up f is a morphism from X.(subst <f> A)
       to Y.A;

     Again along an interpretation <f: X -> Y>: <X> -> <Y> from weakenings into
     substitutions such that:
     - <()> is ();
     - <shift f> is (shift; <f>);
     - <up f> is plus(<f>).

     We can see a weakening from X to Y as a proof-relevant witness that X
     extends Y. We reuse the names "shift" and "up" from the sigma-calculus, of
     course.

     Both object and morphisms capture, syntactically, how a context and a
     substitution were built. Both are also inductive-recursive, which is quite
     annoying as this is not supported by Coq's type theory. We thus build the
     telescope and its interpretation together, and do the same for weakenings
     as specified. *)

  Inductive tel: CTX -> Type :=
    | tel_nil:
      tel NIL
    | tel_snoc:
      forall (G: CTX) (X: tel G) (T: TYPE G),
      tel (SNOC G T).

  Inductive tel_weak: forall {D G}, tel D -> tel G -> SUBST D G -> Type :=
    | tel_weak_nil:
      forall D X,
      @tel_weak D NIL X tel_nil (NIL D)
    | tel_weak_shift:
      forall D G X Y s A,
      @tel_weak D G X Y s ->
      tel_weak (tel_snoc D X A) Y (post P s)
    | tel_weak_up:
      forall D G X Y s A,
      @tel_weak D G X Y s ->
      tel_weak (tel_snoc D X (TSUBST s A)) (tel_snoc G Y A) (UP s).

  Record telescope: Type := {
    tel_int: CTX;
    tel_syntax: tel tel_int
  }.

  Definition telescope_nil: telescope :=
    {| tel_syntax := tel_nil |}.

  Record telescope_weakening (X: telescope) (Y: telescope): Type := {
    tel_weak_int: SUBST (tel_int X) (tel_int Y);
    tel_weak_syntax: tel_weak (tel_syntax X) (tel_syntax Y) tel_weak_int;
  }.

  Definition pack_tel {G: CTX} (X: tel G): telescope :=
    {| tel_syntax := X |}.

  Coercion pack_tel: tel >-> telescope.

  Program Definition weak_id_nil: telescope_weakening tel_nil tel_nil :=
    {| tel_weak_syntax := tel_weak_nil NIL tel_nil |}.

  Lemma weak_id_nil_int_is_identity:
    tel_weak_int telescope_nil telescope_nil weak_id_nil == id.
  Proof.
    simpl.
    symmetry.
    apply terminal_unique.
  Qed.

  Local Lemma cast1:
    forall {G A s},
    s == id ->
    SUBST (SNOC G (TSUBST s A)) (SNOC G A) ->
    SUBST (SNOC G A) (SNOC G A).
  Proof.
    intros.
  Admitted.

  Variable G: CTX.
  Variable s: SUBST G G.

  (* Lemma up_id_is_id:
    forall {G: CTX} A (s: SUBST G G),
    forall H: s == id,
    @cast1 G A s H (@UP s) == id.
  Proof.
    intros.
    unfold cast1. *)

  (* Lemma telescope_id (X: telescope):
    tel_weak (tel_syntax X) (tel_syntax X) id.
  Proof.
    destruct X as (i, X).
    induction X.
    - Print Terminal.
    - destruct IHX as (s, R).
      econstructor; simpl in *.

  Lemma telescope_id_exists:
    forall (G: CTX) (X: tel G),
    { s: SUBST G G & tel_weak X X s & s == id }.
  Proof.
    induction X.
    - exists (NIL NIL).
      + constructor.
      + admit.
    - destruct IHX as (s, R, ?H).
      eexists.
      + enough (T == TSUBST s T).
        * (* Rewrite on the first subterm... *)
          admit.
        * (* Sure! But TSUBST needs to be proper... *)
          admit.
      + (* Hmm... *)
        admit.
  Admitted. *)

  *)

End Normalization.

(* -------------------------------------------------------------------------- *)

(* We're dealing with a subset of Coq's theory inside of Coq. Although it might
   be possible that strong normalization for this is actually provable, at some
   point it would become hopeless because of the incompleteness theorem. Also, I
   do think that proving this (in a proof assistant) for a predicative hierarchy
   with an impredicative universe is still an open problem. So, we will merely
   conjecture that this system is strongly normalizing and go on, just like the
   people in the "Coq Coq Correct!" paper did. *)

Conjecture strong_normalization:
  forall g e t,
  typing g e t conv -> SN (step g) e.

(* For typeable terms, the normal form is computable. *)

Lemma normal_form_is_decidable:
  forall g e t,
  typing g e t conv ->
  exists2 f,
  rt(step g) e f & normal (step g) f.
Proof.
  intros.
  apply strong_normalization in H.
  induction H using SN_ind.
  destruct step_is_decidable with g x as [ (y, ?H) | ?H ].
  - destruct H2 with y as (z, ?, ?).
    + now apply t_step.
    + exists z; eauto with cps.
  - exists x.
    + apply rt_refl.
    + intros y ?.
      now apply H0 with y.
Qed.

Definition bottom: term :=
  pi iset (bound 0).

Lemma bottom_typeable:
  forall R,
  typing [] bottom iset R.
Proof.
  intros.
  repeat econstructor.
  - (* Use vm_compute to bypass opaque definitions. *)
    now vm_compute.
  - (* By definition, as set is impredicative. *)
    reflexivity.
Qed.

(* For this one, we'll follow the proof given by Coquand and Gallier in "A Proof
   Of Strong Normalization For The Theory Of Constructions Using A Kripe-Like
   Interpretation", as their Lemma 5.19. *)

Corollary consistency:
  ~exists e, typing [] e bottom conv.
Proof.
  (* Assume there's an e that is typeable as bottom. *)
  intros (e, ?).
  (* So there's a term in normal form that also is. *)
  assert (exists2 f, typing [] f bottom conv & normal (step []) f) as (f, ?, ?).
  - (* We calculate it from strong normalization and subject reduction. *)
    destruct normal_form_is_decidable with ([]: env) e bottom as (f, ?, ?).
    + assumption.
    + exists f; auto.
      now apply subject_reduction with e.
  - (* So, forget the non-normal one. *)
    clear e H; rename f into e.
    admit.
Admitted.
