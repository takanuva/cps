(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.
Require Import Local.Constructions.Inversion.

Import ListNotations.

(* Following "A New Extraction for Coq", we define a type scheme as something
   that necessarily becomes a type. For example, the term [Pi X: Type, X -> X]
   in Coq is a type scheme because it can't ever generate a term. On the other
   hand, [Pi X: Type, Pi x: X, x] is not a type scheme: it may generate a type,
   if applied, e.g., to [Prop], but it may generate a term, if applied, e.g.,
   to [nat]. Of course, this distinction happens because of cumulativity, since
   there are no unique types anymore (or, rather, a universe of types may also
   contain terms). In the lack of cumulativity, as we will check, there's a
   simpler syntactical distinction that we may use. This is called an arity in
   the MetaCoq project and the "Coq Coq Correct!" paper. We do not assume here
   that arities are well-typed (though they must be!). *)

Inductive is_arity: term -> Prop :=
  | is_arity_now:
    forall s,
    is_arity (sort s)
  | is_arity_pi:
    forall t u,
    is_arity u ->
    is_arity (pi t u)
  (* Note that this constructor will not appear in normal forms. *)
  | is_arity_def:
    forall v t u,
    (* We take [u] instead of [u[v/x]] in here as MetaCoq does it. *)
    is_arity u ->
    is_arity (definition v t u).

Inductive type_scheme: term -> Prop :=
  | type_scheme_mk:
    forall g e t,
    typing g e t typed_conv ->
    is_arity t ->
    type_scheme e.

Goal
  type_scheme polymorphic_id_type.
Proof.
  apply type_scheme_mk with [] (sort prop).
  - repeat econstructor.
    + now vm_compute.
    + now vm_compute.
    + now vm_compute.
    + now vm_compute.
  - constructor.
Qed.

Goal
  ~type_scheme polymorphic_id_term.
Proof.
  intro.
  dependent destruction H.
  (* We need a few inversion lemmas... *)
  admit.
Admitted.

(* TODO: _dec or _is_decidable...? Also, TODO: not sure I'll need this. *)
Lemma is_arity_is_decidable:
  forall t,
  { is_arity t } + { ~is_arity t }.
Proof.
  induction t.
  - left; constructor.
  - right; inversion 1.
  - destruct IHt2.
    + left; now constructor.
    + right; now inversion 1.
  - right; inversion 1.
  - right; inversion 1.
  - destruct IHt3.
    + left; now constructor.
    + right; now inversion 1.
  - right; inversion 1.
  - right; inversion 1.
  - right; inversion 1.
  - right; inversion 1.
  - right; inversion 1.
  - right; inversion 1.
  - right; inversion 1.
  - right; inversion 1.
Qed.

Lemma validity:
  forall g e t,
  typing g e t typed_conv ->
  type_scheme t.
Proof.
  admit.
Admitted.

(* Validity says that if [G |- e : t], then [t] is a type scheme, thus there is
   some arity [a] such that [G |- t : a]. As arities are products, this means
   that there is an [s] such [G |- a : s]... how can we decide what receives or
   not negations during the translation, specially if we allow comulativity?

   IDEA: can we "fix" this by not caring...? E.g., could we, instead of using a
   type such as [~(x: T, ~U)], simply use [Pi x: T.U]? Then we really don't have
   to translate anything... *)

(* ---------------------------------------------------------------------------*)

(* We follow the usual definition of syntactic classes for terms, types and
   kinds in the calculus of constructions. These syntactic classes give us an
   equivalent formulation of the syntax which is guaranteed by typing, as we
   shall verify. Most interestingly, terms can't be type schemes, but types and
   kinds need to be, which is quite convenient. We will promptly ignore the
   distinction between type variables and term variables. TODO: do we want the
   classification to live in Prop...? *)

Variant class: Set :=
  | class_kind
  | class_type
  | class_term.

Inductive stratify: class -> term -> Prop :=
  (* [Prop] *)
  | stratify_prop:
    stratify class_kind prop
  (* [Pi x: T.S] *)
  | stratify_pi_type_kind:
    forall t u,
    stratify class_type t ->
    stratify class_kind u ->
    stratify class_kind (pi t u)
  (* [Pi X: S.S] *)
  | stratify_pi_kind_kind:
    forall t u,
    stratify class_kind t ->
    stratify class_kind u ->
    stratify class_kind (pi t u)
  (* [X] *)
  | stratify_bound_type:
    forall n,
    stratify class_type (bound n)
  (* [Pi x: T.T] *)
  | stratify_pi_type_type:
    forall t u,
    stratify class_type t ->
    stratify class_type u ->
    stratify class_type (pi t u)
  (* [Pi X: S.T] *)
  | stratify_pi_kind_type:
    forall t u,
    stratify class_kind t ->
    stratify class_type u ->
    stratify class_type (pi t u)
  (* [\x: T.T] *)
  | stratify_abs_type_type:
    forall t u,
    stratify class_type t ->
    stratify class_type u ->
    stratify class_type (abstraction t u)
  (* [\X: S.T] *)
  | stratify_abs_sort_type:
    forall t u,
    stratify class_kind t ->
    stratify class_type u ->
    stratify class_type (abstraction t u)
  (* [T e] *)
  | stratify_app_type_term:
    forall t e,
    stratify class_type t ->
    stratify class_term e ->
    stratify class_type (application t e)
  (* [T T] *)
  | stratify_app_type_type:
    forall t u,
    stratify class_type t ->
    stratify class_type u ->
    stratify class_type (application t u)
  (* [x] *)
  | stratify_bound_term:
    forall n,
    stratify class_term (bound n)
  (* [\x: T.e] *)
  | stratify_abs_type_term:
    forall t e,
    stratify class_type t ->
    stratify class_term e ->
    stratify class_term (abstraction t e)
  (* [\X: S.e] *)
  | stratify_abs_sort_term:
    forall t e,
    stratify class_kind t ->
    stratify class_term e ->
    stratify class_term (abstraction t e)
  (* [e e] *)
  | stratify_app_term_term:
    forall e f,
    stratify class_term e ->
    stratify class_term f ->
    stratify class_term (application e f)
  (* [e T] *)
  | stratify_app_term_type:
    forall e t,
    stratify class_term e ->
    stratify class_type t ->
    stratify class_term (application e t).

Global Coercion stratify: class >-> Funclass.
