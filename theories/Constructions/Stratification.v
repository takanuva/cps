(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.TypeSystem.

Import ListNotations.

(* Following "A New Extraction for Coq", we define a type scheme as something
   that necessarily becomes a type. For example, the term [Pi X: Type, X -> X]
   in Coq is a type scheme because it can't ever generate a term. On the other
   hand, [Pi X: Type, Pi x: X, x] is not a type scheme: it may generate a type,
   if applied, e.g., to [Prop], but it may generate a term, if applied, e.g.,
   to [nat]. Of course, this distinction happens because of cumulativity, since
   there are no unique types anymore. In the lack of cumulativity, as we will
   check, there's a simpler syntactical distinction that we may use. This is
   called an arity in the MetaCoq project and the "Coq Coq Correct!" paper. *)

Inductive is_arity: term -> Prop :=
  | is_arity_now:
    forall s,
    is_arity (sort s)
  | is_arity_pi:
    forall t u,
    is_arity u ->
    is_arity (pi t u)
  | is_arity_def:
    forall v t u,
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

(* TODO: classify let definitions. *)
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
