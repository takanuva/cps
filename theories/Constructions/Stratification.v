(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
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
   there are no unique types anymore (or, rather, a universe of types may have
   both large and small types).

   Independent if we use cumulativity or not, we may check that there's a
   syntactic way to check for type schemes: their types are typeable by arities,
   as they are called in the MetaCoq project and the "Coq Coq Correct!" paper.
   We do not assume here that arities are well-typed (though they must be!). *)

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

Inductive type_scheme (R: typing_equivalence) (g: env): term -> Prop :=
  | type_scheme_make:
    forall e t,
    typing g e t R ->
    is_arity t ->
    type_scheme R g e.

Lemma type_scheme_sort:
  forall R g s,
  valid_env g R ->
  type_scheme R g (sort s).
Proof.
  intros.
  destruct s.
  - apply type_scheme_make with (type 0).
    + now repeat constructor.
    + constructor.
  - apply type_scheme_make with (type (1 + n)).
    + now repeat constructor.
    + constructor.
Qed.

(* Goal
  type_scheme polymorphic_id_type.
Proof.
  apply type_scheme_mk with [] (sort iset).
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
Admitted. *)

Lemma is_arity_is_dec:
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
  - right; inversion 1.
  - right; inversion 1.
  - right; inversion 1.
Qed.

Definition schemes_only (R: typing_equivalence) (g: env): Prop :=
  forall d n,
  (* TODO: improve this definition. *)
  item d g n -> exists s, typing g (lift (S n) 0 (snd d)) (sort s) R.

Definition well_sorted (R: typing_equivalence) (g: env) (t: term): Prop :=
  schemes_only R g /\ type_scheme R g t.

Theorem sorting:
  forall R j,
  infer R j ->
  match j with
  | valid_env g => schemes_only R g
  | typing g e t => well_sorted R g t
  end.
Proof.
  induction 1; intros.
  (* Case: iset. *)
  - split; auto.
    exists (type 1).
    + now constructor.
    + constructor.
  (* Case: type. *)
  - split; auto.
    exists (type (2 + n)).
    + now constructor.
    + constructor.
  (* Case: bound. *)
  - subst; split; auto.
    destruct IHinfer with (d, t) n as (s, ?).
    + assumption.
    + econstructor.
      * eassumption.
      * constructor.
  (* Case: pi. *)
  - subst.
    destruct IHinfer1.
    destruct IHinfer2.
    split; auto.
    apply type_scheme_sort.
    apply valid_env_typing in H.
    assumption.
  (* Case: abstraction. *)
  - destruct IHinfer as (?H, ?H).
    split.
    + admit.
    + admit.
  (* Case: application. *)
  - (* Type schemes are stable under substitution according to "A New
       Extraction for Coq". *)
    admit.
  (* Case: definition. *)
  - (* Ditto. *)
    admit.
  (* Case: sigma. *)
  - admit.
  (* Case: pair. *)
  - admit.
  (* Case: projection 1. *)
  - admit.
  (* Case: projection 2. *)
  - admit.
  (* Case: bool. *)
  - admit.
  (* Case: true. *)
  - admit.
  (* Case: false. *)
  - admit.
  (* Case: if. *)
  - admit.
  (* Case: thunk. *)
  - admit.
  (* Case: delay. *)
  - admit.
  (* Case: force. *)
  - admit.
  (* Case: conv. *)
  - admit.
  (* Case: empty env. *)
  - repeat intro.
    exfalso.
    inversion H.
  (* Case: env var. *)
  - repeat intro.
    dependent destruction H0; simpl.
    + exists s.
      replace (sort s) with (lift 1 0 (sort s)) by now sigma.
      apply weakening.
      * assumption.
      * now apply valid_env_var with s.
    + destruct IHinfer.
      specialize (H1 d n H0) as (s2, ?).
      exists s2.
      replace (sort s2) with (lift 1 0 (sort s2)) by now sigma.
      replace (lift (S (S n)) 0 (snd d)) with (lift 1 0 (lift (S n) 0 (snd d)))
        by now sigma.
      apply weakening.
      * assumption.
      * now apply valid_env_var with s.
  (* Case: env def. *)
  - intros d n ?.
    destruct n.
    + dependent destruction H1; simpl.
      exists s.
      replace (sort s) with (lift 1 0 (sort s)) by now sigma.
      apply weakening.
      * assumption.
      * now apply valid_env_def with s.
    + dependent destruction H1.
      destruct IHinfer1.
      specialize (H2 d n H1) as (s2, ?).
      exists s2.
      replace (sort s2) with (lift 1 0 (sort s2)) by now sigma.
      replace (lift (S (S n)) 0 (snd d)) with (lift 1 0 (lift (S n) 0 (snd d)))
        by now sigma.
      apply weakening.
      * assumption.
      * now apply valid_env_def with s.
Admitted.

Corollary validity:
  forall R g e t,
  typing g e t R ->
  type_scheme R g t.
Proof.
  intros.
  now apply sorting in H as (?H, ?H).
Qed.

(* Validity says that if [G |- e : t], then [t] is a type scheme, thus there is
   some arity [a] such that [G |- t : a]. As arities are products, this means
   that there is an [s] such [G |- a : s]... how can we decide what receives or
   not negations during the translation, specially if we allow comulativity?

   IDEA: can we "fix" this by not caring...? E.g., could we, instead of using a
   type such as [~(x: T, ~U)], simply use [Pi x: T.U]? Then we really don't have
   to translate anything... *)

(* ---------------------------------------------------------------------------*)

(* TODO: rewrite this.

   We follow the usual definition of syntactic classes for terms, types and
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
    stratify class_kind iset
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
