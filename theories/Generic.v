(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Local.Prelude.
Require Import Local.Substitution.

(*
  WIP! WIP! WIP! WIP! WIP! WIP! WIP!

  The purpose of this file is to come up with a generic representation that we
  may use for the CPS-calculus' types, so that I can play with different type
  systems and still use the same representation. We're starting with the AACMM
  model, but we may deviate from that a bit (as the goals are different).

  Sources:
  - https://arxiv.org/pdf/1804.00119
  - https://gallais.github.io/pdf/icfp18.pdf
*)

Import ListNotations.

Inductive Description (I: Type): Type :=
  | branch (A: Type) (f: A -> Description I)
  | child (is: list I) (i: I) (d: Description I)
  | done (i: I).

Fixpoint reindex {I J: Type} (g: I -> J) (d: Description I): Description J :=
  match d with
  | branch _ A f => branch J A (fun a => reindex g (f a))
  | child _ is i d => child J (map g is) (g i) (reindex g d)
  | done _ i => done J (g i)
  end.

Section Interpretation.

  Variable I: Type.

  Definition iscoped: Type :=
    I -> list I -> Type.

  Fixpoint interpret (d: Description I): (list I -> iscoped) -> iscoped :=
    fun X i G =>
      match d with
      | branch _ A d => { a: A & interpret (d a) X i G }
      | child _ is i d => X is i G * interpret d X i G
      | done _ j => i = j
      end%type.

  Definition adjust {A: Type} (f: A -> A) (T: A -> Type) (a: A): Type :=
    T (f a).

  Definition scope: iscoped -> list I -> iscoped :=
    fun T D i =>
      adjust (fun G => D ++ G) (T i).

  (* Coq is not happy with this description! Positivity checker is too weak! *)

  (* Inductive Term (d: Description I): iscoped :=
    | term_var:
      forall i is,
      nat -> Term d i is
    | term_con:
      forall i is,
      interpret d (scope (Term d)) i is -> Term d i is. *)

End Interpretation.

Axiom X: iscoped True.
Definition S: list True -> iscoped True := scope True X.

Definition UTLC: Description True :=
  branch _ bool (fun b =>
    if b then
      child _ [] I (child _ [] I (done _ I))
    else
      child _ [I] I (done _ I)).

Local Goal
  interpret True UTLC S I [].
Proof.
  compute.
  exists true.
  admit.
Admitted.

(*

Variant binder: Set :=
  | bound
  | unbound.

Definition vector (A: Type) (n: nat): Type :=
  { xs: list A | length xs = n }.

Program Definition vector_nil {A: Type}: vector A 0 :=
  exist _ [] eq_refl.

Definition Shape (n: nat) (k: nat): Type :=
  vector (vector binder n) k.

Section Syntax.

  Variable T: Type.

  Inductive Description: Prop :=
    | desc_sg (f: T -> Description)
    | desc_node (n: nat) (k: nat) (s: Shape n k).

  Variable d: Description.

  Inductive Form: Type :=
    | form_var:
      nat -> Form
    | form_const:
      Constructor d -> Form

  with Constructor: Description -> Type :=
    | const_sg:
      forall x f,
      Constructor (f x) -> Constructor (desc_sg f)
    | const_node:
      forall n k s,
      list Form (* !!! *) -> Constructor (desc_node n k s).

End Syntax.

Section Example.

  Local Notation VB := (vector binder _).

  Local Program Definition APP_shape: Shape 0 2 :=
    [[]: VB; []: VB].

  Local Program Definition APP {T}: Description T :=
    (* Zero introduced variables, two subterms. *)
    desc_node T 0 2 APP_shape.

  Local Program Definition ABS_shape: Shape 1 1 :=
    [[bound]: VB].

  Local Program Definition ABS {T}: Description T :=
    (* One introduced variable, one subterm. *)
    desc_node T 1 1 ABS_shape.

  Local Program Definition UTLC_gen (b: bool): Description bool :=
    if b then APP else ABS.

  Local Program Definition UTLC: Description bool :=
    desc_sg bool UTLC_gen.

  Local Definition term: Type :=
    Form bool UTLC.

  Arguments form_var {T} {d}.
  Arguments form_const {T} {d}.
  Arguments const_sg {T} {d} x {f}.
  Arguments const_node {T} {d} {n} {k} {s}.

  Local Program Definition var (n: nat): term :=
    form_var n.

  Local Program Definition app (e: term) (f: term): term :=
    form_const (const_sg false (const_node [e; f])).

  Local Program Definition abs (e: term): term :=
    form_const (const_sg true (const_node [e])).

  Example identity: term :=
    abs (var 0).

End Example.

*)
