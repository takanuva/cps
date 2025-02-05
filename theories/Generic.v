(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Local.Prelude.
Require Import Local.Substitution.

Import ListNotations.

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
