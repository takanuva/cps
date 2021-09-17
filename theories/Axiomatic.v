(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Setoid.
Require Import Relations.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Context.

(** ** Axiomatic semantics *)

Definition RECJMP (R: relation pseudoterm): Prop :=
  forall xs ts c,
  length xs = length ts ->
  R (bind (jump 0 xs) ts c)
    (bind (apply_parameters xs 0 (lift 1 (length xs) c)) ts c).

Global Hint Unfold RECJMP: cps.

(* My first intuition was to make the redex as [jump (length ts + k) _], by
   using a bound var (that is not a parameter), but this is too restrictive for
   our "high-order" definition of pseudoterms; lifting k instead solves this,
   and it properly captures the notion of (ETA) for actual terms. *)

Definition ETA (R: relation pseudoterm): Prop :=
  forall b ts k,
  R (bind b ts (jump (lift (length ts) 0 k) (low_sequence (length ts))))
    (subst k 0 b).

Global Hint Unfold ETA: cps.

Definition DISTR (R: relation pseudoterm): Prop :=
  forall b ms m ns n,
  Forall (not_free 0) ms ->
  R (bind (bind b ms m) ns n)
    (bind (bind
      (switch_bindings 0 b)
      (map (lift 1 0) ns)
        (lift 1 (length ns) n))
      (map (remove_binding 0) ms) (bind
        (right_cycle (length ms) 0 m)
        (map (lift (length ms) 0) ns)
          (lift (length ms) (length ns) n))).

Global Hint Unfold DISTR: cps.

Definition CONTR (R: relation pseudoterm): Prop :=
  forall b ts c,
  R (bind (bind b (map (lift 1 0) ts) (lift 1 (length ts) c)) ts c)
    (bind (remove_binding 0 b) ts c).

Global Hint Unfold CONTR: cps.

Definition GC (R: relation pseudoterm): Prop :=
  forall b ts c,
  not_free 0 b ->
  R (bind b ts c) (remove_binding 0 b).

Global Hint Unfold GC: cps.

(* As of now, I'm still unsure whether we'll need a directed, one-step struct
   relation or just it's congruence version. Just to be sure, we'll define it
   anyway. Note that we do not add contraction here as it is derivable in the
   equivalence closure of this relation. *)

Inductive struct: relation pseudoterm :=
  | struct_recjmp:
    RECJMP struct
  | struct_distr:
    DISTR struct
  | struct_eta:
    ETA struct
  | struct_gc:
    GC struct
  | struct_bind_left:
    LEFT struct
  | struct_bind_right:
    RIGHT struct.

Global Hint Constructors struct: cps.

(* We'll just define our structural congruence as the smallest relation closed
   under the [struct] rules above. *)

Notation cong := rst(struct).
Notation "[ a == b ]" := (cong a b)
  (at level 0, a, b at level 200): type_scope.

Lemma cong_refl:
  forall e,
  [e == e].
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_refl: cps.

Lemma cong_sym:
  forall a b,
  [a == b] -> [b == a].
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_sym: cps.

Lemma cong_trans:
  forall a b c,
  [a == b] -> [b == c] -> [a == c].
Proof.
  eauto with cps.
Qed.

Global Hint Resolve cong_trans: cps.

Lemma cong_struct:
  forall a b,
  struct a b -> [a == b].
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_struct: cps.

Lemma cong_recjmp:
  RECJMP cong.
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_recjmp: cps.

Lemma cong_distr:
  DISTR cong.
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_distr: cps.

Lemma cong_eta:
  ETA cong.
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_eta: cps.

Lemma cong_gc:
  GC cong.
Proof.
  auto with cps.
Qed.

Global Hint Resolve cong_gc: cps.

Lemma cong_bind_left:
  LEFT cong.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve cong_bind_left: cps.

Lemma cong_bind_right:
  RIGHT cong.
Proof.
  induction 1; eauto with cps.
Qed.

Global Hint Resolve cong_bind_right: cps.

Instance cong_is_an_equivalence: Equivalence cong.
Proof.
  split.
  - exact cong_refl.
  - exact cong_sym.
  - exact cong_trans.
Defined.

Instance cong_is_a_congruence: Congruence cong.
Proof.
  split.
  - exact cong_is_an_equivalence.
  - exact cong_bind_left.
  - exact cong_bind_right.
Defined.

(* Our (DISTR) rule is particularly annoying to do with de Bruijn indexes and it
   did take some time to approach correctly. Take the following as an example,
   moving from our [ex1] into [ex2].

                                         \j.\x.\y.\z.
    \j.\x.\y.\z.                           h@0<y@3, k@1, x@4>
      h@1<y@3, k@0, x@4>                   { h<c, d, e> =
      { k<a, b> =                 ==           d@1<e@0, z@4> }
          h@2<b@0, j@6, a@1> }             { k<a, b> =
      { h<c, d, e> =                           h@0<b@1, j@6, a@2>
          d@1<e@0, z@3> }                      { h<c, d, e> =
                                                 d@1<e@0, z@5> } }

    We can now show that this equivalence holds. *)

Example ex2: pseudoterm :=
  (bind (bind
    (jump 0 [bound 4; bound 1; bound 3])
    [base; negation [base; base]; base]
      (jump 1 [bound 4; bound 0]))
    [base; base]
      (bind
        (jump 0 [bound 2; bound 6; bound 1])
        [base; negation [base; base]; base]
          (jump 1 [bound 5; bound 0]))).

Goal [ex1 == ex2].
Proof.
  apply cong_distr.
  do 3 constructor.
Qed.
