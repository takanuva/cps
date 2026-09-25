(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Setoid.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Pi.Graph.
Require Import Local.Pi.Calculus.

(*
  Rules:

    ------------------------- (ax)
      I(x,y) |- x: A, y: A^

      p |- ws: G, x: A      q |- vs: D, y: B
    ------------------------------------------ (tensor)
      T(x,y,z,p,q) |- ws: G, vs: D, z: A * B

          p |- ws: G, x: A, y: B
    --------------------------------- (par)
      P(x,y,z,p) |- ws: G, z: A $ B

      p |- us: G, x: C     q |- vs: D, x: C^
    ------------------------------------------ (cut)
             C(x,p,q) |- us: G, vs: D

    Link I(x,y) =
      x(a) y<a>

    Tensor T(x,y,z,p,q) =
      z[x, y] (p | q)

    Par P(x,y,z,p) =
      z(x, y) p

    Cut C(x,p,q) =
      (\x)(p | q)

  Such that...

    Process functions F, G, H, etc, are linear functions: they need to use
    their arguments internally...

    Symmetric reductions:

      C(x,p,q) === C(x,q,p)

      C(x, F x, I(x, y)) -> F[y/x]

      C(z, T(x, y, z, F x, G y), P([x], [y], z, H x y)) ->

          C(y, G y, C(x, F x, H x y)) ===
            C(x, F x, C(y, H x y, G y))

    Commutative reductions:

      C(x, P(c, d, v, F x c d), G x) ===
        P(c, d, v, C(x, F x c d, G x))

      C(x, T(c, d, v, F c, G d x), H x) ===
        T(c, d, v, F c, C(x, G d x, H x))

    Remark:

      P(c, d, v, C(x, F x c, G x d)) do not commute, because c and d have to
      appear on the same branch of the proof tree! Careful with that!

  Reduction must be compatible with well-typed contexts...
*)

Variant polarity: Set :=
  | positive
  | negative.

Inductive formula: Set :=
  (* Base formulas... *)
  | base (p: polarity)
  (* Units... *)
  | one
  | bot
  (* Multiplicatives... *)
  | tensor (t: formula) (u: formula)
  | par (t: formula) (u: formula)
  (* Exponentials... *)
  | ofcourse (t: formula)
  | whynot (t: formula).

Fixpoint negate (t: formula): formula :=
  match t with
  | base positive => base negative
  | base negative => base positive
  | one => bot
  | bot => one
  | tensor t u => par (negate t) (negate u)
  | par t u => tensor (negate t) (negate u)
  | ofcourse t => whynot (negate t)
  | whynot t => ofcourse (negate t)
  end.

Lemma negate_is_involutive:
  forall t,
  negate (negate t) = t.
Proof.
  induction t; simpl.
  - now destruct p.
  - reflexivity.
  - reflexivity.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt1, IHt2.
  - now rewrite IHt.
  - now rewrite IHt.
Qed.
