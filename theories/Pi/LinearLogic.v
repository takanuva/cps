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

    Multiplicative:

      -------------------------- (ax)
        I(x, y) |- x: A, y: A^

         p |- ws: G, x: A      q |- vs: D, y: B
      -------------------------------------------- (tensor)
        T(z, x.p, y.q) |- ws: G, vs: D, z: A * B

            p |- ws: G, x: A, y: B
      --------------------------------- (par)
        P(z, x.y.p) |- ws: G, z: A $ B

        p |- us: G, x: C     q |- vs: D, x: C^
      ------------------------------------------ (cut)
             C(x.p, x.q) |- us: G, vs: D

    Additive:

              p |- ws: G, x: A
      -------------------------------- (L+)
        L(z, x.p) |- ws: G, z: A + B


              q |- ws: G, y: B
      -------------------------------- (R+)
        R(z, y.q) |- ws: G, z: A + B

        p |- ws: G, x: A     q |- ws: G, y: B
      -----------------------------------------
          A(z, x.p, y.q) |- ws: G, z: A & B

    Exponential:

      ...

  Bellin and Scott annotate the bound variables on top of the operator, and the
  active link below it (which might be the x in the cut above too).

  They give:

    - Link I(x, y) = x(a) y<a>            (of course a fresh)
    - Tensor T(z, x.p, y.q) = z[x, y] (p | q)
    - Par P(z, x.y.p) = z(x, y) p
    - Cut C(x.p, x.q) = (\x)(p | q)       (no loss of generality, of course!)

    Note that positive means receiver, and negative means sender.

    - Injection L(z, x.p) = z(u, v) u[x] p
    - Injection R(z, y.q) = z(u, v) v[y] q
    - With A(z, x.p, y.q) = z[u, v] (u(x) p + v(y) q)       (note use of +!)

  Such that...

    Process functions F, G, H, etc, are linear functions: they need to use
    their arguments internally... so we write F x y z for a process in F such
    that x, y and z are free variables.

  Symmetric reductions:

    C(x.p, x.q) == C(x.q, x.p)

    C(x.F x, x.I(x, y)) -> F[y/x]         (seems the link could be a 0...)

    C(z.T(z, x.F x, y.G y), z.P(z, x.y.H x y)) ->

        C(y.G y, y.C(x.F x, x.H x y)) ==
          C(x.F x, x.C(y.H x y, y.G y))   (I can choose which variable to cut)

      (This notation makes it easier to see it!)

    C(z.A(z, x.p, y.q), z.L(z, x.r)) -> C(x.p, x.r)

    C(z.A(z, x.p, y.q), z.L(z, y.r)) -> C(y.q, y.r)

  Commutative reductions:

    C(x.P(v, c.d.F x c d), x.G x) ==
      P(v, c.d.C(x.F x c d, x.G x))

    C(x.T(v, c.F c, d.G d x), x.H x) ==
      T(v, c.F c, d.C(x, G d x, H x))

      (Hmm...)

    C(d.A(z, x.P x d, y.Q y d), d.R d) ==
      A(z, x.C(d.P x d, d.R d), y.C(d.Q y d, d.R d))

  Remark:

    P(v, c.d.C(x.F x c, x.G x d)) does not change, because c and d have to
    appear on the same branch of the proof tree! Careful with that!

    Also, reduction must be compatible with well-typed contexts...
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
