(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Lambda.Calculus.

(*
  This CPS translation for the "extensional" lambda-calculus appears in Murthy's
  "A computational analysis of Girard's translation and LC" paper, and is also
  apdated and presented in Thielecke's thesis. Murthy calls it a "truly CBN"
  translation; of course, it captures the idea that we're identifying terms up
  to HNF instead of WHNF as in the (standard) call-by-name translation.

  The original translation is given as follows:

    [x] = x
    [\x.M] = [M][\h.k (\a.\k.a h)/x] (\b.k (\a.\k.k b))
    [M N] = \k.[M] (\v.v [N] k)

  (Note the presence of substitution above! Of course, it's a beta-reduct.)

  The version into the CPS-calculus is given by Thielecke as follows:

    [x] = x(k)
    [\x.M] = let x(h) =
               let f(a, k) = a(h) in k(f)
             in
             let k(b) =
               let f(a, k) = k(b) in k(f)
             in [M]
    [M N] = let k(f) =
              let v(k) = [N]
              in f(v, k)
            in [M]

  Can we prove this is computationally adequate as well? Looks like fun!
*)
