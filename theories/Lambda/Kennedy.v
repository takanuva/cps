(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Lambda.Calculus.
Require Import Local.Lambda.PlotkinCBV.

(* The naïve one-pass CPS translation of Danvy and Filinski's that Kennedy
   describes in his paper is given as follows:

     [-]: term -> (var -> pseudoterm) -> pseudoterm

                            +------------+
     [x] K = K(x)          \|/           |
     [\x.e] K = K(f) { f<x, k> = [e] (\z.k<z>) }
     [e1 e2] K = [e1] (\z1.
                   [e2] (\z2.
                    z1<z2, k> { k<v> = K(v) }))
                                  |     /|\
                                  +------+

   This translation corresponds to Plotkin's CBV translation, of course. Also,
   modulo a very minor change in application, the above is also used in Appel's
   book (ch. 5), and it is given in Thielecke's thesis; namely, Appel's version
   is given by changing the rule to:

     [e1 e2] K = [e1] (\z1.
                   [e2] (\z2.
                    z1<z2, k>)) { k<v> = K(v) }

   ...which, clearly, doesn't change the meaning of the term.

   Kennedy provides an additional translation which we may also adapt, in that
   tail-calls are optimized on the fly. This may be done by modifying the above
   with the following rule:

     [\x.e] K = K(f) { f<x, k> = (e) k }

   Along with the introduction of an auxiliary, mutually defined definition:

     (-): term -> var -> pseudoterm

     (x) k = k<x>
     (\x.e) k = k<f> { f<x, j> = (e) j }
     (e1 e2) k = [e1] (\z1.[e2] (\z2.z1<z2, k>))

   We ignore that Kennedy's version is a so called double-barrelled translation,
   in which he also gives an additional continuation for exception handlers.

   We would like to show that we can get from Plotkin's translation to the first
   one by performing administrative jumps, then from the that to the final one
   by performing some tail-call eliminations. The combination would lead to the
   result that these translations are adequate and that they give a sound
   denotational semantics for the lambda calculus. Also, they may be helpful in
   studying ANF, as this translation should eliminate administrative redexes. *)
