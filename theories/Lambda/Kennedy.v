(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Lambda.Calculus.
Require Import Local.Lambda.PlotkinCBV.

Import ListNotations.

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

   ...which, clearly, doesn't change the meaning of the term. We use Kennedy's
   version merely as the continuation is kept closer, so it's easier to deal
   with (and it remains as de Bruijn index zero).

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

Local Definition tail: Type :=
  nat -> nat -> CPS.pseudoterm -> Prop.

Local Definition halt: tail :=
  fun k n b =>
    b = CPS.jump (CPS.bound k) [CPS.bound (lift 1 k n)].

Local Notation ABS b t1 t2 c :=
  (CPS.bind b [t1; t2] c) (only parsing).

Inductive kennedy: term -> tail -> CPS.pseudoterm -> Prop :=
  | kennedy_bound:
    (* [x] K = K(x)*)
    forall K n b,
    K 0 n b ->
    kennedy (bound n) K b
  | kennedy_abstraction:
    (* [\x.e] K = K(f) { f<x, k> = [e] (\z.k<z>) } *)
    forall K t e b c,
    K 1 0 b ->
    kennedy e halt c ->
    kennedy (abstraction t e) K (ABS b CPS.void CPS.void c)

  (* | kennedy_application:
    (* [e1 e2] K = [e1] (\z1.[e2] (\z2. z1<z2, k> { k<v> = K(v) })) *) *).

Goal
  forall e b,
  cbv_cps e b ->
  forall c,
  kennedy e halt c ->
  Local.Reduction.conv b c.
Proof.
  (* We'll obviously have to strengthen the inductive hypothesis... *)
  induction 1; intros.
  - dependent destruction H.
    apply Local.Reduction.conv_refl.
  - dependent destruction H0.
    change (lift 1 1 0) with 0.
    admit.
  - admit.
Admitted.
