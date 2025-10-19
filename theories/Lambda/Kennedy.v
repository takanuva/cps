(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Residuals.
Require Import Local.Lambda.Calculus.
Require Import Local.Lambda.PlotkinCBV.

Import ListNotations.

(* The naive one-pass CPS translation of Danvy and Filinski's that Kennedy
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

   This translation corresponds to Plotkin's CBV translation semantically, of
   course. Also, modulo a very minor change in the application rule, the above
   is also used in Appel's book (ch. 5.4), and it's given in Thielecke's thesis;
   namely, Appel's version is given by changing application to:

     [e1 e2] K = [e1] (\z1.            (NOTE: k is outside the lambda now!)
                   [e2] (\z2.
                    z1<z2, k>)) { k<v> = K(v) }

   ...which, clearly, doesn't change the meaning of the term (assuming k fresh).
   We use Kennedy's version merely as the continuation is immediately bound, so
   it's easier to deal with (as it remains as de Bruijn index zero).

   Kennedy provides an additional translation later in this paper which we shall
   also adapt, in that tail-calls are optimized on the fly. This may be done by
   modifying the above with the following rule:

     [\x.e] K = K(f) { f<x, k> = (e) k }

   Along with the introduction of an auxiliary, mutually defined function:

     (-): term -> var -> pseudoterm

     (x) k = k<x>
     (\x.e) k = k<f> { f<x, j> = (e) j }
     (e1 e2) k = [e1] (\z1.[e2] (\z2.z1<z2, k>))

   We ignore that Kennedy's version is given as a so called double-barrelled
   translation, in which he also gives an additional continuation for exception
   handlers. Of course, we also ignored that Appel's version covers primitives.

   We would like to show that we can get from Plotkin's translation to the first
   one by performing administrative jumps, then from the that to the final one
   by performing some shrinking reductions. The combination should lead to the
   result that these translations are adequate and that they give a sound
   denotational semantics for the lambda calculus. *)

Inductive kennedy_callback: Set :=
  | kennedy_halt
  | kennedy_call (f: nat) (t: CPS.pseudoterm) (c: CPS.pseudoterm).

Fixpoint kennedy_apply (K: kennedy_callback) (k n: nat): CPS.pseudoterm :=
  match K with
  (* (k, n) => k<n> *)
  | kennedy_halt =>
    CPS.jump (CPS.bound k) [CPS.bound (lift 1 k n)]
  (* (k, n) => f<n, k> { k<v: t> = b } *)
  | kennedy_call f t c =>
    CPS.bind (CPS.jump (CPS.bound f) [CPS.bound k; CPS.bound (lift 1 k n)]) [t] c
  end.

Local Coercion kennedy_apply: kennedy_callback >-> Funclass.

Inductive kennedy: term -> kennedy_callback -> CPS.pseudoterm -> Prop :=
  (* [x] K = K(x) *)
  | kennedy_bound:
    forall K n,
    (* Straightforward; the current continuation is 0 and thus everything else
       gets shifted by 1 up. *)
    kennedy (bound n) K (K 0 n)
  (* [\x.e] K = K(f) { f<x, k> = [e] (\z.k<z>) } *)
  | kennedy_abstraction:
    forall K t e c,
    (* We have to add the outer k variable to e; of course, we could also add
       it after the translation if we'd deem fit. *)
    kennedy (lift 1 1 e) kennedy_halt c ->
    kennedy (abstraction t e) K (CPS.bind
                                  (* The current continuation is 1, thus 0 here
                                     is bound and refers to f. *)
                                  (K 1 0)
                                  [CPS.void; CPS.void]
                                  (* Unchanged (we already added k). *)
                                  c)
  (* [f e] K = [f] (\f.
                       [e] (\v.
                               f<v, k> { k<x> = K(x) }
                           )
                   )

      In the term f<v, k> { ... }, i.e., the anchor, both *)
  (* | kennedy_application:
    forall (K: kennedy_callback) f e b c,
    (* Oh boy, a tricky one... *)
    kennedy (lift 2 0 e) (kennedy_call 0 CPS.void (K 0 1)) c ->
    kennedy (lift 1 0 f) *)
  .

Goal
  let e := (application 42 51) in
  forall b c,
  cbv_cps e b ->
  kennedy e kennedy_halt c ->
  Reduction.star b c.
Proof.
  compute; intros.
  dependent destruction H.
  vm_compute in H, H0.
  dependent destruction H.
  dependent destruction H0.
  vm_compute.
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_right.
  apply Reduction.step_ctxjmp with (h := Context.context_hole).
  reflexivity.
  vm_compute.
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_right.
  apply Reduction.step_gc.
  repeat constructor; auto.
  vm_compute.
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_ctxjmp with (h := Context.context_hole).
  reflexivity.
  vm_compute.
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_gc.
  repeat constructor; auto.
  vm_compute.
  admit.
Admitted.

Goal
  forall t u n,
  let e := (abstraction t (abstraction u (bound n))) in
  forall b,
  cbv_cps e b ->
  forall c,
  kennedy e kennedy_halt c ->
  b = c.
Proof.
  compute; intros.
  dependent destruction H.
  dependent destruction H.
  destruct n.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  dependent destruction H0.
  vm_compute.
  reflexivity.
  destruct n.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  dependent destruction H0.
  vm_compute.
  reflexivity.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  dependent destruction H0.
  vm_compute.
  reflexivity.
Qed.
