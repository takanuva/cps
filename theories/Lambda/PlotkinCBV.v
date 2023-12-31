(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Context.
(* TODO: remove this one. *)
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Observational.
Require Import Local.Conservation.
Require Export Local.Lambda.Calculus.

Include Lambda.Calculus.
Module CPS := Local.Syntax.

Inductive cbv: relation term :=
  | cbv_betav:
    forall t b x,
    value x ->
    cbv
      (application (abstraction t b) x)
      (subst x 0 b)
  | cbv_app1:
    forall f1 f2 x,
    cbv f1 f2 ->
    cbv (application f1 x) (application f2 x)
  | cbv_app2:
    forall f x1 x2,
    value f ->
    cbv x1 x2 ->
    cbv (application f x1) (application f x2).

Lemma full_cbv:
  inclusion cbv full.
Proof.
  induction 1.
  - constructor.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma cbv_implies_nonvalue:
  forall a b,
  cbv a b -> ~value a.
Proof.
  induction 1; inversion 1.
Qed.

Lemma cbv_is_a_function:
  forall a b1,
  cbv a b1 ->
  forall b2,
  cbv a b2 -> b1 = b2.
Proof.
  induction 1; intros.
  - dependent destruction H0.
    + reflexivity.
    + exfalso.
      inversion H0.
    + exfalso.
      apply cbv_implies_nonvalue with x x2; auto.
  - dependent destruction H0.
    + exfalso.
      apply cbv_implies_nonvalue in H.
      auto with cps.
    + f_equal; auto.
    + exfalso.
      apply cbv_implies_nonvalue in H.
      auto with cps.
  - dependent destruction H1.
    + exfalso.
      apply cbv_implies_nonvalue in H0.
      auto with cps.
    + exfalso.
      apply cbv_implies_nonvalue in H1.
      auto with cps.
    + f_equal; auto.
Qed.

(* TODO: fix typing on the following! *)

Local Notation VAR n :=
  (* [x] = k<x> *)
  (jump 0 [CPS.bound (S n)]).

Local Notation ABS b :=
  (* [\x.e] = k<f> { f<x, k> = [e] } *)
  (bind (jump 1 [CPS.bound 0]) [void; void] b).

Local Notation APP b c :=
  (* [e f] = [e] { k<f> = [f] { k<v> = f<v, k> } } *)
  (bind b [void] (bind c [void] (jump 1 [CPS.bound 2; CPS.bound 0]))).

(* TODO: these lifts could be moved from source to target! *)

Inductive cbv_cps: term -> pseudoterm -> Prop :=
  | cbv_cps_bound:
    forall n: nat,
    cbv_cps n (VAR n)
  | cbv_cps_abstraction:
    forall t e b,
    cbv_cps (lift 1 1 e) b ->
    cbv_cps (abstraction t e) (ABS b)
  | cbv_cps_application:
    forall f x b c,
    cbv_cps (lift 1 0 f) b ->
    cbv_cps (lift 2 0 x) c ->
    cbv_cps (application f x) (APP b c).

Lemma cbv_cps_is_a_function:
  forall e c1,
  cbv_cps e c1 ->
  forall c2,
  cbv_cps e c2 -> c1 = c2.
Proof.
  induction 1; intros.
  - dependent destruction H; auto.
  - dependent destruction H0.
    f_equal; auto.
  - dependent destruction H1.
    f_equal; auto.
    f_equal; auto.
Qed.

Local Hint Resolve cbv_cps_is_a_function: cps.

Lemma cbv_cps_lift:
  forall e c,
  cbv_cps e c ->
  forall i k,
  cbv_cps (lift i k e) (CPS.lift i (S k) c).
Proof.
  induction 1; simpl; intros.
  - destruct (le_gt_dec k n).
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_ge; try lia.
      replace (i + S n) with (S (i + n)); try lia.
      constructor.
    + rewrite lift_distributes_over_jump; simpl.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      constructor.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    rewrite lift_lift_permutation; try lia.
    replace (k + 2) with (2 + k); simpl; try lia.
    apply IHcbv_cps; lia.
  - rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_bind.
    rewrite lift_distributes_over_jump; simpl.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    rewrite lift_bound_lt; try lia.
    constructor.
    + rewrite lift_lift_permutation; try lia.
      apply IHcbv_cps1; lia.
    + rewrite lift_lift_permutation; try lia.
      replace (k + 1) with (1 + k); try lia.
      apply IHcbv_cps2; lia.
Qed.

Lemma cbv_cps_is_compositional:
  forall c1 c2,
  [c1 ~~ c2] ->
  forall e1 e2,
  not_free 0 e1 ->
  not_free 0 e2 ->
  cbv_cps e1 c1 ->
  cbv_cps e2 c2 ->
  forall (h: context) c3 c4,
  cbv_cps (h e1) c3 ->
  cbv_cps (h e2) c4 ->
  [c3 ~~ c4].
Proof.
  admit.
Admitted.

(* -------------------------------------------------------------------------- *)

(* TODO: Add stuff about free variables in here! *)

(* -------------------------------------------------------------------------- *)

(* TODO: Add lemma about administrative redexes in here! *)

(* -------------------------------------------------------------------------- *)

(*
  Let's try to reason about simulation. The proof should follow in a similar way
  from the call-by-name one. Recall the call-by-value translation:

    1) [x] = k<x>
    2) [\x.M] = k<f> { f<x, k> = [M] }
    3) [M N](k) = [M] { k<f> = [N] { k<v> = f<v, k> } }

  Again, we have a term as [(\x.a) b], which will translate into:

    k<f>
    { f<x, k> =
        [a] }
    { k<f> =
        [b]
        { k<v> =
            f<v, k> } }

  We immediately have two linear jump redexes (only the first at head position):

    [b]
    { k<x> =
        [a] }

  This is the opposite of the call-by-name! Of course, I should have expected
  that. If [a] contains a free occurrence of x and is thus equal to C[x], we
  will then have:

    [b]
    { k<x> =
        D[k<x>] }

  This is way more problematic. Does Plotkin prove simulation for the full beta
  reduction in here, or just for the call-by-value beta reduction? AAAAAAAAAAA.

  It seems this simply isn't true for the full beta... could we think of a
  counter example? Anyways, let's consider, thus, that b is a value. We have two
  cases then. The first one, where b is a variable:

    k<y>
    { k<x> =
      D[k<x>] }

  This will simplify in one linear head reduction to:

    D[k<y>]

  Ok, this seems fine. I've replaced one variable by the other. Now, the other
  case is when b is an abstraction. We should then have:

    k<f>
    { f<y, k> =
      [c] }
    { k<x> =
      D[k<x>] }

  This will simply reduce to:

    D[k<f>]
    { f<y, k> =
      [c] }

  As we'd have the reduction be from [(\x.a) (\y.c)] to [a[\y.c/x]], if for
  simplicity we assume there's a single x in there, we'd want to have:

    D[k<f> { f<y, k> = [c] }]

  This is just floating! However, the problem is that f can appear free multiple
  times, so we can't just float this in there. We can duplicate it, of course,
  if we are not trying to reduce but rather show that the terms are equal. This
  is enough to show adequacy, but we don't have one-step simulation anymore. We
  would still have it if we allowed for specialization, just like it's done in
  linear logic! But we'd like to have contraction instead for the CPS-calculus.

  Other notions of reduction: though the call-by-name translation can't validate
  eta (we don't want it to!), the call-by-value translation should validate some
  extra notions of reduction. The call-by-value eta reduction can be simulated,
  but it does need the (ETA) rule. It seems that the id-reduction from Moggi's
  calculus, (\x.x) e, can also be simulated, but it requires floating.

*)

(* -------------------------------------------------------------------------- *)

Fixpoint cbv_type (t: type): pseudoterm :=
  match t with
  | base =>
    CPS.base
  | arrow t s =>
    negation [negation [cbv_type s]; cbv_type t]
  end.

Definition cbv_env (g: env): list pseudoterm :=
  map (fun t => cbv_type t) g.

(* -------------------------------------------------------------------------- *)

(* This should ideally be moved to a new file. Anyway, the naive one-pass CPS
   translation of Danvy and Filinski's that Kennedy describes in his paper is
   given as follows:

     [-]: term -> (var -> pseudoterm) -> pseudoterm

                            +------------+
     [x] K = K(x)          \|/           |
     [\x.e] K = K(f) { f<x, k> = [e] (\z.k z) }
     [e1 e2] K = [e1] (\z1.
                   [e2] (\z2.
                    z1<z2, k> { k<v> = K(v) }))
                                  |     /|\
                                  +------+

   As of writing, I'm still not sure how to handle the de Bruijn indexes in here
   correctly. Probably applying a substitution would be a nice way, as we don't
   know in advance how far the variable will be pushed inside a term... can we
   calculate that? Sigh...

   The final version, which avoids the introduction of tail-calls, i.e., (ETA)
   redexes, can be defined by modifying the above with:

     [\x.e] K = K(f) { f<x, k> = (e) k }

   Along with the introduction of an auxiliary definition:

     (-): term -> var -> pseudoterm

     (x) k = k<x>
     (\x.e) k = k<f> { f<x, j> = (e) j }
     (e1 e2) k = [e1] (\z1.[e2] (\z2.z1<z2, k>))

   Ideally, we would like to show that we can get from Plotkin's translation to
   the naive one by performing some jumps, then from the naive one to the final
   one by performing some tail-call eliminations. The combination would lead to
   the result that these translations are adequate and that they give a sound
   denotational semantics for the lambda calculus. *)