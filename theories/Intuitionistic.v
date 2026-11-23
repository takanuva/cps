(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Reduction.

Import ListNotations.

Variant polarity: Set :=
  | cartesian
  | linear.

Local Definition lift_var (P: nat -> Prop) (b: pseudoterm): Prop :=
  exists2 n: nat,
  P n & b = bound n.

(* A sorting system inspired by Kennedy's paper. This judgement will imply that
   a CPS-calculus term behaves without control effects (i.e., no call/cc), and
   that it respects a stack discipline. As continuation variables respect a
   linear restriction, we call them linear here, and regular variables are
   cartesian.

   Kennedy's system has units, sums and pairs too, but we'll restrict ourselves
   here to functions alone. We could encode these with continuations, of course,
   and we will do that with the dependent type system, but if we'd do it here we
   would lose subject reduction for the sorting system. The reason is that we'd
   not have the syntactic clue as to whether something is a pair/sum or not. So,
   e.g., while Kennedy would write:

     letval x = in1 y in x<z, k>

   We would have:

          x<z, k> { x<a, b> = a<y> }

   While this would NOT be a redex for Kennedy, cause x is syntactically a sum,
   a straightforward encoding has no such information and this would be a redex
   leading to z<y> with both z and y cartesian, which we do not want.

   We could generalize the sorting by listing the polarity of the arguments a
   continuation takes, as x takes two linear variables above. This would solve
   it and a similar approach is taken in the dependent type system. We simplify
   this here by considering functions and thunks only.

   We also take environments to be of the form:

      G ::= . | G, x | G, k | G; .

   With the semicolon working as a "barrier" for linear variables, which is
   necessary for functions. This style of environment keeps track of variable
   indexes, useful for our de Bruijn formulation. Judgements will then be:

     G |- b ok

   Rather then keeping two distinct environments as Kennedy does. In a named
   version of the calculus, it would probably be nicer to keep a presentation
   with two environments, but the one with linear variables should probably be
   on the right-hand side of the sequent, i.e.,

     G |- b : D

   ...for G and D here respectively a list of cartesian variables and linear
   variables.
*)

Definition polarity_env: Set :=
  list (list polarity).

Local Notation env := polarity_env.

Inductive is_cartesian: env -> nat -> Prop :=
  | is_cartesian_caar:
    forall xs ys,
    is_cartesian ((cartesian :: xs) :: ys) 0
  | is_cartesian_cadr:
    forall x xs ys n,
    is_cartesian (xs :: ys) n ->
    is_cartesian ((x :: xs) :: ys) (S n)
  | is_cartesian_cdr:
    forall ys n,
    is_cartesian ys n ->
    is_cartesian ([] :: ys) n.

Inductive is_linear: env -> nat -> Prop :=
  | is_linear_caar:
    forall xs ys,
    is_linear ((linear :: xs) :: ys) 0
  | is_linear_cadr:
    forall x xs ys n,
    is_linear (xs :: ys) n ->
    is_linear ((x :: xs) :: ys) (S n).

Lemma cartesian_not_linear:
  forall g n,
  is_cartesian g n -> ~is_linear g n.
Proof.
  induction 1; repeat intro.
  - inversion H.
  - dependent destruction H0.
    contradiction.
  - inversion H0.
Qed.

Lemma linear_is_not_cartesian:
  forall g n,
  is_linear g n -> ~is_cartesian g n.
Proof.
  induction 1; repeat intro.
  - inversion H.
  - dependent destruction H0.
    contradiction.
Qed.

Local Definition env_append (g: env) (p: polarity): env :=
  match g with
  | [] => [[p]]
  | (xs :: ys) => ((p :: xs) :: ys)
  end.

Inductive intuitionistic: env -> pseudoterm -> Prop :=
  (*
     k in D      x in G
    --------------------- (RET)
        G |- k<x> : D
  *)
  | intuitionistic_ret:
    forall g k x,
    lift_var (is_linear g) k ->
    lift_var (is_cartesian g) x ->
    intuitionistic g (jump k [x])
  (*
     x in G      k in D
    --------------------- (FORCE)
        G |- x<k> : D
  *)
  | intuitionistic_force:
    forall g x k,
    lift_var (is_cartesian g) x ->
    lift_var (is_linear g) k ->
    intuitionistic g (jump x [k])
  (*
      f in G     x in G     k in D
    -------------------------------- (CALL)
            G |- f<x, k> : D
  *)
  | intuitionistic_call:
    forall g f x k,
    lift_var (is_cartesian g) f ->
    lift_var (is_cartesian g) x ->
    lift_var (is_linear g) k ->
    intuitionistic g (jump f [k; x])
  (*
      G |- b : k, D     G, x |- c : D
    ----------------------------------- (CONT)
          G |- b { k<x> = c } : D
  *)
  | intuitionistic_cont:
    forall g b t c,
    intuitionistic (env_append g linear) b ->
    intuitionistic (env_append g cartesian) c ->
    intuitionistic g (bind b [t] c)
  (*
      G, x |- b : D     G |- c : k
    ----------------------------------- (THUNK)
          G |- b { x<k> = c } : D
  *)
  | intuitionistic_thunk:
    forall g b t c,
    intuitionistic (env_append g cartesian) b ->
    intuitionistic ([linear] :: g) c ->
    intuitionistic g (bind b [t] c)
  (*
      G, f |- b : D     G, x |- c : k
    ----------------------------------- (FUN)
        G |- b { f<x, k> = c } : D
  *)
  | intuitionistic_fun:
    forall g b t1 t2 c,
    intuitionistic (env_append g cartesian) b ->
    intuitionistic ([linear; cartesian] :: g) c ->
    intuitionistic g (bind b [t1; t2] c).

Lemma intuitionistic_is_dec:
  forall b g,
  { intuitionistic g b } + { ~intuitionistic g b }.
Proof.
  induction b; intros.
  (* Case: bound. *)
  - right.
    inversion 1.
  (* Case: type. *)
  - right.
    inversion 1.
  (* Case: jump. *)
  - admit.
  (* Case: bind. *)
  - (* This could be a local continuation or a closure definition. We note that
       those two things are mutually exclusive: if this is a local continuation
       then all the arguments must be cartesian and thus none of them may be
       used as a continuation; on the other hand, if this is a closure (like a
       thunk or a local function), then the only continuations will appear in
       the arguments and thus one of them must be used as a continuation. *)
    admit.
Admitted.

Definition all_cartesian (g: env): Prop :=
  forall n, ~is_linear g n.

Theorem intuitionistic_requires_escape:
  forall g,
  all_cartesian g ->
  forall b,
  ~intuitionistic g b.
Proof.
  repeat intro.
  induction H0.
  - dependent destruction H0.
    now apply H with x0.
  - dependent destruction H1.
    now apply H with x0.
  - dependent destruction H2.
    now apply H with x0.
  - apply IHintuitionistic2; repeat intro.
    dependent destruction H0.
    + destruct g; easy.
    + destruct g; simpl in x.
      * dependent destruction x.
        inversion H0.
      * dependent destruction x.
        now apply H with n.
  - apply IHintuitionistic1; repeat intro.
    dependent destruction H0.
    + destruct g; easy.
    + destruct g; simpl in x.
      * dependent destruction x.
        inversion H0.
      * dependent destruction x.
        now apply H with n.
  - apply IHintuitionistic1; repeat intro.
    dependent destruction H0.
    + destruct g; easy.
    + destruct g; simpl in x.
      * dependent destruction x.
        inversion H0.
      * dependent destruction x.
        now apply H with n.
Qed.

Lemma pivot_is_intuitionistic:
  forall g,
  is_linear g 2 ->
  is_cartesian g 1 ->
  is_cartesian g 0 ->
  intuitionistic g (jump 1 [bound 2; bound 0]).
Proof.
  intros.
  apply intuitionistic_call.
  - now exists 1.
  - now exists 0.
  - now exists 2.
Qed.

Lemma intuitionistic_preservation:
  forall b c,
  step b c ->
  forall g,
  intuitionistic g b ->
  intuitionistic g c.
Proof.
  induction 1; intros.
  - admit.
  - admit.
  - dependent destruction H0.
    + constructor 4.
      * now apply IHstep.
      * assumption.
    + constructor 5.
      * now apply IHstep.
      * assumption.
    + constructor 6.
      * now apply IHstep.
      * assumption.
  - dependent destruction H0.
    + constructor 4.
      * assumption.
      * now apply IHstep.
    + constructor 5.
      * assumption.
      * now apply IHstep.
    + constructor 6.
      * assumption.
      * now apply IHstep.
Admitted.

Require Import Local.Lambda.PlotkinCBV.

Lemma plotkin_cbv_is_intuitionistic:
  forall e b,
  cbv_cps e b ->
  forall g,
  is_linear g 0 ->
  (forall k, free k e -> is_cartesian g (S k)) ->
  intuitionistic g b.
Proof.
  induction 1; intros.
  - apply intuitionistic_ret.
    + now exists 0.
    + exists (S n); auto.
      apply H0.
      inversion 1.
      contradiction.
  - apply intuitionistic_fun.
    + apply intuitionistic_ret.
      * exists 1; auto.
        destruct g; simpl; try easy.
        now constructor.
      * exists 0; auto.
        destruct g; constructor.
    + apply IHcbv_cps; intros.
      * constructor.
      * constructor.
        destruct k.
        --- constructor.
        --- constructor.
            constructor.
            destruct k.
            +++ exfalso.
                apply H2.
                apply lifting_more_than_n_makes_not_free_n; lia.
            +++ apply H1; intro.
                dependent destruction H3.
                apply H2.
                replace (S (S n)) with (n + 1 + 1) by lia.
                apply not_free_lift.
                rewrite Nat.add_comm.
                assumption.
  - apply intuitionistic_cont.
    + apply IHcbv_cps1; intros.
      * destruct g; constructor.
      * destruct g; try easy; simpl.
        constructor.
        destruct k.
        --- exfalso.
            apply H3.
            apply lifting_more_than_n_makes_not_free_n; lia.
        --- apply H2; intro.
            dependent destruction H4.
            apply H3.
            replace (S n) with (n + 1 + 0) by lia.
            apply not_free_lift.
            rewrite Nat.add_comm.
            assumption.
    + apply intuitionistic_cont.
      * apply IHcbv_cps2; intros.
        --- destruct g; constructor.
        --- destruct g; try easy; simpl.
            constructor.
            destruct k.
            +++ exfalso.
                apply H3.
                apply lifting_more_than_n_makes_not_free_n; lia.
            +++ constructor.
                destruct k.
                *** exfalso.
                    apply H3.
                    apply lifting_more_than_n_makes_not_free_n; lia.
                *** apply H2; intro.
                    dependent destruction H4.
                    apply H3.
                    replace (S (S n)) with (n + 2 + 0) by lia.
                    apply not_free_lift.
                    rewrite Nat.add_comm.
                    assumption.
      * apply pivot_is_intuitionistic.
        --- destruct g; try easy; simpl.
            constructor.
            constructor.
            assumption.
        --- destruct g; try easy.
            constructor.
            constructor.
        --- destruct g; try easy.
            constructor.
Qed.

Theorem cbv_program_is_intuitionistic:
  forall e,
  closed e ->
  forall b,
  cbv_cps e b ->
  intuitionistic [[linear]] b.
Proof.
  intros.
  apply plotkin_cbv_is_intuitionistic with e; intros.
  - assumption.
  - constructor.
  - exfalso.
    apply H1.
    apply H.
Qed.

Require Import Local.Lambda.PlotkinCBN.

Lemma plotkin_cbn_is_intuitionistic:
  forall e b,
  cbn_cps e b ->
  forall g,
  is_linear g 0 ->
  (forall k, free k e -> is_cartesian g (S k)) ->
  intuitionistic g b.
Proof.
  induction 1; intros.
  - apply intuitionistic_force.
    + exists (S n); auto.
      apply H0.
      inversion 1.
      contradiction.
    + now exists 0.
  - apply intuitionistic_fun.
    + apply intuitionistic_ret.
      * exists 1; auto.
        destruct g; simpl; try easy.
        now constructor.
      * exists 0; auto.
        destruct g; constructor.
    + apply IHcbn_cps; intros.
      * constructor.
      * constructor.
        destruct k.
        --- constructor.
        --- constructor.
            constructor.
            destruct k.
            +++ exfalso.
                apply H2.
                apply lifting_more_than_n_makes_not_free_n; lia.
            +++ apply H1; intro.
                dependent destruction H3.
                apply H2.
                replace (S (S n)) with (n + 1 + 1) by lia.
                apply not_free_lift.
                rewrite Nat.add_comm.
                assumption.
  - apply intuitionistic_cont.
    + apply IHcbn_cps1; intros.
      * destruct g; constructor.
      * destruct g; try easy; simpl.
        constructor.
        destruct k.
        --- exfalso.
            apply H3.
            apply lifting_more_than_n_makes_not_free_n; lia.
        --- apply H2; intro.
            dependent destruction H4.
            apply H3.
            replace (S n) with (n + 1 + 0) by lia.
            apply not_free_lift.
            rewrite Nat.add_comm.
            assumption.
    + apply intuitionistic_thunk.
      * apply pivot_is_intuitionistic.
        --- destruct g; try easy; simpl.
            constructor.
            constructor.
            assumption.
        --- destruct g; try easy.
            constructor.
            constructor.
        --- destruct g; try easy.
            constructor.
      * apply IHcbn_cps2; intros.
        --- constructor.
        --- constructor.
            constructor.
            destruct g; try easy; simpl.
            destruct k.
            +++ exfalso.
                apply H3.
                apply lifting_more_than_n_makes_not_free_n; lia.
            +++ constructor.
                destruct k.
                *** exfalso.
                    apply H3.
                    apply lifting_more_than_n_makes_not_free_n; lia.
                *** apply H2; intro.
                    dependent destruction H4.
                    apply H3.
                    replace (S (S n)) with (n + 2 + 0) by lia.
                    apply not_free_lift.
                    rewrite Nat.add_comm.
                    assumption.
Qed.

Theorem cbn_program_is_intuitionistic:
  forall e,
  closed e ->
  forall b,
  cbn_cps e b ->
  intuitionistic [[linear]] b.
Proof.
  intros.
  apply plotkin_cbn_is_intuitionistic with e; intros.
  - assumption.
  - constructor.
  - exfalso.
    apply H1.
    apply H.
Qed.
