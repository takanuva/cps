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
Require Import Local.Lambda.PlotkinCBV.

Require Local.Residuals.

Import ListNotations.

(* The naive one-pass CPS translation, credited to Danvy and Filinsk, that
   Kennedy describes in his paper is given as follows:

     [-] -: Lambda.term -> (nat -> CPS.pseudoterm) -> CPS.pseudoterm

     [x] K = K(x) +----+    +------------+
                  |   \|/  \|/           |
     [\x.e] K = K(g) { g<x, k> = [e] (\z.k<z>) }

     [f e] K = [f] (\h.              (NOTE: g, h and v fresh)
                 [e] (\v.
                   h<v, k> { k<w> = K(w) }))
                              /|\     |
                               +------+

   This translation corresponds to Plotkin's CBV translation semantically, of
   course. Also, modulo a very minor change in the application rule, the above
   is also used in Appel's book (ch. 5.4), and it's given in Thielecke's thesis;
   namely, Appel's version is given by changing application to:

     [f e] K = [f] (\h.            (NOTE: inner k is outside the lambda now!)
                 [e] (\v.
                   h<v, k>)) { k<w> = K(w) }

   ...which, clearly, doesn't change the meaning of the term (assuming k always
   fresh, which is a given). We use Kennedy's version merely as the continuation
   is immediately bound, so it's a bit easier to deal with (as it remains as de
   Bruijn index zero).

   Kennedy provides an additional translation later in this paper which we also
   adapt, in that tail-calls are removed on the fly. This is done by modifying
   the above with the following rule:

     [\x.e] K = K(f) { f<x, k> = (e) k }

   Along with the introduction of an additional, mutually defined function:

     (-) -: Lambda.term -> var -> CPS.pseudoterm

     (x) k = k<x>

     (\x.e) k = k<g> { g<x, k> = (e) k }

     (e f) k = [e] (\h.[f] (\v.h<v, k>))

   The above function represents a tail context; note we use it for the toplevel
   term as well (since in the toplevel we don't know how to proceed in a sense,
   as the toplevel k stands for termination). Note we use the former translation
   when we know how to continue (in the case of an application) and the latter
   translation when the continuation is not yet bound.

   We would like to show that we can get from Plotkin's CBV translation into the
   optimized translation above by performing administrative jumps and garbage
   collection. This combination show result that this translation is adequate
   and that it gives a sound denotational semantics for the lambda calculus as
   Kennedy intended. *)

Inductive kennedy_code: Set :=
  | kennedy_halt
  | kennedy_then (e: term) (K: kennedy_code)
  | kennedy_call (f: nat) (j: nat) (K: kennedy_code).

Axiom A: nat -> nat -> nat -> nat.
Axiom B: nat -> nat -> nat -> nat.

Inductive kennedy: term -> kennedy_code -> CPS.pseudoterm -> Prop :=
  (* [x] K = K(x) *)
  | kennedy_bound:
    forall K n b,
    kennedy_apply K 0 n b ->
    kennedy (bound n) K b

  (* [\x.e] K = K(f) { f<x, k> = [e] (\z.k<z>) } *)
  | kennedy_abstraction:
    forall K t e b c,
    kennedy_apply K 1 0 b ->
    kennedy (lift 1 1 e) kennedy_halt c ->
    kennedy (abstraction t e) K (CPS.bind b [CPS.void; CPS.void] c)

  (* [f e] K = [f] (\f.[e] (\v.f<v, k> { k<x> = K(x) })) *)
  | kennedy_application:
    forall K f e b,
    kennedy f (kennedy_then e K) b ->
    kennedy (application f e) K b

  (* TODO: come up with translations for thunks (delay and force). *)

with kennedy_apply: kennedy_code -> nat -> nat -> CPS.pseudoterm -> Prop :=
  (* k, x => k<x> *)
  | kennedy_apply_halt:
    forall k n,
    kennedy_apply kennedy_halt k n (CPS.jump (var k) [var (lift 1 k n)])

  (* e, K; k, f => [e] (\v.f<v, k> { k<x> = K(x) }) *)
  | kennedy_apply_then:
    forall K e k f b,
    kennedy (lift k 0 e) (kennedy_call f k K) b ->
    kennedy_apply (kennedy_then e K) k f b

  (* f, j, K; k, v => f<v, k> { k<x> = K(x) } *)
  | kennedy_apply_call:
    forall K f j k v b,
    kennedy_apply K (1 + k + j) 0 b ->
    (* Here lies the optimization for the tail-recursion optimized version of
       the translation. *)
    kennedy_apply (kennedy_call f j K) k v
      (CPS.bind
        (CPS.jump (var (A j k v)) [var 0; var (B j k f)])
        [CPS.void] b).

Local Notation HALT := kennedy_halt.
Local Notation THEN := kennedy_then.
Local Notation CALL := kennedy_call.

Scheme kennedy_ind2 := Minimality for kennedy Sort Prop
  with kennedy_apply_ind2 := Minimality for kennedy_apply Sort Prop.

Local Notation V := CPS.void.

(* Quick sketch to help debugging; I will need a proper notation library later
   on. *)

Local Notation "b '{' ts '=' c '}'" :=
  (CPS.bind b ts c)
  (at level 200,
   b at level 200,
   format "'[v' b '//' '{'  ts  '=' '/  ' '[' c ']' '/' '}' ']'",
   only printing).

Local Notation "x xs" :=
  (CPS.jump x xs)
  (at level 199,
   format "'[v' x xs ']'",
   only printing).

Local Coercion CPS.bound: nat >-> CPS.pseudoterm.

Fixpoint kennedy_code_context (K: kennedy_code): list term :=
  match K with
  | kennedy_halt => []
  | kennedy_then e J =>
    e :: kennedy_code_context J
  | kennedy_call f j J =>
    var f :: map (lift j 0) (kennedy_code_context J)
  end.

Local Notation code_context := kennedy_code_context.

Fixpoint kennedy_offset (K: kennedy_code): nat :=
  match K with
  | kennedy_halt => 0
  | kennedy_then _ J => kennedy_offset J
  | kennedy_call _ j J => j + kennedy_offset J
  end.

Local Lemma Forall_not_free_map_lift:
  forall xs i k,
  Forall (not_free k) xs <->
  Forall (not_free (i + k)) (map (lift i 0) xs).
Proof.
  induction xs; split; intros.
  - constructor.
  - constructor.
  - dependent destruction H.
    simpl; constructor.
    + replace (i + k) with (k + i + 0) by lia.
      apply not_free_lift.
      now rewrite Nat.add_0_r.
    + now apply IHxs.
  - dependent destruction H.
    simpl; constructor.
    + replace (i + k) with (k + i + 0) in H by lia.
      apply not_free_lift in H.
      now rewrite Nat.add_0_r in H.
    + now apply IHxs with i.
Qed.

(* While the following could be proven by possibly simpler means, like showing
   the relation between Kennedy's translation and Plotkin's, the following was
   rather important in helping to derive the proper points for lifting; finding
   the proper invariants was key! Thus, this proof is valuable on its own. *)

Lemma kennedy_not_free_generalized:
  forall e K b,
  kennedy e K b ->
  forall i,
  i >= kennedy_offset K ->
  Forall (not_free i) (e :: code_context K) <-> CPS.not_free (1 + i) b.
Proof.
  (* A complicated issue; proceed by mutual induction with the defunctionalized
     code, keeping an invariant about how they generate terms! *)
  induction 1 using kennedy_ind2 with (P0 :=
    (* For code K, with k new binders, invoked with variable n, producing term
       c... *)
    fun K k n c =>
      (* For any non-fresh variable i... *)
      forall i, (* Note that variables less than that will be used for the... *)
      i >= k + kennedy_offset K -> (* ...local names of computations. *)
      (* If i is not free in n, nor in the terms captured (which will be placed
         in c after k binders)... *)
      Forall (not_free i) (var n :: map (lift k 0) (code_context K)) <->
        (* Then it isn't free on the resulting term (remember that there is now
           space for the current continuation; also: lift 1 k i = 1 + i. *)
        CPS.not_free (1 + i) c
  ); repeat split; intros.
  (* Case: bound, only if. *)
  - apply IHkennedy.
    + assumption.
    + (* Note lift 0 0 is the identity on terms. *)
      rewrite map_ext with (g := fun x => x); intros.
      * now rewrite map_id.
      * apply lift_zero_e_equals_e.
  (* Case: bound, if. *)
  - apply IHkennedy in H1.
    + (* Ditto. *)
      rewrite map_ext with (g := fun x => x) in H1; intros.
      * now rewrite map_id in H1.
      * apply lift_zero_e_equals_e.
    + assumption.
  (* Case: abstraction, only if. *)
  - simpl in IHkennedy, IHkennedy0.
    dependent destruction H2.
    constructor.
    + (* On the left, we proceed by applying the code to the new function. *)
      apply IHkennedy.
      * lia.
      * repeat constructor; try lia.
        (* Fix the offset as we're adding a binder (the function). *)
        now apply Forall_not_free_map_lift.
    + repeat constructor.
    + (* On the right, we proceed with the function body and a new, fresh
         current continuation. *)
      simpl.
      apply IHkennedy0; try lia.
      repeat constructor.
      dependent destruction H2.
      (* We just have to skip the outer current continuation, which is fresh. *)
      replace (S (S n)) with (n + 1 + 1) by lia.
      apply not_free_lift.
      rewrite Nat.add_comm.
      assumption.
  (* Case: abstraction, if. *)
  - simpl in IHkennedy0.
    dependent destruction H2.
    clear H2; simpl in H2_, H2_0.
    rename H2_ into H2, H2_0 into H3.
    constructor.
    + (* From the recursive application we proceed for the original term. *)
      constructor.
      apply IHkennedy0 in H3; try lia.
      dependent destruction H3.
      clear H4.
      replace (S (S i)) with (i + 1 + 1) in H3 by lia.
      apply not_free_lift in H3.
      rewrite Nat.add_comm in H3.
      assumption.
    + (* We may preserve the invariant of the code for remaining terms. *)
      apply IHkennedy in H2.
      * dependent destruction H2.
        (* Fix the offset as we're removing a binder. *)
        now apply Forall_not_free_map_lift with 1.
      * lia.
  (* Case: application, only if. *)
  - (* Simply proceed by induction. *)
    simpl in IHkennedy.
    dependent destruction H1.
    dependent destruction H1.
    apply IHkennedy.
    + assumption.
    + now repeat constructor.
  (* Case: application, if. *)
  - (* Ditto. *)
    simpl in IHkennedy.
    apply IHkennedy in H1.
    + dependent destruction H1.
      dependent destruction H2.
      now repeat constructor.
    + assumption.
  (* Case: halt, only if. *)
  - dependent destruction H0.
    dependent destruction H0.
    clear H1; rename n0 into i; simpl in H.
    repeat constructor.
    + lia.
    + destruct (le_gt_dec k n).
      * (* TODO: enhance sigma! *)
        change n with (@var nat _ n); sigma.
        unfold var, nat_dbVar, Datatypes.id.
        lia.
      * (* TODO: ditto! *)
        change n with (@var nat _ n); sigma.
        unfold var, nat_dbVar, Datatypes.id.
        lia.
  (* Case: halt, if. *)
  - repeat constructor.
    dependent destruction H0.
    dependent destruction H0.
    dependent destruction H1.
    dependent destruction H1.
    clear H2; simpl in H.
    destruct (le_gt_dec k n).
    + (* TODO: improve sigma, please! *)
      generalize H1; clear H1.
      change n with (@var nat _ n) at 1; sigma.
      unfold var, nat_dbVar, Datatypes.id; intro.
      lia.
    + generalize H1; clear H1.
      change n with (@var nat _ n) at 1; sigma.
      change (var n) with n; intro.
      lia.
  (* Case: then, only if. *)
  - simpl in IHkennedy, H0, H1.
    dependent destruction H1.
    dependent destruction H1.
    dependent destruction H2.
    apply IHkennedy.
    + assumption.
    + now repeat constructor.
  (* Case: then, if. *)
  - simpl in IHkennedy, H0 |- *.
    apply IHkennedy in H1.
    + dependent destruction H1.
      dependent destruction H2.
      dependent destruction H2.
      now repeat constructor.
    + assumption.
  (* Case: call, only if. *)
  - simpl in IHkennedy, H0, H1.
    dependent destruction H1.
    dependent destruction H2.
    rewrite map_map in H3.
    repeat constructor; simpl.
    + dependent destruction H1.
      destruct (le_gt_dec k v).
      * admit.
      * admit.
    + lia.
    + admit.
    + apply IHkennedy; [| constructor ].
      * lia.
      * constructor.
        lia.
      * (* Fix the offset as we're adding a binder. This still comes from H3,
           clearly. *)
        admit.
  (* Case: call, if. *)
  - simpl in H0 |- *.
    dependent destruction H1.
    dependent destruction H1_.
    dependent destruction H1_.
    dependent destruction H2.
    clear H2.
    dependent destruction H3.
    dependent destruction H2.
    clear H3 H4.
    rename H1_0 into H3; simpl in H3.
    apply IHkennedy in H3; try lia.
    dependent destruction H3.
    clear H3.
    repeat constructor.
    + admit.
    + admit.
    + (* One less binder, but this information clearly comes from H4. *)
      admit.
Admitted.

Lemma kennedy_not_free:
  forall e b,
  kennedy e kennedy_halt b ->
  forall i,
  not_free i e <-> CPS.not_free (1 + i) b.
Proof.
  intros.
  pose proof kennedy_not_free_generalized.
  specialize (H0 e kennedy_halt b H i).
  simpl in H0; destruct H0.
  - lia.
  - split; intro.
    + apply H0; auto.
    + specialize (H1 H2).
      now inversion H1.
Qed.

(* TODO: question, is Kennedy's translation (the tail-recursive version) really
   the same as Plotkin's CBV then administrative reductions (linear jumps)? I am
   starting to think that maybe there's need for some floating too... *)

Section ModifiedCBV.

  Local Notation jump := Residuals.redexes_jump.

  Local Notation bind := Residuals.redexes_bind.

  Local Notation VAR d n :=
    (* [x] = k<x> *)
    (jump d (var 0) [var (1 + n)]) (only parsing).

  Local Notation ABS d b t1 t2 :=
    (* [\x.e] = k<f> { f<x, k> = [e] } *)
    (bind (jump d (var 1) [var 0]) [t1; t2] b) (only parsing).

  Local Notation APP b c t1 t2 :=
    (* [e f] = [e] { k<f> = [f] { k<v> = f<v, k> } } *)
    (bind b [t1] (bind c [t2]
      (jump false (var 1) [var 2; var 0]))) (only parsing).

  (* The modified CBV translation is just Plotkin's CBV translation, but instead
     it returns marked terms. We underline every jump to a current continuation
     whose content is defined and thus the jump may be performed. We define two
     versions by mutual induction (note the first argument, being a boolean), so
     that we may know whether the current continuation is defined or not. *)

  Inductive modified_cbv_cps: bool -> term -> Residuals.redexes -> Prop :=
    | modified_cbv_cps_bound:
      forall d n,
      modified_cbv_cps d (var n) (VAR d n)
    | modified_cbv_cps_abstraction:
      forall d t e b,
      modified_cbv_cps false (lift 1 1 e) b ->
      modified_cbv_cps d (abstraction t e) (ABS d b CPS.void CPS.void)
    | modified_cbv_cps_application:
      forall d f x b c,
      modified_cbv_cps true (lift 1 0 f) b ->
      modified_cbv_cps true (lift 2 0 x) c ->
      modified_cbv_cps d (application f x) (APP b c CPS.void CPS.void).

  Local Goal
    forall d e r,
    modified_cbv_cps d e r ->
    cbv_cps e (Residuals.unmark r).
  Proof.
    induction 1; intros; simpl.
    - constructor.
    - now constructor.
    - now constructor.
  Qed.

  Print Residuals.regular.

  Lemma modified_cbv_residuals_generalized:
    forall b e r,
    modified_cbv_cps b e r ->
    forall g,
    (if b then
      exists2 s,
      item (Some (1, s)) g 0 & Residuals.redexes_count s = 0
    else
      True) ->
    exists2 t,
    Residuals.residuals g r r t & Residuals.redexes_count t = 0.
  Proof.
    induction 1; intros.
    - (* Are we performing this jump...? *)
      destruct d.
      + (* If we are, we know that it's defined: this was administrative. *)
        destruct H as (s, ?, ?).
        eexists.
        * constructor; simpl.
          eassumption.
        * simpl.
          admit.
      + (* No jump will be performed, so no problem. *)
        eexists.
        * constructor.
        * reflexivity.
    - specialize (IHmodified_cbv_cps (None :: None :: g) ltac:(trivial)).
      destruct IHmodified_cbv_cps as (b', ?, ?).
      destruct d.
      + destruct H0 as (s, ?, ?).
        eexists; try constructor; simpl.
        * do 2 constructor; simpl.
          eassumption.
        * eassumption.
        * simpl.
          admit.
      + eexists; try constructor; simpl.
        * constructor.
        * eassumption.
        * simpl; lia.
    - (* The continuation given to c will be our anchor, which should be put in
         place, but that itself will not be performed as it represents a source
         redex. *)
      set (anchor := jump false (var 1) [var 2; var 0]).
      specialize (IHmodified_cbv_cps2 (Some (1, anchor) :: None :: g)).
      (* By induction, c is fine. *)
      edestruct IHmodified_cbv_cps2 as (c', ?, ?); intros.
      + eexists; eauto with cps.
      + (* The continuation given to b will be c (along with the anchor), which
           is expected to be performed. *)
        specialize (IHmodified_cbv_cps1 (Some (1, bind c' [V] anchor) :: g)).
        (* By induction, b is fine. *)
        edestruct IHmodified_cbv_cps1 as (b', ?, ?); intros.
        * eexists; eauto with cps.
          simpl; lia.
        * eexists; eauto with cps.
          (* None of these items have marks anymore. *)
          simpl; lia.
  Admitted.

  Lemma modified_cbv_residuals:
    forall e r,
    modified_cbv_cps false e r ->
    exists2 s,
    Residuals.residuals [] r r s & Residuals.redexes_count s = 0.
  Proof.
    intros.
    apply modified_cbv_residuals_generalized with false e; intros.
    - assumption.
    - trivial.
  Qed.

  Lemma modified_cbv_regular:
    forall e r,
    modified_cbv_cps false e r ->
    Residuals.regular r.
  Proof.
    intros.
    destruct modified_cbv_residuals with e r as (s, ?, ?).
    - assumption.
    - now exists r, s.
  Qed.

End ModifiedCBV.
