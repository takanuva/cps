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
Require Import Local.Lambda.ModifiedCBV.

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
   as the toplevel k stands for termination). We may see we use the former
   translation when we know how to continue (in the case of an application) and
   the latter translation when the continuation is not yet bound. As we call
   [(e) k] if and only if we would be calling [[e] K] with [K] being the return
   continuation (which has been noted by Danvy and Filinski already!), these two
   functions may be merged in case we use a defunctionalized version of the
   definition instead of using actual meta-level functions because we are able
   to check for equality then; this is, indeed, how we define the relation in
   this formalization.

   We would like to show that we can get from Plotkin's CBV translation into the
   optimized translation above by performing administrative jumps and garbage
   collection. This combination show result that this translation is adequate
   and that it gives a sound denotational semantics for the lambda calculus, as
   Kennedy intended. TODO: do we wanna compare this to Sabry and Felleisen's
   translation, given in the ANF paper? Might be cool. *)

Inductive kennedy_code: Set :=
  | kennedy_halt
  | kennedy_then (e: term) (K: kennedy_code)
  | kennedy_call (f: nat) (j: nat) (K: kennedy_code).

Axiom A: nat -> nat -> nat -> nat.
Axiom B: nat -> nat -> nat -> nat.
Axiom C: nat -> nat -> nat -> nat.
Axiom D: nat -> nat -> nat -> nat.
Axiom X: nat -> nat -> nat.

Section Kennedy.

  Variable optimize: bool.

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
    | kennedy_apply_call1:
      forall K f j k v b,
      (* We pick this either for the naive version, where there is never a tail
         optimization, or for the optimized version in case this is NOT a tail
         call. *)
      optimize = false \/ K <> kennedy_halt ->
      kennedy_apply K (1 + k + j) 0 b ->
      kennedy_apply (kennedy_call f j K) k v
        (CPS.bind
          (CPS.jump (var (A j k f)) [var 0; var (B j k v)])
          [CPS.void] b)

    (* f, j; k, v => f<v, k> *)
    | kennedy_apply_call2:
      forall K f j k v,
      (* We pick this case in the optimized version if we are in a tail call.
         There is no need for a recursive call anymore, as we are only required
         to introduce the anchor now. *)
      optimize = true /\ K = kennedy_halt ->
      kennedy_apply (kennedy_call f j K) k v
        (CPS.jump (var (C j k f)) [var (X j k); var (D j k v)]).

End Kennedy.

Scheme kennedy_ind2 := Minimality for kennedy Sort Prop
  with kennedy_apply_ind2 := Minimality for kennedy_apply Sort Prop.

(* TODO: remove me. *)

Local Notation HALT := kennedy_halt.
Local Notation THEN := kennedy_then.
Local Notation CALL := kennedy_call.

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
  forall o e K b,
  kennedy o e K b ->
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
  (* Case: non-tail call, only if. *)
  - simpl in IHkennedy, H1, H2.
    dependent destruction H2.
    dependent destruction H3.
    rewrite map_map in H4.
    repeat constructor; simpl.
    + dependent destruction H2.
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
  (* Case: non-tail call, if. *)
  - simpl in H1 |- *.
    dependent destruction H2.
    dependent destruction H2_.
    dependent destruction H2_.
    dependent destruction H3.
    clear H3.
    dependent destruction H4.
    dependent destruction H3.
    clear H4 H5.
    rename H2_0 into H4; simpl in H4.
    apply IHkennedy in H4; try lia.
    dependent destruction H4.
    clear H4.
    repeat constructor.
    + admit.
    + admit.
    + (* One less binder, but this information clearly comes from H4. *)
      admit.
  (* Case: tail call, only if. *)
  - simpl in H1 |- *.
    dependent destruction H1.
    dependent destruction H2.
    rewrite map_map in H3.
    repeat constructor; simpl.
    + admit.
    + admit.
    + admit.
  (* Case: tail call, if. *)
  - simpl in H0, H1 |- *.
    dependent destruction H1.
    dependent destruction H2.
    dependent destruction H3.
    clear H4.
    repeat constructor.
    + admit.
    + admit.
    + destruct H as (_, ?).
      subst; simpl.
      constructor.
Admitted.

Lemma kennedy_not_free:
  forall o e b,
  kennedy o e kennedy_halt b ->
  forall i,
  not_free i e <-> CPS.not_free (1 + i) b.
Proof.
  intros.
  pose proof kennedy_not_free_generalized.
  specialize (H0 o e kennedy_halt b H i).
  simpl in H0; destruct H0.
  - lia.
  - split; intro.
    + apply H0; auto.
    + specialize (H1 H2).
      now inversion H1.
Qed.

Example foo :=
  application (application 10 20) (application 30 40).

Example bar :=
  Syntax.bind
    (Syntax.jump 12 [var 0; var 22])
    [V]
    (Syntax.bind
       (Syntax.jump 33 [var 0; var 43])
          [V]
          (Syntax.jump 1 [var 2; var 0])).

Local Coercion Syntax.bound: nat >-> Syntax.pseudoterm.

Local Goal
  exists2 b,
  cbv_cps foo b & rt(Reduction.step) b bar.
Proof.
  eexists.
  unfold foo.
  constructor.
  vm_compute.
  constructor.
  vm_compute.
  constructor.
  vm_compute.
  constructor.
  vm_compute.
  constructor.
  vm_compute.
  constructor.
  vm_compute.
  constructor.
  vm_compute.
  (* Jump #1. *)
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_left.
  change (Syntax.jump (Syntax.bound 0) [Syntax.bound 13]) with
    (Context.apply_context Context.context_hole (Syntax.jump 0 [Syntax.bound 13])).
  apply Reduction.step_ctxjmp.
  reflexivity.
  vm_compute.
  (* GC #1. *)
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_left.
  apply Reduction.step_gc.
  repeat constructor; simpl; lia.
  vm_compute.
  (* Jump #2. *)
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_left.
  change (Syntax.jump (Syntax.bound 0) [Syntax.bound 23]) with
    (Context.apply_context Context.context_hole (Syntax.jump 0 [Syntax.bound 23])).
  apply Reduction.step_ctxjmp.
  reflexivity.
  vm_compute.
  (* GC #2. *)
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_left.
  apply Reduction.step_gc.
  repeat constructor; simpl; lia.
  vm_compute.
  (* Jump #3. *)
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_right.
  apply Reduction.step_bind_left.
  change (Syntax.jump (Syntax.bound 0) [Syntax.bound 34]) with
    (Context.apply_context Context.context_hole (Syntax.jump 0 [Syntax.bound 34])).
  apply Reduction.step_ctxjmp.
  reflexivity.
  vm_compute.
  (* GC #3. *)
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_right.
  apply Reduction.step_bind_left.
  apply Reduction.step_gc.
  repeat constructor; simpl; lia.
  vm_compute.
  (* Step #4. *)
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_right.
  apply Reduction.step_bind_left.
  change (Syntax.jump (Syntax.bound 0) [Syntax.bound 44]) with
    (Context.apply_context Context.context_hole (Syntax.jump 0 [Syntax.bound 44])).
  apply Reduction.step_ctxjmp.
  reflexivity.
  vm_compute.
  (* GC #4. *)
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_right.
  apply Reduction.step_bind_left.
  apply Reduction.step_gc.
  repeat constructor; simpl; lia.
  vm_compute.
  (* Done! *)
  apply rt_refl.
Qed.

Local Goal
  normal Reduction.step bar.
Proof.
  do 2 intro.
  dependent destruction H.
  destruct h; simpl in x.
  inversion x.
  inversion x.
  inversion x.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  contradiction.
  inversion H.
  dependent destruction H.
  destruct h; simpl in x.
  inversion x.
  inversion x.
  inversion x.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  contradiction.
  inversion H.
  inversion H.
Qed.

Local Goal
  exists2 b,
  kennedy true foo kennedy_halt b & b = bar.
Proof.
  eexists.
  constructor.
  constructor.
  constructor.
  constructor.
  vm_compute.
  constructor.
  constructor.
  now right.
  vm_compute.
  constructor.
  vm_compute.
  constructor.
  constructor.
  constructor.
  vm_compute.
  constructor.
  constructor.
  now right.
  vm_compute.
  constructor 4.
  now split.
  vm_compute.
  admit.
Admitted.
