(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Reduction.
Require Import Local.Observational.

Goal
  forall j a (s r: list pseudoterm),
  j >= a ->
  (if le_gt_dec (length s) (length r) then
     j - a + (length r - length s)
   else
     j - a - (length s - length r)) =
  (* Of course... *)
  j - a + length r - length s.
Proof.
  intros.
  generalize (length s).
  generalize (length r).
  clear s r.
  intros n m.
  destruct (le_gt_dec m n).
  lia.
  lia.
Qed.

Inductive value: Set :=
  (* We don't really need this in the named setting, but it's surely useful in
     the de Bruijn setting! With this we can propagate that a variable has been
     substituted by a free variable. *)
  | value_undefined
  (* Continuations in memory. *)
  | value_cont (p: list value) (ts: list pseudoterm) (c: pseudoterm).

Local Notation U := value_undefined.

Local Notation "< r ; \ ts : c >" :=
  (value_cont r ts c) (only printing, format "< r ;  \ ts :  c >").

Definition heap: Set :=
  list value.

Definition configuration: Set :=
  pseudoterm * heap.

(* Please note that parameters are written from right to left, but arguments to
   jumps are written from left to write!

   TODO: in the future we might want to generalize this beyond lists of names,
   such as in the case we have primitive values as well. *)

Definition heap_append (ns: list nat) (r s: heap): heap :=
  (* map (fun n => nth n r U) (rev ns) ++ s *)
  fold_left (fun acc n => nth n r U :: acc) ns s.

(* A predicate that says that a configuration has reached it's final point, and
   that it won't reduce any further. This is signaled by a command that jumps to
   a variable that's not in the heap (i.e., a free variable). *)

Definition configuration_final (c: configuration): Prop :=
  exists k xs r,
  c = (jump (bound k) xs, r) /\ nth k r U = U.

(* Big-step abstract machine semantics for the CPS-calculus. This was derived
   directly from Kennedy's paper, slightly adapting it to use free variables as
   a signal of termination rather than using a "halt" term. This is meant to be
   an "implementation-friendly" semantics for the calculus. *)

Inductive big: configuration -> Prop :=
  (*
      r(k) is undefined
    --------------------- (M-HALT)
       (k<xs>, r) \/ k
  *)
  | big_halt:
    forall k xs r,
    nth k r U = U ->
    big (jump k xs, r)

  (*
      p(k) = <s, \xs.c>       <c, s, xs = r(ys)> \/ j
    --------------------------------------------------- (M-JUMP)
                   <k<ys>, r> \/ j[ys/xs]
  *)
  | big_jump:
    forall r s a c k xs ts ns,
    Forall2 (fun x n => x = bound n) xs ns ->
    a = length ns ->
    item (value_cont s ts c) r k ->
    a = length ts ->
    big (c, heap_append ns r s) ->
    big (jump k xs, r)

  (*
      <b, r, k = <r, \xs.c>> \/ j
    ------------------------------- (M-BIND)
       <b { k<xs> = c }, r> \/ j
  *)
  | big_bind:
    forall b ts c r,
    big (b, value_cont r ts c :: r) ->
    big (bind b ts c, r).

(* A small-step variant of Kennedy's machine semantics for a CPS IR. This is
   useful as it gives us a better inductive principle, allowing us to check for
   individual steps that are otherwise burried deep in the proof tree of the
   big-step semantics. Those two should nevertheless be equivalent. *)

Inductive smol: relation configuration :=
  | smol_jump:
    forall r s a c k xs ts ns,
    Forall2 (fun x n => x = bound n) xs ns ->
    a = length ns ->
    item (value_cont s ts c) r k ->
    a = length ts ->
    smol (jump k xs, r) (c, heap_append ns r s)
  | smol_bind:
    forall b ts c r,
    smol (bind b ts c, r) (b, value_cont r ts c :: r).

Definition smol_eval (c1: configuration): Prop :=
  exists2 c2,
  rt(smol) c1 c2 & configuration_final c2.

Lemma smol_eval_bind_inv:
  forall b1 b2 ts c r,
  (* We note that the inverse here is also true! *)
  (smol_eval (b1, value_cont r ts c :: r) ->
    smol_eval (b2, value_cont r ts c :: r)) ->
  smol_eval (bind b1 ts c, r) -> smol_eval (bind b2 ts c, r).
Proof.
  intros.
  destruct H0.
  apply clos_rt_rt1n_iff in H0.
  dependent destruction H0.
  - exfalso.
    destruct H1 as (k, (xs, (s, [? ?]))).
    inversion H0.
  - apply clos_rt_rt1n_iff in H1.
    dependent destruction H0.
    edestruct H.
    + exists z; auto.
    + exists x; auto.
      eapply rt_trans.
      * apply rt_step.
        constructor.
      * assumption.
Qed.

Lemma smol_preserves_big:
  forall c1 c2,
  smol c1 c2 -> big c2 -> big c1.
Proof.
  induction 1; intros.
  - eapply big_jump; eauto.
  - constructor; auto.
Qed.

Lemma big_smol_eval_are_equivalent:
  forall c,
  big c <-> smol_eval c.
Proof.
  split; intros.
  - induction H.
    + eexists.
      apply rt_refl.
      unfold configuration_final; eauto.
    + dependent destruction IHbig.
      eexists x; auto.
      eapply rt_trans.
      * apply rt_step.
        econstructor; eauto.
      * assumption.
    + dependent destruction IHbig.
      eexists x; auto.
      eapply rt_trans.
      * apply rt_step.
        constructor; auto.
      * assumption.
  - dependent destruction H.
    generalize dependent H0.
    apply clos_rt_rt1n_iff in H.
    induction H; intros.
    + destruct H0 as (k, (xs, (r, [? ?]))).
      rewrite H; clear H.
      constructor; auto.
    + eapply smol_preserves_big; eauto.
Qed.

(*
Fixpoint context_to_heap h s: heap :=
  match h with
  | context_hole =>
    s
  | context_left r ts c =>
    context_to_heap r (value_cont s ts c :: s)
  | context_right b ts r =>
    (* We don't really care about this one. *)
    []
  end.

Lemma rt_smol_static_context:
  forall h,
  static h ->
  forall k xs r,
  rt(smol) (h (jump k xs), r) (jump k xs, context_to_heap h r).
Proof.
  induction 1; intros.
  - simpl.
    apply rt_refl.
  - simpl.
    eapply rt_trans.
    + apply rt_step.
      constructor.
    + auto.
Qed.
*)

Lemma big_is_preserved_backwards_by_head:
  forall c1 c2,
  head c1 c2 ->
  forall r,
  big (c2, r) -> big (c1, r).
Proof.
  intros.
  (* We'd like to reason about small-step machine semantics. *)
  apply big_smol_eval_are_equivalent.
  apply big_smol_eval_are_equivalent in H0.
  generalize dependent r.
  (* TODO: we could make an induction principle for this... *)
  dependent destruction H.
  induction H0; simpl.
  (* Case: head_step. *)
  - admit.
  (* Case: head_bind_left. *)
  - rename h0 into s; intros.
    eapply smol_eval_bind_inv.
    + intros.
      apply IHstatic.
      exact H3.
    + assumption.
Admitted.

Lemma convergent_term_is_trivially_final:
  forall c n,
  converges c n -> big (c, []).
Proof.
  intros.
  assert (exists2 r: heap, [] = r & length r <= n) as (r, ?, ?).
  - exists []; simpl; auto.
    lia.
  - rewrite H0; clear H0.
    generalize dependent r.
    induction H; intros.
    + constructor.
      generalize dependent k.
      induction r; intros.
      * destruct k; auto.
      * simpl in H1.
        destruct k; try lia.
        simpl; apply IHr.
        lia.
    + constructor.
      apply IHconverges.
      simpl; lia.
Qed.

Lemma head_evaluation_implies_big:
  forall c n,
  comp rt(head) converges c n ->
  big (c, []).
Proof.
  intros c1 n (c2, ?, ?).
  apply clos_rt_rt1n_iff in H.
  induction H.
  - apply convergent_term_is_trivially_final with n.
    assumption.
  - eapply big_is_preserved_backwards_by_head.
    + exact H.
    + auto.
Qed.

Lemma big_implies_head_evaluation:
  forall c,
  big (c, []) ->
  exists n,
  comp rt(head) converges c n.
Proof.
  admit.
Admitted.

(*

(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Reduction.
Require Import Local.Observational.

Inductive value: Set :=
  (* We don't really need this in the named setting, but it's surely useful in
     the de Bruijn setting! With this we can propagate that a variable has been
     substituted by a free variable. *)
  | value_undefined
  (* Continuations in memory. *)
  | value_cont (p: list value) (ts: list pseudoterm) (c: pseudoterm).

Local Notation U := value_undefined.

Local Notation "< r ; \ ts : c >" :=
  (value_cont r ts c) (only printing, format "< r ;  \ ts :  c >").

Definition heap: Set :=
  list value.

Definition configuration: Set :=
  pseudoterm * heap.

(* Please note that parameters are written from right to left, but arguments to
   jumps are written from left to write! *)

Definition heap_append (ns: list nat) (r s: heap): heap :=
  (* map (fun n => nth n r U) (rev ns) ++ s *)
  fold_left (fun acc n => nth n r U :: acc) ns s.

(* Big-step abstract machine semantics for the CPS-calculus. This was derived
   directly from Kennedy's paper, slightly adapting it to use free variables as
   a signal of termination rather than using a "halt" term. This is meant to be
   an "implementation-friendly" semantics for the calculus. *)

Inductive big: configuration -> nat -> Prop :=
  (*
      r(k) is undefined
    --------------------- (M-HALT)
       (k<xs>, r) |-> k
  *)
  | big_halt:
    forall k xs r,
    nth k r U = U ->
    big (jump k xs, r) k

  (*
      p(k) = <s, \xs.c>      <c, s, xs = r(ys)> |-> j
    --------------------------------------------------- (M-JUMP)
                  <k<ys>, r> |-> j[ys/xs]
  *)
  | big_jump:
    forall r s a c k xs ts ns j j',
    Forall2 (fun x n => x = bound n) xs ns ->
    a = length ns ->
    item (value_cont s ts c) r k ->
    a = length ts ->
    big (c, heap_append ns r s) j ->
    (* Naughty little index math here! We build the runtime heap for c using s,
       and it may return two continuations: one that we have bound now, from the
       parameters, or one that is already bound in s. We have to map the results
       to the heap r! So, if the result is a parameter, thus j <= a, we already
       know its value in r (which comes from ns). But, if j > a, we'll have to
       remove any newly bound abstractions, subtracting a, and then add any
       new abstractions that have been bound in r but not in s (notice that r is
       always newer and as such has strictly more bindings!). Also remember that
       parameters are in the reverse order, but arguments are not, so we need to
       reverse [ns] here as well. *)

    (* TODO: fix above comment, move following into definition. *)
    j' = (if le_gt_dec (length s) (length r) then
            nth j (rev ns) (j - a + (length r - length s))
          else
            nth j (rev ns) (j - a - (length s - length r))) ->

    (* There we go. *)
    big (jump k xs, r) j'

  (*
      <b, r, k = <r, \xs.c>> |-> j
    -------------------------------- (M-BIND)
       <b { k<xs> = c }, r> |-> j
  *)
  | big_bind:
    forall b ts c r j,
    big (b, value_cont r ts c :: r) (S j) ->
    big (bind b ts c, r) j.

(* TODO: remove the following! We need to prove equivalence of the above and the
   head reduction! *)

Goal
  big (ex1, []) 3.
Proof.
  compute.
  constructor; simpl.
  constructor; simpl.
  eapply big_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  econstructor 1.
  compute; reflexivity.
  compute; reflexivity.
  compute; reflexivity.
  compute; reflexivity.
Qed.

Goal
  weakly_converges ex1 3.
Proof.
  eexists; simpl.
  apply star_trans with ex3.
  compute.
  constructor.
  apply step_ctxjmp with (h := context_left context_hole ?[ts] ?[c]); auto.
  compute.
  eapply star_trans.
  apply star_step.
  apply step_bind_left.
  apply step_recjmp.
  reflexivity.
  compute.
  apply star_step.
  apply step_ctxjmp with (h := context_left context_hole ?[ts] ?[c]); auto.
  compute.
  constructor.
  constructor.
  constructor.
Qed.

Fixpoint context_to_heap h s: heap :=
  match h with
  | context_hole =>
    s
  | context_left r ts c =>
    context_to_heap r (value_cont s ts c :: s)
  | context_right b ts r =>
    (* We don't really care about this one. *)
    []
  end.

Inductive big_aux: configuration -> nat -> Prop :=
  | big_aux_halt:
    forall k xs r,
    nth k r U = U ->
    big_aux (jump k xs, r) k

  | big_aux_jump:
    forall r s a c k xs ts ns j j',
    Forall2 (fun x n => x = bound n) xs ns ->
    a = length ns ->
    item (value_cont s ts c) r k ->
    a = length ts ->
    big_aux (c, heap_append ns r s) j ->
    j' = (if le_gt_dec (length s) (length r) then
            nth j (rev ns) (j - a + (length r - length s))
          else
            nth j (rev ns) (j - a - (length s - length r))) ->
    big_aux (jump k xs, r) j'

  | big_aux_bind:
    forall k xs r j h,
    static h ->
    #h > 0 ->
    big_aux (jump k xs, context_to_heap h r) (#h + j) ->
    big_aux (h (jump k xs), r) j.

Lemma context_to_heap_length:
  forall h,
  static h ->
  forall r,
  length (context_to_heap h r) = #h + length r.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - rewrite IHstatic; simpl.
    lia.
Qed.

Lemma context_to_heap_app:
  forall h,
  static h ->
  forall r,
  exists2 s,
  context_to_heap h r = s ++ r & #h = length s.
Proof.
  induction 1; intros.
  - exists []; simpl; auto.
  - edestruct IHstatic as (s, ?, ?).
    eexists; simpl.
    + rewrite H0.
      replace (s ++ value_cont r ts c :: r) with
        ((s ++ [value_cont r ts c]) ++ r).
      * reflexivity.
      * rewrite <- app_assoc.
        reflexivity.
    + rewrite app_length; simpl.
      lia.
Qed.

Lemma big_implies_big_aux:
  forall h,
  static h ->
  forall c r k,
  big (c, context_to_heap h r) (#h + k) ->
  big_aux (h c, r) k.
Proof.
  induction 1; simpl; intros.
  - induction H.
    + constructor 1; auto.
    + econstructor 2; eauto.
    + replace (bind b ts c0) with (context_left context_hole ts c0 b); auto.
      dependent destruction IHbig.
      * constructor; simpl; eauto with cps.
        constructor; assumption.
      * constructor; simpl; eauto with cps.
        econstructor 2; eauto.
      * rewrite <- compose_context_is_sound.
        constructor; simpl; eauto with cps.
        replace (S (#h + j)) with (#h + S j); try lia.
        assumption.
  - replace (bind (h c0) ts c) with (context_left context_hole ts c (h c0));
      auto.
    replace (S (#h + k)) with (#h + S k) in H0; try lia.
    specialize (IHstatic _ _ _ H0); clear H0.
    dependent destruction IHstatic.
    + destruct h; try discriminate.
      simpl in x; dependent destruction x.
      constructor; simpl; auto with cps.
      constructor 1.
      assumption.
    + destruct h; try discriminate.
      simpl in x0; dependent destruction x0.
      constructor; simpl; auto with cps.
      econstructor 2; eauto.
    + rewrite <- x.
      rewrite <- compose_context_is_sound.
      constructor 3; simpl; auto with cps.
      replace (S (#h0 + k)) with (#h0 + S k); try lia.
      assumption.
Qed.

Lemma big_aux_implies_big:
  forall c r k,
  big_aux (c, r) k ->
  big (c, r) k.
Proof.
  intros.
  dependent induction H.
  - constructor 1; auto.
  - econstructor 2; eauto.
  - specialize (IHbig_aux _ _ JMeq_refl).
    clear H0 H1.
    generalize dependent j.
    generalize dependent r.
    induction H; simpl; intros.
    + assumption.
    + constructor 3.
      apply IHstatic.
      replace (#h + S j) with (S (#h + j)); try lia.
      assumption.
Qed.

Lemma big_and_big_aux_are_equivalent:
  forall c r k,
  big_aux (c, r) k <-> big (c, r) k.
Proof.
  split; intros.
  - apply big_aux_implies_big; auto.
  - apply big_implies_big_aux with (h := context_hole); auto with cps.
Qed.

Fixpoint rebuild_heap (h: heap): context :=
  match h with
  | [] =>
    context_hole
  | value_undefined :: h' =>
    rebuild_heap h'
  | value_cont _ ts c :: h' =>
    compose_context (rebuild_heap h')
      (context_left context_hole ts c)
  end.

Lemma context_to_heap_compose:
  forall h,
  static h ->
  forall r s,
  context_to_heap (compose_context h r) s =
    context_to_heap r (context_to_heap h s).
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - rewrite IHstatic.
    reflexivity.
Qed.

Goal
  forall r,
  static (rebuild_heap r).
Proof.
  induction r; simpl.
  - constructor.
  - destruct a; simpl.
    + assumption.
    + apply static_compose_context.
      * assumption.
      * do 2 constructor.
Qed.

Goal
  forall r,
  ~(In U r) ->
  #(rebuild_heap r) = length r.
Proof.
  induction r; intros; simpl.
  - reflexivity.
  - destruct a; simpl.
    + exfalso; apply H.
      constructor.
      reflexivity.
    + rewrite compose_context_bvars; simpl.
      rewrite plus_comm; simpl; f_equal.
      apply IHr.
      intro; apply H.
      constructor 2.
      assumption.
Qed.

Lemma big_implies_weakly_converges:
  forall r c k,
  big (c, r) k ->
  weakly_converges c k.
Proof.
  intros.
  dependent induction H; simpl.
  - eexists.
    + eapply star_refl.
    + constructor.
  - (* We probably need substitution in heaps as Plotkin did! *)
    rename c0 into c.
    (* Lets check our inductive hypothesis... *)
    specialize (IHbig _ _ JMeq_refl).
    (* Huh...? Perhaps the induction should be on the length of reduction... *)
    admit.
  - rename c0 into c.
    edestruct IHbig; eauto.
    exists (bind x ts c).
    + apply star_bind_left.
      assumption.
    + constructor.
      assumption.
Admitted.

Theorem weakly_converges_and_big_are_equivalent:
  forall c k,
  big (c, []) k <-> weakly_converges c k.
Proof.
  split; intros.
  - apply big_implies_weakly_converges with [].
    assumption.
  - admit.
Admitted.

Example ex_cbn: pseudoterm :=
  (bind (bind (jump 1 [bound 0]) [void; void] (jump 1 [bound 0]))
      [void]
      (bind (jump 1 [bound 0; bound 2]) [void]
         (bind
            (bind (jump 1 [bound 0]) [void; void] (jump 1 [bound 0]))
            [void]
            (bind (jump 1 [bound 0; bound 2]) [void]
               (bind (jump 1 [bound 0]) [void; void]
                  (jump 1 [bound 0])))))).

Example ex_cbv: pseudoterm :=
   (bind (bind (jump 1 [bound 0]) [void; void] (jump 0 [bound 1]))
      [void]
      (bind
         (bind
            (bind (jump 1 [bound 0]) [void; void] (jump 0 [bound 1]))
            [void]
            (bind
               (bind (jump 1 [bound 0]) [void; void]
                  (jump 0 [bound 1])) [void] 
               (jump 1 [bound 0; bound 2]))) [void] 
         (jump 1 [bound 0; bound 2]))).

Definition f :=
  jump 1 [bound 0; bound 2].

Definition l :=
  jump 1 [bound 0; bound 2].

Definition m :=
  jump 0 [bound 1].

Definition g :=
  (bind
  (bind
    (jump 1 [bound 0])
    [void; void]
      m)
    [void]
      l).

Definition h :=
  jump 0 [bound 1].

Definition a :=
  (bind
  (bind
  (bind
    (jump 1 [bound 0])
    [void; void]
      h)
    [void]
      g)
    [void]
      f).

Definition b :=
  jump 0 [bound 1].

Definition v :=
  (bind
  (bind
    (jump 1 [bound 0])
    [void; void]
      b)
    [void]
      a).

Goal
  ex_cbv = v.
Proof.
  reflexivity.
Qed.

Fixpoint foobar (b: pseudoterm): context * pseudoterm :=
  match b with
  | bind b ts c =>
      (context_left (fst (foobar b)) ts c, snd (foobar b))
  | _ =>
    (context_hole, b)
  end.

Lemma foobar_sound:
  forall b,
  b = (fst (foobar b)) (snd (foobar b)).
Proof.
  induction b0.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl.
  rewrite IHb0_1 at 1.
  reflexivity.
Defined.

Goal
  weakly_converges ex_cbn 0.
Proof.
  compute.
  eexists.
  eapply star_trans.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  repeat constructor.
Qed.

Goal
  weakly_converges ex_cbv 0.
Proof.
  compute.
  eexists.
  eapply star_trans.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  repeat constructor.
Qed.

Notation Ca := (value_cont [] 1 a).

Notation Cb := (value_cont [Ca] 2 b).

Notation Cf := (value_cont [Cb] 1 f).

Notation Cg := (value_cont [Cf; Cb] 1 g).

Notation Ch := (value_cont [Cg; Cf; Cb] 2 h).

Notation Cl := (value_cont [Ch; Cf; Cb] 1 l).

Notation Cm := (value_cont [Cl; Ch; Cf; Cb] 2 m).

Goal
  big (ex_cbn, []) 0.
Proof.
  constructor; compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  constructor; compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  constructor; compute.
  eapply big_halt.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.

Goal
  big (v, []) 0.
Proof.
  unfold v.
  constructor; unfold length.
  constructor; unfold length.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  (* At this point, e = b. Ok. *)
  unfold a at 1.
  constructor; unfold length.
  constructor; unfold length.
  constructor; unfold length.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  (* At this point, e = b, k = h. Ok. *)
  unfold g at 1.
  constructor; unfold length.
  constructor; unfold length.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  (* At this point, e = b, k = h, p = m. Ok!
     So this becomes h<m, f>. That typechecks! *)
  unfold l at 1.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  (* Here the problem was! :) *)
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  eapply big_halt.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.

(*
  cbv halt =
    a b
    where
      b c d =
        d c
      a e =
        g h
        where
          h i j =
            j i
          g k =
            l m
            where
              m n o =
                o n
              l p =
                k p f
          f q =
            e q halt

  cbn halt =
    a b
    where
      b c d =
        c d
      a e =
        e f halt
        where
          f g =
            h i
            where
              i j k =
                j k
              h l =
                l m g
                where
                  m n =
                    n o
                    where
                      o p q =
                        p q

  CBV:
    \halt: ~~(b, ~b).

      a<b>
      { b<c: ~(b, ~b), d: ~~(b, ~b)> =
          d<c>
      { a<e: ~(~(b, ~b), ~~(b, ~b))> =
          g<h>
          { h<i: ~(b, ~b), j: ~~(b, ~b)> =
              j<i>
          }
          { g<k: ~(~(b, ~b), ~~(b, ~b))> =
              l<m>
              { m<n: b, o: ~b> =
                  o<n>
              }
              { l<p: ~(b, ~b)> =
                  k<p, f>
              }
          }
          { f<q: ~(b, ~b)> =
              e<q, halt>
          }
      }
*)

(*
  f@0<j@1>
  { f<k> =
    a<k@0> }
  { j<> =
    H<> }
  { b<k> =
    k@0<> }
  { c<k> =
    k@0<> }
  { a<k> =
    k<> }
*)

Goal
  big (
    (bind
    (bind
    (bind
    (bind
    (bind
      (jump 0 [bound 1])
      [void]
        (jump 4 [bound 0]))
      []
        (jump 8 []))
      [void]
        (jump 0 []))
      [void]
        (jump 0 []))
      [void]
        (jump 0 [])),
  []) 5.
Proof.
  constructor; compute.
  constructor; compute.
  constructor; compute.
  constructor; compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_halt.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.

*)
