(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
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
  | value_cont (p: list value) (a: nat) (c: pseudoterm).

Local Notation U := value_undefined.

Local Notation "< r ; \ a : c >" :=
  (value_cont r a c) (only printing, format "< r ;  \ a :  c >").

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
    forall r s a c k xs ns j j',
    Forall2 (fun x n => x = bound n) xs ns ->
    a = length ns ->
    item (value_cont s a c) r k ->
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
    big (b, value_cont r (length ts) c :: r) (S j) ->
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
  compute.
  eapply big_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  compute.
  eapply big_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
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

(* Given a heap, we can bind each value in a tail. *)
Axiom rebuild_heap: heap -> context.

Axiom rebuild_heap_empty: forall r c, rebuild_heap r c = c.

Lemma big_implies_weakly_converges:
  forall r c k,
  big (c, r) k -> weakly_converges (rebuild_heap r c) k.
Proof.
  admit.
Admitted.

Theorem weakly_converges_and_big_are_equivalent:
  forall c k,
  big (c, []) k <-> weakly_converges c k.
Proof.
  split; intros.
  - apply big_implies_weakly_converges in H.
    rewrite rebuild_heap_empty in H.
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
  compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  constructor; compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
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
  unfold heap_append, fold_left, nth, app.
  (* At this point, e = b, k = h. Ok. *)
  unfold g at 1.
  constructor; unfold length.
  constructor; unfold length.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold heap_append, fold_left, nth, app.
  (* At this point, e = b, k = h, p = m. Ok!
     So this becomes h<m, f>. That typechecks! *)
  unfold l at 1.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold heap_append, fold_left, nth, app.
  (* Here the problem was! :) *)
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold heap_append, fold_left, nth, app.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
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
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
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
