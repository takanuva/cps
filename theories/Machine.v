(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
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

Local Notation stack := (list value).

(* Please note that parameters are written from right to left, but arguments to
   jumps are written from left to write: we do need to reverse [ns] here! *)

Definition stack_append (ns: list nat) (r s: stack): stack :=
  map (fun n => nth n r U) (rev ns) ++ s.

(* Big-step abstract machine semantics for the CPS-calculus. This was derived
   directly from Kennedy's paper, slightly adapting it to use free variables as
   a signal of termination rather than using a "halt" term. This is meant to be
   an "implementation-friendly" semantics for the calculus. *)

Inductive machine: pseudoterm -> stack -> nat -> Prop :=
  (*
      r(k) is undefined
    --------------------- (M-HALT)
       (k<xs>, r) |-> k
  *)
  | machine_halt:
    forall k xs r,
    nth k r U = U ->
    machine (jump k xs) r k

  (*
      p(k) = <s, \xs.c>      <c, s, xs = r(ys)> |-> j
    --------------------------------------------------- (M-JUMP)
                  <k<ys>, r> |-> j[ys/xs]
  *)
  | machine_jump:
    forall r s a c k xs ns j j',
    Forall2 (fun x n => x = bound n) xs ns ->
    a = length ns ->
    item (value_cont s a c) r k ->
    machine c (stack_append ns r s) j ->
    (* Naughty little index math here! We build the runtime stack for c using s,
       and it may return two continuations: one that we have bound now, from the
       parameters, or one that is already bound in s. We have to map the results
       to the stack r! So, if the result is a parameter, thus j <= a, we already
       know its value in r (which comes from ns). But, if j > a, we'll have to
       remove any newly bound abstractions, subtracting a, and then add any
       new abstractions that have been bound in r but not in s (notice that r is
       always newer and as such has strictly more bindings!). Also remember that
       parameters are in the reverse order, but arguments are not, so we need to
       reverse [ns] here as well. *)
    j' = nth j (rev ns) (j - a + (length r - length s)) ->
    (* There we go. *)
    machine (jump k xs) r j'

  (*
      <b, r, k = <r, \xs.c>> |-> j
    -------------------------------- (M-BIND)
       <b { k<xs> = c }, r> |-> j
  *)
  | machine_bind:
    forall b ts c r j,
    machine b (value_cont r (length ts) c :: r) (S j) ->
    machine (bind b ts c) r j.

(* TODO: remove the following! We need to prove equivalence of the above and the
   head reduction! *)

Goal
  machine ex1 [] 3.
Proof.
  compute.
  constructor; simpl.
  constructor; simpl.
  eapply machine_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  compute.
  eapply machine_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  compute.
  eapply machine_jump; simpl.
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

(* Given a stack, we can bind each value in a tail. *)
Axiom rebuild_stack: stack -> pseudoterm -> pseudoterm.

(* We always know how to lift parameters: their stack's length is strictly
   smaller than their current depth in the term! *)
Axiom rebuild_stack_empty: forall r c, rebuild_stack r c = c.

Lemma machine_implies_weakly_converges:
  forall r c k,
  machine c r k -> weakly_converges (rebuild_stack r c) k.
Proof.
  admit.
Admitted.

Theorem weakly_converges_and_machine_are_equivalent:
  forall c k,
  machine c [] k <-> weakly_converges c k.
Proof.
  split; intros.
  - apply machine_implies_weakly_converges in H.
    rewrite rebuild_stack_empty in H.
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
  machine ex_cbn [] 0.
Proof.
  constructor; compute.
  constructor; compute.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  constructor; compute.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  constructor; compute.
  constructor; compute.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  constructor; compute.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  compute.
  constructor; compute.
  eapply machine_halt.
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
  machine v [] 0.
Proof.
  unfold v.
  constructor; unfold length.
  constructor; unfold length.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold stack_append, rev, map, nth, app.
  (* At this point, e = b. Ok. *)
  unfold a at 1.
  constructor; unfold length.
  constructor; unfold length.
  constructor; unfold length.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold stack_append, rev, map, nth, app.
  (* At this point, e = b, k = h. Ok. *)
  unfold g at 1.
  constructor; unfold length.
  constructor; unfold length.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold stack_append, rev, map, nth, app.
  (* At this point, e = b, k = h, p = m. Ok!
     So this becomes h<m, f>. That typechecks! *)
  unfold l at 1.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold stack_append, rev, map, nth, app.
  (* Here the problem was! :) *)
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold stack_append, rev, map, nth, app.
  eapply machine_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  unfold stack_append, rev, map, nth, app.
  eapply machine_halt.
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
