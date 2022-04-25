Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Observational.
Require Import Local.TypeSystem.

Inductive value: Set :=
  | value_undefined
  | value_cont (p: list value) (a: nat) (c: pseudoterm).

Notation U := value_undefined.

Notation "< p ; \ a : c >" :=
  (value_cont p a c) (only printing, format "< p ;  \ a :  c >").

Local Notation stack := (list value).

Definition stack_append (ns: list nat) (r s: stack): stack :=
  map (fun n => nth n r U) ns ++ s.

(* These are derived directly from Kennedy's paper, slightly adapting it to use
   free variables as a signal of termination rather than using a "halt" term. *)

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
       to the stack p! So, if the result is a parameter, thus j <= a, we already
       know its value in r (which comes from ns). But, if j > a, we'll have to
       remove any newly bound abstractions, subtracting a, and then add any
       new abstractions that have been bound in r but not in s (notice that r is
       always newer and as such has strictly more bindings!). *)
    j' = nth j ns (j - a + (length r - length s)) ->
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

Require Import Lia.
Require Import Local.Reduction.

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

Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Reduction.

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
Hypothesis rebuild_stack_empty: forall r c, rebuild_stack r c = c.

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
