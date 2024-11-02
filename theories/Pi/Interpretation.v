(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.TypeSystem.
Require Import Local.Pi.Calculus.
Require Import Local.Pi.Control.

Section Interpretation.

  Variable pi_base: type.

  Definition is_variable (k: pseudoterm) (n: nat): Prop :=
    k = bound n.

  Definition local_env p ts q :=
    restriction (channel O ts)
      (parallel p (replication 0 ts q)).

  Inductive interpret_type: pseudoterm -> type -> Prop :=
    | interpret_type_base:
      interpret_type base pi_base
    | interpret_type_negation:
      forall ts cs,
      Forall2 interpret_type ts cs ->
      interpret_type (negation ts) (channel O cs).

  Inductive interpret: pseudoterm -> term -> Prop :=
    | interpret_jump:
      forall x xs n ns,
      is_variable x n ->
      Forall2 is_variable xs ns ->
      interpret (jump x xs) (output n ns)
    | interpret_bind:
      forall b ts c p cs q q',
      interpret b p ->
      interpret c q ->
      Forall2 interpret_type ts cs ->
      q' = (lift 1 (length cs) q) ->
      interpret (bind b ts c) (local_env p cs q').

  Local Notation pB := (pi_base).
  Local Notation cO cs := (channel O cs).
  Local Notation cI cs := (channel I cs).

  Goal
    (* TODO: give an example number here. *)
    let p :=
      (* \j.\x.\y.\z.
           (\h)((\k)(1<y@3, k@0, x@4>
                   | !k@0(a, b).3<b@0, j@7, a@1>)
              | !h@0(c, d, e).1<e@0, z@4>) *)
      (restriction
        (cO [pB; cO [pB; pB]; pB])
        (parallel
          (restriction (cO [pB; pB])
            (parallel
              (output 1 [4; 0; 3])
              (replication 0 [pB; pB]
                (output 3 [1; 7; 0]))))
          (replication 0 [pB; cO [pB; pB]; pB]
            (output 1 [4; 0])))) in
    interpret Syntax.ex1 p.
  Proof.
    compute.
    repeat econstructor.
  Qed.

End Interpretation.
