(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

(** To help proof automation, create a hint database. *)

Create HintDb cps.

(** A lot of proofs on pseudoterm lists may be solved by simple induction on the
    [Forall P] proposition over them, so we'll add a tactic for that. *)

Tactic Notation "list" "induction" "over" hyp(H) :=
  induction H; simpl;
  [ reflexivity
  | f_equal; auto ].
