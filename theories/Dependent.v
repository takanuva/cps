(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Local.Constructions.
Require Import Local.Syntax.

Module TT := Local.Constructions.

(* -------------------------------------------------------------------------- *)

(* Let's start with CBV; after that, lets split the file in two, of course. *)

Print TT.typing_judgement.

Inductive cbv_cps: TT.typing_judgement -> pseudoterm -> Prop :=.

Check fun (f: forall T: Type, T -> T) =>
      fun (x: f Set nat) => f nat 0.

(*

  Consider a source term:

    fun (f: forall T: Type, T -> T) =>
      fun (x: f Set nat) => f nat 0

  How should this be CPS-translated?

      f: (T: Type) -> T -> T,
      k: ~nat
    |-
      k<v>
      { v<x: [f Set nat], k> =
        [nat]k
        { k<b: ...> =
            f<nat, j>
        }
        { j<a: ...> =
            a<0, k>
        }
      }

  Note that f nat : nat -> nat. This means that f nat is not a type scheme: it's
  just a term! Do we want the type nat -> nat in our system?

*)
