(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Local.Constructions.
Require Import Local.Syntax.
Require Import Local.Intuitionistic.

Module TT := Local.Constructions.

(* Let's start with CBV; after that, lets split the file in two, of course. *)

(* Example 1. *)

Eval cbv in let f: (forall T: Type, T -> T) :=
              fun (T: Type) (x: T) =>
                x
            in fun (x: f Set bool) =>
              f bool x.

(*

  Consider a source term:

    |-
      (let f: (forall T: Type, T -> T) :=
        fun (T: Type) (x: T) =>
          x
      in fun (x: f Set bool) =>
        f bool x) : bool -> bool


  How should this be CPS-translated? We notice we're using f both in type-level
  and in term-level! It's CBV translation (as CBV is the standard one) would be
  as follows:

      k: ~~(bool, ~bool)
    |-k
      k<f>
      { f<T: Type, k: ~~(x: T, ~T)> =
        k<v>
        { v<x: T, k: ~T> =
          k<x>
        }
      }
      { k<f: ~(T: Type, k: ~~(x: T, k: ~T))> =
        k<v>
        { v<x: El(f Set bool), k: ~El(f Set bool)> =
          [f nat x]
        }
      }

*)

(* -------------------------------------------------------------------------- *)

Inductive cbv_cps: TT.typing_judgement -> pseudoterm -> Prop :=.
