(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Local.Constructions.
Require Import Local.Syntax.
Require Import Local.Intuitionistic.

Import ListNotations.

Module TT := Local.Constructions.

(* Let's start with CBV; after that, lets split the file in two, of course. *)

(* Example 1. *)

Local Coercion TT.bound: nat >-> TT.term.
Local Coercion TT.sort: TT.universe >-> TT.term.
Local Coercion TT.lift_judgement: TT.typing_judgement >-> Funclass.

(* Eval cbv in let f: (forall T: Type, T -> T) :=
                 fun (T: Type) (x: T) =>
                   x
               in fun (x: f Set bool) =>
                 f bool x. *)

Example dependent_example1: TT.term :=
  TT.definition
    (TT.abstraction (TT.type 0)
      (TT.abstraction 0 0))
    (TT.pi (TT.type 0) (TT.pi 0 1))
    (TT.abstraction (TT.application (TT.application 0 TT.iset) TT.boolean)
      (TT.application (TT.application 1 TT.boolean) 0)).

Example dependent_example1_type: TT.term :=
  TT.pi TT.boolean TT.boolean.

Example dependent_example1_typed:
  TT.typing [] dependent_example1 dependent_example1_type TT.conv.
Proof.
  (* TODO: can't do this one yet, we don't have the subtyping relation yet. *)
Admitted.

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

  TODO: elaborate on the above! Prove it if possible.
*)

(* -------------------------------------------------------------------------- *)

Inductive dependent_cbv_cps: TT.typing_judgement -> pseudoterm -> Prop :=.
