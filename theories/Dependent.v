(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Local.Constructions.
Require Import Local.Syntax.
Require Import Local.Context.
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

Example dependent_example1a: TT.term :=
  TT.abstraction (TT.type 0) (TT.abstraction 0 0).

Example dependent_example1b: TT.term :=
  TT.pi (TT.type 0) (TT.pi 0 1).

Example dependent_example1c: TT.term :=
  TT.application (TT.application 0 TT.iset) TT.boolean.

Example dependent_example1d: TT.term :=
  TT.application (TT.application 1 TT.boolean) 0.

Example dependent_example1: TT.term :=
  TT.definition
    dependent_example1a
    dependent_example1b
    (TT.abstraction dependent_example1c dependent_example1d).

Example dependent_example1_type: TT.term :=
  TT.pi TT.boolean TT.boolean.

Example dependent_example1_typed:
  TT.typing [] dependent_example1 dependent_example1_type TT.conv.
Proof.
  (* This will need cumulativity and conversion. Oh boy! *)
  admit.
Admitted.

(*

  Some musings (TODO: rewrite or move later)...

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

(*
  The dependent CPS language makes a more strict distinction between commands,
  type schemes and arities than the calculus of constructions does. Also, as we
  wish to use negation for small types rather than (as Kennedy does) interpret
  arrow types, we use codes and an interpretation function (à la Tarski). Codes
  may be erased at runtime if so desired, but they could carry information to
  allow for type cases such as done in Idris.

  We start with the a simple CPS translation, unoptimized, based on Plotkin's
  CBV translation, extending it as required with thunks and coproducts.
*)

Local Notation R := TT.conv.

Definition RET (k: nat) (n: nat): pseudoterm :=
  jump (bound k) [bound n].

Definition LET (h: context) (b: pseudoterm): pseudoterm :=
  h b.

Definition FUN (ts: list pseudoterm) (c: pseudoterm): context :=
  context_left context_hole ts c.

Inductive cbv_dcps: TT.env -> TT.term -> pseudoterm -> Prop :=
  (*
    [G |- x] = k<x>

    Given that G |- x : T, and x is not a type scheme under G. Note that it
    could only possibly be one if it is defined as one in G.
  *)
  | cbv_dcps_return:
    forall g n t,
    TT.typing g (TT.bound n) t R ->
    ~TT.type_scheme R g (TT.bound n) ->
    cbv_dcps g (TT.bound n) (RET 0 (1 + n))
  (*
    [G |- \x: T.e] = k<v> { v<x: [G |- T], k: ~[G |- U]> = [e] }

    Given that G, x: T |- e : U, and e is not a type scheme under (G, x: T).
  *)
  | cbv_dcps_letfun:
    forall g t e u c,
    TT.typing (TT.decl_var t :: g) e u R ->
    ~TT.type_scheme R (TT.decl_var t :: g) e ->
    (* TODO: derive c and types... *)
    cbv_dcps g (TT.abstraction t e) (LET (FUN [void; void] c) (RET 1 0)).

Lemma TT_typing_cbv_dcps:
  forall g e b,
  cbv_dcps g e b ->
  exists t,
  TT.typing g e t R.
Proof.
  induction 1.
  - now exists t.
  - exists (TT.pi t u).
    now apply TT.typing_abs.
Qed.

(* TODO: prove that cbv_dcps is total for typed terms! *)
