(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Intuitionistic.
Require Local.Constructions.

Import ListNotations.

Module TT := Local.Constructions.

(* Let's start with CBV; after that, lets split the file in two, of course. *)

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

Local Notation V := void.

(* Quick sketch to help debugging; I will need a proper notation library later
   on. *)

Local Notation "b '{' ts '=' c '}'" :=
  (bind b ts c)
  (at level 200,
   b at level 200,
   format "'[v' b '//' '{'  ts  '=' '/  ' '[' c ']' '/' '}' ']'",
   only printing).

Local Notation "x xs" :=
  (jump x xs)
  (at level 199,
   format "'[v' x xs ']'",
   only printing).

(*
  The dependent CPS language makes a more strict distinction between commands,
  type schemes and arities than the calculus of constructions does. Also, as we
  wish to use negation for small types rather than (as Kennedy does) interpret
  arrow types, we use codes and an interpretation function (à la Tarski). Codes
  may be erased at runtime if so desired, but they could carry information to
  allow for type cases such as done in Idris.

  We start with the a simple CPS translation, unoptimized, based on Plotkin's
  CBV translation, extending it as required with thunks and coproducts.

  TODO: doc! Doc! Doc!
*)

(*
  Grammar:

    T ::= ...
    U ::= ...

    v ::= x

    t ::= ...

    W ::= ...

    b ::= x<v...> | b { x<x: W, ...> = b }

    G ::= . | G, x: T

    D ::= . | D, k: U

  Judgements:

    G |- b : D

  CBV translation, acting on judgements:

    (1) [G |- x : A term] =
      k<x>

    (2) [G |- \x: A.e : A -> B term] =
      k<f>
      { f<x: El([G |- A : s1 type]), k: ~El([G, x: A |- B : s2 type])> =
        [G, x: A |- e : B term]
      }

    (3) [G |- e f : B term] =
      [G |- e : A -> B term]
      { k<f: El([G |- A -> B : s1 type])> =
        [G |- f : A term]
        { k<v: El([G |- A : s2 type])> =
          f<v, k>
        }
      }

*)

Inductive env: Set :=
  | env_nil: env.

Variant typing_judgement: Set :=
  (* A judgement G |- b : D. *)
  | typing (g: env) (b: pseudoterm).

Definition CBV_TVAR (n: nat): pseudoterm :=
  (jump 0 [bound (S n)]).

Inductive cbv_dcps: TT.env -> TT.term -> TT.term -> pseudoterm -> Prop :=
  (* Rule (1) above. *)
  | cbv_dcps_term_var:
    (* TODO: restrict to terms, please! *)
    forall g d n t u,
    TT.infer TT.std (TT.valid_env g) ->
    item (d, t) g n ->
    u = lift (1 + n) 0 t ->
    cbv_dcps g (TT.bound n) u (CBV_TVAR n).

Lemma cbv_dcps_valid_domain:
  forall g e t b,
  cbv_dcps g e t b ->
  TT.infer TT.std (TT.typing g e t).
Proof.
  induction 1.
  - destruct d as [ e | ].
    + now apply TT.typing_ref with e t.
    + now apply TT.typing_var with t.
Qed.
