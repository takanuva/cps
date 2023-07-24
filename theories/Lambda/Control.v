(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

(* TODO: this is a temporary file, meant just to check the properties of control
   operators in the CPS translation. Please, move this code to the proper place
   once I'm finished! *)

Require Import Prelude.
Require Import Local.Syntax.
Require Import Local.TypeSystem.

Section Control.

  Require Import Local.Lambda.Calculus.

  Axiom C: term.
  Axiom A: term.
  Axiom F: type.

  Hypothesis typing_C:
    forall g T,
    (* C: ~~T -> T *)
    typing g C (arrow (arrow (arrow T F) F) T).

  Hypothesis typing_A:
    forall g T,
    (* A: F -> T *)
    typing g A (arrow F T).

  Definition K T U: term :=
    (* K = \f: (T -> U) -> T.C (\k: T -> F.k (f (\x: T.A (k x)))) *)
    abstraction (arrow (arrow T U) T)
      (application C
        (abstraction (arrow T F)
          (application 0
            (application 1
              (abstraction T
                (application A
                  (application 1 0))))))).

  Lemma typing_K:
    forall g T U,
    (* K: ((T -> U) -> T) -> T *)
    typing g (K T U) (arrow (arrow (arrow T U) T) T).
  Proof.
    intros.
    repeat econstructor.
    - apply typing_C.
    - apply typing_A.
  Qed.

End Control.

Section CBV.

  Require Import Local.Lambda.CallByValue.

End CBV.

Section CBN.

  Require Import Local.Lambda.CallByName.

End CBN.
