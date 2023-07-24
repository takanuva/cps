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

  Axiom typing_C:
    forall g T,
    (* C: ~~T -> T *)
    typing g C (arrow (arrow (arrow T F) F) T).

  Axiom typing_A:
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

  (*
    Plotkin's CBV CPS translation:

      [x]    = k<x>
      [\x.e] = k<f> { f<x, k> = [e] }
      [e f]  = [e] { k<f> = [f] { k<v> = f<v, k> } }

      [X]      = X
      [A -> B] = ~([A], ~[B])
      [F]      = ~()

      [x: A |- e: B] = x: [A], k: ~[B] |- [e]
  *)

  Axiom cbv_type_F:
    cbv_type F = negation [].

  Definition cbv_A {T}: pseudoterm :=
    (* [|- A: F -> T] = [k: ~~(~(), ~[T]) |- [A]].

       k<f>
       { f<x: ~(), k: ~[T]> =
         x<> }
    *)
    bind (jump 1 [Syntax.bound 0]) [negation [T]; negation []] (jump 1 []).

  Axiom cbv_cps_A:
    forall T,
    cbv_cps A (@cbv_A T).

  Goal
    forall T: type,
    (forall g, TypeSystem.typing g (cbv_type T) prop) ->
    exists2 U,
      typing [] A U
    & TypeSystem.typing [negation [cbv_type U]] (@cbv_A (cbv_type T)) void.
  Proof.
    intros.
    exists (arrow F T).
    - apply typing_A.
    - repeat (simpl; try econstructor; auto; try rewrite cbv_type_F).
  Qed.

End CBV.

Section CBN.

  Require Import Local.Lambda.CallByName.

  (*
    Plotkin's CBN CPS translation:

      [x]    = x<k>
      [\x.e] = k<f> { f<x, k> = [e] }
      [e f]  = [e] { k<f> = f<v, k> { v<k> = [f] } }

      [X]      = ~X
      [A -> B] = ~~(~[A], [B])
      [F]      = ~~()

      [x: A |- e: B] = x: ~[A], k: [B] |- [e]
  *)

  Axiom cbn_type_F:
    cbn_type F = negation [negation []].

  Definition cbn_A {T}: pseudoterm :=
    (* [|- A: F -> T] = [k: ~~(~~~(), [T]) |- [A]].

       k<f>
       { f<x: ~~~(), k: [T]> =
         x<k>
         { k<k: ~()> =
           k<> } }
    *)
    bind
      (jump 1 [Syntax.bound 0])
      [T; negation [negation [negation []]]]
      (bind
        (jump 2 [Syntax.bound 0])
        [negation []]
        (jump 0 [])).

  Axiom cbn_cps_A:
    forall T,
    cbn_cps A (@cbn_A T).

  Goal
    forall T: type,
    (forall g, TypeSystem.typing g (cbn_type T) prop) ->
    exists2 U,
      typing [] A U
    & TypeSystem.typing [cbn_type U] (@cbn_A (cbn_type T)) void.
  Proof.
    intros.
    exists (arrow F T).
    - apply typing_A.
    - repeat (simpl; try econstructor; auto; try rewrite cbn_type_F).
  Qed.

End CBN.
