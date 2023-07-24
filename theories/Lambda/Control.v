(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

(* TODO: this is a temporary file, meant just to check the properties of control
   operators in the CPS translation. Please, move this code to the proper place
   once I'm finished! *)

Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.TypeSystem.

Local Notation N := negation.

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
    cbv_type F = N [].

  Definition cbv_C {T}: pseudoterm :=
    (* [|- C: ~~T -> T] = [k: ~~(~(~([T], ~~()), ~~()), ~[T]) |- [C]]

       k<f>
       { f<x: ~(~([T], ~~()), ~~()), k: ~[T]> =
         x<p, q>
         { p<y: [T], j: ~~()> =
           j<r>
           { r<> =
             k<y> } }
         { q<j: ~()> =
           j<> } }
    *)
    bind
      (jump 1 [Syntax.bound 0])
      [N [T]; N [N [N []]; N [N [N []]; T]]]
      (bind
        (bind
          (jump 3 [Syntax.bound 0; Syntax.bound 1])
          [N [N []]; T]
          (bind
            (jump 1 [Syntax.bound 0])
            []
            (jump 3 [Syntax.bound 1])))
        [N []]
        (jump 0 [])).

  Axiom cbv_cps_C:
    forall T,
    cbv_cps C (@cbv_C T).

  Goal
    forall T: type,
    (forall g, TypeSystem.typing g (cbv_type T) prop) ->
    exists2 U,
      typing [] C U
    & TypeSystem.typing [N [cbv_type U]] (@cbv_C (cbv_type T)) void.
  Proof.
    intros.
    exists (arrow (arrow (arrow T F) F) T).
    - apply typing_C.
    - repeat (simpl; try econstructor; auto; try rewrite cbv_type_F).
  Qed.

  Definition cbv_A {T}: pseudoterm :=
    (* [|- A: F -> T] = [k: ~~(~(), ~[T]) |- [A]]

       k<f>
       { f<x: ~(), k: ~[T]> =
         x<> }
    *)
    bind
      (jump 1 [Syntax.bound 0])
      [N [T]; N []]
      (jump 1 []).

  Axiom cbv_cps_A:
    forall T,
    cbv_cps A (@cbv_A T).

  Goal
    forall T: type,
    (forall g, TypeSystem.typing g (cbv_type T) prop) ->
    exists2 U,
      typing [] A U
    & TypeSystem.typing [N [cbv_type U]] (@cbv_A (cbv_type T)) void.
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
    cbn_type F = N [N []].

  Definition cbn_A {T}: pseudoterm :=
    (* [|- A: F -> T] = [k: ~~(~~~(), [T]) |- [A]]

       k<f>
       { f<x: ~~~(), k: [T]> =
         x<k>
         { k<k: ~()> =
           k<> } }
    *)
    bind
      (jump 1 [Syntax.bound 0])
      [T; N [N [N []]]]
      (bind
        (jump 2 [Syntax.bound 0])
        [N []]
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
