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

Local Coercion TT.lift_judgement: TT.typing_judgement >-> Funclass.

Definition RET (k: nat) (n: nat): pseudoterm :=
  jump (bound k) [bound n].

Definition LET (h: context) (b: pseudoterm): pseudoterm :=
  h b.

Definition FUN (ts: list pseudoterm) (c: pseudoterm): context :=
  context_left context_hole ts c.

(* TODO: check requirements for constructors, please. *)

Axiom PLACEHOLDER: TT.decl.

Inductive cbv_dcps: TT.env -> TT.term -> pseudoterm -> Prop :=
  (*
    [G |- x] = k<x>

             = RETURN x
  *)
  | cbv_dcps_return:
    forall g n t,
    TT.typing g (TT.bound n) t R ->
    ~TT.type_scheme R g (TT.bound n) ->
    cbv_dcps g (TT.bound n) (RET 0 (1 + n))
  (*
    [G |- \x: T.e] = k<v> { v<x: [T], k: ~[U]> = [e] }

                   = LET
                       v = FUN[x: [T], k: ~[U]] => [e]
                     IN RETURN v
  *)
  | cbv_dcps_letfun:
    forall g t e u b,
    TT.typing (TT.decl_var t :: g) e u R ->
    ~TT.type_scheme R (TT.decl_var t :: g) e ->
    (* Hmmm... *)
    cbv_dcps (TT.decl_var (lift 1 0 t) :: PLACEHOLDER :: g) (lift 1 1 e) b ->
    (* TODO: derive c and types... *)
    cbv_dcps g (TT.abstraction t e) (LET (FUN [void; void] b) (RET 1 0)).

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

Local Goal
  exists2 b,
  cbv_dcps [] TT.dependent_example1 b & b = V.
Proof.
  eexists.
  unfold TT.dependent_example1.
  eapply cbv_dcps_letfun.
  eapply TT.typing_abs.
  eapply TT.typing_abs.
  eapply TT.typing_abs.
  eapply TT.typing_app.
  eapply TT.typing_bound.
  repeat econstructor; vm_compute; reflexivity.
  repeat constructor.
  now simpl.
  now vm_compute.
  eapply TT.typing_bound.
  repeat econstructor; vm_compute; reflexivity.
  constructor.
  now simpl.
  now vm_compute.
  now vm_compute.
  admit.
  vm_compute.
  eapply cbv_dcps_letfun.
  eapply TT.typing_abs.
  eapply TT.typing_abs.
  eapply TT.typing_app.
  eapply TT.typing_bound.
  admit.
  repeat constructor.
  now simpl.
  now vm_compute.
  eapply TT.typing_bound.
  admit.
  constructor.
  now simpl.
  now vm_compute.
  now vm_compute.
  admit.
  vm_compute.
  eapply cbv_dcps_letfun.
  eapply TT.typing_abs.
  eapply TT.typing_app.
  eapply TT.typing_bound.
  admit.
  repeat constructor.
  now simpl.
  now vm_compute.
  eapply TT.typing_bound.
  admit.
  constructor.
  now simpl.
  now vm_compute.
  now vm_compute.
  admit.
  vm_compute.
  eapply cbv_dcps_letfun.
  eapply TT.typing_app.
  eapply TT.typing_bound.
  admit.
  repeat constructor.
  now simpl.
  now vm_compute.
  eapply TT.typing_bound.
  admit.
  constructor.
  now simpl.
  now vm_compute.
  now vm_compute.
  admit.
  vm_compute.
  admit.
  simpl.
Admitted.
