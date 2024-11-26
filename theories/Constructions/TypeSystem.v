(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.

Import ListNotations.

Inductive typing: env -> relation term :=
  (*
           |- G
    --------------------
      G |- Prop : Type
  *)
  | typing_prop:
    forall g,
    valid_env g ->
    typing g (sort prop) (sort type)
  (*
      (x: T) or (x = e: T) in G
    -----------------------------
             G |- x : T
  *)
  | typing_bound:
    forall g n d t u,
    valid_env g ->
    item (d, t) g n ->
    u = lift (1 + n) 0 t ->
    typing g (bound n) u
  (*
       G, X: T |- U : s
    ----------------------
      G |- Pi X: T.U : s
  *)
  | typing_pi:
    forall g t u s,
    typing (decl_var t :: g) u (sort s) ->
    typing g (pi t u) (sort s)
  (*
          G, x: T |- e: U
    ----------------------------
      G |- \x: T.e : Pi x: T.U
  *)
  | typing_abs:
    forall g t e u,
    typing (decl_var t :: g) e u ->
    typing g (abstraction t e) (pi t u)
  (*
      G |- f : Pi x: T.U     G |- e : T
    -------------------------------------
              G |- f e : U[e/x]
  *)
  | typing_app:
    forall g f e t u,
    typing g f (pi t u) ->
    typing g e t ->
    typing g (application f e) (subst e 0 u)
  (*
      G |- e : T     G, x = e: T |- f : U
    ---------------------------------------
        G |- let x = e: T in f : U[e/x]
  *)
  | typing_def:
    forall g e f t u,
    typing g e t ->
    typing (decl_def e t :: g) f u ->
    typing g (definition e t f) (subst e 0 u)
  (*
      G |- e : T     G |- U : s     G |- T = U
    --------------------------------------------
                     G |- e : U
  *)
  | typing_conv:
    forall g e t u s,
    typing g e t ->
    typing g u (sort s) ->
    conv g t u ->
    typing g e u

with valid_env: env -> Prop :=
  (*
    --------
      |- .
  *)
  | valid_env_nil:
    valid_env []
  (*
      |- G     G |- T: s
    -----------------------
          |- G, x: T
  *)
  | valid_env_var:
    forall g t s,
    valid_env g ->
    typing g t (sort s) ->
    valid_env (decl_var t :: g)
  (*
      |- G     G |- e : T     G |- T : s
    --------------------------------------
              |- G, x = e: T
  *)
  | valid_env_def:
    forall g e t s,
    valid_env g ->
    typing g e t ->
    typing g t (sort s) ->
    valid_env (decl_def e t :: g).

(* Coq term: [\X: Prop.\x: X.x]. *)
Example polymorphic_id_term: term :=
  abstraction (sort prop) (abstraction (bound 0) (bound 0)).

(* Coq term: [Pi X: Prop.X -> X]. *)
Example polymorphic_id_type: term :=
  pi (sort prop) (pi (bound 0) (bound 1)).

(* Let's check typeability. *)
Goal
  typing [] polymorphic_id_term polymorphic_id_type.
Proof.
  simpl.
  repeat econstructor.
  (* Of course! *)
  now vm_compute.
Qed.

Lemma valid_env_typing:
  forall g e t,
  typing g e t ->
  valid_env g.
Proof.
  induction 1.
  - assumption.
  - assumption.
  - dependent destruction IHtyping.
    assumption.
  - dependent destruction IHtyping.
    assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.
