(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Substitution.
Require Import Local.AbstractRewriting.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
(* Require Import Local.Constructions.Confluence. *)

Import ListNotations.

Section Cumulativity.

  Variable R: typing_equivalence.

  (* As Luo defines it, the smallest partial order over terms with regard to
     conversion (here R) such that:
     - iset <= type 0 <= type 1 <= ...;
     - if U1 <= U2, Pi x: T.U1 <= Pi x: T.U2;   (pi types are covariant!)
     - if T1 <= T2 and U1 <= U2, Sigma x: T1.U1 <= Sigma x: T2.U2.

     TODO: please check that A <= A' and B <= B' implies A + B <= A' + B'...
     this means that we have to relax rules on branches of matches, we can check
     how the MetaCoq project does that! I do believe, though, that it should be
     admissible.

     TODO: I really wanna tweak this definition so that I do not allow reduction
     in it, separating the concerns... but still, this is the one given by Luo,
     Bowman, and Assaf (the latter on the "A calculus of Constructions with
     Explicit Subtyping" paper). *)

  Inductive cumul: env -> relation term :=
    | cumul_refl:
      forall g e1 e2,
      R g e1 e2 ->
      cumul g e1 e2
    | cumul_trans:
      forall g e1 e2 e3,
      cumul g e1 e2 ->
      cumul g e2 e3 ->
      cumul g e1 e3
    | cumul_iset:
      forall g n,
      cumul g iset (type n)
    | cumul_type:
      forall g n m,
      n < m ->
      cumul g (type n) (type m)
    | cumul_pi:
      forall g t u1 u2,
      cumul (decl_var t :: g) u1 u2 ->
      cumul g (pi t u1) (pi t u2).

  Hypothesis R_is_equiv: forall g, equivalence (R g).

  Lemma cumul_pi_inv:
    forall g t u1 u2,
    cumul g (pi t u1) (pi t u2) ->
    cumul (decl_var t :: g) u1 u2.
  Proof.
    intros.
    admit.
  Admitted.

  Lemma cumul_antisym:
    forall g e1 e2,
    cumul g e1 e2 ->
    cumul g e2 e1 ->
    R g e1 e2.
  Proof.
    induction 1; intros.
    - assumption.
    - apply equiv_trans with e2.
      + apply R_is_equiv.
      + apply IHcumul1.
        now apply cumul_trans with e3.
      + apply IHcumul2.
        now apply cumul_trans with e1.
    - (* Of course H can't happen. *)
      exfalso.
      admit.
    - (* Ditto! *)
      exfalso.
      admit.
    - apply cumul_pi_inv in H0.
      specialize (IHcumul H0).
      (* Now by congruence, great. *)
      admit.
  Admitted.

End Cumulativity.
