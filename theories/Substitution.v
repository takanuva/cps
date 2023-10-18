(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Set Implicit Arguments.
Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Relations.
Require Import Morphisms.
(* TODO: remove me. *)
Require Import String.

(* We'll make a database just for rewriting substitution stuff, so that we can
   easily add rewriting rules to it and rewrite just that if we wish. *)
Create HintDb sigma.

(* We define in here renaming, well-scoped substitution, and an algebra for
   substitution (or de Bruijn algebra), inspired by the work of Schafer et al.
   on the autosubst library, particularly by the Completeness and Decidability
   of de Bruijn Substitution Algebra in Coq paper. This was inspired by the
   definition of the lambda sigma calculus, from Abadi et al., introduced in
   their Explicit Substitutions paper. By using an algebra like this a few
   proofs should become easier, like the completeness for machine semantics. See
   also Stark et al.'s Autosubst 2: Reasoning with Multi-sorted de Bruijn Terms
   and Vector Substitutions paper. *)

Section DeBruijn.

  Variable X: Set.

  Class deBruijn: Type := {
    var:
      nat -> X;
    traverse:
      (nat -> nat -> X) -> nat -> X -> X
  }.

  Context `{deBruijn}.

  #[nonuniform]
  Local Coercion var: nat >-> X.

  Inductive substitution: Set :=
    | subst_id
    | subst_lift (i: nat)
    | subst_cons (x: X) (s: substitution)
    | subst_comp (s: substitution) (t: substitution).

  Local Notation I := subst_id.
  Local Notation L i := (subst_lift i).
  Local Notation S := (L 1).
  Local Notation "( x1 , .. , xn , s )" :=
    (subst_cons x1 .. (subst_cons xn s) ..) (at level 0, right associativity).
  Local Notation "s 'o' r" :=
    (subst_comp s r) (at level 11, left associativity).

  Local Notation up s :=
    (0, s o L 1).

  (* Definition lift (i: nat) (k: nat) (n: nat): nat :=
    if le_gt_dec k n then
      i + n
    else
      n. *)

  Axiom TODO: forall {T}, string -> T.

  Fixpoint subst_apply (s: substitution) (k: nat) (n: nat): X :=
    if le_gt_dec k n then
      match s with
      | I =>
        n
      | L i =>
        i + n
      | (y, s) =>
        TODO "cons"
      | s o r =>
        TODO "comp"
      end
    else
      n.

  Notation instantiate_rec s :=
    (traverse (subst_apply s)).

  Definition instantiate (s: substitution): X -> X :=
    instantiate_rec s 0.

  Coercion instantiate: substitution >-> Funclass.

  Lemma traverse_subst_instantiate:
    forall s x,
    instantiate_rec s 0 x = s x.
  Proof.
    intros.
    reflexivity.
  Qed.

  Definition subst_equiv: relation substitution :=
    fun s r =>
      forall x, s x = r x.

  (*
    Instantiation laws:

      - 0[y, s] = y
      - (1 + n)[y, s] = n[s]
      - n[S^i] = i + n

    Monad laws:

      - e[I] = e
      - e[s][r] = e[s >> r]

    Algebraic laws:

      - 0 .: S = I (could be derived from the eta-like law and the monad laws)
      - S >> (e .: s) = s
      - I >> s = s
      - s >> I = s
      - (s >> r) >> u = s >> (r >> u) (we need to reverse this one!)
      - (e .: s) >> r = e[r] .: (s >> r)
      - (0[s], S >> s) = s (is this an eta law...?)

    We also need extra care since we want to simplify stuff by using the up
    combinator... so in normal form, we'll associate composition to the left
    instead of to the right. Also, as we are taking the lift primitive indexed
    by a number to optimize stuff a bit, we probably need laws such as, e.g.,
    (s >> L n) >> L m = s >> L (n + m). As s can be I, L n >> L m = L (n + m)
    too, we probably need an extra reduction law for that. Ideally we would want
    to prove confluence and completeness for this eventually, but this is not
    important right now.
  *)

  Lemma instantiate_cons_zero:
    forall y s,
    (y, s) 0 = y.
  Proof.
    intros.
    unfold instantiate.
    admit.
  Admitted.

  Lemma instantiate_cons_succ:
    forall y s n,
    (y, s) (1 + n) = s n.
  Proof.
    admit.
  Admitted.

  Lemma instantiate_lift:
    forall (n: nat) i,
    L i n = i + n.
  Proof.
    admit.
  Admitted.

  Lemma instantiate_id:
    forall x,
    I x = x.
  Proof.
    admit.
  Admitted.

  Lemma instantiate_comp:
    forall x s r,
    (s o r) x = r (s x).
  Proof.
    admit.
  Admitted.

  (* TODO: do we want to import SetoidClass? *)

  Local Notation "s == r" := (subst_equiv s r) (at level 70, no associativity).

  Lemma subst_cons_lift_simpl:
    (0, S) == I.
  Proof.
    admit.
  Admitted.

  Lemma subst_lift_cons_simpl:
    forall y s,
    S o (y, s) == s.
  Proof.
    admit.
  Admitted.

  Lemma subst_comp_left_identity:
    forall s,
    I o s == s.
  Proof.
    admit.
  Admitted.

  Lemma subst_comp_right_identity:
    forall s,
    s o I == s.
  Proof.
    admit.
  Admitted.

  Lemma subst_comp_assoc:
    forall s r t,
    s o (r o t) == s o r o t.
  Proof.
    admit.
  Admitted.

  Lemma subst_comp_cons_distr:
    forall y s r,
    (y, s) o r == (r y, s o r).
  Proof.
    admit.
  Admitted.

  Lemma subst_cons_eta:
    forall s: substitution,
    (s 0, S o s) == s.
  Proof.
    admit.
  Admitted.

  (* ---------------------------------------------------------------------- *)

  Global Instance subst_equiv_equivalence:
    Equivalence subst_equiv.
  Proof.
    split.
    - intros s x.
      reflexivity.
    - intros s r ? x.
      symmetry; auto.
    - intros s r t ? ? x.
      transitivity (r x); auto.
  Qed.

  Global Instance subst_equiv_cons_proper:
    Proper (eq ==> subst_equiv ==> subst_equiv) subst_cons.
  Proof.
    intros y _ () s r ? x.
    admit.
  Admitted.

  Global Instance subst_equiv_comp_proper:
    Proper (subst_equiv ==> subst_equiv ==> subst_equiv) subst_comp.
  Proof.
    intros s r ? t u ? x.
    admit.
  Admitted.

  Global Instance instantiate_subst_equiv_proper:
    Proper (subst_equiv ==> eq ==> eq) instantiate.
  Proof.
    intros s r ? x _ ().
    apply H0.
  Qed.

  (* ---------------------------------------------------------------------- *)

End DeBruijn.

Global Opaque instantiate.

Arguments subst_id {X}.
Arguments subst_lift {X}.
Arguments subst_cons {X}.
Arguments subst_comp {X}.

(* -------------------------------------------------------------------------- *)

(* Below we have some tests. TODO: remove this and move into proper places. *)

Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Machine.

Global Instance pseudoterm_deBruijn: deBruijn pseudoterm.
Proof.
  apply (Build_deBruijn bound traverse).
Defined.
