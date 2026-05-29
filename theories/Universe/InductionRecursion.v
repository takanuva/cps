(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Set Universe Polymorphism.

Section IR.

  Context {O: Type}.

  Inductive Sig: Type :=
    | iota (o: O)
    | sigma (A: Set) (K: A -> Sig): Sig
    | delta (A: Type) (K: (A -> O) -> Sig): Sig.

  Fixpoint E (S: Sig) (X: Type) (H: X -> O): Type :=
    match S return Type with
    | iota o => unit
    | sigma A K => { a: A & E (K a) X H }
    | delta A K => { f: A -> X & E (K (fun x => H (f x))) X H }
    end.

  Fixpoint F (S: Sig) (X: Type) (H: X -> O): E S X H -> O :=
    match S with
    | iota o =>
      fun x =>
        o
    | sigma A K =>
      fun x =>
        F (K (projT1 x)) X H (projT2 x)
    | delta A K =>
      fun x =>
        F (K (fun a => H (projT1 x a))) X H (projT2 x)
    end.

  Definition E_fmap:
    forall {X: Type},
    forall {Y: Type},
    forall emb: X -> Y,
    forall H: Y -> O,
    forall s: Sig,
    E s X (fun x => H (emb x)) ->
    E s Y H.
  Proof.
    induction s; simpl; intros.
    - assumption.
    - destruct X1 as (a, x).
      exists a.
      now apply X0.
    - destruct X1 as (f, x).
      exists (fun a => emb (f a)).
      now eapply X0.
  Defined.

  Lemma F_coh:
    forall X: Type,
    forall Y: Type,
    forall emb: X -> Y,
    forall H: Y -> O,
    forall s: Sig,
    forall e: E s X (fun x => H (emb x)),
    F s Y H (E_fmap emb H s e) = F s X (fun x => H (emb x)) e.
  Proof.
    induction s; simpl; intros.
    - reflexivity.
    - destruct e as (a, e); simpl.
      apply H0.
    - destruct e as (f, e); simpl.
      apply H0.
  Qed.

  Definition total (X: O -> Type): Type :=
    { o: O & X o }.

  Definition total_fmap:
    forall {X: O -> Type},
    forall {Y: O -> Type},
    forall f: (forall o: O, X o -> Y o),
    total X -> total Y.
  Proof.
    intros.
    exists (projT1 X0).
    apply f.
    apply projT2.
  Defined.

  Definition fiber (X: Type) (p: X -> O) (o: O): Type :=
    { x: X | p x = o }.

  (* The actual O-indexed functor induced by (E, F), we call it E'. *)

  Definition E' (S: Sig): (O -> Type) -> (O -> Type) :=
    fun (X: O -> Type) o =>
      fiber
        (E S (total X) (@projT1 O X))
        (F S (total X) (@projT1 O X)) o.

  Definition E'_fmap:
    forall {X: O -> Type},
    forall {Y: O -> Type},
    forall s: Sig,
    (forall o, X o -> Y o) ->
    forall o,
    E' s X o -> E' s Y o.
  Proof.
    intros.
    unfold E', fiber in X1 |- *.
    destruct X1 as (x, ?H).
    exists (E_fmap (total_fmap X0) (@projT1 O Y) s x).
    rewrite F_coh; simpl.
    assumption.
  Defined.

  Variable S: Sig.

  Local Definition G: (O -> Type) -> (O -> Type) :=
    E' S.

  Local Definition IN (X: O -> Set): Set :=
    forall o, G X o -> X o.

  Definition muE: O -> Set :=
    fun o =>
      forall X: O -> Set, IN X -> X o.

  Definition foldE {o: O} (x: muE o) (X: O -> Set) (k: IN X): X o :=
    x X k.

  Definition inE {o: O} (x: G muE o): muE o :=
    fun X k =>
      k o (E'_fmap S (fun w y => foldE y X k) o x).

End IR.
