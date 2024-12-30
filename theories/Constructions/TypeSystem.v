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

(*
Compute
  fun e P (a: e = true -> P true) (b: false = e -> P false) =>
    (if e as c return ((c = true -> P true) -> (false = c -> P false) -> P c) then
       fun (x : true = true -> P true) (_ : false = true -> P false) =>
         x eq_refl
     else
       fun (_ : false = true -> P true) (x : false = false -> P false) =>
         x eq_refl) a b.
*)

Definition typing_equivalence: Type :=
  env -> term -> relation term.

Section TypeSystem.

  Variant typing_judgement: Set :=
    | valid_env (g: env)
    | typing (g: env) (e: term) (t: term).

  Variable R: typing_equivalence.

  Inductive infer: typing_judgement -> Prop :=
    (*
               |- G
      ----------------------
        G |- Prop : Type 0
    *)
    | typing_prop:
      forall g,
      infer (valid_env g) ->
      infer (typing g prop (type 0))
    (*
        (x: T) or (x = e: T) in G
      -----------------------------
               G |- x : T
    *)
    | typing_bound:
      forall g n d t u,
      infer (valid_env g) ->
      item (d, t) g n ->
      u = lift (1 + n) 0 t ->
      infer (typing g (bound n) u)
    (*
         G |- T : s1     G, x: T |- U : s2
      --------------------------------------
             G |- Pi x: T.U : s1 o s2
    *)
    | typing_pi:
      (* Sort of products will deal with impredicativity for prop, and will get
         the right universe level otherwise. *)
      forall g t u s1 s2 s3,
      infer (typing g t (sort s1)) ->
      infer (typing (decl_var t :: g) u (sort s2)) ->
      s3 = sort_of_product s1 s2 ->
      infer (typing g (pi t u) s3)
    (*
            G, x: T |- e : U
      ----------------------------
        G |- \x: T.e : Pi x: T.U
    *)
    | typing_abs:
      forall g t e u,
      infer (typing (decl_var t :: g) e u) ->
      infer (typing g (abstraction t e) (pi t u))
    (*
        G |- f : Pi x: T.U     G |- e : T
      -------------------------------------
                G |- f e : U[e/x]
    *)
    | typing_app:
      forall g f e t u,
      infer (typing g f (pi t u)) ->
      infer (typing g e t) ->
      infer (typing g (application f e) (subst e 0 u))
    (*
        G |- e : T     G, x = e: T |- f : U
      ---------------------------------------
          G |- let x = e: T in f : U[e/x]
    *)
    | typing_def:
      forall g e f t u,
      infer (typing g e t) ->
      infer (typing (decl_def e t :: g) f u) ->
      infer (typing g (definition e t f) (subst e 0 u))
    (*
        G |- T: s1     G, x: T |- U: s2
      -----------------------------------
          G |- Sigma x: T.U : s1 & s2
    *)
    | typing_sigma:
      forall g t u s1 s2 s3,
      infer (typing g t (sort s1)) ->
      infer (typing (decl_var t :: g) u (sort s2)) ->
      s3 = supremum s1 s2 ->
      infer (typing g (sigma t u) s3)
    (*
               G |- e : T     G |- f : U[e/x]
      ------------------------------------------------
        G |- (e, f) as (Sigma x: T.U) : Sigma x: T.U
    *)
    | typing_pair:
      (* Notice we require the typing annotation in the pair to keep the type
         unique; this is similar to how it's encoded in Coq and how it was done
         by Luo. The "x" used in the hypothesis would come from there. *)
      forall g e f t u,
      infer (typing g e t) ->
      infer (typing g f (subst e 0 u)) ->
      infer (typing g (pair e f (sigma t u)) (sigma t u))
    (*
        G |- e : Sigma x: T.U
      -------------------------
           G |- proj1 e : T
    *)
    | typing_proj1:
      forall g e t u,
      infer (typing g e (sigma t u)) ->
      infer (typing g (proj1 e) t)
    (*
           G |- e : Sigma x: T.U
      -------------------------------
        G |- proj2 e : U[proj1 e/x]
    *)
    | typing_proj2:
      forall g e t u,
      infer (typing g e (sigma t u)) ->
      infer (typing g (proj2 e) (subst (proj1 e) 0 u))
    (*
        G |- e : T     G |- U : s     G |- T R U : s
      ------------------------------------------------
                         G |- e : U
    *)
    | typing_conv:
      forall g e t u s,
      infer (typing g e t) ->
      infer (typing g u (sort s)) ->
      R g (sort s) t u ->
      infer (typing g e u)
    (*
      --------
        |- .
    *)
    | valid_env_nil:
      infer (valid_env [])
    (*
        |- G     G |- T : s
      -----------------------
            |- G, x: T
    *)
    | valid_env_var:
      forall g t s,
      infer (valid_env g) ->
      infer (typing g t (sort s)) ->
      infer (valid_env (decl_var t :: g))
    (*
        |- G     G |- e : T     G |- T : s
      --------------------------------------
                |- G, x = e: T
    *)
    | valid_env_def:
      forall g e t s,
      infer (valid_env g) ->
      infer (typing g e t) ->
      infer (typing g t (sort s)) ->
      infer (valid_env (decl_def e t :: g)).

  (* Coq term: [\X: Prop.\x: X.x]. *)
  Example polymorphic_id_term: term :=
    abstraction (sort prop) (abstraction (bound 0) (bound 0)).

  (* Coq term: [Pi X: Prop.X -> X]. *)
  Example polymorphic_id_type: term :=
    pi (sort prop) (pi (bound 0) (bound 1)).

  (* Let's check typeability. *)
  Goal
    infer (typing [] polymorphic_id_term polymorphic_id_type).
  Proof.
    simpl.
    repeat econstructor.
    (* Of course! *)
    now vm_compute.
  Qed.

End TypeSystem.

Definition lift_judgement (j: typing_judgement): typing_equivalence -> Prop :=
  fun R => infer R j.

Global Coercion lift_judgement: typing_judgement >-> Funclass.

Definition get_environment (j: typing_judgement): env :=
  match j with
  | valid_env g => g
  | typing g _ _ => g
  end.

Coercion get_environment: typing_judgement >-> env.

Lemma valid_env_typing:
  forall R j,
  infer R j ->
  valid_env j R.
Proof.
  induction 1; simpl.
  - assumption.
  - assumption.
  - dependent destruction IHinfer2.
    assumption.
  - dependent destruction IHinfer.
    assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - constructor.
  - now apply valid_env_var with s.
  - now apply valid_env_def with s.
Qed.
