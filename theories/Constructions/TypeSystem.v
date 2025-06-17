(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
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

Definition typing_equivalence: Type :=
  env -> relation term.

Section TypeSystem.

  Variant typing_judgement: Set :=
    | valid_env (g: env)
    | typing (g: env) (e: term) (t: term).

  Variable R: typing_equivalence.

  Inductive infer: typing_judgement -> Prop :=
    (*
               |- G
      ----------------------
        G |- Set : Type 0
    *)
    | typing_iset:
      forall g,
      infer (valid_env g) ->
      infer (typing g iset (type 0))
    (*
               |- G
      ----------------------
        G |- Type n : Type (1 + n)
    *)
    | typing_type:
      forall g n,
      infer (valid_env g) ->
      infer (typing g (type n) (type (1 + n)))
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
        G |- T : s1     G, x: T |- U : s2
      -------------------------------------
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
             |- G
      -------------------
        G |- bool: Set
    *)
    | typing_bool:
      forall g,
      infer (valid_env g) ->
      infer (typing g boolean (sort iset))
    (*
            |- G
      -----------------
        G |- tt: bool
    *)
    | typing_true:
      forall g,
      infer (valid_env g) ->
      infer (typing g bool_tt boolean)
    (*
            |- G
      -----------------
        G |- ff: bool
    *)
    | typing_false:
      forall g,
      infer (valid_env g) ->
      infer (typing g bool_ff boolean)
    (*
             G |- e : bool        G, x: bool |- T : s
          G |- f1 : T[true/x]     G |- f2 : T[false/x]
      ----------------------------------------------------
        G |- if e as x return T then f1 else f2 : T[e/x]
    *)
    | typing_if:
      forall g e t s f1 f2,
      infer (typing g e boolean) ->
      infer (typing (decl_var boolean :: g) t (sort s)) ->
      infer (typing g f1 (subst bool_tt 0 t)) ->
      infer (typing g f2 (subst bool_ff 0 t)) ->
      infer (typing g (bool_if e t f1 f2) (subst e 0 t))
    (*
         G |- T : s
      ----------------
        G |- <T> : s
    *)
    | typing_thunk:
      forall g t s,
      infer (typing g t (sort s)) ->
      infer (typing g (thunk t) (sort s))
    (*
          G |- e : T
      -------------------
        G |- ?(e) : <T>
    *)
    | typing_delay:
      forall g e t,
      infer (typing g e t) ->
      infer (typing g (delay e) (thunk t))
    (*
         G |- e : <T>
      -----------------
        G |- !(e) : T
    *)
    | typing_force:
      forall g e t,
      infer (typing g e (thunk t)) ->
      infer (typing g (force e) t)
    (*
        G |- e : T     G |- U : s     G |- T R U
      --------------------------------------------
                       G |- e : U
    *)
    | typing_conv:
      forall g e t u s,
      infer (typing g e t) ->
      infer (typing g u (sort s)) ->
      R g t u ->
      infer (typing g e u)
    (*
      --------
        |- .
    *)
    | valid_env_nil:
      infer (valid_env [])
    (*
        G |- T : s
      --------------
        |- G, x: T
    *)
    | valid_env_var:
      forall g t s,
      infer (typing g t (sort s)) ->
      infer (valid_env (decl_var t :: g))
    (*
        G |- e : T     G |- T : s
      -----------------------------
            |- G, x = e: T
    *)
    | valid_env_def:
      forall g e t s,
      infer (typing g e t) ->
      infer (typing g t (sort s)) ->
      infer (valid_env (decl_def e t :: g)).

  (* Coq term: [\X: Prop.\x: X.x]. *)
  Example polymorphic_id_term: term :=
    abstraction (sort iset) (abstraction (bound 0) (bound 0)).

  (* Coq term: [Pi X: Prop.X -> X]. *)
  Example polymorphic_id_type: term :=
    pi (sort iset) (pi (bound 0) (bound 1)).

  (* Let's check typeability. *)
  Goal
    infer (typing [] polymorphic_id_term polymorphic_id_type).
  Proof.
    repeat econstructor.
    (* Of course! *)
    now vm_compute.
  Qed.

  (* Are we safe with higher sigma types? *)
  Goal
    infer (typing [] (sigma iset (bound 0)) (type 0)).
  Proof.
    repeat econstructor.
    - now vm_compute.
    - now vm_compute.
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

Lemma valid_env_infer:
  forall R j,
  infer R j ->
  valid_env (get_environment j) R.
Proof.
  (* Because the case for definitions doesn't have a subterm with the same
     environment, we need to slightly generalize the inductive hypothesis to
     say that every tail is valid instead. *)
  intros.
  change (get_environment j) with (skipn 0 (get_environment j)).
  generalize O.
  (* Now we can proceed... *)
  induction H; simpl in *; intros; auto.
  (* Case: definition. *)
  - (* Now the trick is to decrease a bit more from the hypothesis. *)
    apply IHinfer with (n := 1 + n).
  (* Case: empty env. *)
  - destruct n.
    + constructor.
    + constructor.
  (* Case: env var. *)
  - destruct n; simpl.
    + now apply valid_env_var with s.
    + apply IHinfer.
  (* Case: env def. *)
  - destruct n; simpl.
    + now apply valid_env_def with s.
    + (* Either one of the hypotheses work... *)
      apply IHinfer1.
Qed.

Lemma valid_env_typing:
  forall R g e t,
  typing g e t R ->
  valid_env g R.
Proof.
  intros.
  apply valid_env_infer in H.
  assumption.
Qed.

Lemma infer_subset:
  forall R S,
  (forall g, inclusion (R g) (S g)) ->
  forall j,
  infer R j ->
  infer S j.
Proof.
  (* We simply reconstruct the proof tree, judgement by judgement. *)
  induction 2.
  (* Case: iset. *)
  - now apply typing_iset.
  (* Case: type. *)
  - now apply typing_type.
  (* Case: bound. *)
  - now apply typing_bound with d t.
  (* Case: pi. *)
  - now apply typing_pi with s1 s2.
  (* Case: abstraction. *)
  - now apply typing_abs.
  (* Case: application. *)
  - now apply typing_app with t.
  (* Case: definition. *)
  - now apply typing_def.
  (* Case: sigma. *)
  - now apply typing_sigma with s1 s2.
  (* Case: pair. *)
  - now apply typing_pair.
  (* Case: projection 1. *)
  - now apply typing_proj1 with u.
  (* Case: projection 2. *)
  - now apply typing_proj2 with t.
  (* Case: bool. *)
  - now apply typing_bool.
  (* Case: true. *)
  - now apply typing_true.
  (* Case: false. *)
  - now apply typing_false.
  (* Case: if. *)
  - now apply typing_if with s.
  (* Case: thunk. *)
  - now apply typing_thunk.
  (* Case: delay. *)
  - now apply typing_delay.
  (* Case: force. *)
  - now apply typing_force.
  - (* The only difference in the structure is on the (CONV) rule, which will
       require us to show that [t] and [u] are still convertible under the new
       rule. *)
    apply typing_conv with t s.
    + assumption.
    + assumption.
    + now apply H.
  (* Case: empty env. *)
  - apply valid_env_nil.
  (* Case: env var. *)
  - now apply valid_env_var with s.
  (* Case: env def. *)
  - now apply valid_env_def with s.
Qed.

Conjecture weakening:
  (* TODO: prove this later! *)
  forall g e t R,
  typing g e t R ->
  forall d,
  valid_env (d :: g) R ->
  typing (d :: g) (lift 1 0 e) (lift 1 0 t) R.

Conjecture subject_reduction:
  (* TODO: prove this later. TODO: generalize to other equivalences. *)
  forall g e t,
  typing g e t conv ->
  forall f,
  rt(step g) e f ->
  typing g f t conv.
