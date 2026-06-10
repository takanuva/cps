(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Import Program.
Require Import Morphisms.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Setoid.
Require Import Local.Category.
Require Import Local.Substitution.
Require Import Local.Constructions.Calculus.
Require Import Local.Constructions.Conversion.
Require Import Local.Constructions.Cumulativity.
Require Import Local.Constructions.TypeSystem.
(* Require Import Local.Constructions.Inversion. *)

Import ListNotations.

(*
(* TODO: move me! *)

Set Universe Polymorphism.

Section SubSetoid.

  Variable T: Type.
  Variable Q: T -> Prop.
  Variable R: T -> T -> Prop.

  Structure restriction (x: T) (y: T): Prop := {
    restriction_left: Q x;
    restriction_right: Q y;
    restriction_rel: R x y
  }.

  Definition restriction_sym:
    (forall x y, R x y -> R y x) ->
    forall x y,
    restriction x y -> restriction y x.
  Proof.
    intros.
    destruct H0 as (?H, ?H, ?H).
    constructor.
    - assumption.
    - assumption.
    - now apply H.
  Qed.

  Definition restriction_trans:
    (forall x y z, R x y -> R y z -> R x z) ->
    forall x y z,
    restriction x y -> restriction y z -> restriction x z.
  Proof.
    intros.
    destruct H0 as (?H, _, ?H).
    destruct H1 as (_, ?H, ?H).
    constructor.
    - assumption.
    - assumption.
    - now apply H with y.
  Qed.

End SubSetoid.

Arguments restriction {T}.
Arguments restriction_left {T} {Q} {R}.
Arguments restriction_right {T} {Q} {R}.
Arguments restriction_rel {T} {Q} {R}.

Global Instance restrition_per {T Q R} `{RelationClasses.PER T R}:
  RelationClasses.PER (@restriction T Q R).
Proof.
  constructor; repeat intro.
  - apply restriction_sym.
    + apply PER_Symmetric.
    + assumption.
  - apply restriction_trans with y.
    + apply PER_Transitive.
    + assumption.
    + assumption.
Qed.
*)

Definition welltyped_env: Set :=
  { g: env | valid_env g conv }.

Definition welltyped_subst (g: welltyped_env) (d: welltyped_env) :=
  { s: substitution | valid_subst s (`g) (`d) conv }.

Program Definition subst_setoid g d: Setoid := {|
  setoid_carrier := welltyped_subst g d;
  setoid_equiv := subst_equiv
|}.

Next Obligation of subst_setoid.
  reflexivity.
Qed.

Next Obligation of subst_setoid.
  now symmetry.
Qed.

Next Obligation of subst_setoid.
  now transitivity (`y).
Qed.

Program Definition term_category: Category := {|
  obj := welltyped_env;
  hom := subst_setoid;
  id X := subst_ids;
  post X Y Z := map f g => subst_comp g f
|}.

Next Obligation of term_category.
  constructor.
  apply proj2_sig.
Qed.

Next Obligation of term_category.
  apply valid_subst_comp with (`Y).
  - apply proj2_sig.
  - apply proj2_sig.
Qed.

Next Obligation of term_category.
  now rewrite H.
Qed.

Next Obligation of term_category.
  now rewrite H.
Qed.

Next Obligation of term_category.
  repeat intro.
  now sigma.
Qed.

Next Obligation of term_category.
  repeat intro.
  now sigma.
Qed.

Next Obligation of term_category.
  repeat intro.
  now sigma.
Qed.

Local Fixpoint iterate (n: nat) {T: Type} (f: T -> T) (x: T): T :=
  match n with
  | 0 => x
  | S m => f (iterate m f x)
  end.

Definition terminal_subst (g: env): @substitution term :=
  iterate (length g) (fun s => subst_comp s (subst_lift 1)) subst_ids.

Lemma terminal_subst_nil:
  terminal_subst [] = subst_ids.
Proof.
  reflexivity.
Qed.

Lemma terminal_subst_cons:
  forall g t,
  terminal_subst (t :: g) = subst_comp (terminal_subst g) (subst_lift 1).
Proof.
  intros.
  reflexivity.
Qed.

Lemma terminal_subst_simpl:
  forall g,
  subst_equiv (terminal_subst g) (subst_lift (length g)).
Proof.
  induction g; simpl.
  - rewrite terminal_subst_nil.
    now sigma.
  - rewrite terminal_subst_cons.
    rewrite IHg.
    now sigma.
Qed.

Lemma terminal_subst_is_valid:
  forall g: welltyped_env,
  valid_subst (terminal_subst (`g)) (`g) [] conv.
Proof.
  destruct g as (g, ?H); simpl.
  induction g; simpl.
  - rewrite terminal_subst_nil.
    do 2 constructor.
  - rewrite terminal_subst_cons.
    apply valid_subst_comp with g.
    + apply IHg; clear IHg.
      dependent destruction H.
      * now apply valid_env_typing with t s.
      * now apply valid_env_typing with t s.
    + clear IHg.
      dependent destruction H.
      * now apply valid_subst_lift_var with s.
      * now apply valid_subst_lift_def with s.
Qed.

Lemma terminal_subst_is_unique:
  forall g s,
  valid_subst s g [] conv ->
  subst_equiv s (terminal_subst g).
Proof.
  intros.
  (* Simplify this definition to something equivalent, just so sigma may help us
     a bit more. *)
  rewrite terminal_subst_simpl.
  dependent induction H.
  - clear IHinfer; simpl.
    now sigma.
  - clear IHinfer; simpl.
    reflexivity.
  - clear IHinfer1 IHinfer2; simpl.
    reflexivity.
  - rename g2 into d, f into s, g0 into t.
    (* Composition gets complicated as we have an arbitrary substitution t on
       the mix. We proceed with our inductive hypothesis, showing that s has to
       be a lift with the appropriate length. *)
    clear IHinfer2.
    specialize (IHinfer1 _ _ eq_refl eq_refl).
    (* We know that s is equivalent to the terminal substitution; an important
       property is that: composition with the terminal substitution on the left
       will always produce the terminal substitution again, as we show here. *)
    rewrite IHinfer1.
    clear H; clear IHinfer1 s.
    (* Now that we have simplified our goal, we perform another induction to
       show that, no matter which t : G -> D we have, it can't produce anything
       that won't be skipped by the lift by (length d) here. *)
    dependent induction H0.
    + clear IHinfer.
      now sigma.
    + clear IHinfer; simpl.
      now sigma.
    + clear IHinfer1 IHinfer2; simpl.
      now sigma.
    + (* Most complicated case: we need both inductive hypotheses to show that
         we'll accumulate the right amount of shifting! Luckly we can just
         rewrite these and sigma will do the work. *)
      specialize (IHinfer1 _ _ _ eq_refl).
      specialize (IHinfer2 _ _ _ eq_refl).
      rewrite <- IHinfer2.
      rewrite <- IHinfer1.
      now sigma.
    + (* Similar to the above. *)
      clear IHinfer2 IHinfer3.
      specialize (IHinfer1 _ _ _ eq_refl).
      rewrite <- IHinfer1; simpl.
      now sigma.
Qed.

Lemma welltyped_env_is_valid:
  forall G: welltyped_env,
  infer conv (valid_env (` G)).
Proof.
  intros.
  destruct G as (g, ?H); simpl.
  assumption.
Qed.

(* -------------------------------------------------------------------------- *)

Definition welltyped_type (g: env) :=
  { t: term | exists s: sort, typing g t (sort_term s) conv }.

Program Definition type_setoid (g: env): Setoid := {|
  setoid_carrier := welltyped_type g;
  setoid_equiv T U := conv g (`T) (`U)
|}.

Next Obligation of type_setoid.
  apply conv_refl.
Qed.

Next Obligation of type_setoid.
  now apply conv_sym.
Qed.

Next Obligation of type_setoid.
  now apply conv_trans with (`y).
Qed.

Definition welltyped_term (g: env) (t: term) :=
  { e: term | typing g e t conv }.

Program Definition term_setoid (g: env) (t: term): Setoid := {|
  setoid_carrier := welltyped_term g t;
  setoid_equiv E F := conv g (`E) (`F)
|}.

Next Obligation of term_setoid.
  apply conv_refl.
Qed.

Next Obligation of term_setoid.
  now apply conv_sym.
Qed.

Next Obligation of term_setoid.
  now apply conv_trans with (`y).
Qed.

Program Definition term_model: CwF := {|
  cwf_cat := term_category;
  cwf_empty := {|
    terminal := [];
    terminal_hom := terminal_subst
  |};
  cwf_ty (G: welltyped_env) :=
    type_setoid (`G);
  cwf_tsub (G D: welltyped_env) :=
    map (S: welltyped_subst D G) (T: welltyped_type G) =>
      inst (`S) (`T);
  cwf_el (G: welltyped_env) := {|
    setoid_family (T: welltyped_type G) :=
      term_setoid (`G) (`T);
    setoid_family_prf := {|
      setoid_transport T U H := {|
        setoid_map E := E
      |}
    |}
  |};
  cwf_esub G D T (S: welltyped_subst D G) :=
    map (E: welltyped_term G T) =>
      inst (`S) (`E);
  (* cwf_ext (G: welltyped_env) (T: welltyped_type G) :=
    decl_var (`T) :: (`G); *)
  cwf_u (G: welltyped_env) (n: nat) :=
    sort_term (type n);
  cwf_t (G: welltyped_env) (n: nat) U :=
    U;
  cwf_lift (G: welltyped_env) n l (H: n < l) U :=
    U
|}.

Next Obligation of term_model.
  constructor.
Qed.

Next Obligation of term_model.
  apply terminal_subst_is_valid.
Qed.

Next Obligation of term_model.
  destruct f as (f, ?H); simpl in *.
  now apply terminal_subst_is_unique.
Qed.

Next Obligation of term_model.
  destruct G as (g, ?H); simpl in *.
  destruct D as (d, ?H); simpl in *.
  destruct S as (s, ?H); simpl in *.
  destruct T as (t, (u, ?H)); simpl in *.
  exists u.
  (* Since substitution doesn't change sorts... *)
  change (sort_term u) with (inst s (sort_term u)).
  now apply typing_inst with g.
Qed.

Next Obligation of term_model.
  (* Well, haven't proven that yet, but it's true! *)
  admit.
Admitted.

Next Obligation of term_model.
  now rewrite H.
Qed.

Next Obligation of term_model.
  destruct T as (t, (s1, ?H)); simpl in *.
  destruct U as (u, (s2, ?H)); simpl in *.
  destruct E as (e, ?H); simpl in *.
  apply typing_conv with t s2.
  - assumption.
  - assumption.
  - now apply cumul_refl.
Qed.

Next Obligation of term_model.
  apply conv_refl.
Qed.

Next Obligation of term_model.
  apply conv_refl.
Qed.

Next Obligation of term_model.
  apply conv_refl.
Qed.

Next Obligation of term_model.
  destruct G as (g, ?H); simpl in *.
  destruct D as (d, ?H); simpl in *.
  destruct T as (t, (u, ?H)); simpl in *.
  destruct S as (s, ?H); simpl in *.
  destruct E as (e, ?H); simpl in *.
  now apply typing_inst with g.
Qed.

Next Obligation of term_model.
  (* Same as above, gotta admit that! *)
  admit.
Admitted.

(* Next Obligation of term_model.
  destruct T as (t, (u, ?H)); simpl.
  apply valid_env_var with u.
  assumption.
Qed. *)

Next Obligation of term_model.
  exists (type (1 + n)).
  apply typing_type.
  apply welltyped_env_is_valid.
Qed.

Next Obligation of term_model.
  destruct U as (u, ?H); simpl in *.
  now exists (type n).
Qed.

Next Obligation of term_model.
  destruct U as (u, ?H); simpl in *.
  apply typing_hierarchy with n.
  - assumption.
  - apply welltyped_env_is_valid.
  - assumption.
Qed.

Next Obligation of term_model.
  apply conv_refl.
Qed.

(*
  cwf_ty: cwf_env -> PartialSetoid;
  cwf_el G: Domain (cwf_ty G) ~> PartialSetoid;
  (* ... *)
  cwf_u {G}: nat -> Domain (cwf_ty G);
  cwf_t {G n}:
    forall X: Domain (cwf_el G (cwf_u n)),
    Domain (cwf_ty G);
  cwf_lift {G n l}:
    forall H: n < l,
    forall X: Domain (cwf_el G (cwf_u n)),
    Domain (cwf_el G (cwf_u l));
  cwf_ucoh {G n l}:
    forall H: n < l,
    forall X: Domain (cwf_el G (cwf_u n)),
    cwf_t (cwf_lift H X) == cwf_t X
*)






(*

Definition type_valid (g: welltyped_env) (t: term) :=
  exists s, typing (`g) t (sort s) conv.

Program Definition type_setoid (g: welltyped_env): PartialSetoid := {|
  partial_carrier := term;
  partial_equiv := restriction (type_valid g) (conv (`g))
|}.

Next Obligation of type_setoid.
  now symmetry.
Qed.

Next Obligation of type_setoid.
  now transitivity y.
Qed.

Notation welltyped_type g :=
  (Domain (type_setoid g)).

Lemma type_valid_inst:
  forall g: welltyped_env,
  forall d: welltyped_env,
  forall s: welltyped_subst d g,
  forall t: welltyped_type g,
  type_valid d (inst (`s) (`t)).
Proof.
  intros.
  destruct g as (g, ?H); simpl in *.
  destruct d as (d, ?H); simpl in *.
  destruct s as (s, ?H); simpl in *.
  destruct H1 as (?H, _, ?H); simpl in *.
  unfold subst_valid in H1; simpl in H1.
  destruct t as (t, ?H); simpl in *.
  destruct H3 as (?H, _, ?H); simpl in *.
  unfold type_valid in *; simpl in *.
  destruct H3 as (u, ?H).
  exists u.
  (* As sorts are stable under substitution... *)
  change (sort u) with (inst s (sort u)).
  (* Now we can close the proof. *)
  now apply typing_inst with g.
Qed.

Definition term_valid (g: welltyped_env) (t: welltyped_type g) (e: term) :=
  typing (`g) e (`t) conv.

Program Definition term_setoid g t: PartialSetoid := {|
  partial_carrier := term;
  partial_equiv := restriction (term_valid g t) (conv (`g))
|}.

Next Obligation of term_setoid.
  now symmetry.
Qed.

Next Obligation of term_setoid.
  now transitivity y.
Qed.

(* Finally, we can build the term model as a category with families, picking
   the term category, well-typed types and well-typed terms. *)

Program Definition term_model: CwF := {|
  cwf_cat := term_category;
  cwf_empty := {|
    terminal := [];
    terminal_hom := terminal_subst
  |};
  cwf_ty := type_setoid;
  cwf_tsub g d s t := inst (`s) (`t);
  cwf_el g := map t => term_setoid g t;
  cwf_esub g d a s t := inst (`s) (`t);
  cwf_ext g t := decl_var (`t) :: (`g);
  cwf_cons g d s t e := subst_cons (`e) (`s);
  cwf_proj g t := subst_lift 1;
  cwf_zero g t := bound 0
|}.

Next Obligation of term_model.
  constructor.
Qed.

Next Obligation of term_model.
  constructor.
  - apply terminal_subst_is_valid.
  - apply terminal_subst_is_valid.
  - reflexivity.
Qed.

Next Obligation of term_model.
  unfold subst_valid; simpl.
  constructor.
  - destruct f as (f, ?H); simpl in *.
    apply H.
  - apply terminal_subst_is_valid.
  - destruct f as (f, ?H); simpl in *.
    apply terminal_subst_is_unique.
    apply H.
Qed.

Next Obligation of term_model.
  constructor.
  - apply type_valid_inst.
  - apply type_valid_inst.
  - reflexivity.
Qed.

Next Obligation of term_model.
  exists (eq_refl term).
  simpl; split; intros.
  - destruct H as (?H, ?H, ?H).
    destruct H0 as (?H, ?H, ?H).
    constructor; simpl in *.
    + unfold type_valid in *.
      unfold term_valid in *.
      destruct H1 as (u, ?H).
      apply typing_conv with (`x) u.
      * assumption.
      * assumption.
      * now apply Cumulativity.cumul_refl.
    + unfold type_valid in *.
      unfold term_valid in *.
      destruct H1 as (u, ?H).
      apply typing_conv with (`x) u.
      * assumption.
      * assumption.
      * now apply Cumulativity.cumul_refl.
    + assumption.
  - destruct H as (?H, ?H, ?H).
    destruct H0 as (?H, ?H, ?H).
    constructor; simpl in *.
    + unfold type_valid in *.
      unfold term_valid in *.
      destruct H as (u, ?H).
      apply typing_conv with (`y) u.
      * assumption.
      * assumption.
      * now apply Cumulativity.cumul_refl.
    + unfold type_valid in *.
      unfold term_valid in *.
      destruct H as (u, ?H).
      apply typing_conv with (`y) u.
      * assumption.
      * assumption.
      * now apply Cumulativity.cumul_refl.
    + assumption.
Qed.

Next Obligation of term_model.
  unfold term_valid; simpl.
  constructor; simpl.
  - destruct s as (s, ?H); simpl in *.
    destruct t as (e, ?H); simpl in *.
    apply typing_inst with (`g).
    + apply H0.
    + apply H.
  - destruct s as (s, ?H); simpl in *.
    destruct t as (e, ?H); simpl in *.
    apply typing_inst with (`g).
    + apply H0.
    + apply H.
  - reflexivity.
Qed.

Next Obligation of term_model.
  destruct g as (g, ?H); simpl in *.
  destruct t as (t, ?H); simpl in *.
  destruct H0 as (?H, ?H, ?H); simpl in *.
  unfold type_valid in H0; clear H1; simpl in *.
  destruct H0 as (s, ?H).
  now apply valid_env_var with s.
Qed.

Next Obligation of term_model.
  destruct e as (e, ?H); simpl in *.
  unfold term_valid in *; simpl in *.
  unfold subst_valid in *; simpl in *.
  constructor.
  - destruct t as (t, ?H); simpl in *.
    destruct H0 as (?H, _, ?H); simpl in *.
    destruct H0 as (u, ?H); simpl in *.
    apply valid_subst_cons with u.
    + destruct s as (s, ?H); simpl in *.
      apply H2.
    + assumption.
    + apply H.
  - destruct t as (t, ?H); simpl in *.
    destruct H0 as (?H, _, ?H); simpl in *.
    destruct H0 as (u, ?H); simpl in *.
    apply valid_subst_cons with u.
    + destruct s as (s, ?H); simpl in *.
      apply H2.
    + assumption.
    + apply H.
  - reflexivity.
Qed.

Next Obligation of term_model.
  unfold subst_valid; simpl.
  constructor; simpl.
  - destruct t as (t, ?H); simpl in *.
    destruct H as (?H, _, ?H); simpl in *.
    destruct H as (u, ?H); simpl in *.
    now apply valid_subst_lift_var with u.
  - destruct t as (t, ?H); simpl in *.
    destruct H as (?H, _, ?H); simpl in *.
    destruct H as (u, ?H); simpl in *.
    now apply valid_subst_lift_var with u.
  - reflexivity.
Qed.

Next Obligation of term_model.
  unfold term_valid; simpl.
  constructor; simpl.
  - destruct t as (t, ?H); simpl.
    apply typing_var with t.
    + destruct H as (?H, _, ?H).
      destruct H as (u, ?H).
      now apply valid_env_var with u.
    + constructor.
    + now sigma.
  - destruct t as (t, ?H); simpl.
    apply typing_var with t.
    + destruct H as (?H, _, ?H).
      destruct H as (u, ?H).
      now apply valid_env_var with u.
    + constructor.
    + now sigma.
  - reflexivity.
Qed.

Next Obligation of term_model.
  repeat intro; simpl.
  constructor; simpl.
  - apply type_valid_inst.
  - apply type_valid_inst.
  - destruct H as (?H, ?H, ?H); simpl.
    destruct H0 as (?H, ?H, ?H); simpl.
    (* Oops! *)
    admit.
Admitted.

Next Obligation of term_model.
  destruct A as (t, ?H); simpl.
  constructor.
  - sigma; apply H.
  - apply H.
  - now sigma.
Qed.

Next Obligation of term_model.
  destruct A as (t, ?H); simpl.
  constructor.
  - sigma.
    admit.
  - admit.
  - now sigma.
Admitted.

*)
