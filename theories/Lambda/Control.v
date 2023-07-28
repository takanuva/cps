(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

(* TODO: this is a temporary file, meant just to check the properties of control
   operators in the CPS translation. Please, move this code to the proper place
   once I'm finished! *)

Require Import Lia.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.Axiomatic.
Require Import Local.Reduction.
Require Import Local.TypeSystem.

Local Notation N := negation.

(* TODO: I *really* gotta make a tactics file for automating reduction steps. *)

Fixpoint foobar (b: pseudoterm): context * pseudoterm :=
  match b with
  | bind b ts c =>
      (context_left (fst (foobar b)) ts c, snd (foobar b))
  | _ =>
    (context_hole, b)
  end.

Lemma foobar_sound:
  forall b,
  b = (fst (foobar b)) (snd (foobar b)).
Proof.
  induction b.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl.
  rewrite IHb1 at 1.
  reflexivity.
Defined.

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

  Goal
    (* We can derive A from C! *)
    forall T,
    typing
      []
      (* \x.C (\k.x) *)
      (abstraction F (application C (abstraction (arrow T F) 1)))
      (arrow F T).
  Proof.
    intros.
    apply typing_abstraction.
    apply typing_application with (arrow (arrow T F) F).
    - apply typing_C.
    - apply typing_abstraction.
      apply typing_bound.
      do 2 constructor.
  Qed.

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

  Definition cbv_typing g c t :=
    TypeSystem.typing (N [cbv_type t] :: cbv_env g) c void.

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
    typing [] C U & cbv_typing [] (@cbv_C (cbv_type T)) U.
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
    typing [] A U & cbv_typing [] (@cbv_A (cbv_type T)) U.
  Proof.
    intros.
    exists (arrow F T).
    - apply typing_A.
    - repeat (simpl; try econstructor; auto; try rewrite cbv_type_F).
  Qed.

  Local Lemma struct_eta_helper:
    forall b ts k x1 x2,
    x1 = jump (Syntax.lift (length ts) 0 k) (low_sequence (length ts)) ->
    x2 = Syntax.subst k 0 b ->
    struct (bind b ts x1) x2.
  Proof.
    intros.
    rewrite H, H0.
    apply struct_eta.
  Qed.

  (* Let's see if Felleisen's abbreviation holds in here... *)
  Goal
    (* This should work for *any* T, but... *)
    let T := F in
    forall b c,
    cbv_cps A b ->
    cbv_cps (abstraction F (application C (abstraction (arrow T F) 1))) c ->
    [b == c].
  Proof.
    intros.
    assert (b = @cbv_A (cbv_type T)).
    eapply cbv_cps_is_a_function.
    eassumption.
    apply cbv_cps_A.
    dependent destruction H1.
    clear H.
    unfold cbv_A.
    dependent destruction H0.
    dependent destruction H0.
    dependent destruction H0_0.
    dependent destruction H0_0.
    assert (b = Syntax.lift 1 1 (Syntax.lift 1 2 (@cbv_C (cbv_type T)))).
    eapply cbv_cps_is_a_function.
    eassumption.
    apply cbv_cps_lift.
    apply cbv_cps_lift.
    apply cbv_cps_C.
    dependent destruction H.
    clear H0_.
    unfold cbv_C.
    unfold T.
    rewrite cbv_type_F.
    compute.
    symmetry.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; try lia.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    apply beta_bind_left.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    apply beta_bind_left.
    apply beta_bind_left.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_bind_left.
    apply tidy_gc.
    repeat constructor; simpl; try lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_bind_left.
    apply tidy_gc.
    repeat constructor; simpl; try lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; try lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; try lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; try lia.
    compute.
    (* Typing is degenerate in the equational theory... we can use (ETA) now to
       fix this! *)
    etransitivity.
    transitivity
      (bind (bind (jump 2 [CPS.bound 0]) [N [N []]; N []]
        (jump 2 (low_sequence 2))) [void; void]
          (jump 1 [])).
    apply sema_sym.
    apply sema_bind_left.
    apply sema_struct.
    compute.
    apply struct_eta_helper with (k := 0).
    reflexivity.
    reflexivity.
    etransitivity.
    apply sema_step.
    apply step_beta.
    replace ((bind (jump 2 [CPS.bound 0]) [
        N [N []]; N []]
        (jump 2 (CPS.low_sequence 2)))) with
      (context_right (jump 2 [CPS.bound 0]) [
        N [N []]; N []] Context.context_hole (jump 2 (CPS.low_sequence 2)));
    auto.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; try lia.
    compute.
    reflexivity.
  Qed.

End CBV.

Section CBN.

  Require Import Local.Lambda.CallByName.

  Definition cbn_typing g c t :=
    TypeSystem.typing (cbn_type t :: cbn_env g) c void.

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

  Definition cbn_C {T}: pseudoterm :=
    (* [|- C: ~~T -> T] = [k: ~~(~~~(~~~(~[T], ~~()), ~~()), [T]) |- [C]]

       k<f>
       { f<x: ~~~(~~~(~[T], ~~()), ~~()), k: [T]> =
         x<j>
         { j<i: ~(~~~(~[T], ~~()), ~~())> =
           i<p, q>
           { p<l: ~~(~[T], ~~())> =
             l<n>
             { n<y: ~[T], o: ~~()> =
               o<z>
               { z<> =
                 y<k> }
             }
           }
           { q<m: ~()> =
             m<> } } }
    *)
    let U := N [N [N [N []]; N [T]]] in
    (bind
      (jump 1 [Syntax.bound 0])
      [T; N [N [N [N [N []]; N [U]]]]]
      (bind
        (jump 2 [Syntax.bound 0])
        [N [N [N []]; N [U]]]
        (bind
          (bind
            (jump 2 [Syntax.bound 0; Syntax.bound 1])
            [U]
            (bind
              (jump 1 [Syntax.bound 0])
              [N [N []]; N [T]]
              (bind
                (jump 1 [Syntax.bound 0])
                []
                (jump 1 [Syntax.bound 5]))))
          [N []]
          (jump 0 [])))).

  Axiom cbn_cps_C:
    forall T,
    cbn_cps C (@cbn_C T).

  Goal
    forall T: type,
    (forall g, TypeSystem.typing g (cbn_type T) prop) ->
    exists2 U,
    typing [] C U & cbn_typing [] (@cbn_C (cbn_type T)) U.
  Proof.
    intros.
    exists (arrow (arrow (arrow T F) F) T).
    - apply typing_C.
    - repeat (simpl; try econstructor; auto; try rewrite cbn_type_F).
  Qed.

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
    typing [] A U & cbn_typing [] (@cbn_A (cbn_type T)) U.
  Proof.
    intros.
    exists (arrow F T).
    - apply typing_A.
    - repeat (simpl; try econstructor; auto; try rewrite cbn_type_F).
  Qed.

  (* I hope I've done everything correctly...! *)
  Goal
    (* This should work for *any* T, still... *)
    let T := F in
    forall b c,
    cbn_cps A b ->
    cbn_cps (abstraction F (application C (abstraction (arrow T F) 1))) c ->
    [b == c].
  Proof.
    intros.
    assert (b = @cbn_A (cbn_type T)).
    eapply cbn_cps_is_a_function.
    eassumption.
    apply cbn_cps_A.
    dependent destruction H1.
    clear H.
    unfold cbn_A.
    dependent destruction H0.
    dependent destruction H0.
    dependent destruction H0_0.
    dependent destruction H0_0.
    assert (b = Syntax.lift 1 1 (Syntax.lift 1 2 (@cbn_C (cbn_type T)))).
    eapply cbn_cps_is_a_function.
    eassumption.
    apply cbn_cps_lift.
    apply cbn_cps_lift.
    apply cbn_cps_C.
    dependent destruction H.
    clear H0_.
    unfold cbn_C.
    unfold T.
    rewrite cbn_type_F.
    compute.
    symmetry.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; lia.
    compute.
    etransitivity.
    apply sema_bind_right.
    apply sema_bind_left.
    apply sema_step.
    apply step_tidy.
    apply tidy_gc.
    repeat constructor; simpl; lia.
    compute.
    (* Yey, typing is degenerate! *)
    admit.
  Admitted.

End CBN.
