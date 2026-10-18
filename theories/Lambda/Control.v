(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

(* TODO: this is a temporary file, meant just to check the properties of control
   operators in the CPS translation. Please, move this code to the proper place
   once I'm finished!

   TODO: ok I might keep this file but please refactor it, a lot! *)

Require Import Lia.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Syntax.
Require Import Local.Context.
Require Import Local.Metatheory.
Require Import Local.Equational.
Require Import Local.Reduction.
Require Import Local.TypeSystem.

Import ListNotations.

Local Notation N ts := (negation ts).

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
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl.
    now rewrite IHb1 at 1.
Defined.

Section Control.

  Require Import Local.Lambda.Calculus.

  Axiom C: term.
  Axiom A: term.
  Axiom K: term.
  Axiom F: type.

  Axiom typing_C:
    forall g T,
    (* C: ~~T -> T *)
    typing g C (arrow (arrow (arrow T F) F) T).

  Axiom typing_A:
    forall g T,
    (* A: F -> T *)
    typing g A (arrow F T).

  Axiom typing_K:
    forall g T U,
    (* K: ((T -> U) -> T) -> T *)
    typing g K (arrow (arrow (arrow T U) T) T).

  Definition A_def T: term :=
    (* A = \x.C (\k.x) *)
    (abstraction F (application C (abstraction (arrow T F) 1))).

  Lemma typing_A_def:
    forall g T,
    (* A: F -> T *)
    typing g (A_def T) (arrow F T).
  Proof.
    intros.
    apply typing_abstraction.
    apply typing_application with (arrow (arrow T F) F).
    - apply typing_C.
    - apply typing_abstraction.
      apply typing_bound.
      do 2 constructor.
  Qed.

  Definition K_def T U: term :=
    (* K = \f: (T -> U) -> T.C (\k: T -> F.k (f (\x: T.A (k x))))
                                                ^^^^^^^^^^^^^^^^
                                                changes the type! *)
    abstraction (arrow (arrow T U) T)
      (application C
        (abstraction (arrow T F)
          (application 0
            (application 1
              (abstraction T
                (application A
                  (application 1 0))))))).

  Lemma typing_K_def:
    forall g T U,
    (* K: ((T -> U) -> T) -> T *)
    typing g (K_def T U) (arrow (arrow (arrow T U) T) T).
  Proof.
    intros.
    repeat econstructor.
    - apply typing_C.
    - apply typing_A.
  Qed.

End Control.

Local Transparent lift.
Local Transparent subst.
Local Transparent inst.
Local Transparent inst_rec.

Section CBV.

  Require Import Local.Lambda.PlotkinCBV.

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

      [xs: As |- e: B] = xs: [As], k: ~[B] |- [e]
  *)

  Axiom cbv_type_F:
    cbv_type F = N [].

  Definition cbv_C {T}: pseudoterm :=
    (* [|- C: ~~T -> T] = [k: ~~(~(~([T], ~~()), ~~()), ~[T]) |- [C]]

       k<f>
       { f<x: ~(~([T], ~~()), ~~()), k: ~[T]> =
         x@3<p@0, q@1>
         { p<y: [T], j: ~~()> =
           j@1<r@0>
           { r<> =
             k@3<y@1> } }
         { q<j: ~()> =
           j@0<> } }
    *)
    bind
      (jump 1 [Syntax.bound 0])
      [N [T]; N [N [N []]; N [N [N []]; T]]]
      (bind
        (bind
          (jump 3 [Syntax.bound 1; Syntax.bound 0])
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
    forall T,
    simple (cbv_type T) ->
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

       k@1<f@0>
       { f<x: ~(), k: ~[T]> =
         x@1<> }
    *)
    bind
      (jump 1 [Syntax.bound 0])
      [N [T]; N []]
      (jump 1 []).

  Axiom cbv_cps_A:
    forall T,
    cbv_cps A (@cbv_A (cbv_type T)).

  Goal
    forall T,
    simple (cbv_type T) ->
    exists2 U,
    typing [] A U & cbv_typing [] (@cbv_A (cbv_type T)) U.
  Proof.
    intros.
    exists (arrow F T).
    - apply typing_A.
    - repeat (simpl; try econstructor; auto; try rewrite cbv_type_F).
  Qed.

  Local Lemma axiom_eta_helper:
    forall b ts k x1 x2,
    x1 = jump (lift (length ts) 0 k) (low_sequence (length ts)) ->
    x2 = subst k 0 b ->
    axiom (bind b ts x1) x2.
  Proof.
    intros.
    rewrite H, H0.
    apply axiom_eta.
  Qed.

  Lemma lift_distributes_over_abstraction:
    forall i k t b,
    lift i k (abstraction t b) = abstraction t (lift i (S k) b).
  Proof.
    auto.
  Qed.

  Lemma lift_distributes_over_application:
    forall i k f x,
    lift i k (application f x) = application (lift i k f) (lift i k x).
  Proof.
    auto.
  Qed.

  (* Let's see if Felleisen's abbreviation holds in here... *)
  Goal
    (* This should work for *any* T, but... *)
    let T := F in
    forall b c,
    cbv_cps A b ->
    cbv_cps (A_def T) c ->
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
    rewrite lift_distributes_over_application in H0.
    rewrite lift_distributes_over_abstraction in H0.
    dependent destruction H0.
    rewrite lift_distributes_over_abstraction in H0_0.
    dependent destruction H0_0.
    rewrite_strat topdown (hints sigma) in H0_0.
    simpl in H0_0.
    dependent destruction H0_0.
    assert (b = lift 1 1 (lift 1 2 (@cbv_C (cbv_type T)))).
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
    cbv.
    symmetry.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; try lia.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    cbv.
    apply beta_bind_left.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    apply beta_bind_left.
    apply beta_bind_left.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_bind_left.
    apply smol_gc.
    repeat constructor; simpl; try lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_bind_left.
    apply smol_gc.
    repeat constructor; simpl; try lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; try lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; try lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; try lia.
    cbv.
    (* Typing is degenerate in the equational theory... we can use (ETA) now to
       fix this! *)
    etransitivity.
    transitivity
      (bind (bind (jump 2 [CPS.bound 0]) [N [N []]; N []]
        (jump 2 (low_sequence 2))) [void; void]
          (jump 1 [])).
    apply sema_sym.
    apply sema_bind_left.
    apply sema_axiom.
    cbv.
    apply axiom_eta_helper with (k := 0).
    reflexivity.
    reflexivity.
    etransitivity.
    apply sema_step.
    apply step_beta.
    replace ((bind (jump 2 [CPS.bound 0]) [
        N [N []]; N []]
        (jump 2 (low_sequence 2)))) with
      (context_right (jump 2 [CPS.bound 0]) [
        N [N []]; N []] Context.context_hole (jump 2 (low_sequence 2)));
    auto.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; try lia.
    cbv.
    reflexivity.
  Qed.

  Definition cbv_K {T U}: pseudoterm :=
    (* [|- K: ((T -> U) -> T) -> T] =
         [k: ~~(~(~([T], ~[U]), ~[T]), ~[T]) |- [K]]

       k@1<f@0>
       { f<x: ~(~([T], ~[U]), ~[T]), j: ~[T]> =
         x@2<v@0, j@1>
         { v<y: [T], h: ~[U]> =
           j@2<y@1>
         }
       }
    *)
    bind
      (jump 1 [Syntax.bound 0])
      [N [T]; N [N [T]; N [N [U]; T]]]
      (bind
        (jump 2 [Syntax.bound 1; Syntax.bound 0])
        [N [U]; T]
        (jump 2 [Syntax.bound 1])).

  Axiom cbv_cps_K:
    forall T U,
    cbv_cps K (@cbv_K (cbv_type T) (cbv_type U)).

  Goal
    forall T U,
    simple (cbv_type T) ->
    simple (cbv_type U) ->
    exists2 V,
    typing [] K V & cbv_typing [] (@cbv_K (cbv_type T) (cbv_type U)) V.
  Proof.
    intros.
    exists (arrow (arrow (arrow T U) T) T).
    - apply typing_K.
    - repeat (simpl; try econstructor; auto; try rewrite cbv_type_F).
  Qed.

  Goal
    forall b c,
    let T := F in
    let U := F in
    cbv_cps K b ->
    cbv_cps (K_def T U) c ->
    [b == c].
  Proof.
    intros.
    assert (b = @cbv_K (cbv_type T) (cbv_type U)).
    eapply cbv_cps_is_a_function.
    eassumption.
    apply cbv_cps_K.
    dependent destruction H1.
    clear H.
    unfold cbv_K.
    dependent destruction H0.
    rewrite lift_distributes_over_application in H0.
    rewrite lift_distributes_over_abstraction in H0.
    dependent destruction H0.
    rewrite lift_distributes_over_abstraction in H0_0.
    dependent destruction H0_0.
    rewrite_strat topdown (hints sigma) in H0_0.
    simpl in H0_0.
    dependent destruction H0_0.
    cbv in H0_0_1.
    dependent destruction H0_0_1.
    assert (b = lift 1 1 (lift 1 2 (@cbv_C (cbv_type T)))).
    eapply cbv_cps_is_a_function.
    eassumption.
    apply cbv_cps_lift.
    apply cbv_cps_lift.
    apply cbv_cps_C.
    dependent destruction H.
    clear H0_.
    rename H0_0_2 into H.
    rewrite_strat topdown (hints sigma) in H.
    simpl in H.
    dependent destruction H.
    cbv in H.
    dependent destruction H.
    rewrite_strat topdown (hints sigma) in H0.
    simpl in H0.
    dependent destruction H0.
    rewrite_strat topdown (hints sigma) in H0.
    simpl in H0.
    dependent destruction H0.
    cbv in H0_0.
    dependent destruction H0_0.
    cbv in H0_0_1, H0_0_2.
    dependent destruction H0_0_1.
    dependent destruction H0_0_2.
    rewrite_strat topdown (hints sigma) in H0_.
    simpl in H0_.
    (* Oh boy... sigma should get a better normal form here! *)
    replace A with (bound 0) in H0_ by admit.

    (* unfold cbv_C.
    unfold T, U.
    rewrite cbv_type_F.
    cbv.
    symmetry.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    simpl. *)
    admit.
  Admitted.

End CBV.

Section CBN.

  Require Import Local.Lambda.PlotkinCBN.

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

      [xs: As |- e: B] = xs: ~[As], k: [B] |- [e]
  *)

  Axiom cbn_type_F:
    cbn_type F = N [N []].

  Definition cbn_C {T}: pseudoterm :=
    (* [|- C: ~~T -> T] = [k: ~~(~~~(~~~(~[T], ~~()), ~~()), [T]) |- [C]]

       k@1<f@0>
       { f<x: ~~~(~~~(~[T], ~~()), ~~()), k: [T]> =
         x@2<j@0>
         { j<i: ~(~~~(~[T], ~~()), ~~())> =
           i@2<p@0, q@1>
           { p<l: ~~(~[T], ~~())> =
             l@1<n@0>
             { n<y: ~[T], o: ~~()> =
               o@1<z@0>
               { z<> =
                 y@1<k@5> }
             }
           }
           { q<m: ~()> =
             m@0<> } } }
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
            (jump 2 [Syntax.bound 1; Syntax.bound 0])
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
    forall T,
    simple (cbn_type T) ->
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

       k@1<f@0>
       { f<x: ~~~(), _: [T]> =
         x@2<k@0>
         { k<k: ~()> =
           k@0<> } }
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
    cbn_cps A (@cbn_A (cbn_type T)).

  Goal
    forall T: type,
    simple (cbn_type T) ->
    exists2 U,
    typing [] A U & cbn_typing [] (@cbn_A (cbn_type T)) U.
  Proof.
    intros.
    exists (arrow F T).
    - apply typing_A.
    - repeat (simpl; try econstructor; auto; try rewrite cbn_type_F).
  Qed.

  Notation bind := PlotkinCBV.CPS.bind.
  Notation jump := PlotkinCBV.CPS.jump.
  Notation bound := PlotkinCBV.CPS.bound.
  Notation void := PlotkinCBV.CPS.void.

  (* I hope I've done everything correctly...! *)
  Goal
    (* This should work for *any* T, still... *)
    let T := F in
    forall b c,
    cbn_cps A b ->
    cbn_cps (A_def T) c ->
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
    rewrite lift_distributes_over_application in H0.
    rewrite lift_distributes_over_abstraction in H0.
    dependent destruction H0.
    rewrite lift_distributes_over_abstraction in H0_0.
    dependent destruction H0_0.
    rewrite_strat topdown (hints sigma) in H0_0.
    simpl in H0_0.
    dependent destruction H0_0.
    assert (b = lift 1 1 (lift 1 2 (@cbn_C (cbn_type T)))).
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
    cbv.
    symmetry.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_beta.
    rewrite foobar_sound at 1.
    apply beta_ctxjmp.
    reflexivity.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; lia.
    cbv.
    etransitivity.
    apply sema_bind_right.
    apply sema_bind_left.
    apply sema_step.
    apply step_smol.
    apply smol_gc.
    repeat constructor; simpl; lia.
    cbv.
    (* Yey, typing is degenerate! *)
    admit.
  Admitted.

End CBN.
