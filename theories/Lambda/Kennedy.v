(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.
Require Import Local.Lambda.Calculus.
Require Import Local.Lambda.PlotkinCBV.

Require Local.Residuals.

Import ListNotations.

(* The naive one-pass CPS translation, credited to Danvy and Filinsk, that
   Kennedy describes in his paper is given as follows:

     [-] -: Lambda.term -> (nat -> CPS.pseudoterm) -> CPS.pseudoterm

     [x] K = K(x) +----+    +------------+
                  |   \|/  \|/           |
     [\x.e] K = K(g) { g<x, k> = [e] (\z.k<z>) }

     [f e] K = [f] (\h.              (NOTE: g, h and v fresh)
                 [e] (\v.
                   h<v, k> { k<w> = K(w) }))
                              /|\     |
                               +------+

   This translation corresponds to Plotkin's CBV translation semantically, of
   course. Also, modulo a very minor change in the application rule, the above
   is also used in Appel's book (ch. 5.4), and it's given in Thielecke's thesis;
   namely, Appel's version is given by changing application to:

     [f e] K = [f] (\h.            (NOTE: inner k is outside the lambda now!)
                 [e] (\v.
                   h<v, k>)) { k<w> = K(w) }

   ...which, clearly, doesn't change the meaning of the term (assuming k always
   fresh, which is a given). We use Kennedy's version merely as the continuation
   is immediately bound, so it's a bit easier to deal with (as it remains as de
   Bruijn index zero).

   Kennedy provides an additional translation later in this paper which we also
   adapt, in that tail-calls are removed on the fly. This is done by modifying
   the above with the following rule:

     [\x.e] K = K(f) { f<x, k> = (e) k }

   Along with the introduction of an additional, mutually defined function:

     (-) -: Lambda.term -> var -> CPS.pseudoterm

     (x) k = k<x>

     (\x.e) k = k<g> { g<x, k> = (e) k }

     (e f) k = [e] (\h.[f] (\v.h<v, k>))

   The above function represents a tail context; note we use it for the toplevel
   term as well (since in the toplevel we don't know how to proceed in a sense,
   as the toplevel k stands for termination). Note we use the former translation
   when we know how to continue (in the case of an application) and the latter
   translation when the continuation is not yet bound.

   We would like to show that we can get from Plotkin's CBV translation into the
   optimized translation above by performing administrative jumps and garbage
   collection. This combination show result that this translation is adequate
   and that it gives a sound denotational semantics for the lambda calculus as
   Kennedy intended. *)

Inductive kennedy_code: Set :=
  | kennedy_halt
  | kennedy_then (e: term) (K: kennedy_code)
  | kennedy_call (f: nat) (j: nat) (K: kennedy_code).

(* Fixpoint kennedy_apply (K: kennedy_callback) (k n: nat): CPS.pseudoterm :=
  match K with
  (* (k, n) => k<n> *)
  | kennedy_halt =>
    CPS.jump (CPS.bound k) [CPS.bound (lift 1 k n)]
  (* (k, n) => f<n, k> { k<v: t> = b } *)
  | kennedy_call f t c =>
    CPS.bind (CPS.jump (CPS.bound f) [CPS.bound k; CPS.bound (lift 1 k n)]) [t] c
  end. *)

Axiom CNT: nat -> nat -> nat.
Axiom A: nat -> nat -> nat -> nat.
Axiom B: nat -> nat -> nat -> nat.

Inductive kennedy: term -> kennedy_code -> CPS.pseudoterm -> Prop :=
  (* [x] K = K(x) *)
  | kennedy_bound:
    forall K n b,
    kennedy_apply K 0 n b ->
    kennedy (bound n) K b

  (* [\x.e] K = K(f) { f<x, k> = [e] (\z.k<z>) } *)
  | kennedy_abstraction:
    forall K t e b c,
    kennedy_apply K 1 0 b ->
    kennedy (lift 1 1 e) kennedy_halt c ->
    kennedy (abstraction t e) K (CPS.bind b [CPS.void; CPS.void] c)

  (* [f e] K = [f] (\f.[e] (\v.f<v, k> { k<x> = K(x) })) *)
  | kennedy_application:
    forall K f e b,
    kennedy f (kennedy_then e K) b ->
    kennedy (application f e) K b

with kennedy_apply: kennedy_code -> nat -> nat -> CPS.pseudoterm -> Prop :=
  (* k, x => k<x> *)
  | kennedy_apply_halt:
    forall k n,
    kennedy_apply kennedy_halt k n (CPS.jump (var k) [var (lift 1 k n)])

  (* e, K; k, f => [e] (\v.f<v, k> { k<x> = K(x) }) *)
  | kennedy_apply_then:
    forall K e k f b,
    kennedy (lift k 0 e) (kennedy_call f k K) b ->
    kennedy_apply (kennedy_then e K) k f b

  (* f, j, K; k, v => f<v, k> { k<x> = K(x) } *)
  | kennedy_apply_call:
    forall K f j k v b,
    kennedy_apply K (CNT j k) 0 b ->
    kennedy_apply (kennedy_call f j K) k v
      (CPS.bind (CPS.jump (var (A j k f))
                          [var (j + k); var (B j k v)])
                [CPS.void]
                  b).

Local Notation HALT := kennedy_halt.
Local Notation THEN := kennedy_then.
Local Notation CALL := kennedy_call.

Scheme kennedy_ind2 := Minimality for kennedy Sort Prop
  with kennedy_apply_ind2 := Minimality for kennedy_apply Sort Prop.

Definition kennedy_well_behaved (K: kennedy_code) k n c: kennedy_apply K k n c -> Prop :=
  fun _ =>
    match K with
    | kennedy_halt =>
      forall j,
      j <> k ->
      j <> (lift 1 k n) ->
      CPS.not_free j c
    | _ =>
      True
    end.

Fixpoint code_context (K: kennedy_code): list term :=
  match K with
  | kennedy_halt => []
  | kennedy_then e J =>
    e :: code_context J
  | kennedy_call f j J =>
    var f :: map (lift j 0) (code_context J)
  end.

Lemma Forall_not_free_map_lift:
  forall xs i k,
  Forall (not_free k) xs <->
  Forall (not_free (i + k)) (map (lift i 0) xs).
Proof.
  induction xs; split; intros.
  - constructor.
  - constructor.
  - dependent destruction H.
    simpl; constructor.
    + replace (i + k) with (k + i + 0) by lia.
      apply not_free_lift.
      now rewrite Nat.add_0_r.
    + now apply IHxs.
  - dependent destruction H.
    simpl; constructor.
    + replace (i + k) with (k + i + 0) in H by lia.
      apply not_free_lift in H.
      now rewrite Nat.add_0_r in H.
    + now apply IHxs with i.
Qed.

Lemma kennedy_not_free_generalized:
  forall e K b,
  kennedy e K b ->
  forall i,
  Forall (not_free i) (e :: code_context K) <-> CPS.not_free (1 + i) b.
Proof.
  induction 1 using kennedy_ind2 with (P0 :=
    fun K k n c =>
      forall i,
      i >= k ->
      Forall (not_free i) (var n :: map (lift k 0) (code_context K)) <->
        CPS.not_free (1 + i) c
  ); repeat split; intros.
  - apply IHkennedy.
    + lia.
    + erewrite map_ext; intros.
      * now rewrite map_id.
      * now rewrite lift_zero_e_equals_e.
  - rewrite <- map_id.
    rewrite map_ext with (g := lift 0 0); intros.
    + simpl.
      apply IHkennedy.
      * lia.
      * assumption.
    + now rewrite lift_zero_e_equals_e.
  - simpl in IHkennedy, IHkennedy0.
    dependent destruction H1.
    constructor.
    + apply IHkennedy.
      * lia.
      * repeat constructor; try lia.
        (* Fix the offset as we're adding a binder. *)
        now apply Forall_not_free_map_lift.
    + repeat constructor.
    + simpl.
      apply IHkennedy0.
      repeat constructor.
      dependent destruction H1.
      replace (S (S n)) with (n + 1 + 1) by lia.
      apply not_free_lift.
      now rewrite Nat.add_comm.
  - simpl in IHkennedy0.
    dependent destruction H1.
    clear H1; simpl in H1_, H1_0.
    constructor.
    + constructor.
      apply IHkennedy0 in H1_0.
      dependent destruction H1_0.
      clear H1_0.
      replace (S (S i)) with (i + 1 + 1) in H1 by lia.
      apply not_free_lift in H1.
      now rewrite Nat.add_comm in H1.
    + apply IHkennedy in H1_.
      * dependent destruction H1_.
        (* Fix the offset as we're removing a binder. *)
        now apply Forall_not_free_map_lift with 1.
      * lia.
  - simpl in IHkennedy.
    dependent destruction H0.
    dependent destruction H0.
    apply IHkennedy.
    now repeat constructor.
  - simpl in IHkennedy.
    apply IHkennedy in H0.
    dependent destruction H0.
    dependent destruction H1.
    now repeat constructor.
  - dependent destruction H0.
    clear H1.
    dependent destruction H0.
    rename n0 into i.
    repeat constructor.
    + lia.
    + destruct (le_gt_dec k n).
      * replace (lift 1 k n) with (1 + n) by admit.
        lia.
      * replace (lift 1 k n) with n by admit.
        lia.
  - simpl.
    repeat constructor.
    dependent destruction H0.
    dependent destruction H0.
    dependent destruction H1.
    dependent destruction H1.
    clear H2.
    destruct (le_gt_dec k n).
    + replace (lift 1 k n) with (1 + n) in H1 by admit.
      lia.
    + replace (lift 1 k n) with n in H1 by admit.
      lia.
  - apply IHkennedy; simpl.
    dependent destruction H1.
    dependent destruction H2.
    auto.
  - simpl in IHkennedy |- *.
    apply IHkennedy in H1.
    dependent destruction H1.
    dependent destruction H2.
    auto.
  - dependent destruction H1.
    dependent destruction H2.
    (* TODO: use sigma! *)
    change (lift k 0 (var f): term) with (var (k + f): term) in H2;
    simpl in H2.
    constructor.
    + repeat constructor.
      * admit.
      * admit.
      * admit.
    + repeat constructor.
    + simpl.
      apply IHkennedy.
      * admit.
      * constructor.
        constructor.
        lia.
        (* So that's probably... 1 + j + k? *)
        admit.
  - simpl.
    dependent destruction H1.
    dependent destruction H1_.
    dependent destruction H1.
    dependent destruction H2.
    clear H3 H4; simpl in H1_0.
    apply IHkennedy in H1_0.
    + dependent destruction H1_0.
      constructor.
      * admit.
      * constructor.
        change (lift k 0 (var f): term) with (var (k + f): term);
        simpl.
        admit.
        rewrite map_map.
        rewrite map_ext with (g := lift (k + j) 0); intros.
        admit.
        rewrite lift_lift_simplification.
        reflexivity.
        lia.
        lia.
    + admit.
Admitted.

Lemma kennedy_not_free:
  forall e b,
  kennedy e kennedy_halt b ->
  forall i,
  not_free i e <-> CPS.not_free (1 + i) b.
Proof.
  intros.
  pose proof kennedy_not_free_generalized.
  specialize (H0 e kennedy_halt b H i).
  simpl in H0; destruct H0.
  split; intro.
  - apply H0; auto.
  - specialize (H1 H2).
    now inversion H1.
Qed.

Local Notation V := CPS.void.

Goal
  let e :=
    application (
      application
        (abstraction (arrow base base) 0)
        (abstraction base 0))
      42
  in
  exists2 b,
  kennedy e kennedy_halt b & CPS.free 43 b.
Proof.
  compute; eexists.
  constructor.
  constructor.
  constructor.
  constructor.
  vm_compute.
  constructor.
  constructor.
  constructor.
  change (lift (CNT 1 1) 0 (bound 42)) with
    (bound (CNT 1 1 + 42)).
  constructor.
  constructor.
  constructor.
  vm_compute.
  constructor.
  constructor.
  vm_compute.
  constructor.
  constructor.
  admit.
Admitted.

Goal
  let e := (application 42 51) in
  forall b c,
  cbv_cps e b ->
  kennedy e kennedy_halt c ->
  Reduction.star b c.
Proof.
  compute; intros.
  dependent destruction H.
  vm_compute in H, H0.
  dependent destruction H.
  dependent destruction H0.
  vm_compute.
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_right.
  apply Reduction.step_ctxjmp with (h := Context.context_hole).
  reflexivity.
  vm_compute.
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_bind_right.
  apply Reduction.step_gc.
  repeat constructor; auto.
  vm_compute.
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_ctxjmp with (h := Context.context_hole).
  reflexivity.
  vm_compute.
  eapply rt_trans.
  apply rt_step.
  apply Reduction.step_gc.
  repeat constructor; auto.
  vm_compute.
  dependent destruction H1.
  dependent destruction H1.
  dependent destruction H.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H.
  vm_compute.
  admit.
Admitted.

Goal
  forall t u n,
  let e := (abstraction t (abstraction u (bound n))) in
  forall b,
  cbv_cps e b ->
  forall c,
  kennedy e kennedy_halt c ->
  b = c.
Proof.
  compute; intros.
  dependent destruction H.
  dependent destruction H.
  destruct n.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H.
  vm_compute in H0.
  dependent destruction H0.
  dependent destruction H.
  vm_compute in H0.
  dependent destruction H0.
  dependent destruction H.
  vm_compute.
  reflexivity.
  destruct n.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H.
  vm_compute in H0.
  dependent destruction H0.
  dependent destruction H.
  vm_compute in H0.
  dependent destruction H0.
  dependent destruction H.
  vm_compute.
  reflexivity.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H.
  vm_compute in H0.
  dependent destruction H0.
  dependent destruction H.
  vm_compute in H0.
  dependent destruction H0.
  dependent destruction H.
  vm_compute.
  reflexivity.
Qed.

Section ModifiedCBV.

  Local Notation jump := Residuals.redexes_jump.

  Local Notation bind := Residuals.redexes_bind.

  Local Notation VAR d n :=
    (* [x] = k<x> *)
    (jump d (var 0) [var (1 + n)]) (only parsing).

  Local Notation ABS d b t1 t2 :=
    (* [\x.e] = k<f> { f<x, k> = [e] } *)
    (bind (jump d (var 1) [var 0]) [t1; t2] b) (only parsing).

  Local Notation APP b c t1 t2 :=
    (* [e f] = [e] { k<f> = [f] { k<v> = f<v, k> } } *)
    (bind b [t1] (bind c [t2]
      (jump false (var 1) [var 2; var 0]))) (only parsing).

  (* TODO: these lifts should be moved from source to target! *)

  Inductive modified_cbv_cps: bool -> term -> Residuals.redexes -> Prop :=
    | modified_cbv_cps_bound:
      forall d n,
      modified_cbv_cps d (var n) (VAR d n)
    | modified_cbv_cps_abstraction:
      forall d t e b,
      modified_cbv_cps false (lift 1 1 e) b ->
      modified_cbv_cps d (abstraction t e) (ABS d b CPS.void CPS.void)
    | modified_cbv_cps_application:
      forall d f x b c,
      modified_cbv_cps true (lift 1 0 f) b ->
      modified_cbv_cps true (lift 2 0 x) c ->
      modified_cbv_cps d (application f x) (APP b c CPS.void CPS.void).

  Goal
    forall d e r,
    modified_cbv_cps d e r ->
    cbv_cps e (Residuals.unmark r).
  Proof.
    induction 1; intros; simpl.
    - constructor.
    - now constructor.
    - now constructor.
  Qed.

  Local Coercion Syntax.bound: nat >-> CPS.pseudoterm.

  Goal
    let e := (application (application 0 1) (application 2 3)) in
    let x := (CPS.bind
                (CPS.jump 2 [var 0; var 3])
                [V]
                (CPS.bind
                   (CPS.jump 5 [var 0; var 6])
                   [V]
                   (CPS.jump 1 [var 2; var 0]))) in
    forall b,
    modified_cbv_cps false e b ->
    exists2 c,
    Residuals.residuals [] b b c &
      rt(Reduction.smol) (Residuals.unmark c) x.
  Proof.
    simpl; intros.
    dependent destruction H.
    vm_compute in *.
    dependent destruction H.
    dependent destruction H1.
    vm_compute in *.
    dependent destruction H.
    dependent destruction H0.
    dependent destruction H1_.
    dependent destruction H1_0.
    vm_compute.
    eexists.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    vm_compute.
    eapply rt_trans.
    apply rt_step.
    apply Reduction.smol_bind_left.
    apply Reduction.smol_gc.
    repeat constructor; simpl; auto.
    vm_compute.
    eapply rt_trans.
    apply rt_step.
    apply Reduction.smol_bind_left.
    apply Reduction.smol_gc.
    repeat constructor; simpl; auto.
    vm_compute.
    eapply rt_trans.
    apply rt_step.
    apply Reduction.smol_bind_right.
    apply Reduction.smol_bind_left.
    apply Reduction.smol_gc.
    repeat constructor; simpl; auto.
    vm_compute.
    eapply rt_trans.
    apply rt_step.
    apply Reduction.smol_bind_right.
    apply Reduction.smol_bind_left.
    apply Reduction.smol_gc.
    repeat constructor; simpl; auto.
    vm_compute.
    apply rt_refl.
  Qed.

  Goal
    let e := (abstraction base 1) in
    let x := (Syntax.bind
                (Syntax.jump 1 [var 0])
                [V; V]
                (Syntax.jump 0 [var 3])) in
    forall b,
    modified_cbv_cps false e b ->
    exists2 c,
    Residuals.residuals [] b b c &
      rt(Reduction.smol) (Residuals.unmark c) x.
  Proof.
    vm_compute; intros.
    dependent destruction x0.
    vm_compute in *.
    dependent destruction x0.
    vm_compute.
    eexists.
    constructor; simpl.
    constructor; simpl.
    constructor; simpl.
    simpl.
    apply rt_refl.
  Qed.

End ModifiedCBV.
