(******************************************************************************)
(*   Copyright (c) 2019--2025 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import List.
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

Inductive kennedy_callback: Set :=
  | kennedy_halt
  | kennedy_call (f: nat) (t: CPS.pseudoterm) (c: CPS.pseudoterm).

Fixpoint kennedy_apply (K: kennedy_callback) (k n: nat): CPS.pseudoterm :=
  match K with
  (* (k, n) => k<n> *)
  | kennedy_halt =>
    CPS.jump (CPS.bound k) [CPS.bound (lift 1 k n)]
  (* (k, n) => f<n, k> { k<v: t> = b } *)
  | kennedy_call f t c =>
    CPS.bind (CPS.jump (CPS.bound f) [CPS.bound k; CPS.bound (lift 1 k n)]) [t] c
  end.

Local Coercion kennedy_apply: kennedy_callback >-> Funclass.

Inductive kennedy: term -> kennedy_callback -> CPS.pseudoterm -> Prop :=
  (* [x] K = K(x) *)
  | kennedy_bound:
    forall K n,
    (* Straightforward; the current continuation is 0 and thus everything else
       gets shifted by 1 up. *)
    kennedy (bound n) K (K 0 n)
  (* [\x.e] K = K(f) { f<x, k> = [e] (\z.k<z>) } *)
  | kennedy_abstraction:
    forall K t e c,
    (* We have to add the outer k variable to e; of course, we could also add
       it after the translation if we'd deem fit. *)
    kennedy (lift 1 1 e) kennedy_halt c ->
    kennedy (abstraction t e) K (CPS.bind
                                  (* The current continuation is 1, thus 0 here
                                     is bound and refers to f. *)
                                  (K 1 0)
                                  [CPS.void; CPS.void]
                                  (* Unchanged (we already added k). *)
                                  c)
  (* [f e] K = [f] (\f.
                       [e] (\v.
                               f<v, k> { k<x> = K(x) }
                           )
                   )

      In the term f<v, k> { ... }, i.e., the anchor, both *)
  (* | kennedy_application:
    forall (K: kennedy_callback) f e b c,
    (* Oh boy, a tricky one... *)
    kennedy (lift 2 0 e) (kennedy_call 0 CPS.void (K 0 1)) c ->
    kennedy (lift 1 0 f) *)
  .

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
  dependent destruction H0.
  dependent destruction H0.
  vm_compute.
  reflexivity.
  destruct n.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  dependent destruction H0.
  vm_compute.
  reflexivity.
  vm_compute in H.
  dependent destruction H.
  dependent destruction H0.
  dependent destruction H0.
  dependent destruction H0.
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

  Local Notation V := CPS.void.
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
