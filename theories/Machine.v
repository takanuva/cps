(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Reduction.
Require Import Local.Equational.
Require Import Local.Observational.

(* A runtime value, which is either a continuation closure, a suspended
   computation, or undefined. *)

Inductive value: Set :=
  (* We don't really need this in the named setting, but it's surely useful in
     the de Bruijn setting! With this we can propagate that a variable has been
     substituted by a free variable. *)
  | value_undefined
  (* We have higher-order terms in this formalization, so we may have suspended
     computations; these, however, will never appear in pseudoterms which are
     proper terms. *)
  | value_suspend (p: list value) (c: pseudoterm)
  (* Continuations in memory. *)
  | value_closure (p: list value) (ts: list pseudoterm) (c: pseudoterm).

Local Notation U := value_undefined.

Local Notation "< r ; \ ts : c >" :=
  (value_closure r ts c) (only printing, format "< r ;  \ ts :  c >").

(* A heap is a named list (like an environment) associating names to runtime
   values. It is called an environment by both Appel and Kennedy. *)

Definition heap: Set :=
  list value.

(* A configuration is just a tuple of a command and a heap, which is what the
   machine semantics reasons about. *)

Definition configuration: Set :=
  pseudoterm * heap.

(* Given a heap s, we may write s(x) to get the value of x in it. Ideally, x
   should just be a de Bruijn index, which would have an obvious meaning, but
   I've messed things up. *)

Definition heap_get (x: pseudoterm) (r: heap): value :=
  (* As of now, there are no constants or values... however, our structure
     allows for higher-order terms, and, if this is the case, we should thunk
     our computations with this heap for later use. TODO: add constants. *)
  match x with
  | bound n =>
    nth n r U
  | jump _ _ =>
    value_suspend r x
  | bind _ _ _ =>
    value_suspend r x
  | _ =>
    (* ...so simply ignore those. *)
    U
  end.

(* This definition is denoted as (s, ys = r(xs)), i.e., we are extending a heap
   s by naming values ys as what xs mean in the heap r. So, if some x is not
   defined in r, then accordingly y won't be defined in the resulting heap.

   Please note that parameters are written from right to left, but arguments to
   jumps are written from left to write! *)

Definition heap_append (xs: list pseudoterm) (r s: heap): heap :=
  fold_left (fun acc x => heap_get x r :: acc) xs s.

(* A predicate that says that a configuration has successfully reached it's
   final point, and that it won't reduce any further. This is signaled by a
   command that jumps to a variable that's not in the heap (i.e., a free
   variable). *)

Definition configuration_final (c: configuration): Prop :=
  exists k xs r,
  c = (jump (bound k) xs, r) /\ nth k r U = U.

(* Big-step abstract machine semantics for the CPS-calculus. This was derived
   directly from Kennedy's paper, slightly adapting it to use any free variable
   as a signal of termination rather than using a distinguished "halt". This
   represents the trace of an interpreter as the one in Appel's book (see
   Chapter 3), also similar to what's being done in the CertiCoq project. This
   is meant to be an "implementation-friendly" semantics. *)

Inductive big: configuration -> Prop :=
  (*
      r(k) is undefined
    --------------------- (M-HALT)
        (k<xs>, r) \/
  *)
  | big_halt:
    forall k xs r,
    nth k r U = U ->
    big (jump k xs, r)

  (*
      r(k) = <s, \ys.c>       <c, s, ys = r(xs)> \/
    ------------------------------------------------- (M-JUMP)
                       <k<xs>, r> \/
  *)
  | big_jump:
    forall r s c k xs ts,
    item (value_closure s ts c) r k ->
    length xs = length ts ->
    big (c, heap_append xs r s) ->
    big (jump k xs, r)

  (*
      <b, r, k = <r, \ys.c>> \/
    ----------------------------- (M-BIND)
       <b { k<ys> = c }, r> \/
  *)
  | big_bind:
    forall b ts c r,
    big (b, value_closure r ts c :: r) ->
    big (bind b ts c, r)

  (*
    TODO: how to properly describe this hacky rule? This should only be needed
    in case we're working with higher-order terms. This rule should, however,
    fix the dissonance between proper terms and higher-order pseudoterms.
  *)
  | big_high:
    forall r s c k,
    item (value_suspend s c) r k ->
    big (c, s) ->
    big (bound k, r).

(* Quick test! *)

Goal
  big (ex1, []) (* 3 *).
Proof.
  unfold ex1.
  do 2 apply big_bind.
  eapply big_jump.
  - constructor.
    constructor.
  - simpl.
    reflexivity.
  - simpl.
    eapply big_jump.
    + constructor.
      constructor.
    + simpl.
      reflexivity.
    + simpl.
      eapply big_jump.
      * constructor.
        constructor.
        constructor.
      * simpl.
        reflexivity.
      * apply big_halt.
        simpl; reflexivity.
Qed.

Fixpoint context_to_heap h s: heap :=
  match h with
  | context_hole =>
    s
  | context_left r ts c =>
    context_to_heap r (value_closure s ts c :: s)
  | context_right b ts r =>
    (* We don't really care about this one. *)
    []
  end.

Local Notation C2H := context_to_heap.

Lemma context_to_heap_size:
  forall h,
  static h ->
  forall r,
  exists2 s,
  C2H h r = s ++ r & #h = length s.
Proof.
  induction 1; simpl; intros.
  - exists []; eauto.
  - edestruct IHstatic as (s, ?, ?).
    rewrite H0.
    eexists (s ++ [_]).
    + rewrite <- app_assoc; simpl.
      reflexivity.
    + rewrite app_length; simpl.
      lia.
Qed.

Lemma big_static_context:
  forall h,
  static h ->
  forall c r,
  (* We'll need it both ways! *)
  big (c, C2H h r) <-> big (h c, r).
Proof.
  split; intros.
  (* Case: if. *)
  - generalize dependent r.
    induction H; simpl; intros.
    + assumption.
    + constructor.
      apply IHstatic.
      assumption.
  (* Case: then. *)
  - generalize dependent r.
    induction H; simpl; intros.
    + assumption.
    + dependent destruction H0.
      apply IHstatic.
      assumption.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO: move this definition somewhere else. I think I've defined this thing
   elsewhere too, also in the wrong place... oh well... *)

Definition eval a n: Prop :=
  comp rt(head) converges a n.

(* This is clearly not a first-order term, but it's valid in our higher-order
   formulation...

   j@0<k@1<>>
   { j<x> =
     x@0 }

   And I expect that eval will reach a normal form, halting at k... *)

Example ohno: pseudoterm :=
  bind
    (jump 0 [jump 1 []])
    [base]
    0.

Goal
  eval ohno 0.
Proof.
  eexists.
  - constructor.
    unfold ohno.
    replace (bind (jump 0 [jump 1 []]) [base] 0) with
      (context_hole (bind (context_hole (jump 0 [jump 1 []])) [base] 0)); auto.
    constructor.
    + constructor.
    + constructor.
    + reflexivity.
  - simpl.
    compute.
    constructor.
    constructor.
Qed.

Goal
  big (ohno, []).
Proof.
  constructor.
  eapply big_jump.
  constructor.
  reflexivity.
  eapply big_high.
  constructor.
  apply big_halt.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

Class proper (f: nat -> pseudoterm -> pseudoterm): Prop := {
  proper_respects_structure:
    forall x k,
    f k x = traverse f k x;
  proper_preserves_bound:
    forall k n,
    n < k -> f k n = n;
  proper_avoids_capture:
    forall k n,
    f (S k) (S n) = lift 1 0 (f k n)
}.

Global Instance lift_proper: forall i, proper (lift i).
Proof.
  constructor; intros.
  - reflexivity.
  - rewrite lift_bound_lt; try lia.
    reflexivity.
  - destruct (le_gt_dec k n).
    + rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      rewrite lift_bound_ge; try lia.
      f_equal; lia.
    + rewrite lift_bound_lt; try lia.
      rewrite lift_bound_lt; try lia.
      rewrite lift_bound_ge; try lia.
      reflexivity.
Qed.

Global Hint Resolve lift_proper: cps.

Global Instance subst_proper: forall x, proper (subst x).
Proof.
  constructor; intros.
  - reflexivity.
  - rewrite subst_bound_lt; try lia.
    reflexivity.
  - destruct (lt_eq_lt_dec k n) as [ [ ? | ? ] | ? ].
    + rewrite subst_bound_gt; try lia.
      rewrite subst_bound_gt; try lia.
      rewrite lift_bound_ge; try lia.
      f_equal; lia.
    + rewrite subst_bound_eq; try lia.
      rewrite subst_bound_eq; try lia.
      rewrite lift_lift_simplification; try lia.
      reflexivity.
    + rewrite subst_bound_lt; try lia.
      rewrite subst_bound_lt; try lia.
      rewrite lift_bound_ge; try lia.
      reflexivity.
Qed.

Global Hint Resolve subst_proper: cps.

Global Instance apply_parameters_proper:
  forall xs, proper (apply_parameters xs).
Proof.
  constructor; intros.
  - generalize dependent k.
    induction x using pseudoterm_deepind; simpl; intros.
    + apply apply_parameters_type.
    + apply apply_parameters_prop.
    + apply apply_parameters_base.
    + apply apply_parameters_void.
    + reflexivity.
    + rewrite apply_parameters_distributes_over_negation.
      f_equal.
      list induction over H.
      do 2 rewrite traverse_list_length.
      apply H.
    + rewrite apply_parameters_distributes_over_jump.
      f_equal.
      * apply IHx.
      * list induction over H.
    + rewrite apply_parameters_distributes_over_bind.
      f_equal.
      * apply IHx1.
      * list induction over H.
        do 2 rewrite traverse_list_length.
        apply H.
      * apply IHx2.
  - rewrite apply_parameters_bound_lt; try lia.
    reflexivity.
  - destruct (le_gt_dec k n).
    + destruct (le_gt_dec (k + length xs) n).
      * rewrite apply_parameters_bound_gt; try lia.
        rewrite apply_parameters_bound_gt; try lia.
        rewrite lift_bound_ge; try lia.
        f_equal; lia.
      * (* TODO: refactor me, please. I'm so tired. *)
        assert (exists x, item x xs (n - k)) as (x, ?).
        apply item_exists.
        lia.
        replace (S n) with (S k + (S n - S k)); try lia.
        rewrite apply_parameters_bound_in with (x := x); try lia.
        replace n with (k + (n - k)); try lia.
        rewrite apply_parameters_bound_in with (x := x); try lia.
        rewrite lift_lift_simplification; try lia.
        reflexivity.
        assumption.
        assumption.
    + rewrite apply_parameters_bound_lt; try lia.
      rewrite apply_parameters_bound_lt; try lia.
      rewrite lift_bound_ge; try lia.
      reflexivity.
Qed.

Global Hint Resolve apply_parameters_proper: cps.

Definition ids (k: nat) (c: pseudoterm): pseudoterm :=
  c.

Global Hint Unfold ids: cps.

Global Instance ids_proper: proper ids.
Proof.
  unfold ids.
  constructor; intros.
  - generalize dependent k.
    induction x using pseudoterm_deepind; simpl; intros.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal.
      list induction over H.
    + f_equal; auto.
      list induction over H.
    + f_equal; auto.
      list induction over H.
  - reflexivity.
  - rewrite lift_bound_ge; try lia.
    reflexivity.
Qed.

Global Hint Resolve ids_proper: cps.

Goal
  forall f,
  `{proper f} ->
  forall p k n,
  f (p + k) (p + n) = lift p 0 (f k n).
Proof.
  induction p; simpl; intros.
  - rewrite lift_zero_e_equals_e.
    reflexivity.
  - rewrite proper_avoids_capture.
    rewrite IHp.
    rewrite lift_lift_simplification; try lia.
    reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

Inductive big_at_time: configuration -> nat -> Prop :=
  | big_at_time_halt:
    forall k xs r,
    nth k r U = U ->
    big_at_time (jump k xs, r) 0
  | big_at_time_jump:
    forall r s c k xs ts t,
    item (value_closure s ts c) r k ->
    length xs = length ts ->
    big_at_time (c, heap_append xs r s) t ->
    big_at_time (jump k xs, r) (S t)
  | big_at_time_bind:
    forall b ts c r t,
    big_at_time (b, value_closure r ts c :: r) t ->
    big_at_time (bind b ts c, r) (S t)
  | big_at_time_high:
    forall r s c k t,
    item (value_suspend s c) r k ->
    big_at_time (c, s) t ->
    big_at_time (bound k, r) t.

Lemma big_has_time:
  forall c,
  big c <-> exists t, big_at_time c t.
Proof.
  split; intros.
  - induction H.
    + eexists.
      apply big_at_time_halt; auto.
    + destruct IHbig as (t, ?); eexists.
      eapply big_at_time_jump; eauto.
    + destruct IHbig as (t, ?); eexists.
      eapply big_at_time_bind; eauto.
    + destruct IHbig as (t, ?); eexists.
      eapply big_at_time_high; eauto.
  - destruct H as (t, ?).
    induction H.
    + apply big_halt; auto.
    + eapply big_jump; eauto.
    + eapply big_bind; eauto.
    + eapply big_high; eauto.
Qed.

(*
  In order to show soundness of the machine semantics, we first have to show
  some correspondence between heaps. This is a bit awkward in here as we are in
  a de Bruijn setting and because we allow for high order terms, but it may be
  simplified as such:

  TODO: describe the relations.
*)

Definition corresponding_valueF :=
  fun p (f: forall m, fst (fst m) < fst (fst p) -> Prop) =>
    let t := fst (fst p) in
    let v1 := snd (fst p) in
    let v2 := snd p in
    match v1, v2 with
    | value_closure p ts c, value_closure q us b =>
      length ts = length us /\
        forall m r s xs ys (H: m < t) g k,
        `{proper g} ->
        xs = map (traverse g k) ys ->
        big_at_time (c, heap_append xs r p) m ->
        length xs = length ts ->
        Forall2 (fun x y =>
                  f (m, heap_get x r, heap_get y s) H) xs ys ->
        big_at_time (b, heap_append ys s q) m
    | value_suspend r b, value_suspend s c =>
      forall m,
      m <= t ->
      big_at_time (b, r) m ->
      big_at_time (c, s) m
    | U, U =>
      True
    | _, _ =>
      False
    end.

Definition corresponding_valueP (p: nat * value * value): Prop :=
  let wf := well_founded_ltof _ (fun p => fst (fst p)) in
  Fix wf _ corresponding_valueF p.

Definition corresponding_value t: relation value :=
  fun x y =>
    corresponding_valueP (t, x, y).

Lemma corresponding_value_isorec:
  forall t v1 v2,
  corresponding_value t v1 v2 <->
    corresponding_valueF (t, v1, v2) (fun m H => corresponding_valueP m).
Proof.
  intros.
  apply Fix_equiv with (r := fun _ => iff); intros.
  clear t v1 v2; destruct x as ((t, v1), v2).
  split; intros.
  - destruct v1; destruct v2; try contradiction.
    + assumption.
    + assumption.
    + destruct H0; split; intros.
      * assumption.
      * apply H1 with r xs H2 g0 k; auto.
        clear H0 H1 H3 H4 H5 H6.
        induction H7; constructor; auto.
        apply H; auto.
  - destruct v1; destruct v2; try contradiction.
    + assumption.
    + assumption.
    + destruct H0; split; intros.
      * assumption.
      * apply H1 with r xs H2 g0 k; auto.
        clear H0 H1 H3 H4 H5 H6.
        induction H7; constructor; auto.
        apply H; auto.
Qed.

Lemma corresponding_value_inv:
  forall t,
  forall P: value -> value -> Prop,
  (forall p ts c q us b,
     length ts = length us ->
     (forall m r s xs ys (H: m < t) g k,
        `{proper g} ->
        xs = map (traverse g k) ys ->
        big_at_time (c, heap_append xs r p) m ->
        length xs = length ts ->
        Forall2 (fun x y =>
          corresponding_value m (heap_get x r) (heap_get y s)) xs ys ->
        big_at_time (b, heap_append ys s q) m) ->
        P (value_closure p ts c) (value_closure q us b)) ->
  (forall r b s c,
    (forall m,
       m <= t ->
       big_at_time (b, r) m ->
       big_at_time (c, s) m) ->
    P (value_suspend r b) (value_suspend s c)) ->
  P U U ->
  forall x y,
  corresponding_value t x y -> P x y.
Proof.
  intros.
  destruct x; destruct y; try contradiction.
  - assumption.
  - apply H0; intros.
    apply H2; auto with arith.
  - rewrite corresponding_value_isorec in H2; simpl in H2.
    destruct H2.
    apply H; intros.
    + assumption.
    + apply H3 with r xs g k; auto.
Qed.

Definition corresponding (f: nat -> pseudoterm -> pseudoterm) r s k t :=
  forall n: nat,
  corresponding_value t (heap_get (f k n) r) (heap_get n s).

Lemma heap_get_heap_append_simplification:
  forall xs n r s,
  n >= length xs ->
  heap_get n (heap_append xs r s) = heap_get (n - length xs) s.
Proof.
  induction xs; intros.
  - simpl.
    replace (n - 0) with n; try lia.
    reflexivity.
  - simpl in H.
    destruct n; try lia.
    simpl in IHxs |- *.
    rewrite IHxs; try lia.
    replace (S n - length xs) with (1 + (n - length xs)); try lia.
    simpl; reflexivity.
Qed.

(* TODO: rename me. *)

Lemma foobar:
  forall t r s xs ys,
  Forall2
    (fun x y => corresponding_valueP (t, heap_get x r, heap_get y s))
     xs ys ->
  forall p q n,
  n < length xs ->
  corresponding_value t (heap_get n (heap_append xs r p))
    (heap_get n (heap_append ys s q)).
Proof.
  intros until 1.
  dependent induction H; intros.
  - inversion H.
  - simpl in H1.
    replace (heap_append (x :: l) r p) with
      (heap_append l r (heap_get x r :: p)); auto.
    replace (heap_append (y :: l') s q) with
      (heap_append l' s (heap_get y s :: q)); auto.
    destruct (Nat.eq_dec n (length l)).
    + apply Forall2_length in H0.
      rewrite heap_get_heap_append_simplification; try lia.
      rewrite heap_get_heap_append_simplification; try lia.
      replace (n - length l) with 0; try lia.
      replace (n - length l') with 0; try lia.
      simpl; exact H.
    + apply IHForall2.
      lia.
Qed.

Lemma corresponding_value_refl_aux:
  forall t,
  (forall m c f r s k,
     `{proper f} ->
     m <= t ->
     corresponding f r s k m ->
     big_at_time (f k c, r) m ->
     big_at_time (c, s) m) ->
  reflexive (corresponding_value t).
Proof.
  intros t ?H.
  induction t using lt_wf_ind.
  (* First, fix this inductive principle... *)
  assert (forall m, m < t -> reflexive (corresponding_value m)); intros.
  - apply H0; intros; auto.
    apply H with f r k; auto.
    lia.
  (* There we go. *)
  - clear H0.
    intro v; destruct v; simpl.
    + constructor.
    + intros m ?H ?H.
      assumption.
    + (* The main case is here. *)
      rewrite corresponding_value_isorec; simpl.
      split; intros; auto.
      simpl in H0.
      replace c with (ids 0 c) in H1; auto.
      apply H with ids (heap_append xs r p) (length xs + 0);
        eauto with arith cps.
      intro n; unfold ids.
      destruct (le_gt_dec (length xs) n).
      * apply Forall2_length in H6.
        rewrite heap_get_heap_append_simplification; try lia.
        rewrite heap_get_heap_append_simplification; try lia.
        rewrite H6; apply H1.
        assumption.
      * apply foobar; auto.
Qed.

Lemma corresponding_lift:
  forall x r t,
  (forall m c f r s k,
     `{proper f} ->
     m <= t ->
     corresponding f r s k m ->
     big_at_time (f k c, r) m ->
     big_at_time (c, s) m) ->
  corresponding (lift 1) (x :: r) r 0 t.
Proof.
  intros; intro n.
  rewrite lift_bound_ge; try lia.
  apply corresponding_value_refl_aux; auto.
Qed.

Lemma corresponding_extension:
  forall f r s k t,
  forall P: `{proper f},
  corresponding f r s k t ->
  (forall m c f' r' s' k',
     `{proper f'} ->
     m <= t ->
     corresponding f' r' s' k' m ->
     big_at_time (f' k' c, r') m ->
     big_at_time (c, s') m) ->
  forall x y,
  corresponding_value t x y ->
  corresponding f (x :: r) (y :: s) (S k) t.
Proof.
  intros; intro n.
  destruct n.
  - rewrite proper_preserves_bound; try lia.
    simpl; assumption.
  - clear H1.
    specialize (H n).
    rewrite proper_avoids_capture.
    dependent destruction H using corresponding_value_inv.
    + destruct (f k n); try discriminate.
      simpl in x0, x |- *.
      rewrite <- x.
      rewrite <- x0.
      rewrite corresponding_value_isorec; simpl.
      split; eauto.
    + rename r0 into r', s0 into s'.
      destruct (f k n); try discriminate.
      * rewrite lift_bound_ge; try lia.
        simpl in x, x0 |- *.
        rewrite <- x.
        rewrite <- x0.
        intros m ?H ?H.
        simpl in H0.
        apply H; auto.
      * simpl in x, x0 |- *.
        rewrite <- x.
        intros m ?H ?H.
        simpl in H1.
        apply H; auto.
        dependent destruction x0.
        apply H0 with (lift 1) (x1 :: r) 0; auto with cps.
        apply corresponding_lift; intros.
        eapply H0; eauto with arith.
      * simpl in x, x0 |- *.
        rewrite <- x.
        intros m ?H ?H.
        simpl in H1.
        apply H; auto.
        dependent destruction x0.
        apply H0 with (lift 1) (x1 :: r) 0; auto with cps.
        apply corresponding_lift; intros.
        eapply H0; eauto with arith.
    + simpl in x |- *.
      rewrite <- x.
      destruct (f k n);
        try discriminate;
        try constructor.
      simpl in x0 |- *.
      rewrite <- x0.
      constructor.
Qed.

Lemma corresponding_value_decrease:
  forall t v u,
  corresponding_value t v u ->
  forall m,
  m < t ->
  corresponding_value m v u.
Proof.
  intros until 1.
  dependent destruction H using corresponding_value_inv; intros.
  - rewrite corresponding_value_isorec; simpl.
    split; intros.
    + assumption.
    + eapply H0.
      * simpl in H2; lia.
      * eassumption.
      * eassumption.
      * eassumption.
      * assumption.
      * assumption.
  - intros o ?H ?H.
    simpl in H1.
    apply H; eauto with arith.
  - constructor.
Qed.

Lemma corresponding_decrease:
  forall f r s k t,
  corresponding f r s k t ->
  forall m,
  m < t ->
  corresponding f r s k m.
Proof.
  intros; intro n.
  apply corresponding_value_decrease with t; auto.
Qed.

Local Hint Resolve corresponding_decrease: cps.

Goal
  forall f r s k t,
  `{proper f} ->
  corresponding f r s k t ->
  (forall m c,
     m <= t ->
     big_at_time (f k c, r) m ->
     big_at_time (c, s) m) ->
  forall c,
  corresponding_value t (heap_get (f k c) r) (heap_get c s).
Proof.
  intros.
  rewrite proper_respects_structure; simpl.
  destruct c.
  - simpl.
    constructor.
  - simpl.
    constructor.
  - simpl.
    constructor.
  - simpl.
    constructor.
  - specialize (H0 n); simpl.
    assumption.
  - simpl.
    constructor.
  - intros m ?H ?H; simpl in H2.
    apply H1; auto.
    rewrite proper_respects_structure; simpl.
    assumption.
  - intros m ?H ?H; simpl in H2.
    apply H1; auto.
    rewrite proper_respects_structure; simpl.
    assumption.
Qed.

Local Lemma technical1:
  forall f r s k t,
  `{proper f} ->
  corresponding f r s k t ->
  (forall m c,
     m <= t ->
     big_at_time (f k c, r) m ->
     big_at_time (c, s) m) ->
  forall xs,
  Forall2
    (fun x y => corresponding_value t (heap_get x r) (heap_get y s))
    (map (traverse f k) xs) xs.
Proof.
  intros.
  induction xs.
  - simpl.
    constructor.
  - simpl.
    constructor.
    + clear IHxs xs.
      destruct a.
      * simpl; constructor.
      * simpl; constructor.
      * simpl; constructor.
      * simpl; constructor.
      * specialize (H0 n); simpl.
        assumption.
      * simpl; constructor.
      * rewrite <- proper_respects_structure.
        rewrite proper_respects_structure; simpl.
        intros m ?H ?H.
        simpl in H2.
        apply H1; auto.
        rewrite proper_respects_structure; simpl.
        assumption.
      * rewrite <- proper_respects_structure.
        rewrite proper_respects_structure; simpl.
        intros m ?H ?H.
        simpl in H2.
        apply H1; auto.
        rewrite proper_respects_structure; simpl.
        assumption.
    + assumption.
Qed.

Local Lemma technical2:
  forall f t,
  `{proper f} ->
  (forall m c f' r' s' k',
     `{proper f'} ->
     m <= t ->
     corresponding f' r' s' k' m ->
     big_at_time (f' k' c, r') m ->
     big_at_time (c, s') m) ->
  forall r' s' xs ys,
  Forall2
    (fun x y => corresponding_value t (heap_get x r') (heap_get y s'))
    xs ys ->
  forall r s k,
  corresponding f r s k t ->
  corresponding f (heap_append xs r' r) (heap_append ys s' s) (length xs + k) t.
Proof.
  intros.
  dependent induction H1; intros.
  - simpl.
    assumption.
  - replace (heap_append (x :: l) r' r) with
      (heap_append l r' (heap_get x r' :: r)); auto.
    replace (heap_append (y :: l') s' s) with
      (heap_append l' s' (heap_get y s' :: s)); auto.
    simpl.
    replace (S (length l + k)) with (length l + S k); try lia.
    apply IHForall2.
    apply corresponding_extension; auto.
Qed.

Lemma corresponding_heaps_preserve_semantics:
  forall f r s k t,
  forall P: `{proper f},
  corresponding f r s k t ->
  forall c,
  big_at_time (traverse f k c, r) t ->
  big_at_time (c, s) t.
Proof.
  intros.
  generalize dependent s.
  generalize dependent r.
  generalize dependent k.
  generalize dependent f.
  generalize dependent c.
  induction t using lt_wf_ind.
  destruct c; intros.
  (* Case: type. *)
  - inversion H0.
  (* Case: prop. *)
  - inversion H0.
  (* Case: base. *)
  - inversion H0.
  (* Case: void. *)
  - inversion H0.
  (* Case: bound. *)
  - simpl in H0.
    remember (f k n) as x.
    destruct x.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + inversion H0.
    + rename n0 into m.
      specialize (H1 n).
      rewrite <- Heqx in H1; simpl in H1.
      dependent destruction H0.
      rename s into r', s0 into s.
      apply nth_item with (y := U) in H0.
      rewrite H0 in H2.
      dependent destruction H2 using corresponding_value_inv.
      rename c0 into b, s0 into s'.
      apply big_at_time_high with s' b.
      * apply item_nth with U; auto.
        congruence.
      * apply H2; auto with arith.
    + inversion H0.
    + specialize (H1 n).
      rewrite <- Heqx in H1; simpl in H1.
      dependent destruction H1 using corresponding_value_inv.
      rename s0 into s'.
      apply big_at_time_high with s' c.
      * apply item_nth with U; auto.
        congruence.
      * apply H1; auto.
    + specialize (H1 n).
      rewrite <- Heqx in H1; simpl in H1.
      dependent destruction H1 using corresponding_value_inv.
      rename s0 into s'.
      apply big_at_time_high with s' c.
      * apply item_nth with U; auto.
        congruence.
      * apply H1; auto.
  (* Case: negation. *)
  - inversion H0.
  (* Case: jump. *)
  - simpl in H0.
    dependent destruction H0.
    + destruct c; try discriminate.
      rename k0 into j.
      apply big_at_time_halt.
      specialize (H1 n); simpl in H1.
      simpl in x; rewrite <- x in H1.
      simpl in H1; rewrite H0 in H1.
      dependent destruction H1 using corresponding_value_inv.
      congruence.
    + destruct c; try discriminate.
      rename k0 into j, c0 into c, s into r', s0 into s.
      (* ... *)
      simpl in x.
      assert (corresponding_value (S t) (heap_get (f k n) r) (heap_get n s)) by
        auto.
      apply nth_item with (y := U) in H0.
      (*
        Since we have...

          <f(n<x>), r> @ 1+t

        By inversion, there are r', y and c such that...

          r(f(n)) = <r', \y.c>

        And...

          <c, r', y = r(f(x))> @ t

        We also know that...

          r corresponds to s through f at 1+t

        We want to show that...

          <n<x>, s> @ 1+t

        So we need to show that there are s' and b such that...

          s(n) = <s', \y.b>

        And then...

          <b, s', y = s(x)> @ t

      *)
      rewrite <- x in H4; simpl in H4.
      rewrite H0 in H4.
      dependent destruction H4 using corresponding_value_inv.
      rename q into s'.
      eapply big_at_time_jump.
      * eapply item_nth; eauto.
        congruence.
      * rewrite map_length in H1.
        congruence.
      * eapply H5; eauto.
        apply technical1; eauto with cps.
        intros m d ?H ?H.
        rewrite proper_respects_structure in H7.
        apply H with f k r; eauto with arith cps.
  (* Case: bind. *)
  - simpl in H0.
    dependent destruction H0.
    apply big_at_time_bind.
    eapply H; eauto.
    apply corresponding_extension; intros.
    + assumption.
    + apply corresponding_decrease with (S t); auto.
    + apply H with f' k' r'; auto with arith.
      rewrite proper_respects_structure in H5.
      assumption.
    + rewrite corresponding_value_isorec; simpl.
      split; intros.
      * rewrite traverse_list_length.
        reflexivity.
      * simpl in H2.
        rewrite traverse_list_length in H6.
        rename r0 into r', s0 into s'.
        eapply H with (f := f); eauto.
        rewrite <- H6, Nat.add_comm.
        apply technical2; eauto with cps; intros.
        rewrite proper_respects_structure in H11.
        eapply H; eauto with arith.
Qed.

Lemma corresponding_value_refl:
  forall t,
  reflexive (corresponding_value t).
Proof.
  intros.
  apply corresponding_value_refl_aux; intros.
  eapply corresponding_heaps_preserve_semantics.
  - eassumption.
  - eassumption.
  - rewrite proper_respects_structure in H2.
    assumption.
Qed.

(* This lemma may be a bit awkward in the de Bruijn setting, but it should be
   straightforward in the named setting. What we'd like to show in here is that
   the following rule is admissible:

             H is static      (H[c[xs/ys]] { k<ys> = c }, r) \/
           ------------------------------------------------------
                       (H[k<xs>] { k<ys> = c }, r) \/

  ...TODO...

  We now define a new heap s such that:

    s := (r, k = \ys.c, H)

  And the desired proof is as follow:

                                (c[xs/ys], s) \/
                           -------------------------
                             (c, r, ys = s(xs)) \/

  Of course, c can't refer to k neither the variables in the domain of H.

  ...TODO...
*)

Lemma backwards_head_preservation:
  forall h,
  static h ->
  forall xs ts,
  length xs = length ts ->
  forall c r,
  big (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c))) ts c, r) ->
  big (bind (h (jump #h xs)) ts c, r).
Proof.
  intros.
  (* First we move our command c into the heap. *)
  dependent destruction H1.
  constructor.
  (* Then we proceed to move the enclosing context. *)
  apply <- big_static_context in H1; auto.
  apply big_static_context; auto.
  (* There's only one way to go from here. *)
  eapply big_jump with (s := r) (ts := ts) (c := c).
  - (* We simply have to skip h now! On paper this should be obvious... *)
    clear H0 H1 xs.
    edestruct context_to_heap_size as (s, ?, ?); eauto.
    rewrite H0; clear H0.
    rewrite H1; clear H1.
    clear H h.
    induction s; eauto with cps.
  - assumption.
  - (* Hmm... *)
    remember (C2H h (value_closure r ts c :: r)) as s.
    apply big_has_time in H1; destruct H1 as (t, ?H).
    apply big_has_time; exists t.
    admit.
Admitted.

Lemma big_is_preserved_backwards_by_head:
  forall c1 c2,
  head c1 c2 ->
  forall r,
  big (c2, r) -> big (c1, r).
Proof.
  intros until 1.
  (* TODO: we could make an induction principle for this, as if we had a
     head_bind_left constructor... *)
  dependent destruction H.
  induction H0; simpl.
  (* Case: head_step. *)
  - apply backwards_head_preservation; auto.
  (* Case: head_bind_left. *)
  - rename h0 into s; intros.
    dependent destruction H2.
    constructor; auto.
Qed.

Lemma convergent_term_is_trivially_final:
  forall c n,
  converges c n ->
  forall r,
  length r <= n -> big (c, r).
Proof.
  induction 1; intros.
  (* Case: halt. *)
  - constructor.
    generalize dependent k.
    induction r; intros.
    + destruct k; auto.
    + simpl in H.
      destruct k; try lia.
      simpl; apply IHr.
      lia.
  (* Case: bind. *)
  - constructor.
    apply IHconverges.
    simpl; lia.
Qed.

Lemma head_evaluation_implies_big:
  forall c n,
  eval c n ->
  big (c, []).
Proof.
  intros c1 n (c2, ?, ?).
  apply clos_rt_rt1n_iff in H.
  induction H.
  (* Case: refl. *)
  - apply convergent_term_is_trivially_final with n.
    + assumption.
    + simpl; lia.
  (* Case: step. *)
  - apply big_is_preserved_backwards_by_head with y.
    + assumption.
    + firstorder.
Qed.

(* -------------------------------------------------------------------------- *)

(* TODO: we also define sumup in [Normalization.v]... move to a common place! *)

Definition sumup {T} (f: T -> nat) (ts: list T): nat :=
  fold_right Nat.add 0 (map f ts).

Definition heap_depth (r: heap): nat :=
  let fix value_depth (v: value): nat :=
    match v with
    | value_closure r _ _ =>
      1 + sumup value_depth r
    | value_suspend r _ =>
      1 + sumup value_depth r
    | value_undefined =>
      1
    end
  in sumup value_depth r.

Lemma smaller_heap_tail:
  forall {r r' v},
  r = v :: r' ->
  heap_depth r' < heap_depth r.
Proof.
  intros; subst.
  admit.
Admitted.

Lemma smaller_heap_closure_heap:
  forall {r r' s ts c},
  r = value_closure s ts c :: r' ->
  heap_depth s < heap_depth r.
Proof.
  admit.
Admitted.

Lemma heap_depth_is_well_founded:
  well_founded (ltof _ heap_depth).
Proof.
  apply well_founded_ltof.
Defined.

(* Our idea is to define a context by induction on the heap in that we can check
   that 1) the context is static, 2) the context binds the same variables as the
   heap defines, and 3) we have that jumps are preserved by bisimilarity.

   In particular, we need to define:

     [r, k = <s; \xs.c>] = [r][[-] { k<xs> = [s][c] }]

   As the heap isn't dependent (r doesn't bind in s or c), we assume, without
   loss of generality that the free variables in s and c are different from the
   ones bound by r. Note also that, in the de Bruijn setting, we have to switch
   the indexes bound in xs and s.
*)

Definition heap_to_context :=
  Fix heap_depth_is_well_founded (fun _ => context) (fun r f =>
    match r as x return (r = x -> context) with
    | value_closure t ts c :: s =>
      fun H =>
        let h := f _ (smaller_heap_tail H) in
        let i := f _ (smaller_heap_closure_heap H) in
        compose_context h (context_left context_hole ts
          (* TODO: add renaming constraints. *)
          (i c))
    | value_suspend t c :: s =>
      fun H =>
        context_hole
    | value_undefined :: s =>
      fun H =>
        context_hole
    | [] =>
      fun H =>
        context_hole
    end eq_refl).

Coercion heap_to_context: heap >-> context.

Lemma heap_to_context_nil:
  heap_to_context [] = context_hole.
Proof.
  reflexivity.
Qed.

Lemma heap_to_context_closure_unfold:
  forall r s ts c,
  heap_to_context (value_closure s ts c :: r) =
    compose_context (heap_to_context r)
      (context_left context_hole ts (heap_to_context s c)).
Proof.
  intros.
  unfold heap_to_context.
  rewrite Fix_eq; simpl.
  - fold heap_to_context.
    reflexivity.
  - intros.
    destruct x; simpl; auto.
    destruct v; simpl; auto.
    now do 2 rewrite H.
Qed.

Lemma heap_to_context_app:
  forall r s,
  heap_to_context (r ++ s) =
    compose_context (heap_to_context s) (heap_to_context r).
Proof.
  induction r; simpl; intros.
  - (* Of course. *)
    admit.
  - destruct a.
    + admit.
    + admit.
    + do 2 rewrite heap_to_context_closure_unfold.
      rewrite IHr; simpl.
      admit.
Admitted.

Lemma static_heap_to_context:
  forall r,
  static (heap_to_context r).
Proof.
  induction r.
  - constructor.
  - destruct a.
    + admit.
    + admit.
    + rewrite heap_to_context_closure_unfold.
      apply static_compose_context; auto with cps.
Admitted.

Lemma heap_to_context_preserves_jumps:
  forall (r s: heap) ts c k xs,
  length ts = length xs ->
  item (value_closure s ts c) r k ->
  [r (jump k xs) ~~ heap_append xs r s c].
Proof.
  intros.
  apply barb_sema.
  admit.
Admitted.

(* Soundness! *)

Lemma heap_to_context_preserves_semantics:
  forall c r,
  big (c, r) ->
  exists n,
  eval (r c) n.
Proof.
  intros.
  remember (c, r) as p.
  generalize dependent r.
  generalize dependent c.
  induction H; intros.
  (* Case: halt. *)
  - dependent destruction Heqp.
    rename r0 into r.
    admit.
  (* Case: jump. *)
  - dependent destruction Heqp.
    rename r0 into r.
    specialize (IHbig _ _ eq_refl) as (n, ?).
    exists n.
    apply weak_convergence_characterization in H2.
    apply weak_convergence_characterization.
    apply barb_weak_convergence with (heap_append xs r s c).
    + now apply heap_to_context_preserves_jumps with ts.
    + assumption.
  (* Case: bind. *)
  - dependent destruction Heqp.
    rename r0 into r.
    specialize (IHbig _ _ eq_refl) as (n, ?).
    exists n.
    rewrite heap_to_context_closure_unfold in H0.
    rewrite compose_context_is_sound in H0; simpl in H0.
    admit.
  (* Case: high. *)
  - dependent destruction Heqp.
    rename r0 into r.
    specialize (IHbig _ _ eq_refl) as (n, ?).
    admit.
Admitted.

Lemma big_implies_head_evaluation:
  forall c,
  big (c, []) ->
  exists n,
  eval c n.
Proof.
  intros.
  apply heap_to_context_preserves_semantics in H as (n, ?).
  rewrite heap_to_context_nil in H.
  now exists n.
Qed.

(* -------------------------------------------------------------------------- *)

Theorem machine_correctness:
  forall c,
  big (c, []) <-> (exists n, eval c n).
Proof.
  split; intros.
  - now apply big_implies_head_evaluation.
  - destruct H as (n, ?).
    now apply head_evaluation_implies_big with n.
Qed.

Definition machine_equiv: relation pseudoterm :=
  fun b c =>
    forall h: context,
    big (h b, []) <-> big (h c, []).

Lemma machine_equiv_refl:
  reflexive machine_equiv.
Proof.
  firstorder.
Qed.

Lemma machine_equiv_sym:
  symmetric machine_equiv.
Proof.
  firstorder.
Qed.

Lemma machine_equiv_trans:
  transitive machine_equiv.
Proof.
  firstorder.
Qed.

Lemma machine_equiv_bind_left:
  LEFT machine_equiv.
Proof.
  intros b1 b2 ts c ? h.
  specialize (H (compose_context h (context_left context_hole ts c))).
  do 2 rewrite compose_context_is_sound in H.
  now simpl in H.
Qed.

Lemma machine_equiv_bind_right:
  RIGHT machine_equiv.
Proof.
  intros b ts c1 c2 ? h.
  specialize (H (compose_context h (context_right b ts context_hole))).
  do 2 rewrite compose_context_is_sound in H.
  now simpl in H.
Qed.

Lemma machine_semantics_preserves_barb:
  forall b c,
  machine_equiv b c ->
  forall (h: context) k,
  eval (h b) k ->
  eval (h c) k.
Proof.
  intros.
  (* Since h b halts, and b is machine equivalent to c, we know that c also has
     to halt to some continuation. *)
  assert (exists k, eval (h b) k) by eauto.
  apply machine_correctness in H1.
  apply H in H1.
  apply machine_correctness in H1 as (j, ?).
  (* Now, we have to show that k has to be the same as j. *)
  destruct (Nat.eq_dec k j); subst.
  - (* If they are the same, we are done. *)
    assumption.
  - (* If they aren't, we have a contradiction given that b and c should always
       halt if and only if the other does for every possible context. *)
    exfalso.
    (* We have that h b will reduce to some b' such that it halts at a variable
       k, and h c will reduce to some c' such that it halts at a variable j. *)
    destruct H0 as (b', ?, ?).
    destruct H1 as (c', ?, ?).
    (* However, since k and j are not the same, b' and c' have, respectively,
       k<xs> and j<ys> at their head positions. We can thus build a context r
       such that r = [] { k<...> = f<> } { j<...> = O }, by using the right
       arities for parameters and taking f to be fresh and O to be the looping
       continuation (omega). We then can check that (r . h) b will still halt,
       thus we know that (r . h) c should halt as well, but it will loop. *)
    admit.
Admitted.

Lemma machine_equiv_preserves_observational_equivalence:
  forall b c,
  machine_equiv b c ->
  forall h: context,
  observational_equivalence head converges (h b) (h c).
Proof.
  intros b c ? h k; split; intros.
  - now apply machine_semantics_preserves_barb with b.
  - now apply machine_semantics_preserves_barb with c.
Qed.

Theorem machine_equiv_characterization:
  same_relation machine_equiv barb.
Proof.
  split; intros b c ?.
  - intros h.
    exists (observational_equivalence head converges).
    + apply observational_equivalence_is_a_barbed_bisimulation.
      * (* Clearly, as head is deterministic! *)
        admit.
      * clear H h b c.
        intros b c ? k ?.
        (* Well, if b converges, then b = c and we're done. *)
        admit.
    + now apply machine_equiv_preserves_observational_equivalence.
  - intros h; split; intros.
    + apply machine_correctness in H0 as (k, ?).
      apply weak_convergence_characterization in H0.
      apply machine_correctness; exists k.
      apply weak_convergence_characterization.
      apply barb_weak_convergence with (h b).
      * (* Huh, clearly, as barbed congruence is, well, a congruence. *)
        admit.
      * assumption.
    + apply machine_correctness in H0 as (k, ?).
      apply weak_convergence_characterization in H0.
      apply machine_correctness; exists k.
      apply weak_convergence_characterization.
      apply barb_weak_convergence with (h c).
      * (* Just as above. *)
        admit.
      * assumption.
Admitted.
