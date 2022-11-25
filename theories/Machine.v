(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
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
Require Import Local.Observational.

(*
Goal
  forall j a (s r: list pseudoterm),
  j >= a ->
  (if le_gt_dec (length s) (length r) then
     j - a + (length r - length s)
   else
     j - a - (length s - length r)) =
  (* Of course... *)
  j - a + length r - length s.
Proof.
  intros.
  generalize (length s).
  generalize (length r).
  clear s r.
  intros n m.
  destruct (le_gt_dec m n).
  lia.
  lia.
Qed.
*)

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
   as a signal of termination rather than using a distinguished "halt", and then
   keeping track of it (so it's a function, not a predicate). Something really
   similar is also implemented in Appel's book (see Chapter 3). This is meant to
   be an "implementation-friendly" semantics. *)

Inductive big: configuration -> Prop :=
  (*
      r(k) is undefined
    --------------------- (M-HALT)
       (k<xs>, r) \/ k
  *)
  | big_halt:
    forall k xs r,
    nth k r U = U ->
    big (jump k xs, r)

  (*
      p(k) = <s, \xs.c>       <c, s, xs = r(ys)> \/ j
    --------------------------------------------------- (M-JUMP)
                   <k<ys>, r> \/ j[ys/xs]
  *)
  | big_jump:
    forall r s c k xs ts,
    item (value_closure s ts c) r k ->
    length xs = length ts ->
    big (c, heap_append xs r s) ->
    big (jump k xs, r)

  (*
      <b, r, k = <r, \xs.c>> \/ j
    ------------------------------- (M-BIND)
       <b { k<xs> = c }, r> \/ j
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

(* TODO: move this definition somewhere else. *)

Definition eval a n: Prop :=
  comp rt(head) converges a n.

(* Oh no, oh no, oh no no no no no...

   This is clearly not a first-order term, but it's valid in our higher-order
   formulation...

   j@0<k@1<>>
   { j<x> =
     x@0 }

   And I expect that eval will reach a normal form, halting at k...

*)

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

Instance lift_proper: forall i, proper (lift i).
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

Instance subst_proper: forall x, proper (subst x).
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

Instance apply_parameters_proper: forall xs, proper (apply_parameters xs).
Proof.
  constructor; intros.
  - generalize dependent k.
    induction x using pseudoterm_deepind; simpl; intros.
    + induction xs; simpl; auto.
    + induction xs; simpl; auto.
    + induction xs; simpl; auto.
    + induction xs; simpl; auto.
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
      * assert (exists x, item x (rev xs) (n - k)) as (x, ?).
        apply item_exists.
        rewrite rev_length.
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

Instance ids_proper: proper ids.
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
  forall c r,
  big (c, r) ->
  exists t,
  big_at_time (c, r) t.
Proof.
  intros.
  remember (c, r) as x.
  generalize dependent r.
  generalize dependent c.
  induction H; intros.
  - dependent destruction Heqx.
    exists 0.
    eapply big_at_time_halt; eauto.
  - dependent destruction Heqx.
    edestruct IHbig as (t, ?); eauto.
    exists (S t).
    eapply big_at_time_jump; eauto.
  - dependent destruction Heqx.
    edestruct IHbig as (t, ?); eauto.
    exists (S t).
    eapply big_at_time_bind; eauto.
  - dependent destruction Heqx.
    edestruct IHbig as (t, ?); eauto.
    exists t.
    eapply big_at_time_high; eauto.
Qed.

Definition corresponding_valueF :=
  fun p (f: forall m, fst (fst m) < fst (fst p) -> Prop) =>
    let t := fst (fst p) in
    let v1 := snd (fst p) in
    let v2 := snd p in
    match v1, v2 with
    | value_closure p ts c, value_closure q us b =>
      length ts = length us /\
        forall m r s xs ys,
        forall H: m < t,
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

Definition corresponding_valueP p: Prop :=
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
      * apply H1 with r xs H2; auto.
        clear H0 H1 H3 H4.
        induction H5; constructor; auto.
        apply H; assumption.
  - destruct v1; destruct v2; try contradiction.
    + assumption.
    + assumption.
    + destruct H0; split; intros.
      * assumption.
      * apply H1 with r xs H2; auto.
        clear H0 H1 H3 H4.
        induction H5; constructor; auto.
        apply H; assumption.
Qed.

Lemma corresponding_value_inv:
  forall t,
  forall P: value -> value -> Prop,
  (forall p ts c q us b,
     length ts = length us ->
     (forall m r s xs ys,
        m < t ->
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
    + apply H3 with r xs; auto.
Qed.

Definition corresponding (f: nat -> pseudoterm -> pseudoterm) r s k t :=
  (forall n: nat,
  corresponding_value t (heap_get (f k n) r) (heap_get n s)).

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

(* TODO: move this lemma somewhere else. *)
Lemma Forall2_length:
  forall {A} {B} R xs ys,
  @Forall2 A B R xs ys -> length xs = length ys.
Proof.
  induction 1; simpl; lia.
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
      * apply Forall2_length in H4.
        rewrite heap_get_heap_append_simplification; try lia.
        rewrite heap_get_heap_append_simplification; try lia.
        rewrite H4; apply H1.
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
      assert (corresponding_value (S t) (heap_get (f k n) r) (heap_get n s));
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

          r corresponds to s through f

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
        rewrite traverse_list_length in H4.
        rename r0 into r', s0 into s'.
        eapply H; eauto.
        rewrite plus_comm.
        rewrite <- H4.
        apply technical2; eauto with cps; intros.
        rewrite proper_respects_structure in H9.
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

    s := r, k = \ys.c, H

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
  - apply convergent_term_is_trivially_final with n; eauto with arith.
  (* Case: step. *)
  - eapply big_is_preserved_backwards_by_head; eauto.
Qed.

Lemma big_implies_head_evaluation:
  forall c,
  big (c, []) ->
  exists n,
  eval c n.
Proof.
  admit.
Admitted.

(*

(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.AbstractRewriting.
Require Import Local.Context.
Require Import Local.Reduction.
Require Import Local.Observational.

Inductive value: Set :=
  (* We don't really need this in the named setting, but it's surely useful in
     the de Bruijn setting! With this we can propagate that a variable has been
     substituted by a free variable. *)
  | value_undefined
  (* Continuations in memory. *)
  | value_cont (p: list value) (ts: list pseudoterm) (c: pseudoterm).

Local Notation U := value_undefined.

Local Notation "< r ; \ ts : c >" :=
  (value_cont r ts c) (only printing, format "< r ;  \ ts :  c >").

Definition heap: Set :=
  list value.

Definition configuration: Set :=
  pseudoterm * heap.

(* Please note that parameters are written from right to left, but arguments to
   jumps are written from left to write! *)

Definition heap_append (ns: list nat) (r s: heap): heap :=
  (* map (fun n => nth n r U) (rev ns) ++ s *)
  fold_left (fun acc n => nth n r U :: acc) ns s.

(* Big-step abstract machine semantics for the CPS-calculus. This was derived
   directly from Kennedy's paper, slightly adapting it to use free variables as
   a signal of termination rather than using a "halt" term. This is meant to be
   an "implementation-friendly" semantics for the calculus. *)

Inductive big: configuration -> nat -> Prop :=
  (*
      r(k) is undefined
    --------------------- (M-HALT)
       (k<xs>, r) |-> k
  *)
  | big_halt:
    forall k xs r,
    nth k r U = U ->
    big (jump k xs, r) k

  (*
      p(k) = <s, \xs.c>      <c, s, xs = r(ys)> |-> j
    --------------------------------------------------- (M-JUMP)
                  <k<ys>, r> |-> j[ys/xs]
  *)
  | big_jump:
    forall r s a c k xs ts ns j j',
    Forall2 (fun x n => x = bound n) xs ns ->
    a = length ns ->
    item (value_cont s ts c) r k ->
    a = length ts ->
    big (c, heap_append ns r s) j ->
    (* Naughty little index math here! We build the runtime heap for c using s,
       and it may return two continuations: one that we have bound now, from the
       parameters, or one that is already bound in s. We have to map the results
       to the heap r! So, if the result is a parameter, thus j <= a, we already
       know its value in r (which comes from ns). But, if j > a, we'll have to
       remove any newly bound abstractions, subtracting a, and then add any
       new abstractions that have been bound in r but not in s (notice that r is
       always newer and as such has strictly more bindings!). Also remember that
       parameters are in the reverse order, but arguments are not, so we need to
       reverse [ns] here as well. *)

    (* TODO: fix above comment, move following into definition. *)
    j' = (if le_gt_dec (length s) (length r) then
            nth j (rev ns) (j - a + (length r - length s))
          else
            nth j (rev ns) (j - a - (length s - length r))) ->

    (* There we go. *)
    big (jump k xs, r) j'

  (*
      <b, r, k = <r, \xs.c>> |-> j
    -------------------------------- (M-BIND)
       <b { k<xs> = c }, r> |-> j
  *)
  | big_bind:
    forall b ts c r j,
    big (b, value_cont r ts c :: r) (S j) ->
    big (bind b ts c, r) j.

(* TODO: remove the following! We need to prove equivalence of the above and the
   head reduction! *)

Goal
  big (ex1, []) 3.
Proof.
  compute.
  constructor; simpl.
  constructor; simpl.
  eapply big_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump; simpl.
  repeat constructor.
  reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  econstructor 1.
  compute; reflexivity.
  compute; reflexivity.
  compute; reflexivity.
  compute; reflexivity.
Qed.

Goal
  weakly_converges ex1 3.
Proof.
  eexists; simpl.
  apply star_trans with ex3.
  compute.
  constructor.
  apply step_ctxjmp with (h := context_left context_hole ?[ts] ?[c]); auto.
  compute.
  eapply star_trans.
  apply star_step.
  apply step_bind_left.
  apply step_recjmp.
  reflexivity.
  compute.
  apply star_step.
  apply step_ctxjmp with (h := context_left context_hole ?[ts] ?[c]); auto.
  compute.
  constructor.
  constructor.
  constructor.
Qed.

Fixpoint context_to_heap h s: heap :=
  match h with
  | context_hole =>
    s
  | context_left r ts c =>
    context_to_heap r (value_cont s ts c :: s)
  | context_right b ts r =>
    (* We don't really care about this one. *)
    []
  end.

Inductive big_aux: configuration -> nat -> Prop :=
  | big_aux_halt:
    forall k xs r,
    nth k r U = U ->
    big_aux (jump k xs, r) k

  | big_aux_jump:
    forall r s a c k xs ts ns j j',
    Forall2 (fun x n => x = bound n) xs ns ->
    a = length ns ->
    item (value_cont s ts c) r k ->
    a = length ts ->
    big_aux (c, heap_append ns r s) j ->
    j' = (if le_gt_dec (length s) (length r) then
            nth j (rev ns) (j - a + (length r - length s))
          else
            nth j (rev ns) (j - a - (length s - length r))) ->
    big_aux (jump k xs, r) j'

  | big_aux_bind:
    forall k xs r j h,
    static h ->
    #h > 0 ->
    big_aux (jump k xs, context_to_heap h r) (#h + j) ->
    big_aux (h (jump k xs), r) j.

Lemma context_to_heap_length:
  forall h,
  static h ->
  forall r,
  length (context_to_heap h r) = #h + length r.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - rewrite IHstatic; simpl.
    lia.
Qed.

Lemma context_to_heap_app:
  forall h,
  static h ->
  forall r,
  exists2 s,
  context_to_heap h r = s ++ r & #h = length s.
Proof.
  induction 1; intros.
  - exists []; simpl; auto.
  - edestruct IHstatic as (s, ?, ?).
    eexists; simpl.
    + rewrite H0.
      replace (s ++ value_cont r ts c :: r) with
        ((s ++ [value_cont r ts c]) ++ r).
      * reflexivity.
      * rewrite <- app_assoc.
        reflexivity.
    + rewrite app_length; simpl.
      lia.
Qed.

Lemma big_implies_big_aux:
  forall h,
  static h ->
  forall c r k,
  big (c, context_to_heap h r) (#h + k) ->
  big_aux (h c, r) k.
Proof.
  induction 1; simpl; intros.
  - induction H.
    + constructor 1; auto.
    + econstructor 2; eauto.
    + replace (bind b ts c0) with (context_left context_hole ts c0 b); auto.
      dependent destruction IHbig.
      * constructor; simpl; eauto with cps.
        constructor; assumption.
      * constructor; simpl; eauto with cps.
        econstructor 2; eauto.
      * rewrite <- compose_context_is_sound.
        constructor; simpl; eauto with cps.
        replace (S (#h + j)) with (#h + S j); try lia.
        assumption.
  - replace (bind (h c0) ts c) with (context_left context_hole ts c (h c0));
      auto.
    replace (S (#h + k)) with (#h + S k) in H0; try lia.
    specialize (IHstatic _ _ _ H0); clear H0.
    dependent destruction IHstatic.
    + destruct h; try discriminate.
      simpl in x; dependent destruction x.
      constructor; simpl; auto with cps.
      constructor 1.
      assumption.
    + destruct h; try discriminate.
      simpl in x0; dependent destruction x0.
      constructor; simpl; auto with cps.
      econstructor 2; eauto.
    + rewrite <- x.
      rewrite <- compose_context_is_sound.
      constructor 3; simpl; auto with cps.
      replace (S (#h0 + k)) with (#h0 + S k); try lia.
      assumption.
Qed.

Lemma big_aux_implies_big:
  forall c r k,
  big_aux (c, r) k ->
  big (c, r) k.
Proof.
  intros.
  dependent induction H.
  - constructor 1; auto.
  - econstructor 2; eauto.
  - specialize (IHbig_aux _ _ JMeq_refl).
    clear H0 H1.
    generalize dependent j.
    generalize dependent r.
    induction H; simpl; intros.
    + assumption.
    + constructor 3.
      apply IHstatic.
      replace (#h + S j) with (S (#h + j)); try lia.
      assumption.
Qed.

Lemma big_and_big_aux_are_equivalent:
  forall c r k,
  big_aux (c, r) k <-> big (c, r) k.
Proof.
  split; intros.
  - apply big_aux_implies_big; auto.
  - apply big_implies_big_aux with (h := context_hole); auto with cps.
Qed.

Fixpoint rebuild_heap (h: heap): context :=
  match h with
  | [] =>
    context_hole
  | value_undefined :: h' =>
    rebuild_heap h'
  | value_cont _ ts c :: h' =>
    compose_context (rebuild_heap h')
      (context_left context_hole ts c)
  end.

Lemma context_to_heap_compose:
  forall h,
  static h ->
  forall r s,
  context_to_heap (compose_context h r) s =
    context_to_heap r (context_to_heap h s).
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - rewrite IHstatic.
    reflexivity.
Qed.

Goal
  forall r,
  static (rebuild_heap r).
Proof.
  induction r; simpl.
  - constructor.
  - destruct a; simpl.
    + assumption.
    + apply static_compose_context.
      * assumption.
      * do 2 constructor.
Qed.

Goal
  forall r,
  ~(In U r) ->
  #(rebuild_heap r) = length r.
Proof.
  induction r; intros; simpl.
  - reflexivity.
  - destruct a; simpl.
    + exfalso; apply H.
      constructor.
      reflexivity.
    + rewrite compose_context_bvars; simpl.
      rewrite plus_comm; simpl; f_equal.
      apply IHr.
      intro; apply H.
      constructor 2.
      assumption.
Qed.

Lemma big_implies_weakly_converges:
  forall r c k,
  big (c, r) k ->
  weakly_converges c k.
Proof.
  intros.
  dependent induction H; simpl.
  - eexists.
    + eapply star_refl.
    + constructor.
  - (* We probably need substitution in heaps as Plotkin did! *)
    rename c0 into c.
    (* Lets check our inductive hypothesis... *)
    specialize (IHbig _ _ JMeq_refl).
    (* Huh...? Perhaps the induction should be on the length of reduction... *)
    admit.
  - rename c0 into c.
    edestruct IHbig; eauto.
    exists (bind x ts c).
    + apply star_bind_left.
      assumption.
    + constructor.
      assumption.
Admitted.

Theorem weakly_converges_and_big_are_equivalent:
  forall c k,
  big (c, []) k <-> weakly_converges c k.
Proof.
  split; intros.
  - apply big_implies_weakly_converges with [].
    assumption.
  - admit.
Admitted.

Example ex_cbn: pseudoterm :=
  (bind (bind (jump 1 [bound 0]) [void; void] (jump 1 [bound 0]))
      [void]
      (bind (jump 1 [bound 0; bound 2]) [void]
         (bind
            (bind (jump 1 [bound 0]) [void; void] (jump 1 [bound 0]))
            [void]
            (bind (jump 1 [bound 0; bound 2]) [void]
               (bind (jump 1 [bound 0]) [void; void]
                  (jump 1 [bound 0])))))).

Example ex_cbv: pseudoterm :=
   (bind (bind (jump 1 [bound 0]) [void; void] (jump 0 [bound 1]))
      [void]
      (bind
         (bind
            (bind (jump 1 [bound 0]) [void; void] (jump 0 [bound 1]))
            [void]
            (bind
               (bind (jump 1 [bound 0]) [void; void]
                  (jump 0 [bound 1])) [void] 
               (jump 1 [bound 0; bound 2]))) [void] 
         (jump 1 [bound 0; bound 2]))).

Definition f :=
  jump 1 [bound 0; bound 2].

Definition l :=
  jump 1 [bound 0; bound 2].

Definition m :=
  jump 0 [bound 1].

Definition g :=
  (bind
  (bind
    (jump 1 [bound 0])
    [void; void]
      m)
    [void]
      l).

Definition h :=
  jump 0 [bound 1].

Definition a :=
  (bind
  (bind
  (bind
    (jump 1 [bound 0])
    [void; void]
      h)
    [void]
      g)
    [void]
      f).

Definition b :=
  jump 0 [bound 1].

Definition v :=
  (bind
  (bind
    (jump 1 [bound 0])
    [void; void]
      b)
    [void]
      a).

Goal
  ex_cbv = v.
Proof.
  reflexivity.
Qed.

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
  induction b0.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  simpl.
  rewrite IHb0_1 at 1.
  reflexivity.
Defined.

Goal
  weakly_converges ex_cbn 0.
Proof.
  compute.
  eexists.
  eapply star_trans.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  repeat constructor.
Qed.

Goal
  weakly_converges ex_cbv 0.
Proof.
  compute.
  eexists.
  eapply star_trans.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  rewrite foobar_sound at 1.
  unfold foobar, fst, snd.
  apply star_ctxjmp.
  reflexivity.
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  eapply star_trans.
  apply star_bind_left.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  apply star_step.
  apply step_gc.
  repeat (constructor; simpl; try lia).
  compute.
  repeat constructor.
Qed.

Notation Ca := (value_cont [] 1 a).

Notation Cb := (value_cont [Ca] 2 b).

Notation Cf := (value_cont [Cb] 1 f).

Notation Cg := (value_cont [Cf; Cb] 1 g).

Notation Ch := (value_cont [Cg; Cf; Cb] 2 h).

Notation Cl := (value_cont [Ch; Cf; Cb] 1 l).

Notation Cm := (value_cont [Cl; Ch; Cf; Cb] 2 m).

Goal
  big (ex_cbn, []) 0.
Proof.
  constructor; compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  constructor; compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  constructor; compute.
  eapply big_halt.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.

Goal
  big (v, []) 0.
Proof.
  unfold v.
  constructor; unfold length.
  constructor; unfold length.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  (* At this point, e = b. Ok. *)
  unfold a at 1.
  constructor; unfold length.
  constructor; unfold length.
  constructor; unfold length.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  (* At this point, e = b, k = h. Ok. *)
  unfold g at 1.
  constructor; unfold length.
  constructor; unfold length.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  (* At this point, e = b, k = h, p = m. Ok!
     So this becomes h<m, f>. That typechecks! *)
  unfold l at 1.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  (* Here the problem was! :) *)
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  unfold heap_append, fold_left, nth, app.
  eapply big_halt.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.

(*
  cbv halt =
    a b
    where
      b c d =
        d c
      a e =
        g h
        where
          h i j =
            j i
          g k =
            l m
            where
              m n o =
                o n
              l p =
                k p f
          f q =
            e q halt

  cbn halt =
    a b
    where
      b c d =
        c d
      a e =
        e f halt
        where
          f g =
            h i
            where
              i j k =
                j k
              h l =
                l m g
                where
                  m n =
                    n o
                    where
                      o p q =
                        p q

  CBV:
    \halt: ~~(b, ~b).

      a<b>
      { b<c: ~(b, ~b), d: ~~(b, ~b)> =
          d<c>
      { a<e: ~(~(b, ~b), ~~(b, ~b))> =
          g<h>
          { h<i: ~(b, ~b), j: ~~(b, ~b)> =
              j<i>
          }
          { g<k: ~(~(b, ~b), ~~(b, ~b))> =
              l<m>
              { m<n: b, o: ~b> =
                  o<n>
              }
              { l<p: ~(b, ~b)> =
                  k<p, f>
              }
          }
          { f<q: ~(b, ~b)> =
              e<q, halt>
          }
      }
*)

(*
  f@0<j@1>
  { f<k> =
    a<k@0> }
  { j<> =
    H<> }
  { b<k> =
    k@0<> }
  { c<k> =
    k@0<> }
  { a<k> =
    k<> }
*)

Goal
  big (
    (bind
    (bind
    (bind
    (bind
    (bind
      (jump 0 [bound 1])
      [void]
        (jump 4 [bound 0]))
      []
        (jump 8 []))
      [void]
        (jump 0 []))
      [void]
        (jump 0 []))
      [void]
        (jump 0 [])),
  []) 5.
Proof.
  constructor; compute.
  constructor; compute.
  constructor; compute.
  constructor; compute.
  constructor; compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_jump.
  repeat constructor.
  compute; reflexivity.
  repeat constructor.
  reflexivity.
  compute.
  eapply big_halt.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
  compute.
  reflexivity.
Qed.

*)
