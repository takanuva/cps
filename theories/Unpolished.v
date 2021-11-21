(******************************************************************************)
(*   Copyright (c) 2019--2021 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.
Require Import Local.Reduction.
Require Import Local.TypeSystem.

(* This file, for now, contains a few unfinished, unpolished stuff. These thigns
   will eventually be moved to their proper development files, or be removed. *)

Lemma step_redex_inv:
  forall P: pseudoterm -> Prop,
  forall (h: context) xs ts c e,
  forall f1: P (bind (h (apply_parameters xs 0 (lift (S #h) (length ts) c)))
                  ts c),
  forall f2: (forall r, #h = #r -> P (bind (r (jump #h xs)) ts c)),
  forall f3: (forall c2, [c => c2] -> P (bind (h (jump #h xs)) ts c2)),
  [bind (h (jump #h xs)) ts c => e] -> P e.
Proof.
  intros.
  dependent destruction H.
  - rename h0 into r.
    destruct context_eq_dec with h r.
    + destruct e.
      apply context_is_injective in x; auto.
      dependent destruction x.
      exact f1.
    + edestruct context_difference as (s, (?, (?, _))); eauto.
      erewrite H0.
      apply f2; auto with cps.
  - destruct step_noninterference with h #h xs b2 as (r, ?, ?); auto.
    rewrite H0.
    apply f2; auto with cps.
  - apply f3; auto with cps.
Qed.

(** ** Multi-hole contexts *)

Inductive multicontext: Set :=
  | multicontext_context (h: context)
  | multicontext_left (b: multicontext) (ts: list pseudoterm) (c: pseudoterm)
  | multicontext_right (b: pseudoterm) (ts: list pseudoterm) (c: multicontext)
  | multicontext_both (b: multicontext) (ts: list pseudoterm) (c: multicontext).

Coercion multicontext_context: context >-> multicontext.

Lemma multicontext_eq_dec:
  forall h r: multicontext,
  { h = r } + { h <> r }.
Proof.
  decide equality.
  - apply context_eq_dec.
  - apply pseudoterm_eq_dec.
  - apply list_eq_dec.
    apply pseudoterm_eq_dec.
  - apply list_eq_dec.
    apply pseudoterm_eq_dec.
  - apply pseudoterm_eq_dec.
  - apply list_eq_dec.
    apply pseudoterm_eq_dec.
Qed.

Fixpoint apply_multicontext (h: multicontext) (f: nat -> pseudoterm) :=
  match h with
  | multicontext_context h =>
      h (f #h)
  | multicontext_left b ts c =>
      bind (apply_multicontext b (fun n => f (S n))) ts c
  | multicontext_right b ts c =>
      bind b ts (apply_multicontext c (fun n => f (length ts + n)))
  | multicontext_both b ts c =>
      bind (apply_multicontext b (fun n => f (S n))) ts
        (apply_multicontext c (fun n => f (length ts + n)))
  end.

Coercion apply_multicontext: multicontext >-> Funclass.

Lemma multicontext_image:
  forall h: multicontext,
  forall f g,
  (forall n, f n = g n) -> h f = h g.
Proof.
  induction h; simpl; intros.
  - rewrite H; auto.
  - f_equal.
    apply IHh; intros.
    apply H.
  - f_equal.
    apply IHh; intros.
    apply H.
  - f_equal.
    + apply IHh1; intros.
      apply H.
    + apply IHh2; intros.
      apply H.
Qed.

(* Our multi-hole contexts are sound. But...
   TODO: we probably want to apply this for ANY xs... how??? *)
Goal
  forall xs ts c,
  length xs = length ts ->
  forall h: multicontext,
  forall r: context,
  [bind (r (h (fun n => (jump (#r + n) xs)))) ts c =>*
    bind
      (r (h (fun n =>
               (apply_parameters xs 0
                 (lift (S (#r + n)) (length ts) c))))) ts c].
Proof.
  induction h; simpl; intros.
  - rewrite <- compose_context_is_sound.
    rewrite <- compose_context_is_sound.
    replace (#r + #h) with (#(compose_context r h)).
    + apply star_ctxjmp.
      assumption.
    + apply compose_context_bvars.
  - pose (compose_context r (context_left context_hole ts0 c0)) as X.
    assert (forall e, r (bind e ts0 c0) = X e).
    + intros; unfold X.
      rewrite compose_context_is_sound; simpl.
      reflexivity.
    + rewrite H0.
      rewrite H0.
      (* Ugly proof... rewrite me... *)
      rewrite multicontext_image with (g := fun n =>
        jump (#X + n) xs).
      rewrite multicontext_image with (f :=
        (fun n : nat =>
         apply_parameters xs 0
           (lift (S (#r + S n)) (length ts) c))) (g := fun n =>
        apply_parameters xs 0
           (lift (S (#X + n)) (length ts) c)).
      apply IHh.
      * intros; f_equal; f_equal.
        unfold X.
        rewrite compose_context_bvars; simpl.
        lia.
      * intros; f_equal.
        unfold X.
        rewrite compose_context_bvars; simpl.
        f_equal; lia.
  - pose (compose_context r (context_right b ts0 context_hole)) as X.
    assert (forall e, r (bind b ts0 e) = X e).
    + intros; unfold X.
      rewrite compose_context_is_sound; simpl.
      reflexivity.
    + rewrite H0.
      rewrite H0.
      rewrite multicontext_image with (g := fun n =>
        jump (#X + n) xs).
      rewrite multicontext_image with (f :=
        (fun n : nat =>
         apply_parameters xs 0
           (lift (S (#r + (length ts0 + n))) (length ts) c))) (g := fun n =>
        apply_parameters xs 0
           (lift (S (#X + n)) (length ts) c)).
      apply IHh.
      * intros; f_equal; f_equal.
        unfold X.
        rewrite compose_context_bvars; simpl.
        lia.
      * intros; f_equal.
        unfold X.
        rewrite compose_context_bvars; simpl.
        f_equal; lia.
  - (* Clearly follow from transitivity and the hypotheses. *)
    eapply star_trans.
    epose (compose_context r (context_left context_hole ts0 _)) as X.
    eassert (forall e, r (bind e ts0 _) = X e).
    intros; unfold X.
    rewrite compose_context_is_sound; simpl.
    reflexivity.
    rewrite H0.
    rewrite multicontext_image with (g := fun n =>
      jump (#X + n) xs).
    apply IHh1.
    intros; f_equal.
    unfold X.
    rewrite compose_context_bvars; simpl.
    f_equal; lia.
    rewrite compose_context_is_sound; simpl.
    rewrite compose_context_bvars; simpl.
    rewrite multicontext_image with (g := fun n =>
      apply_parameters xs 0
               (lift (S (#r + S n)) (length ts) c)).
    epose (compose_context r (context_right _ ts0 context_hole)) as X.
    eassert (forall e, r (bind _ ts0 e) = X e).
    intros; unfold X.
    rewrite compose_context_is_sound; simpl.
    reflexivity.
    rewrite H0.
    rewrite H0.
    rewrite multicontext_image with (g := fun n =>
      jump (#X + n) xs).
    rewrite multicontext_image with (f := fun n =>
      apply_parameters xs 0 _
    ) (g := fun n =>
         apply_parameters xs 0
           (lift (S (#X + n)) (length ts) c)).
    apply IHh2.
    intros; f_equal; f_equal.
    unfold X.
    rewrite compose_context_bvars; simpl.
    f_equal; lia.
    intros; f_equal.
    unfold X.
    rewrite compose_context_bvars; simpl.
    f_equal; lia.
    intros; f_equal; f_equal.
    lia.
Qed.

(** ** Head Reduction... long tail style *)

Inductive long: list env -> list pseudoterm -> relation pseudoterm :=
  | long_head:
    forall b,
    long [] [] b b
  | long_tail:
    forall tss ts cs c b e,
    long tss cs (bind b ts c) e ->
    long (ts :: tss) (c :: cs) b e.

Local Hint Constructors long: cps.

Lemma long_rev:
  forall tss ts cs c h b,
  long tss cs h b -> long (tss ++ [ts]) (cs ++ [c]) h (bind b ts c).
Proof.
  induction tss; intros.
  - dependent destruction H; simpl.
    auto with cps.
  - dependent destruction H; simpl.
    constructor.
    apply IHtss; auto.
Qed.

Lemma long_rev_inv:
  forall tss ts cs c h b,
  long (tss ++ [ts]) (cs ++ [c]) h (bind b ts c) -> long tss cs h b.
Proof.
  induction tss; intros.
  - destruct cs; simpl in H.
    + dependent destruction H.
      dependent destruction H.
      constructor.
    + exfalso.
      dependent destruction H.
      destruct cs; inversion H.
  - destruct cs.
    + simpl in H.
      dependent destruction H.
      destruct tss; inversion H.
    + constructor; simpl in H.
      dependent destruction H.
      eapply IHtss.
      eassumption.
Qed.

Lemma long_tail_inv:
  forall tss cs ts c b e,
  long (tss ++ [ts]) (cs ++ [c]) b e ->
  exists x, bind x ts c = e.
Proof.
  induction tss; intros.
  - destruct cs.
    + dependent destruction H.
      dependent destruction H.
      exists b; auto.
    + inversion H.
      destruct cs; inversion H6.
  - destruct cs.
    + dependent destruction H.
      destruct tss; inversion H.
    + dependent destruction H.
      edestruct IHtss; eauto.
Qed.

Lemma long_rev_ind:
  forall P: list env -> list pseudoterm -> relation pseudoterm,
  forall f1: (forall b, P [] [] b b),
  forall f2: (forall tss cs ts c h b, long tss cs h b ->
              P tss cs h b -> P (tss ++ [ts]) (cs ++ [c]) h (bind b ts c)),
  forall tss cs b e, long tss cs b e -> P tss cs b e.
Proof.
  induction tss using rev_ind; intros.
  - destruct cs.
    + dependent destruction H.
      apply f1.
    + inversion H.
  - destruct cs using rev_ind.
    + destruct tss; inversion H.
    + clear IHcs.
      rename x into ts, x0 into c.
      edestruct long_tail_inv; eauto.
      destruct H0.
      apply long_rev_inv in H.
      apply f2; auto.
Qed.

Lemma long_type_body_length:
  forall tss cs b e,
  long tss cs b e -> length tss = length cs.
Proof.
  induction 1; simpl; auto.
Qed.

Local Hint Resolve long_type_body_length: cps.

Lemma long_implies_context:
  forall tss cs,
  length tss = length cs ->
  exists h,
  #h = length tss /\ static h /\ forall b e,
  long tss cs b e -> e = h b.
Proof.
  induction tss; intros.
  - destruct cs; try discriminate.
    exists context_hole; intuition.
    inversion H0; auto.
  - destruct cs; try discriminate.
    destruct IHtss with cs as (h, (?, (?, ?))); auto.
    exists (compose_context h (context_left context_hole a p)).
    repeat split; simpl; intros.
    + rewrite compose_context_bvars; simpl; lia.
    + apply static_compose_context; auto with cps.
    + rewrite compose_context_is_sound; simpl.
      dependent destruction H3.
      rewrite H2 with (bind b a p) e; auto.
Qed.

Lemma item_too_far:
  forall {T} xs x k,
  length xs <= k ->
  ~@item T x xs k.
Proof.
  induction xs; intros.
  - inversion 1.
  - intro.
    dependent destruction H0.
    + simpl in H; lia.
    + eapply IHxs with (k := n).
      * simpl in H; lia.
      * eassumption.
Qed.

Lemma item_last_item:
  forall {T} xs k,
  length xs = k ->
  forall a b,
  @item T a (xs ++ [b]) k -> a = b.
Proof.
  intros.
  dependent induction H0.
  + destruct xs; try discriminate.
    dependent destruction x; auto.
  + destruct xs; try discriminate.
    dependent destruction x.
    eapply IHitem; eauto.
Qed.

Definition LONGJMP (R: relation pseudoterm): Prop :=
  forall tss cs k xs e1,
  long tss cs (jump (bound k) xs) e1 ->
  forall ts,
  length xs = length ts ->
  item ts tss k ->
  forall c,
  item c cs k ->
  forall e2,
  long tss cs (apply_parameters xs 0 (lift (S k) (length ts) c)) e2 ->
  R e1 e2.

Lemma step_longjmp:
  LONGJMP step.
Proof.
  unfold LONGJMP; intros until 1.
  dependent induction H using long_rev_ind; intros.
  - inversion H1.
  - edestruct long_tail_inv; eauto.
    destruct H4.
    destruct (lt_eq_lt_dec (length tss) k) as [ [ ? | ? ] | ? ].
    + exfalso.
      apply item_too_far with (tss ++ [ts]) ts0 k; auto.
      rewrite app_length; simpl; lia.
    + apply long_rev_inv in H3.
      destruct long_implies_context with tss cs; eauto with cps.
      destruct H4; destruct H5.
      erewrite H6 with _ b in H |- *; eauto.
      erewrite H6 with _ x in H3 |- *; eauto.
      apply long_type_body_length in H.
      apply item_last_item in H1; auto.
      apply item_last_item in H2; try congruence.
      destruct H1; destruct H2.
      replace k with #x0.
      * apply step_ctxjmp.
        assumption.
      * congruence.
    + apply step_bind_left.
      apply long_rev_inv in H3.
      eapply IHlong.
      * reflexivity.
      * eassumption.
      * eapply item_ignore_tail; eauto.
      * eapply item_ignore_tail; eauto.
        replace (length cs) with (length tss); eauto with cps.
      * assumption.
Qed.

Inductive insert x: nat -> relation env :=
  | insert_head:
    forall tail,
    insert x 0 tail (x :: tail)
  | insert_tail:
    forall n head tail new_tail,
    insert x n tail new_tail ->
    insert x (S n) (head :: tail) (lift 1 n head :: new_tail).

Local Hint Constructors insert: cps.

Lemma item_lift_insert_ge:
  forall x n g h,
  insert x n g h ->
  forall m,
  n <= m ->
  forall y, item_lift y g m -> item_lift (lift 1 n y) h (S m).
Proof.
  induction 1; intros.
  - destruct H0 as (z, ?, ?).
    exists z; auto with cps.
    rewrite H0.
    rewrite lift_lift_simplification; auto with arith.
  - destruct H1 as (z, ?, ?).
    dependent destruction H2.
    + exfalso.
      inversion H0.
    + rename n0 into m.
      destruct IHinsert with m (lift (S m) 0 z); try lia.
      * exists z; auto.
      * rewrite lift_lift_simplification in H3; try lia.
        exists x0; auto with cps.
        rewrite H1; rewrite lift_lift_simplification; try lia.
        admit.
Admitted.

Lemma item_lift_insert_lt:
  forall e n g h,
  insert e n g h ->
  forall m,
  n > m ->
  forall y, item_lift y g m -> item_lift (lift 1 n y) h m.
Proof.
  induction 1; intros.
  - inversion H.
  - destruct H1.
    dependent destruction H2.
    + clear IHinsert H0.
      exists (lift 1 n head); auto with cps.
      symmetry; rewrite lift_lift_permutation; auto with arith.
    + rename n0 into m.
      destruct IHinsert with m (lift (S m) 0 x) as (z, ?, ?); try lia.
      * exists x; auto.
      * exists z; auto with cps.
        admit.
Admitted.

(*
Lemma env_prepend_rev:
  forall ts t g,
  env_prepend (ts ++ [t]) g = env_prepend (map (lift 1 0) ts) (t :: g).
Proof.
  induction ts; simpl; intros.
  - rewrite lift_zero_e_equals_e; auto.
  - rewrite app_length; simpl.
    rewrite map_length.
    rewrite lift_lift_simplification; try lia.
    rewrite IHts; f_equal.
Qed.

Lemma typing_weak_lift:
  forall g e t,
  typing g e t ->
  forall x n h,
  insert x n g h -> valid_env h -> typing h (lift 1 n e) (lift 1 n t).
Proof.
  induction 1 using typing_deepind; intros.
  (* Case: typing_base. *)
  - apply typing_base.
    assumption.
  (* Case: typing_negation. *)
  - rewrite lift_distributes_over_negation.
    apply typing_negation; auto.
    induction H; simpl.
    + constructor.
    + constructor; auto.
      apply H with x; auto.
  (* Case: typing_bound. *)
  - rename n0 into m.
    destruct (le_gt_dec m n).
    + rewrite lift_bound_ge; auto.
      apply typing_bound; auto.
      apply item_lift_insert_ge with x g; auto.
    + rewrite lift_bound_lt; auto.
      apply typing_bound; auto.
      apply item_lift_insert_lt with x g; auto.
  (* Case: typing_jump. *)
  - rewrite lift_distributes_over_jump.
    apply typing_jump with (map (lift 1 n) ts).
    + apply IHtyping with x; auto.
    + clear IHtyping.
      induction H; simpl.
      * constructor.
      * constructor; auto.
        apply H with x; auto.
  (* Case: typing_bind. *)
  - rewrite lift_distributes_over_bind.
    apply typing_bind.
    + apply IHtyping with x.
      * constructor; auto.
      * constructor; auto.
        clear IHtyping IHtyping0.
        constructor; auto.
        induction H; simpl; auto.
        constructor; auto.
        replace prop with (lift 1 n prop); auto.
        apply H with x; auto.
    + clear IHtyping IHtyping0.
      induction H; simpl; auto.
      constructor; auto.
      replace prop with (lift 1 n prop); auto.
      apply H with x; auto.
    + simpl in *.
      apply IHtyping0 with x.
      * clear IHtyping IHtyping0.
        rewrite Nat.add_comm.
        induction H; simpl; auto.
        rewrite map_length.
        rewrite lift_lift_permutation; try lia.
        constructor; auto.
      * admit.
Admitted.

Theorem weakening:
  forall g e t,
  typing g e t ->
  forall x,
  valid_env (x :: g) -> typing (x :: g) (lift 1 0 e) (lift 1 0 t).
Proof.
  intros.
  apply typing_weak_lift with g x; auto with cps.
Qed.
*)
