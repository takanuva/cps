(******************************************************************************)
(*   Copyright (c) 2019--2024 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Lia.
Require Import Arith.
Require Import Setoid.
Require Import List.
Require Import Relations.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.AbstractRewriting.
Require Import Local.Substitution.

Export ListNotations.

Variant mode: Set :=
  | mode_input
  | mode_output.

Notation I := mode_input.
Notation O := mode_output.

Inductive type: Set :=
  | channel (m: mode) (ts: list type).

Inductive term: Set :=
  | inactive
  | restriction (t: type) (p: term)
  | parallel (p: term) (q: term)
  | output (k: nat) (ns: list nat)
  | input (k: nat) (ts: list type) (p: term)
  | replication (k: nat) (ts: list type) (p: term).

Local Notation poly_restriction :=
  (fold_left (fun e t => restriction t e)).

Fixpoint sequence i n :=
  match n with
  | 0 => []
  | S m => i :: sequence (1 + i) m
  end.

Definition bound_output (n: nat) (ts: list type) (p: term) :=
  (* TODO: reuse this from the CPS-calculus? *)
  poly_restriction ts (parallel (output (length ts + n)
                                (sequence 0 (length ts))) p).

Fixpoint traverse (f: nat -> nat -> nat) (k: nat) (e: term): term :=
  match e with
  | inactive =>
    inactive
  | restriction t p =>
    restriction t (traverse f (S k) p)
  | parallel p q =>
    parallel (traverse f k p) (traverse f k q)
  | output n ns =>
    output (f k n) (map (f k) ns)
  | input n ts p =>
    input (f k n) ts (traverse f (length ts + k) p)
  | replication n ts p =>
    replication (f k n) ts (traverse f (length ts + k) p)
  end.

Global Instance pi_dbTraverse: dbTraverse term nat :=
  traverse.

Global Instance pi_dbTraverseLaws: dbTraverseLaws term nat.
Proof.
  split; unfold Substitution.traverse; intros.
  - generalize dependent k.
    induction x; intros; simpl; auto;
    f_equal; eauto.
    induction ns; auto; simpl;
    f_equal; eauto.
  - specialize (H k (output n [])).
    dependent destruction H.
    assumption.
  - generalize dependent j.
    generalize dependent k.
    induction x; intros; simpl; auto;
    f_equal; auto.
    + apply IHx; intros.
      replace (l + S k) with (S l + k) by lia.
      replace (l + S j) with (S l + j) by lia.
      apply H.
    + apply H with (l := 0).
    + induction ns; auto; simpl; f_equal; auto.
      apply H with (l := 0).
    + apply H with (l := 0).
    + apply IHx; intros.
      do 2 rewrite Nat.add_assoc.
      apply H.
    + apply H with (l := 0).
    + apply IHx; intros.
      do 2 rewrite Nat.add_assoc.
      apply H.
  - generalize dependent k.
    induction x; intros; simpl; auto;
    f_equal; auto.
    now rewrite map_map.
Qed.

Definition switch_bindings: substitution :=
  subst_app [1; 0] (subst_lift 2).

Definition remove_binding: substitution :=
  subst_cons 0 subst_ids.

Definition inverse (m: mode): mode :=
  match m with
  | I => O
  | O => I
  end.

Fixpoint dual (t: type): type :=
  match t with
  | channel m ts =>
    channel (inverse m) (map dual ts)
  end.

Lemma dual_is_involutive:
  forall t,
  dual (dual t) = t.
Proof.
  fix H 1; destruct t.
  destruct m; simpl.
  - rewrite map_map; f_equal.
    induction ts; simpl.
    + reflexivity.
    + f_equal; auto.
  - rewrite map_map; f_equal.
    induction ts; simpl.
    + reflexivity.
    + f_equal; auto.
Qed.

Inductive alternating: mode -> type -> Prop :=
  | alternating_input:
    forall ts,
    Forall (alternating O) ts ->
    alternating I (channel I ts)
  | alternating_output:
    forall ts,
    Forall (alternating I) ts ->
    alternating O (channel O ts).

Lemma alternating_inverse_dual:
  forall m t,
  alternating m t ->
  alternating (inverse m) (dual t).
Proof.
  fix H 3; destruct 1; simpl.
  - constructor.
    induction H0; simpl.
    + constructor.
    + constructor; auto.
      now apply H in H0.
  - constructor.
    induction H0; simpl.
    + constructor.
    + constructor; auto.
      now apply H in H0.
Qed.

Definition get_mode (t: type): mode :=
  match t with
  | channel m ts => m
  end.

(* TODO: define size? *)

(* TODO: define subterm? *)

Inductive context: Set :=
  | context_hole
  | context_restriction (t: type) (p: context)
  | context_parallel_left (p: context) (q: term)
  | context_parallel_right (p: term) (q: context)
  | context_input (n: nat) (ts: list type) (p: context)
  | context_replication (n: nat) (ts: list type) (p: context).

Fixpoint apply_context (h: context) (e: term): term :=
  match h with
  | context_hole => e
  | context_restriction t p => restriction t (apply_context p e)
  | context_parallel_left p q => parallel (apply_context p e) q
  | context_parallel_right p q => parallel p (apply_context q e)
  | context_input n ts p => input n ts (apply_context p e)
  | context_replication n ts p => replication n ts (apply_context p e)
  end.

Coercion apply_context: context >-> Funclass.

Definition context_bound_output (n: nat) (ts: list type) (p: context) :=
  fold_left (fun e t => context_restriction t e) ts
    (context_parallel_right
      (output (length ts + n) (sequence 0 (length ts))) p).

Lemma apply_context_bound_output_is_sound:
  forall ts n h e,
  context_bound_output n ts h e = bound_output n ts (h e).
Proof.
  intros.
  unfold bound_output.
  unfold context_bound_output.
  generalize (output (length ts + n) (sequence 0 (length ts))) as p.
  clear n.
  generalize dependent e.
  generalize dependent h.
  induction ts using rev_ind; intros.
  - simpl.
    reflexivity.
  - do 2 rewrite fold_left_app; simpl.
    f_equal; apply IHts.
Qed.

Inductive not_free: nat -> term -> Prop :=
  | not_free_inactive:
    forall n,
    not_free n inactive
  | not_free_restriction:
    forall n t p,
    not_free (S n) p ->
    not_free n (restriction t p)
  | not_free_parallel:
    forall n p q,
    not_free n p ->
    not_free n q ->
    not_free n (parallel p q)
  | not_free_output:
    forall n k ns,
    n <> k ->
    Forall (fun m => n <> m) ns ->
    not_free n (output k ns)
  | not_free_input:
    forall n k ts p,
    n <> k ->
    not_free (length ts + n) p ->
    not_free n (input k ts p)
  | not_free_replication:
    forall n k ts p,
    n <> k ->
    not_free (length ts + n) p ->
    not_free n (replication k ts p).

Definition free (n: nat) (e: term): Prop :=
  ~not_free n e.

Definition closed (e: term): Prop :=
  forall n, not_free n e.

Inductive structural: relation term :=
  | structural_parallel_inactive:
    (* p | 0 = p *)
    forall p,
    structural (parallel p inactive)
               p
  | structural_parallel_commutative:
    (* p | q = q | p *)
    forall p q,
    structural (parallel p q)
               (parallel q p)
  | structural_paralllel_associative:
    (* (p | q) | r = p | (q | r) *)
    forall p q r,
    structural (parallel (parallel p q) r)
               (parallel p (parallel q r))
  | structural_restriction_inactive:
    (* (\x)0 = 0 *)
    forall t,
    structural (restriction t inactive)
               inactive
  | structural_restriction_switch:
    (* (\x)(\y)p = (\y)(\x)p *)
    forall t u p,
    structural (restriction t (restriction u p))
               (restriction u (restriction t (switch_bindings 0 p)))
  | structural_extrusion:
    (* (\x)(p | q) = (\x)p | q, given x not free in q *)
    forall t p q,
    not_free 0 q ->
    structural (restriction t (parallel p q))
               (parallel (restriction t p) (remove_binding 0 q))
  | structural_restriction:
    (* if p = q, then (\x)p = (\x)q *)
    forall t p q,
    structural p q ->
    structural (restriction t p) (restriction t q)
  | structural_parallel_left:
    (* if p = q, then p | r = q | r *)
    forall p q r,
    structural p q ->
    structural (parallel p r) (parallel q r)
  | structural_input:
    (* if p = q, then x(y).p = x(y).q *)
    forall x ts p q,
    structural p q ->
    structural (input x ts p) (input x ts q)
  | structural_replication:
    (* if p = q, then !x(y).p = !x(y).q *)
    forall x ts p q,
    structural p q ->
    structural (replication x ts p) (replication x ts q)
  | structural_refl:
    (* p = p *)
    forall p,
    structural p p
  | structural_sym:
    (* if p = q, then q = p *)
    forall p q,
    structural p q ->
    structural q p
  | structural_trans:
    (* if p = q and q = r, then p = r *)
    forall p q r,
    structural p q ->
    structural q r ->
    structural p r.

Global Instance structural_is_an_equivalence: Equivalence structural.
Proof.
  split.
  - exact structural_refl.
  - exact structural_sym.
  - exact structural_trans.
Qed.

Lemma structural_parallel_right:
  (* if p = q, then r | p = r | q *)
  forall p q r,
  structural p q ->
  structural (parallel r p) (parallel r q).
Proof.
  intros.
  transitivity (parallel p r).
  - constructor.
  - transitivity (parallel q r).
    + now constructor.
    + constructor.
Qed.

Lemma structural_context:
  forall (h: context) p q,
  structural p q ->
  structural (h p) (h q).
Proof.
  induction h; simpl; intros.
  - assumption.
  - constructor.
    now apply IHh.
  - constructor.
    now apply IHh.
  - apply structural_parallel_right.
    now apply IHh.
  - constructor.
    now apply IHh.
  - constructor.
    now apply IHh.
Qed.

(* TODO: check the structural rule x[y] z[w] p = z[w] x[y] p. *)

(* TODO: check the structural rule (\z)x[y] p = x[y] (\z)p. *)

(* TODO: check the structural rule x[y] (p | q) = x[y] p | q. *)

(* TODO: define canonical forms. Oh boy. *)

Inductive step: relation term :=
  | step_linear:
    (* x<y> | x(z).p -> p[y/z] *)
    forall x ys ts p,
    length ys = length ts ->
    step (parallel (output x ys) (input x ts p))
         (inst (subst_app ys subst_ids) p)
  | step_replicated:
    (* x<y> | !x(z).p -> p[y/z] | !x(z).p *)
    forall x ys ts p,
    length ys = length ts ->
    step (parallel (output x ys) (replication x ts p))
         (parallel (inst (subst_app ys subst_ids) p) (replication x ts p))
  | step_restriction:
    (* if p -> q, then (\x)p -> (\x)q *)
    forall t p q,
    step p q ->
    step (restriction t p) (restriction t q)
  | step_parallel_left:
    (* if p -> q, then p | r -> q | r *)
    forall p q r,
    step p q ->
    step (parallel p r) (parallel q r)
  | step_structural:
    (* if p = q, q -> r, and r = s, then p -> s *)
    forall p q r s,
    structural p q ->
    step q r ->
    structural r s ->
    step p s.

Lemma step_parallel_right:
  (* if p -> q, then r | p -> r | q *)
  forall p q r,
  step p q ->
  step (parallel r p) (parallel r q).
Proof.
  intros.
  eapply step_structural.
  - apply structural_parallel_commutative.
  - apply step_parallel_left.
    eassumption.
  - apply structural_parallel_commutative.
Qed.

Goal
  (* Let's check that the bound output version, [y] p | x(y).q -> (\y)(p | q),
     as described in Honda's paper, is derivable with the above definitions. *)
  forall ts x p q,
  step (parallel (bound_output x ts p) (input x ts p))
       (poly_restriction ts (parallel p q)).
Proof.
  induction ts using rev_ind; intros.
  - simpl.
    admit.
  - admit.
Admitted.

Definition label: Set := mode * nat.

Inductive observable: term -> label -> Prop :=
  (* TODO: observability predicate. *)
  .

Lemma structural_is_barb_preserving:
  forall p l,
  observable p l ->
  forall q,
  structural p q ->
  observable q l.
Proof.
  admit.
Admitted.

Definition barb: relation term :=
  barbed_congruence step observable apply_context.

Global Instance barb_is_an_equivalence: Equivalence barb.
Proof.
  split.
  - apply barbed_congruence_refl.
  - apply barbed_congruence_sym.
  - apply barbed_congruence_trans.
Qed.

Lemma structural_congruence_is_a_barbed_simulation:
  barbed_simulation step observable structural.
Proof.
  split; repeat intro.
  - exists c.
    + apply rt_step.
      eapply step_structural.
      * symmetry.
        eassumption.
      * eassumption.
      * reflexivity.
    + reflexivity.
  - exists b.
    + apply rt_refl.
    + now apply structural_is_barb_preserving with a.
Qed.

Lemma barb_structural:
  inclusion structural barb.
Proof.
  intros x y ?.
  exists structural.
  - clear H h x y.
    apply symmetric_barbed_simulation_is_bisimulation.
    + apply structural_congruence_is_a_barbed_simulation.
    + exact structural_sym.
  - now apply structural_context.
Qed.
