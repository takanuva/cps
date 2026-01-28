Require Import Lia.
Require Import Arith.
Require Import Program.
Require Import Equality.
Require Import Relations.
Require Import RelationClasses.

Section Sigma.

  Variant sort: Set :=
    | TERM
    | SUBST
    | NUM
    | VECTOR.

  Inductive t: sort -> Set :=
    (* Term syntax: *)
    | metat (n: nat): t TERM
    | index (n: t NUM): t TERM
    | abstraction (e: t TERM): t TERM
    | application (e: t TERM) (f: t TERM): t TERM
    | dblift (i: t NUM) (k: t NUM) (e: t TERM): t TERM
    | dbtraverse (s: t SUBST) (k: t NUM) (e: t TERM): t TERM
    | instantiation (s: t SUBST) (e: t TERM): t TERM
    (* Substitution syntax: *)
    | metas (n: nat): t SUBST
    | iota: t SUBST
    | slift (n: t NUM): t SUBST
    | concatenate (v: t VECTOR) (s: t SUBST): t SUBST
    | compose (s: t SUBST) (r: t SUBST): t SUBST
    | uplift (n: t NUM) (s: t SUBST): t SUBST
    | subst (e: t TERM): t SUBST
    (* Vector syntax: *)
    | metav (n: nat): t VECTOR
    | nil: t VECTOR
    | cons (e: t TERM) (es: t VECTOR): t VECTOR
    | join (es: t VECTOR) (fs: t VECTOR): t VECTOR
    (* Number syntax: *)
    | metan (n: nat): t NUM
    | zero: t NUM
    | succ (n: t NUM): t NUM
    | length (v: t VECTOR): t NUM
    | SUB (n: t NUM) (m: t NUM): t NUM
    | ADD (n: t NUM) (m: t NUM): t NUM
    (* | MIN (n: t NUM) (m: t NUM): t NUM
    | MAX (n: t NUM) (m: t NUM): t NUM *).

  Coercion t: sort >-> Sortclass.

  Fixpoint number (n: nat): NUM :=
    match n with
    | 0 => zero
    | S m => succ (number m)
    end.

  Coercion number: nat >-> t.

  Variable ORACLE_NUM: nat -> nat.
  Variable ORACLE_VEC: nat -> nat.

  Fixpoint interpretation_length (x: VECTOR): nat :=
    match x with
    | metav n =>
      ORACLE_VEC n
    | nil =>
      0
    | cons _ v =>
      1 + interpretation_length v
    | join v1 v2 =>
      interpretation_length v1 + interpretation_length v2
    end.

  Fixpoint interpretation (x: NUM): nat :=
    match x with
    | metan n =>
      ORACLE_NUM n
    | zero =>
      0
    | succ n =>
      1 + interpretation n
    | length v =>
      interpretation_length v
    | SUB n m =>
      interpretation n - interpretation m
    | ADD n m =>
      interpretation n + interpretation m
    (* | MIN n m =>
      min (interpretation n) (interpretation m)
    | MAX n m =>
      max (interpretation n) (interpretation m) *)
    end.

  (* Definition DIF n m :=
    SUB (MAX n m) (MIN n m). *)

  Infix "::" := cons (at level 60, right associativity).
  Infix "++" := join (right associativity, at level 60).
  Notation " [ ] " := nil.
  Notation " [ x ] " := (cons x nil).
  Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).

  Notation var := index.
  Notation app := application.
  Notation abs := abstraction.
  Notation traverse := dbtraverse.
  Notation inst := instantiation.
  Notation lift := dblift.
  Notation subst_lift := slift.
  Notation subst_app := concatenate.
  Notation subst_ids := iota.
  Notation subst_upn := uplift.
  Notation subst_comp := compose.

  Declare Scope sigma_scope.
  Bind Scope sigma_scope with t.
  Delimit Scope sigma_scope with sigma.
  Notation "x - y" := (SUB x y): sigma_scope.
  Notation "x + y" := (ADD x y): sigma_scope.

  (* TODO: should we add drop...? *)

  (* Notation subst_drop i :=
    (subst_comp (subst_lift i))
    (only parsing). *)

  Inductive compctx: Set :=
    | compctx_hole
    | compctx_left (s: SUBST) (h: compctx).

  Fixpoint fill (h: compctx) (r: SUBST): SUBST :=
    match h with
    | compctx_hole => r
    | compctx_left s h => subst_comp s (fill h r)
    end.

  Local Coercion fill: compctx >-> Funclass.

  Inductive step: forall {s: sort}, relation (t s) :=
    (* Structural rules: *)
    | A1 e f s:
      step (inst s (app e f))
           (app (traverse s 0 e) (traverse s 0 f))
    | A2 e s:
      step (inst s (abs e))
           (abs (traverse s 1 e))
    (* Classical rules: *)
    | A3 i k e:
      step (lift i k e)
           (traverse (subst_lift i) k e)
    | A4 y:
      step (subst y)
           (subst_app [y] subst_ids)
    | A5 s k e:
      step (traverse s k e)
           (inst (subst_upn k s) e)
    (* Congruence rules: *)
    | C0 n1 n2:
      step n1 n2 -> step (index n1) (index n2)
    | C1 e1 e2:
      step e1 e2 -> step (abs e1) (abs e2)
    | C2 e1 e2 f:
      step e1 e2 -> step (app e1 f) (app e2 f)
    | C3 e f1 f2:
      step f1 f2 -> step (app e f1) (app e f2)
    | C4 i1 i2 k e:
      step i1 i2 -> step (lift i1 k e) (lift i2 k e)
    | C5 i k1 k2 e:
      step k1 k2 -> step (lift i k1 e) (lift i k2 e)
    | C6 i k e1 e2:
      step e1 e2 -> step (lift i k e1) (lift i k e2)
    | C10 s1 s2 k e:
      step s1 s2 -> step (traverse s1 k e) (traverse s2 k e)
    | C11 s k1 k2 e:
      step k1 k2 -> step (traverse s k1 e) (traverse s k2 e)
    | C12 s k e1 e2:
      step e1 e2 -> step (traverse s k e1) (traverse s k e2)
    | C13 s1 s2 e:
      step s1 s2 -> step (inst s1 e) (inst s2 e)
    | C14 s e1 e2:
      step e1 e2 -> step (inst s e1) (inst s e2)
    | C15 n1 n2:
      step n1 n2 -> step (subst_lift n1) (subst_lift n2)
    | C16 v1 v2 s:
      step v1 v2 -> step (subst_app v1 s) (subst_app v2 s)
    | C17 v s1 s2:
      step s1 s2 -> step (subst_app v s1) (subst_app v s2)
    | C18 s1 s2 r:
      step s1 s2 -> step (subst_comp s1 r) (subst_comp s2 r)
    | C19 s r1 r2:
      step r1 r2 -> step (subst_comp s r1) (subst_comp s r2)
    | C20 n1 n2 s:
      step n1 n2 -> step (subst_upn n1 s) (subst_upn n2 s)
    | C21 n s1 s2:
      step s1 s2 -> step (subst_upn n s1) (subst_upn n s2)
    | C7 y1 y2:
      step y1 y2 -> step (subst y1) (subst y2)
    | C22 e1 e2 x:
      step e1 e2 -> step (e1 :: x) (e2 :: x)
    | C23 e x1 x2:
      step x1 x2 -> step (e :: x1) (e :: x2)
    | C24 x1 x2 y:
      step x1 x2 -> step (x1 ++ y) (x2 ++ y)
    | C25 x y1 y2:
      step y1 y2 -> step (x ++ y1) (x ++ y2)
    | C26 n1 n2:
      step n1 n2 -> step (succ n1) (succ n2)
    | C27 v1 v2:
      step v1 v2 -> step (length v1) (length v2)
    | C28 n1 n2 m:
      step n1 n2 -> step (SUB n1 m) (SUB n2 m)
    | C29 n m1 m2:
      step m1 m2 -> step (SUB n m1) (SUB n m2)
    | C30 n1 n2 m:
      step n1 n2 -> step (ADD n1 m) (ADD n2 m)
    | C31 n m1 m2:
      step m1 m2 -> step (ADD n m1) (ADD n m2)
    (* Simplification laws: *)
    | A6 n:
      interpretation n = 0 ->
      step (subst_lift n) subst_ids
    | A7 n s:
      interpretation n = 0 ->
      step (subst_upn n s) s
    | A8 n:
      step (subst_upn n subst_ids) subst_ids
    | A9 e:
      step (inst subst_ids e) e
    (* Main rules for composition: *)
    | A10 s:
      step (subst_comp subst_ids s) s
    | A11 s:
      step (subst_comp s subst_ids) s
    | A12 s t u:
      step (subst_comp (subst_comp s t) u)
           (subst_comp s (subst_comp t u)).

  Create HintDb sigma.

  Hint Constructors step: sigma.
  Hint Extern 1 => lia: sigma.

  Notation star s :=
    (clos_refl_trans _ (@step s)).

  Hint Constructors clos_refl_trans: sigma.

  Instance star_refl: forall s, Reflexive (star s).
  Proof.
    repeat intro.
    apply rt_refl.
  Qed.

  Instance star_sym: forall s, Transitive (star s).
  Proof.
    repeat intro.
    now apply rt_trans with y.
  Qed.

  Hint Constructors clos_refl_trans: sigma.

  Lemma interpretation_zero:
    interpretation zero = 0.
  Proof.
    auto.
  Qed.

  Lemma interpretation_succ:
    forall n,
    interpretation (succ n) = S (interpretation n).
  Proof.
    auto.
  Qed.

  Lemma interpretation_number:
    forall n,
    interpretation (number n) = n.
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma interpretation_add:
    forall a b,
    interpretation (a + b) = interpretation a + interpretation b.
  Proof.
    simpl; auto.
  Qed.

  Lemma interpretation_sub:
    forall a b,
    interpretation (a - b) = interpretation a - interpretation b.
  Proof.
    simpl; auto.
  Qed.

  (* Lemma interpretation_min:
    forall a b,
    interpretation (MIN a b) = min (interpretation a) (interpretation b).
  Proof.
    simpl; auto.
  Qed.

  Lemma interpretation_max:
    forall a b,
    interpretation (MAX a b) = max (interpretation a) (interpretation b).
  Proof.
    simpl; auto.
  Qed. *)

  Lemma interpretation_cons_length:
    forall y ys,
    interpretation (length (y :: ys)) = interpretation (1 + length ys).
  Proof.
    simpl; auto.
  Qed.

  Lemma interpretation_nil_length:
    interpretation (length []) = interpretation 0.
  Proof.
    simpl; auto.
  Qed.

  Lemma interpretation_app_length:
    forall xs ys,
    interpretation (length (xs ++ ys)) =
      interpretation (length xs) + interpretation (length ys).
  Proof.
    simpl; auto.
  Qed.

  Create HintDb interpretation.

  Hint Rewrite interpretation_zero: interpretation.
  Hint Rewrite interpretation_succ: interpretation.
  Hint Rewrite interpretation_number: interpretation.
  Hint Rewrite interpretation_add: interpretation.
  Hint Rewrite interpretation_sub: interpretation.
  (* Hint Rewrite interpretation_min: interpretation.
  Hint Rewrite interpretation_max: interpretation. *)
  Hint Rewrite interpretation_cons_length: interpretation.
  Hint Rewrite interpretation_nil_length: interpretation.
  Hint Rewrite interpretation_app_length: interpretation.

  Lemma interpretation_consistent_vec:
    forall v u,
    @step VECTOR v u ->
    interpretation (length v) = interpretation (length u).
  Proof.
    intros.
    dependent induction H; simpl.
    - clear IHstep.
      reflexivity.
    - specialize (IHstep _ _ eq_refl JMeq_refl JMeq_refl).
      simpl in IHstep.
      congruence.
    - specialize (IHstep _ _ eq_refl JMeq_refl JMeq_refl).
      simpl in IHstep.
      congruence.
    - specialize (IHstep _ _ eq_refl JMeq_refl JMeq_refl).
      simpl in IHstep.
      congruence.
  Qed.

  Lemma interpretation_consistent_num:
    forall n m,
    @step NUM n m ->
    interpretation n = interpretation m.
  Proof.
    intros.
    dependent induction H.
    - specialize (IHstep _ _ eq_refl JMeq_refl JMeq_refl).
      simpl; rewrite IHstep.
      reflexivity.
    - clear IHstep.
      now apply interpretation_consistent_vec.
    - specialize (IHstep _ _ eq_refl JMeq_refl JMeq_refl).
      simpl; rewrite IHstep.
      reflexivity.
    - specialize (IHstep _ _ eq_refl JMeq_refl JMeq_refl).
      simpl; rewrite IHstep.
      reflexivity.
    - specialize (IHstep _ _ eq_refl JMeq_refl JMeq_refl).
      simpl; rewrite IHstep.
      reflexivity.
    - specialize (IHstep _ _ eq_refl JMeq_refl JMeq_refl).
      simpl; rewrite IHstep.
      reflexivity.
  Qed.

  Lemma interpretation_consistent_len:
    forall xs ys,
    @step VECTOR xs ys ->
    interpretation (length xs) = interpretation (length ys).
  Proof.
    intros.
    dependent induction H.
    - simpl; auto.
    - simpl; eauto.
    - simpl; eauto.
    - simpl; eauto.
  Qed.

  Hint Resolve interpretation_consistent_num: sigma.
  Hint Resolve interpretation_consistent_len: sigma.

  Definition joinable {s} (y: t s) (z: t s): Prop :=
    exists2 w,
    @star s y w & @star s z w.

  Instance joinable_refl: forall {s}, Reflexive (@joinable s).
  Proof.
    repeat intro.
    exists x; eauto with sigma.
  Qed.

  Instance joinable_sym: forall {s}, Symmetric (@joinable s).
  Proof.
    repeat intro.
    destruct H as (z, ?, ?).
    firstorder.
  Qed.

  Lemma joinable_step:
    forall {s} e1 e2,
    @step s e1 e2 ->
    @joinable s e1 e2.
  Proof.
    intros.
    exists e2; auto with sigma.
  Qed.

  Lemma C0_join:
    forall n1 n2,
    joinable n1 n2 ->
    joinable (index n1) (index n2).
  Proof with eauto with sigma.
    intros n1 n2 (n3, ?, ?).
    exists (var n3).
    - clear H0.
      induction H...
    - clear H.
      induction H0...
  Qed.

  Lemma C1_join:
    forall e1 e2,
    joinable e1 e2 ->
    joinable (abs e1) (abs e2).
  Proof with eauto with sigma.
    intros e1 e2 (e3, ?, ?).
    exists (abs e3).
    - clear H0.
      induction H...
    - clear H.
      induction H0...
  Qed.

  Lemma C2_join:
    forall e1 e2 f1 f2,
    joinable e1 e2 ->
    joinable f1 f2 ->
    joinable (app e1 f1) (app e2 f2).
  Proof with eauto with sigma.
    intros e1 e2 f1 f2 (e3, ?, ?) (f3, ?, ?).
    exists (app e3 f3).
    - clear H0 H2.
      apply rt_trans with (app e3 f1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (app e3 f2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C3_join:
    forall i1 i2 k1 k2 e1 e2,
    joinable i1 i2 ->
    joinable k1 k2 ->
    joinable e1 e2 ->
    joinable (lift i1 k1 e1) (lift i2 k2 e2).
  Proof with eauto with sigma.
    intros i1 i2 k1 k2 e1 e2 (i3, ?, ?) (k3, ?, ?) (e3, ?, ?).
    exists (lift i3 k3 e3).
    - clear H0 H2 H4.
      apply rt_trans with (lift i3 k1 e1).
      + clear H1 H3.
        induction H...
      + clear H.
        apply rt_trans with (lift i3 k3 e1).
        * clear H3.
          induction H1...
        * clear H1.
          induction H3...
    - clear H H1 H3.
      apply rt_trans with (lift i3 k2 e2).
      + clear H2 H4.
        induction H0...
      + clear H0.
        apply rt_trans with (lift i3 k3 e2).
        * clear H4.
          induction H2...
        * clear H2.
          induction H4...
  Qed.

  Lemma C4_join:
    forall y1 y2,
    joinable y1 y2 ->
    joinable (subst y1) (subst y2).
  Proof with eauto with sigma.
    intros y1 y2 (y3, ?, ?).
    exists (subst y3).
    - clear H0.
      induction H...
    - clear H.
      induction H0...
  Qed.

  Lemma C5_join:
    forall s1 s2 k1 k2 e1 e2,
    joinable s1 s2 ->
    joinable k1 k2 ->
    joinable e1 e2 ->
    joinable (traverse s1 k1 e1) (traverse s2 k2 e2).
  Proof with eauto with sigma.
    intros s1 s2 k1 k2 e1 e2 (s3, ?, ?) (k3, ?, ?) (e3, ?, ?).
    exists (traverse s3 k3 e3).
    - clear H0 H2 H4.
      apply rt_trans with (traverse s3 k1 e1).
      + clear H1 H3.
        induction H...
      + clear H.
        apply rt_trans with (traverse s3 k3 e1).
        * clear H3.
          induction H1...
        * clear H1.
          induction H3...
    - clear H H1 H3.
      apply rt_trans with (traverse s3 k2 e2).
      + clear H2 H4.
        induction H0...
      + clear H0.
        apply rt_trans with (traverse s3 k3 e2).
        * clear H4.
          induction H2...
        * clear H2.
          induction H4...
  Qed.

  Lemma C6_join:
    forall s1 s2 e1 e2,
    joinable s1 s2 ->
    joinable e1 e2 ->
    joinable (inst s1 e1) (inst s2 e2).
  Proof with eauto with sigma.
    intros s1 s2 e1 e2 (s3, ?, ?) (e3, ?, ?).
    exists (inst s3 e3).
    - clear H0 H2.
      apply rt_trans with (inst s3 e1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (inst s3 e2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C7_join:
    forall n1 n2,
    joinable n1 n2 ->
    joinable (subst_lift n1) (subst_lift n2).
  Proof with eauto with sigma.
    intros n1 n2 (n3, ?, ?).
    exists (subst_lift n3).
    - clear H0.
      induction H...
    - clear H.
      induction H0...
  Qed.

  Lemma C8_join:
    forall v1 v2 s1 s2,
    joinable v1 v2 ->
    joinable s1 s2 ->
    joinable (subst_app v1 s1) (subst_app v2 s2).
  Proof with eauto with sigma.
    intros v1 v2 s1 s2 (v3, ?, ?) (s3, ?, ?).
    exists (subst_app v3 s3).
    - clear H0 H2.
      apply rt_trans with (subst_app v3 s1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (subst_app v3 s2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C9_join:
    forall s1 s2 r1 r2,
    joinable s1 s2 ->
    joinable r1 r2 ->
    joinable (subst_comp s1 r1) (subst_comp s2 r2).
  Proof with eauto with sigma.
    intros s1 s2 r1 r2 (s3, ?, ?) (r3, ?, ?).
    exists (subst_comp s3 r3).
    - clear H0 H2.
      apply rt_trans with (subst_comp s3 r1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (subst_comp s3 r2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C10_join:
    forall n1 n2 s1 s2,
    joinable n1 n2 ->
    joinable s1 s2 ->
    joinable (subst_upn n1 s1) (subst_upn n2 s2).
  Proof with eauto with sigma.
    intros n1 n2 s1 s2 (n3, ?, ?) (s3, ?, ?).
    exists (subst_upn n3 s3).
    - clear H0 H2.
      apply rt_trans with (subst_upn n3 s1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (subst_upn n3 s2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C11_join:
    forall e1 e2 x1 x2,
    joinable e1 e2 ->
    joinable x1 x2 ->
    joinable (e1 :: x1) (e2 :: x2).
  Proof with eauto with sigma.
    intros e1 e2 x1 x2 (e3, ?, ?) (x3, ?, ?).
    exists (e3 :: x3).
    - clear H0 H2.
      apply rt_trans with (e3 :: x1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (e3 :: x2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C12_join:
    forall x1 x2 y1 y2,
    joinable x1 x2 ->
    joinable y1 y2 ->
    joinable (x1 ++ y1) (x2 ++ y2).
  Proof with eauto with sigma.
    intros x1 x2 y1 y2 (x3, ?, ?) (y3, ?, ?).
    exists (x3 ++ y3).
    - clear H0 H2.
      apply rt_trans with (x3 ++ y1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (x3 ++ y2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C13_join:
    forall n1 n2 m1 m2,
    joinable n1 n2 ->
    joinable m1 m2 ->
    joinable (SUB n1 m1) (SUB n2 m2).
  Proof with eauto with sigma.
    intros n1 n2 m1 m2 (n3, ?, ?) (m3, ?, ?).
    exists (SUB n3 m3).
    - clear H0 H2.
      apply rt_trans with (SUB n3 m1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (SUB n3 m2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C14_join:
    forall n1 n2 m1 m2,
    joinable n1 n2 ->
    joinable m1 m2 ->
    joinable (ADD n1 m1) (ADD n2 m2).
  Proof with eauto with sigma.
    intros n1 n2 m1 m2 (n3, ?, ?) (m3, ?, ?).
    exists (ADD n3 m3).
    - clear H0 H2.
      apply rt_trans with (ADD n3 m1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (ADD n3 m2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Hint Resolve joinable_step: sigma.
  Hint Resolve C0_join: sigma.
  Hint Resolve C1_join: sigma.
  Hint Resolve C2_join: sigma.  
  Hint Resolve C3_join: sigma.
  Hint Resolve C4_join: sigma.
  Hint Resolve C5_join: sigma.
  Hint Resolve C6_join: sigma.
  Hint Resolve C7_join: sigma.
  Hint Resolve C8_join: sigma.
  Hint Resolve C9_join: sigma.
  Hint Resolve C10_join: sigma.
  Hint Resolve C11_join: sigma.
  Hint Resolve C12_join: sigma.
  Hint Resolve C13_join: sigma.
  Hint Resolve C14_join: sigma.

  Definition sumup (k: nat) (f: TERM -> nat) :=
    fix sumup (v: VECTOR) :=
      match v with
      | metav _ => 0
      | nil => 0
      | cons e v => k + f e + sumup v
      | join v u => sumup v + sumup u
      end.

  (* ---------------------------------------------------------------------- *)

  Fixpoint measure1 {s: sort} (expr: s) {struct expr}: nat :=
    match expr with
    (* TERM *)
    | metat _ => 2
    | index n => 2 ^ interpretation n
    | abstraction e => 2 + measure1 e
    | application e f => measure1 e + measure1 f
    | dblift i k e => max 2 (2 ^ interpretation i) * measure1 e
    | dbtraverse s k e => measure1 s * measure1 e
    | instantiation s e => measure1 s * measure1 e
    (* SUBST *)
    | metas _ => 2
    | iota => 2
    | slift n => max 2 (2 ^ interpretation n)
    | concatenate v s => sumup 0 measure1 v + measure1 s
    | compose s t => measure1 s * measure1 t
    | uplift n s => measure1 s
    | subst y => 2 + measure1 y
    (* VECTOR *)
    | metav _ => 0
    | nil => 0
    | cons e v => measure1 e + sumup 0 measure1 v
    | join v u => sumup 0 measure1 v + sumup 0 measure1 u
    (* NUMBER *)
    | metan n => 1
    | zero => 1
    | succ n => 1 + measure1 n
    | length v => 1 + measure1 v
    | SUB n m => 1 + measure1 n + measure1 m
    | ADD n m => 1 + measure1 n + measure1 m
    (* | MIN n m => interpretation (MIN n m)
    | MAX n m => interpretation (MAX n m) *)
    end.

  Fixpoint measure2 {s: sort} (expr: s) {struct expr}: nat :=
    match expr with
    (* TERM *)
    | metat _ => 1
    | index n => 1
    | abstraction e => 2 * measure2 e
    | application e f => 1 + measure2 e + measure2 f
    | dblift i k e => measure2 e *
                        (1 + 4 ^ interpretation k * max 1 (interpretation i))
    | dbtraverse s k e => measure2 e * (1 + 4 ^ interpretation k * measure2 s)
    | instantiation s e => measure2 e * (1 + measure2 s)
    (* SUBST *)
    | metas _ => 1
    | iota => 1
    | slift n => max 1 (interpretation n)
    | concatenate v s => sumup 1 measure2 v + measure2 s
    | compose s t => measure2 s * (1 + measure2 t)
    | uplift n s => 4 ^ interpretation n * measure2 s
    | subst y => 2 + measure2 y
    (* VECTOR *)
    | metav _ => 0
    | nil => 0
    | cons e v => 1 + measure2 e + sumup 1 measure2 v
    | join v u => sumup 1 measure2 v + sumup 1 measure2 u
    (* NUMBER *)
    | metan n => interpretation (metan n)
    | zero => interpretation zero
    | succ n => interpretation (succ n)
    | length v => interpretation (length v)
    | SUB n m => interpretation (SUB n m)
    | ADD n m => interpretation (ADD n m)
    (* | MIN n m => interpretation (MIN n m)
    | MAX n m => interpretation (MAX n m) *)
    end.

  (*
    In order to properly calculate the optimal values for the 3rd weight, we
    will use linear optimization in here, taking the formulas from the desired
    properties as we check them below.

    For now, I assume those exist by simple addition on subterms; it might be
    possible that some stuff (e.g., composition) might require multiplication.

    We use the following model, giving the optimal solutions:

    var x1 >= 1;
    var x2 >= 1;
    var x3 >= 1;
    var x4 >= 1;
    var x5 >= 1;
    var x6 >= 1;
    var x7 >= 1;
    var x8 >= 1;
    var x9 >= 1;
    var x10 >= 1;
    var x11 >= 1;
    var x12 >= 1;
    var x13 >= 1;
    var x14 >= 1;
    var x15 >= 1;
    var x16 >= 1;
    var x17 >= 1;
    var x18 >= 1;
    var x19 >= 1;
    var x20 >= 1;
    var x21 >= 1;
    var x22 >= 1;
    var x23 >= 1;
    var x24 >= 1;
    var x25 >= 1;
    var x26 >= 1;

    subject to lift: x7 + x11 + 1 <= x5;
    subject to subst: x10 + x12 + x16 + x17 + 1 <= x6;
    subject to traverse: x8 + x14 + 1 <= x7;
    subject to lift_ids: x10 <= x11;
    subject to upn_join: x14 + x24 + 1 <= 2 * x14;
    subject to simpl_app: x18 + 1 <= x12;

    minimize s: x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 +
                x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 +
                x20 + x21 + x22 + x23 + x24 + x25 + x26;

    end; *)

  Definition X1 := 1.
  Definition X2 := 1.
  Definition X3 := 1.
  Definition X4 := 1.
  Definition X5 := 6.
  Definition X6 := 6.
  Definition X7 := 4.
  Definition X8 := 1.
  Definition X9 := 1.
  Definition X10 := 1.
  Definition X11 := 1.
  Definition X12 := 2.
  Definition X13 := 1.
  Definition X14 := 2.
  Definition X15 := 1.
  Definition X16 := 1.
  Definition X17 := 1.
  Definition X18 := 1.
  Definition X19 := 1.
  Definition X20 := 1.
  Definition X21 := 1.
  Definition X22 := 1.
  Definition X23 := 1.
  Definition X24 := 1.
  Definition X25 := 1.
  Definition X26 := 1.

  Hint Unfold X1: sigma.
  Hint Unfold X2: sigma.
  Hint Unfold X3: sigma.
  Hint Unfold X4: sigma.
  Hint Unfold X5: sigma.
  Hint Unfold X6: sigma.
  Hint Unfold X7: sigma.
  Hint Unfold X8: sigma.
  Hint Unfold X9: sigma.
  Hint Unfold X10: sigma.
  Hint Unfold X11: sigma.
  Hint Unfold X12: sigma.
  Hint Unfold X13: sigma.
  Hint Unfold X14: sigma.
  Hint Unfold X15: sigma.
  Hint Unfold X16: sigma.
  Hint Unfold X17: sigma.
  Hint Unfold X18: sigma.
  Hint Unfold X19: sigma.
  Hint Unfold X20: sigma.
  Hint Unfold X21: sigma.
  Hint Unfold X22: sigma.
  Hint Unfold X23: sigma.
  Hint Unfold X24: sigma.
  Hint Unfold X25: sigma.
  Hint Unfold X26: sigma.

  Ltac unfold_weight :=
    autounfold with sigma.

  Fixpoint measure3 {s: sort} (expr: s) {struct expr}: nat :=
    match expr with
    (* TERM *)
    | metat _ => X1
    | index n => X2 + measure3 n
    | abstraction e => X3 + measure3 e
    | application e f => X4 + measure3 e + measure3 f
    | dblift i k e => X5 + measure3 i + measure3 k + measure3 e
    | dbtraverse s k e => X7 + measure3 s + measure3 k + measure3 e
    | instantiation s e => X8 + measure3 s + measure3 e
    (* SUBST *)
    | metas _ => X9
    | iota => X10
    | slift n => X11 + measure3 n
    | concatenate v s => X12 + measure3 v + measure3 s
    | compose s t => X13 + measure3 s + measure3 t
    | uplift n s => X14 + measure3 n + measure3 s
    | subst y => X6 + measure3 y
    (* VECTOR *)
    | metav _ => X15
    | nil => X16
    | cons e v => X17 + measure3 e + measure3 v
    | join v u => X18 + measure3 v + measure3 u
    (* NUMBER *)
    | metan n => X19
    | zero => X20
    | succ n => X21 + measure3 n
    | length v => X22 + measure3 v
    | SUB n m => X23 + measure3 n + measure3 m
    | ADD n m => X24 + measure3 n + measure3 m
    (* | MIN n m => X25 + measure3 n + measure3 m
    | MAX n m => X26 + measure3 n + measure3 m *)
    end.

  Lemma power_is_positive:
    forall i n,
    S i ^ n > 0.
  Proof.
    induction n; simpl; lia.
  Qed.

  Lemma measure1_subst_pos:
    forall e: SUBST,
    measure1 e > 1.
  Proof.
    intros.
    dependent induction e; simpl.
    - auto.
    - auto.
    - clear IHe.
      remember (2 ^ interpretation e) as n.
      destruct n.
      + exfalso.
        assert (2 ^ interpretation e > 0) by apply power_is_positive.
        lia.
      + destruct n; try lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHe1 _ eq_refl JMeq_refl).
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      assumption.
    - nia.
  Qed.

  Lemma measure1_num_pos:
    forall n: NUM,
    measure1 n > 0.
  Proof.
    intros.
    dependent induction n; simpl; lia.
  Qed.

  Lemma measure1_term_pos:
    forall e: TERM,
    measure1 e > 0.
  Proof.
    intros.
    dependent induction e; simpl.
    - auto.
    - clear IHe.
      apply power_is_positive.
    - lia.
    - specialize (IHe1 _ eq_refl JMeq_refl).
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - clear IHe1 IHe2.
      specialize (IHe3 _ eq_refl JMeq_refl).
      remember (2 ^ interpretation e1) as n.
      destruct n; simpl; lia.
    - clear IHe1 IHe2.
      specialize (IHe3 _ eq_refl JMeq_refl).
      assert (measure1 e1 > 1) by apply measure1_subst_pos.
      lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      assert (measure1 e1 > 1) by apply measure1_subst_pos.
      lia.
  Qed.

  Lemma measure2_subst_pos:
    forall e: SUBST,
    measure2 e > 0.
  Proof.
    intros.
    dependent induction e; simpl.
    - auto.
    - auto.
    - clear IHe.
      destruct (interpretation e); lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHe1 _ eq_refl JMeq_refl).
      lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      assert (4 ^ interpretation e1 > 0).
      + apply power_is_positive.
      + lia.
    - nia.
  Qed.

  Lemma measure2_term_pos:
    forall e: TERM,
    measure2 e > 0.
  Proof.
    intros.
    dependent induction e; simpl.
    - auto.
    - auto.
    - specialize (IHe _ eq_refl JMeq_refl).
      lia.
    - lia.
    - specialize (IHe3 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHe3 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
  Qed.

  Lemma measure1_lift_unfolding:
    forall i k e,
    measure1 (lift i k e) = measure1 (traverse (subst_lift i) k e).
  Proof.
    intros; simpl.
    lia.
  Qed.

  Lemma measure1_subst_unfolding:
    forall y,
    measure1 (subst y) = measure1 (subst_app [y] subst_ids).
  Proof.
    intros; simpl.
    lia.
  Qed.

  Lemma measure1_traverse_unfolding:
    forall s k e,
    measure1 (traverse s k e) = measure1 (inst (subst_upn k s) e).
  Proof.
    intros; simpl.
    reflexivity.
  Qed.

  Lemma measure2_lift_unfolding:
    forall i k e,
    measure2 (lift i k e) = measure2 (traverse (subst_lift i) k e).
  Proof.
    intros; simpl.
    reflexivity.
  Qed.

  Lemma measure2_subst_unfolding:
    forall y,
    measure2 (subst y) = measure2 (subst_app [y] subst_ids).
  Proof.
    intros; simpl.
    lia.
  Qed.

  Lemma measure2_traverse_unfolding:
    forall s k e,
    measure2 (traverse s k e) = measure2 (inst (subst_upn k s) e).
  Proof.
    intros; simpl.
    reflexivity.
  Qed.

  Inductive LT {s: sort}: relation s :=
    | LT1:
      forall x y,
      measure1 x < measure1 y ->
      LT x y
    | LT2:
      forall x y,
      measure1 x = measure1 y ->
      measure2 x < measure2 y ->
      LT x y
    | LT3:
      forall x y,
      measure1 x = measure1 y ->
      measure2 x = measure2 y ->
      measure3 x < measure3 y ->
      LT x y.

  Lemma LT_trans:
    forall s x y z,
    @LT s x y ->
    @LT s y z ->
    @LT s x z.
  Proof.
    destruct 1; destruct 1.
    - constructor 1; lia.
    - constructor 1; lia.
    - constructor 1; lia.
    - constructor 1; lia.
    - constructor 2; lia.
    - constructor 2; lia.
    - constructor 1; lia.
    - constructor 2; lia.
    - constructor 3; lia.
  Qed.

  Lemma LT_is_well_founded:
    forall s,
    well_founded (@LT s).
  Proof.
    repeat intro.
    remember (measure1 a) as n1.
    remember (measure2 a) as n2.
    remember (measure3 a) as n3.
    generalize dependent a.
    generalize dependent n3.
    generalize dependent n2.
    induction n1 using lt_wf_ind.
    intro.
    induction n2 using lt_wf_ind.
    intro.
    induction n3 using lt_wf_ind.
    intros; subst.
    constructor; intros.
    destruct H2.
    - eapply H; now try reflexivity.
    - eapply H0; now try reflexivity.
    - eapply H1; now try reflexivity.
  Qed.

  Lemma sumup0_measure1_simpl:
    forall v,
    sumup 0 measure1 v = measure1 v.
  Proof.
    intros.
    dependent induction v; simpl; auto.
  Qed.

  Lemma sumup1_measure2_simpl:
    forall v,
    sumup 1 measure2 v = measure2 v.
  Proof.
    intros.
    dependent induction v; auto.
  Qed.

  Lemma measure3_pos:
    forall s x,
    @measure3 s x > 0.
  Proof.
    induction x; simpl;
    unfold_weight; nia.
  Qed.

  Lemma decreasing:
    forall s x y,
    @step s x y ->
    @LT s y x.
  Proof with (unfold_weight; ring_simplify).
    induction 1; intros.
    - constructor 2; simpl.
      + nia.
      + assert (measure2 s > 0) by apply measure2_subst_pos.
        nia.
    - constructor 1; simpl.
      assert (measure1 s > 1) by apply measure1_subst_pos.
      nia.
    - constructor 3.
      + now rewrite measure1_lift_unfolding.
      + now rewrite measure2_lift_unfolding.
      + simpl...
        nia.
    - constructor 3.
      + now rewrite measure1_subst_unfolding.
      + now rewrite measure2_subst_unfolding.
      + simpl...
        nia.
    - constructor 3.
      + now rewrite measure1_traverse_unfolding.
      + now rewrite measure2_traverse_unfolding.
      + simpl...
        nia.
    (* From this point forward, congruences... *)
    - admit.
    - dependent destruction IHstep.
      + constructor 1; simpl; nia.
      + constructor 2; simpl; nia.
      + constructor 3; simpl; nia.
    - dependent destruction IHstep.
      + constructor 1; simpl; nia.
      + constructor 2; simpl; nia.
      + constructor 3; simpl; nia.
    - dependent destruction IHstep.
      + constructor 1; simpl; nia.
      + constructor 2; simpl; nia.
      + constructor 3; simpl; nia.
    - admit.
    - admit.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 x > 0) by apply measure1_term_pos.
        remember (2 ^ interpretation i) as m.
        destruct m; nia.
      + constructor 2; simpl.
        * now rewrite H0.
        * nia.
      + constructor 3; simpl.
        * now rewrite H0.
        * now rewrite H1.
        * nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 e > 0) by apply measure1_term_pos.
        nia.
      + constructor 2; simpl.
        * nia.
        * assert (measure2 e > 0) by apply measure2_term_pos.
          assert (measure2 x > 0) by apply measure2_subst_pos.
          apply Mult.mult_lt_compat_l_stt; try nia.
          apply -> Nat.succ_lt_mono.
          apply Mult.mult_lt_compat_l_stt; try nia.
          assert (4 ^ interpretation k > 0) by apply power_is_positive.
          lia.
      + constructor 3; simpl; nia.
    - admit.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 s > 1) by apply measure1_subst_pos.
        nia.
      + constructor 2; simpl.
        * now rewrite H0.
        * nia.
      + constructor 3; simpl.
        * now rewrite H0.
        * now rewrite H1.
        * nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 e > 0) by apply measure1_term_pos.
        nia.
      + constructor 2; simpl.
        * nia.
        * assert (measure2 e > 0) by apply measure2_term_pos.
          nia.
      + constructor 3; simpl; nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 s > 1) by apply measure1_subst_pos.
        nia.
      + constructor 2; simpl; nia.
      + constructor 3; simpl; nia.
    - admit.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        do 2 rewrite sumup0_measure1_simpl.
        nia.
      + constructor 2; simpl.
        * do 2 rewrite sumup0_measure1_simpl.
          nia.
        * do 2 rewrite sumup1_measure2_simpl.
          nia.
      + constructor 3; simpl.
        * do 2 rewrite sumup0_measure1_simpl.
          nia.
        * do 2 rewrite sumup1_measure2_simpl.
          nia.
        * nia.
    - dependent destruction IHstep.
      + constructor 1; simpl; nia.
      + constructor 2; simpl; nia.
      + constructor 3; simpl; nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 r > 1) by apply measure1_subst_pos.
        nia.
      + constructor 2; simpl.
        * now rewrite H0.
        * apply Mult.mult_lt_compat_r_stt; auto.
          nia.
      + constructor 3; simpl.
        * now rewrite H0.
        * now rewrite H1.
        * nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 s > 1) by apply measure1_subst_pos.
        nia.
      + constructor 2; simpl.
        * now rewrite H0.
        * assert (measure2 s > 0) by apply measure2_subst_pos.
          nia.
      + constructor 3; simpl.
        * now rewrite H0.
        * now rewrite H1.
        * nia.
    - admit.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assumption.
      + constructor 2; simpl.
        * assumption.
        * apply Mult.mult_lt_compat_l_stt; auto.
          assert (4 ^ interpretation n > 0) by apply power_is_positive.
          lia.
      + constructor 3; simpl.
        * assumption.
        * now rewrite H1.
        * nia.
    - dependent induction IHstep.
      + constructor 1; simpl; nia.
      + constructor 2; simpl; nia.
      + constructor 3; simpl; nia.
    - dependent induction IHstep.
      + constructor 1; simpl; nia.
      + constructor 2; simpl; nia.
      + constructor 3; simpl; nia.
    - dependent induction IHstep.
      + constructor 1; simpl.
        do 2 rewrite sumup0_measure1_simpl.
        nia.
      + constructor 2; simpl.
        * do 2 rewrite sumup0_measure1_simpl.
          nia.
        * do 2 rewrite sumup1_measure2_simpl.
          nia.
      + constructor 3; simpl.
        * do 2 rewrite sumup0_measure1_simpl.
          nia.
        * do 2 rewrite sumup1_measure2_simpl.
          nia.
        * nia.
    - dependent induction IHstep.
      + constructor 1; simpl.
        do 3 rewrite sumup0_measure1_simpl.
        nia.
      + constructor 2; simpl.
        * do 3 rewrite sumup0_measure1_simpl.
          nia.
        * do 3 rewrite sumup1_measure2_simpl.
          nia.
      + constructor 3; simpl.
        * do 3 rewrite sumup0_measure1_simpl.
          nia.
        * do 3 rewrite sumup1_measure2_simpl.
          nia.
        * nia.
    - dependent induction IHstep.
      + constructor 1; simpl.
        do 3 rewrite sumup0_measure1_simpl.
        nia.
      + constructor 2; simpl.
        * do 3 rewrite sumup0_measure1_simpl.
          nia.
        * do 3 rewrite sumup1_measure2_simpl.
          nia.
      + constructor 3; simpl.
        * do 3 rewrite sumup0_measure1_simpl.
          nia.
        * do 3 rewrite sumup1_measure2_simpl.
          nia.
        * nia.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    (* ------------------------------------------------------------------ *)
    - constructor 3; simpl.
      + rewrite H; simpl.
        reflexivity.
      + rewrite H; simpl.
        reflexivity.
      + assert (measure3 n > 0) by apply measure3_pos.
        unfold X10.
        lia.
    - constructor 3; simpl.
      + reflexivity.
      + rewrite H; simpl.
        lia.
      + lia.
    - destruct (le_gt_dec (interpretation n) 0).
      + constructor 3; simpl.
        * reflexivity.
        * replace (interpretation n) with 0 by lia.
          simpl; reflexivity.
        * lia.
      + constructor 2; simpl.
        * reflexivity.
        * remember (interpretation n) as m.
          destruct m; try lia; simpl.
          assert (4 ^ m > 0) by apply power_is_positive.
          lia.
    - constructor 1; simpl.
      assert (measure1 e > 0) by apply measure1_term_pos.
      lia.
    - constructor 1; simpl.
      assert (measure1 s > 1) by apply measure1_subst_pos.
      lia.
    - constructor 1; simpl.
      assert (measure1 s > 1) by apply measure1_subst_pos.
      lia.
    - constructor 2; simpl.
      + lia.
      + rename t0 into t.
        assert (measure2 s > 0) by apply measure2_subst_pos.
        assert (measure2 t > 0) by apply measure2_subst_pos.
        assert (measure2 u > 0) by apply measure2_subst_pos.
        lia.
  Admitted.

  Theorem normalization:
    forall {s},
    (* Recall that for steps, the RHS is smaller, thus transp. *)
    well_founded (transp (t s) step).
  Proof.
    intros s x.
    assert (well_founded (@LT s)).
    - apply LT_is_well_founded.
    - specialize (H x).
      induction H.
      clear H; rename H0 into H.
      constructor; intros y ?.
      apply H.
      apply decreasing.
      assumption.
  Qed.

  Ltac boundscheck :=
    repeat match goal with
    | H: @step NUM ?n ?m |- _ => apply interpretation_consistent_num in H
    | H: @step VECTOR ?xs ?ys |- _ => apply interpretation_consistent_len in H
    end;
    subst;
    autorewrite with interpretation in *;
    solve [ lia ].

  Hint Extern 1 (_ = _) => boundscheck: sigma.
  Hint Extern 1 (_ <> _) => boundscheck: sigma.
  Hint Extern 1 (_ > _) => boundscheck: sigma.
  Hint Extern 1 (_ >= _) => boundscheck: sigma.
  Hint Extern 1 (_ < _) => boundscheck: sigma.
  Hint Extern 1 (_ <= _) => boundscheck: sigma.

  Ltac reduce :=
    eapply rt_trans; [
      apply rt_step;
      (* progress econstructor;
      solve [ repeat eauto with sigma ] *)
      idtac "applying step";
      solve [ progress info_eauto 10 with sigma ]
    | idtac ].

  Ltac normalize :=
    progress repeat reduce.

  Ltac join :=
    eexists;
    [| idtac "right hand side";
      try normalize;
      reflexivity ];
    idtac "left hand side";
    try normalize.

  Hint Extern 1 => reflexivity: sigma.
  Hint Extern 4 => symmetry: sigma.

  Ltac skip :=
    now easy + now (exfalso; boundscheck).

  Ltac break :=
    match goal with
    | H: @step _ (_ _) _ |- _ => dependent destruction H
    | H: @step _ _ (_ _) |- _ => dependent destruction H
    end;
    try skip.

  Axiom TODO: forall n m, interpretation n = interpretation m -> n = m.

  Ltac force :=
    match goal with
    | |- @clos_refl_trans (t _) _ ?a ?b => replace b with a; try reflexivity
    | |- @eq (t TERM) ?a ?b => f_equal
    | |- @eq (t SUBST) ?a ?b => f_equal
    | |- @eq (t VECTOR) ?a ?b => f_equal
    | |- @eq (t NUM) ?a ?b => apply TODO
    end.

  Ltac work :=
    try solve [ join; try easy; repeat force; boundscheck ].

  Ltac wonder i j :=
    destruct (le_gt_dec (interpretation i) (interpretation j)).

  Tactic Notation "just" "do" "it" :=
    repeat break;
    try solve [ work | eauto with sigma ].

  Local Notation one := (succ zero).

  Theorem locally_confluent:
    forall s x y,
    let origX := x in
    let origY := y in
    forall X: @step s x y,
    forall z,
    let origZ := z in
    forall Y: @step s x z,
    joinable y z.
  Proof.
    induction 3; intros.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
  Admitted.

  (* (Clos)       (a[s])[t] = a[s o t] *)
  Example Clos: 
    forall a s t,
    joinable (inst t (inst s a))
             (inst (subst_comp s t) a).
  Proof.
    intros.
  Admitted.

  (* (VarShift1)  n[!] = 1+n *)
  Example VarShift1:
    forall n,
    joinable (inst (subst_lift 1) (index n))
             (index (1 + n)).
  Proof.
    admit.
  Admitted.

  (* (VarShift2)  n[! o s] = (1+n)[s] *)
  Example VarShift2:
    forall n s,
    joinable (inst (subst_comp (subst_lift 1) s) (index n))
             (inst s (index (1 + n))).
  Proof.
    admit.
  Admitted.

  (* (FVarCons)   0[a, s] = a *)
  Example FVarCons:
    forall a s,
    joinable (inst (subst_app [a] s) (index 0))
             a.
  Proof.
    admit.
  Admitted.

  (* (FVarLift1)  0[U(s)] = 0 *)
  Example FVarLift1:
    forall s,
    joinable (inst (subst_upn 1 s) (index 0))
             (index 0).
  Proof.
    admit.
  Admitted.

  (* (FVarLift2)  0[U(s) o t] = 0[t] *)
  Example FVarLift2:
    forall s t,
    joinable (inst (subst_comp (subst_upn 1 s) t) (index 0))
             (inst t (index 0)).
  Proof.
    admit.
  Admitted.

  (* (RVarCons)   (1+n)[a, s] = n[s] *)
  Example RVarCons:
    forall n a s,
    joinable (inst (subst_app [a] s) (index (1 + n)))
             (inst s (index n)).
  Proof.
    admit.
  Admitted.

  (* (RVarLift1)  (1+n)[U(s)] = n[s o !] *)
  Example RVarLift1:
    forall n s,
    joinable (inst (subst_upn 1 s) (index (1 + n)))
             (inst (subst_comp s (subst_lift 1)) (index n)).
  Proof.
    admit.
  Admitted.

  (* (RVarLift2)  (1+n)[U(s) o t] = n[s o ! o t] *)
  (* TODO *)

  (* (AssEnv)     (s o t) o u = s o (t o u) *)
  (* TODO *)

  (* (MapEnv)     (a, s) o t = (a[t], s o t) *)
  (* TODO *)

  (* (ShiftCons)  ! o (a, s) = s *)
  (* TODO *)

  (* (ShiftLift1) ! o U(s) = s o ! *)
  (* TODO *)

  (* (ShiftLift2) ! o U(s) o t = s o ! o t *)
  (* TODO *)

  (* (Lift1)      U(s) o U(t) = U(s o t) *)
  (* TODO *)

  (* (Lift2)      U(s) o U(t) o u = U(s o t) o u *)
  (* TODO *)

  (* (LiftEnv)    U(s) o (a, t) = (a, s o t) *)
  Example LiftEnv:
    forall s a t,
    joinable (subst_comp (subst_upn 1 s) (subst_app [a] t))
             (subst_app [a] (subst_comp s t)).
  Proof.
    admit.
  Admitted.

  (* (IdL)        id o s = s *)
  Example IdL:
    forall s,
    joinable (subst_comp subst_ids s) s.
  Proof.
    just do it.
  Qed.

  (* (IdR)        s o id = s *)
  Example IdR:
    forall s,
    joinable (subst_comp s subst_ids) s.
  Proof.
    just do it.
  Qed.

  (* (LiftId)     U(id) = id *)
  Example LiftId:
    joinable (subst_upn 1 subst_ids) subst_ids.
  Proof.
    just do it.
  Qed.

  (* (Id)         a[id] = a *)
  Example Id:
    forall a,
    joinable (inst subst_ids a) a.
  Proof.
    just do it.
  Qed.

  (* ---------------------------------------------------------------------- *)

  Hint Resolve clos_rt_rt1n: sigma.
  Hint Resolve clos_rt1n_rt: sigma.

  Arguments clos_refl_sym_trans {A}.

  Notation conv s :=
    (clos_refl_sym_trans (@step s)).

  Corollary confluent:
    forall {s} x y,
    star s x y ->
    forall z,
    star s x z ->
    joinable y z.
  Proof.
    (* As we have normalization and local confluence, by Newman's lemma we also
       have confluence. *)
    intros.
    apply clos_rt_rt1n in H.
    generalize dependent z.
    generalize dependent y.
    induction (normalization x); intros.
    destruct H1.
    - exists z; auto with sigma.
    - apply clos_rt_rt1n in H2.
      destruct H2.
      + rename z0 into w.
        exists w; eauto with sigma.
      + rename y0 into z, z into v, z0 into w.
        destruct locally_confluent with s x y z as (u, ?, ?); auto.
        (* We have to fill the gap using induction twice! *)
        edestruct H0 with y u w as (t, ?, ?); auto with sigma.
        edestruct H0 with z t v as (r, ?, ?); auto with sigma.
        * eauto with sigma.
        * exists r; eauto with sigma.
  Qed.

  Corollary church_rosser:
    forall {s} x y,
    conv s x y ->
    joinable x y.
  Proof.
    (* Confluence easily implies the Church-Rosser property. *)
    induction 1.
    - exists y; auto with sigma.
    - exists x; auto with sigma.
    - now apply joinable_sym.
    - destruct IHclos_refl_sym_trans1 as (w, ?, ?).
      destruct IHclos_refl_sym_trans2 as (v, ?, ?).
      destruct @confluent with s y w v as (u, ?, ?).
      + assumption.
      + assumption.
      + exists u; eauto with sigma.
  Qed.

End Sigma.

Print Assumptions normalization.
Print Assumptions church_rosser.
