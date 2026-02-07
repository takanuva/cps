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
    | NUMBER
    | VECTOR.

  (* TODO:
     - test pack and unpack for n-tuples. *)

  Inductive T: sort -> Set :=
    (* Term syntax: *)
    | metat (n: nat): T TERM
    | var (n: T NUMBER): T TERM
    | abs (e: T TERM): T TERM
    | app (e: T TERM) (f: T TERM): T TERM
    | traverse (s: T SUBST) (k: T NUMBER) (e: T TERM): T TERM
    | inst (s: T SUBST) (e: T TERM): T TERM
    (* Substitution syntax: *)
    | metas (n: nat): T SUBST
    | subst_ids: T SUBST
    | subst_lift (n: T NUMBER): T SUBST
    | subst_app (v: T VECTOR) (s: T SUBST): T SUBST
    | subst_comp (s: T SUBST) (r: T SUBST): T SUBST
    | subst_upn (n: T NUMBER) (s: T SUBST): T SUBST
    | subst_slash (e: T TERM): T SUBST
    | subst_drop (n: T NUMBER) (s: T SUBST): T SUBST
    (* Vector syntax: *)
    | metav (n: nat): T VECTOR
    | nil: T VECTOR
    | cons (e: T TERM) (es: T VECTOR): T VECTOR
    | join (es: T VECTOR) (fs: T VECTOR): T VECTOR
    | smap (s: T SUBST) (es: T VECTOR): T VECTOR
    (* Number syntax: *)
    | metan (n: nat): T NUMBER
    | zero: T NUMBER
    | succ (n: T NUMBER): T NUMBER
    | length (v: T VECTOR): T NUMBER
    | SUB (n: T NUMBER) (m: T NUMBER): T NUMBER
    | ADD (n: T NUMBER) (m: T NUMBER): T NUMBER
    (* | MIN (n: T NUMBER) (m: T NUMBER): T NUMBER *).

  Notation lift i := (traverse (subst_lift i)) (only parsing).
  Notation subst y := (traverse (subst_slash y)) (only parsing).
  Coercion T: sort >-> Sortclass.

  Fixpoint number (n: nat): NUMBER :=
    match n with
    | 0 => zero
    | S m => succ (number m)
    end.

  Coercion number: nat >-> T.

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
    | smap _ v =>
      interpretation_length v
    end.

  Fixpoint interpretation (x: NUMBER): nat :=
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
      min (interpretation n) (interpretation m) *)
    end.

  Infix "::" := cons (at level 60, right associativity).
  Infix "++" := join (right associativity, at level 60).
  Notation "[ ]" := nil.
  Notation "[ x ]" := (cons x nil).
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Declare Scope sigma_scope.
  Bind Scope sigma_scope with T.
  Delimit Scope sigma_scope with sigma.
  Notation "x - y" := (SUB x y): sigma_scope.
  Notation "x + y" := (ADD x y): sigma_scope.

  Inductive step: forall {s: sort}, relation (T s) :=
    (* Structural rules: *)
    | A1 e f s:
      step (inst s (app e f))
           (app (traverse s 0 e) (traverse s 0 f))
    | A2 e s:
      step (inst s (abs e))
           (abs (traverse s 1 e))
    (* Congruence rules: *)
    | C1 n1 n2:
      step n1 n2 -> step (var n1) (var n2)
    | C2 e1 e2:
      step e1 e2 -> step (abs e1) (abs e2)
    | C3 e1 e2 f:
      step e1 e2 -> step (app e1 f) (app e2 f)
    | C4 e f1 f2:
      step f1 f2 -> step (app e f1) (app e f2)
    | C5 s1 s2 k e:
      step s1 s2 -> step (traverse s1 k e) (traverse s2 k e)
    | C6 s k1 k2 e:
      step k1 k2 -> step (traverse s k1 e) (traverse s k2 e)
    | C7 s k e1 e2:
      step e1 e2 -> step (traverse s k e1) (traverse s k e2)
    | C8 s1 s2 e:
      step s1 s2 -> step (inst s1 e) (inst s2 e)
    | C9 s e1 e2:
      step e1 e2 -> step (inst s e1) (inst s e2)
    | C10 n1 n2:
      step n1 n2 -> step (subst_lift n1) (subst_lift n2)
    | C11 v1 v2 s:
      step v1 v2 -> step (subst_app v1 s) (subst_app v2 s)
    | C12 v s1 s2:
      step s1 s2 -> step (subst_app v s1) (subst_app v s2)
    | C13 s1 s2 r:
      step s1 s2 -> step (subst_comp s1 r) (subst_comp s2 r)
    | C14 s r1 r2:
      step r1 r2 -> step (subst_comp s r1) (subst_comp s r2)
    | C15 n1 n2 s:
      step n1 n2 -> step (subst_upn n1 s) (subst_upn n2 s)
    | C16 n s1 s2:
      step s1 s2 -> step (subst_upn n s1) (subst_upn n s2)
    | C17 y1 y2:
      step y1 y2 -> step (subst_slash y1) (subst_slash y2)
    | C18 n1 n2 s:
      step n1 n2 -> step (subst_drop n1 s) (subst_drop n2 s)
    | C19 n s1 s2:
      step s1 s2 -> step (subst_drop n s1) (subst_drop n s2)
    | C20 e1 e2 x:
      step e1 e2 -> step (e1 :: x) (e2 :: x)
    | C21 e x1 x2:
      step x1 x2 -> step (e :: x1) (e :: x2)
    | C22 x1 x2 y:
      step x1 x2 -> step (x1 ++ y) (x2 ++ y)
    | C23 x y1 y2:
      step y1 y2 -> step (x ++ y1) (x ++ y2)
    | C24 s1 s2 v:
      step s1 s2 -> step (smap s1 v) (smap s2 v)
    | C25 s v1 v2:
      step v1 v2 -> step (smap s v1) (smap s v2)
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
    (* ------------------------------------------------------------------ *)
    | N1 n m:
      step (ADD (succ n) m) (succ (ADD n m))
    | N2 n m:
      step (ADD n (succ m)) (succ (ADD n m))
    | N3 n m o:
      step (ADD n (ADD m o)) (ADD (ADD n m) o)
    | N4 n m:
      interpretation n = 0 ->
      step (ADD n m) m
    | N5 n m:
      interpretation m = 0 ->
      step (ADD n m) n
    | N6 n m:
      step (SUB (succ n) (succ m)) (SUB n m)
    | N7 n m:
      interpretation m = 0 ->
      step (SUB n m) n
    | N8 n m:
      interpretation n = interpretation m ->
      step (SUB n m) 0
    | N9:
      step (length []) 0
    | N10 x xs:
      step (length (x :: xs)) (succ (length xs))
    | N11 xs ys:
      step (length (xs ++ ys)) (ADD (length xs) (length ys))
    | N12 s xs:
      step (length (smap s xs)) (length xs)
    (* ------------------------------------------------------------------ *)
    | V1 x xs ys:
      step ((x :: xs) ++ ys) (x :: (xs ++ ys))
    | V2 xs ys zs:
      step ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs))
    | V3 xs ys:
      (* TODO: might prefer using [] instead. *)
      interpretation (length ys) = 0 ->
      step (xs ++ ys)
           xs
    | V4 xs ys:
      (* TODO: might prefer using [] instead. *)
      interpretation (length ys) = 0 ->
      step (ys ++ xs)
           xs
    | V5 s ys:
      (* TODO: might prefer using [] instead. *)
      interpretation (length ys) = 0 ->
      step (smap s ys)
           []
    | V6 s x xs:
      step (smap s (x :: xs))
           (inst s x :: smap s xs)
    | V7 s xs ys:
      step (smap s (xs ++ ys))
           (smap s xs ++ smap s ys)
    | V8 s t xs:
      step (smap t (smap s xs))
           (smap (subst_comp s t) xs)
    | V9 xs:
      step (smap subst_ids xs)
           xs
    (* ------------------------------------------------------------------ *)
    | A3 e:
      step (subst_slash e)
           (subst_app [e] subst_ids)
    | A4 i s:
      step (subst_drop i s)
           (subst_comp (subst_lift i) s)
    | A5 s k e:
      step (traverse s k e)
           (inst (subst_upn k s) e)
    | A6 s t e:
      step (inst t (inst s e))
           (inst (subst_comp s t) e)
    | A7 e:
      step (inst subst_ids e)
           e
    | A8 s:
      step (subst_comp subst_ids s)
           s
    | A9 s:
      step (subst_comp s subst_ids)
           s
    | A10 s t u:
      step (subst_comp (subst_comp s t) u)
           (subst_comp s (subst_comp t u))
    | A11 n s t:
      step (subst_upn n (subst_comp s t))
           (subst_comp (subst_upn n s) (subst_upn n t))
    | A12 n s:
      interpretation n = 0 ->
      step (subst_upn n s)
           s
    | A13 n:
      step (subst_upn n subst_ids)
           subst_ids
    (* TODO: A14: join U(U(s)) together... *)
    | A15 i:
      interpretation i = 0 ->
      step (subst_lift i)
           subst_ids
    | A16 xs s t:
      step (subst_comp (subst_app xs s) t)
           (subst_app (smap t xs) (subst_comp s t)).

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

  Lemma interpretation_smap_length:
    forall s xs,
    interpretation (length (smap s xs)) =
      interpretation (length xs).
  Proof.
    simpl; auto.
  Qed.

  Create HintDb interpretation.

  Hint Rewrite interpretation_zero: interpretation.
  Hint Rewrite interpretation_succ: interpretation.
  Hint Rewrite interpretation_number: interpretation.
  Hint Rewrite interpretation_add: interpretation.
  Hint Rewrite interpretation_sub: interpretation.
  (* Hint Rewrite interpretation_min: interpretation. *)
  Hint Rewrite interpretation_cons_length: interpretation.
  Hint Rewrite interpretation_nil_length: interpretation.
  Hint Rewrite interpretation_app_length: interpretation.
  Hint Rewrite interpretation_smap_length: interpretation.

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
    - lia.
    - now apply IHstep.
    - reflexivity.
    - lia.
    - simpl in H.
      lia.
    - simpl in H.
      lia.
    - simpl in H.
      assumption.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma interpretation_consistent_num:
    forall n m,
    @step NUMBER n m ->
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
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
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
    - simpl; auto.
    - simpl in IHstep |- *.
      now apply IHstep.
    - simpl; lia.
    - simpl; lia.
    - simpl in H.
      simpl; lia.
    - simpl in H.
      simpl; lia.
    - simpl in H.
      simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
    - simpl; lia.
  Qed.

  Hint Resolve interpretation_consistent_num: sigma.
  Hint Resolve interpretation_consistent_len: sigma.

  Definition joinable {s} (y: T s) (z: T s): Prop :=
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

  Lemma C1_join:
    forall n1 n2,
    joinable n1 n2 ->
    joinable (var n1) (var n2).
  Proof with eauto with sigma.
    intros n1 n2 (n3, ?, ?).
    exists (var n3).
    - clear H0.
      induction H...
    - clear H.
      induction H0...
  Qed.

  Lemma C2_join:
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

  Lemma C3_join:
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

  Lemma C4_join:
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

  Lemma C5_join:
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

  Lemma C6_join:
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

  Lemma C7_join:
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

  Lemma C8_join:
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

  Lemma C9_join:
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

  Lemma C10_join:
    forall y1 y2,
    joinable y1 y2 ->
    joinable (subst_slash y1) (subst_slash y2).
  Proof with eauto with sigma.
    intros y1 y2 (y3, ?, ?).
    exists (subst_slash y3).
    - clear H0.
      induction H...
    - clear H.
      induction H0...
  Qed.

  Lemma C11_join:
    forall n1 n2 s1 s2,
    joinable n1 n2 ->
    joinable s1 s2 ->
    joinable (subst_drop n1 s1) (subst_drop n2 s2).
  Proof with eauto with sigma.
    intros n1 n2 s1 s2 (n3, ?, ?) (s3, ?, ?).
    exists (subst_drop n3 s3).
    - clear H0 H2.
      apply rt_trans with (subst_drop n3 s1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (subst_drop n3 s2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C12_join:
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

  Lemma C13_join:
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

  Lemma C14_join:
    forall s1 s2 v1 v2,
    joinable s1 s2 ->
    joinable v1 v2 ->
    joinable (smap s1 v1) (smap s2 v2).
   Proof with eauto with sigma.
    intros s1 s2 v1 v2 (s3, ?, ?) (v3, ?, ?).
    exists (smap s3 v3).
    - clear H0 H2.
      apply rt_trans with (smap s3 v1).
      + clear H1.
        induction H...
      + clear H.
        induction H1...
    - clear H H1.
      apply rt_trans with (smap s3 v2).
      + clear H2.
        induction H0...
      + clear H0.
        induction H2...
  Qed.

  Lemma C15_join:
    forall n1 n2,
    joinable n1 n2 ->
    joinable (succ n1) (succ n2).
  Proof with eauto with sigma.
    intros n1 n2 (n3, ?, ?).
    exists (succ n3).
    - clear H0.
      induction H...
    - clear H.
      induction H0...
  Qed.

  Lemma C16_join:
    forall v1 v2,
    joinable v1 v2 ->
    joinable (length v1) (length v2).
  Proof with eauto with sigma.
    intros v1 v2 (v3, ?, ?).
    exists (length v3).
    - clear H0.
      induction H...
    - clear H.
      induction H0...
  Qed.

  Lemma C17_join:
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

  Lemma C18_join:
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
  Hint Resolve C15_join: sigma.
  Hint Resolve C16_join: sigma.
  Hint Resolve C17_join: sigma.
  Hint Resolve C18_join: sigma.

  Axiom TODO: nat.

  Definition sumup (k: nat) (f: TERM -> nat) :=
    fix sumup (v: VECTOR) :=
      match v with
      | metav _ => 0
      | nil => 0
      | cons e v => k + f e + sumup v
      | join v u => sumup v + sumup u
      | smap s v => TODO
      end.

  (* ---------------------------------------------------------------------- *)

  Fixpoint measure1 {s: sort} (expr: s) {struct expr}: nat :=
    match expr with
    (* TERM *)
    | metat _ => 2
    | var n => 2 ^ measure1 n
    | abs e => 2 + measure1 e
    | app e f => measure1 e + measure1 f
    | traverse s k e => measure1 s * measure1 e
    | inst s e => measure1 s * measure1 e
    (* SUBST *)
    | metas _ => 2
    | subst_ids => 2
    | subst_lift n => max 2 (2 ^ measure1 n)
    | subst_app v s => sumup 0 measure1 v + measure1 s
    | subst_comp s t => measure1 s * measure1 t
    | subst_upn n s => measure1 s
    | subst_slash y => 2 + measure1 y
    | subst_drop n s => 2
    (* VECTOR *)
    | metav _ => 0
    | nil => 0
    | cons e v => measure1 e + sumup 0 measure1 v
    | join v u => sumup 0 measure1 v + sumup 0 measure1 u
    | smap s v => TODO
    (* NUMBER *)
    | metan n => 0
    | zero => 0
    | succ n => measure1 n
    | length v => measure1 v
    | SUB n m => measure1 n + measure1 m
    | ADD n m => measure1 n + measure1 m
    (* | MIN n m => TODO *)
    end.

  Fixpoint measure2 {s: sort} (expr: s) {struct expr}: nat :=
    let M := 4 in
    match expr with
    (* TERM *)
    | metat _ => 1
    | var n => 1 + measure2 n
    | abs e => 2 * measure2 e
    | app e f => 1 + measure2 e + measure2 f
    | traverse s k e => measure2 e * (1 + M ^ measure2 k * measure2 s)
    | inst s e => measure2 e * (1 + measure2 s)
    (* SUBST *)
    | metas _ => 1
    | subst_ids => 1
    | subst_lift n => max 1 (measure2 n)
    | subst_app v s => sumup 1 measure2 v + measure2 s
    | subst_comp s t => measure2 s * (1 + measure2 t)
    | subst_upn n s => M ^ measure2 n * measure2 s
    | subst_slash y => 2 + measure2 y
    | subst_drop n s => 2
    (* VECTOR *)
    | metav _ => 0
    | nil => 0
    | cons e v => 1 + measure2 e + sumup 1 measure2 v
    | join v u => sumup 1 measure2 v + sumup 1 measure2 u
    | smap s v => TODO
    (* NUMBER *)
    | metan n => 0
    | zero => 0
    | succ n => measure2 n
    | length v => measure2 v
    | SUB n m => measure2 n + measure2 m
    | ADD n m => measure2 n + measure2 m
    (* | MIN n m => TODO *)
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
    subject to aaa: 2 <= x19;
    subject to bbb: 2 <= x20;
    subject to ccc: x20 + 1 <= x16;
    subject to ddd: 2 <= x15;
    subject to eee: x24 + 1 <= x18;

    minimize s: x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 +
                x10 + x11 + x12 + x13 + x14 + x15 + x16 + x17 + x18 + x19 +
                x20 + x21 + x22 + x23 + x24 + x25 + x26;

    end; *)

  Definition X1 := 1.
  Definition X2 := 1.
  Definition X3 := 1.
  Definition X4 := 1.
  Definition X5 := 6.
  Definition X6 := 9.
  Definition X7 := 4.
  Definition X8 := 1.
  Definition X9 := 1.
  Definition X10 := 1.
  Definition X11 := 1.
  Definition X12 := 3.
  Definition X13 := 1.
  Definition X14 := 2.
  Definition X15 := 2.
  Definition X16 := 3.
  Definition X17 := 1.
  Definition X18 := 2.
  Definition X19 := 2.
  Definition X20 := 2.
  Definition X21 := 1.
  (* Definition X22 := 1. *)
  Definition X23 := 1.
  Definition X24 := 1.
  (* Definition X25 := 1.
  Definition X26 := 1. *)

  Fixpoint measure3 {s: sort} (expr: s) {struct expr}: nat :=
    match expr with
    (* TERM *)
    | metat _ => X1
    | var n => X2 + measure3 n
    | abs e => X3 + measure3 e
    | app e f => X4 + measure3 e + measure3 f
    | traverse s k e => X7 + measure3 s + measure3 k + measure3 e
    | inst s e => X8 + measure3 s + measure3 e
    (* SUBST *)
    | metas _ => X9
    | subst_ids => X10
    | subst_lift n => X11 + measure3 n
    | subst_app v s => X12 + measure3 v + measure3 s
    | subst_comp s t => X13 + measure3 s + measure3 t
    | subst_upn n s => X14 + measure3 n + measure3 s
    | subst_slash y => X6 + measure3 y
    | subst_drop n s => 2
    (* VECTOR *)
    | metav _ => X15
    | nil => X16
    | cons e v => X17 + measure3 e + measure3 v
    | join v u => X18 + measure3 v * (1 + measure3 u)
    | smap s v => TODO
    (* NUMBER *)
    | metan n => X19
    | zero => X20
    | succ n => X21 + measure3 n
    | length v => measure3 v
    | SUB n m => X23 + measure3 n + measure3 m
    | ADD n m => X24 + measure3 n * (1 + measure3 m)
    (* | MIN n m => TODO *)
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
      remember (2 ^ measure1 e) as n.
      destruct n.
      + exfalso.
        assert (2 ^ measure1 e > 0) by apply power_is_positive.
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
    - lia.
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
      destruct (measure2 e); lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHe1 _ eq_refl JMeq_refl).
      lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      assert (4 ^ measure2 e1 > 0).
      + apply power_is_positive.
      + lia.
    - nia.
    - lia.
  Qed.

  Lemma measure2_term_pos:
    forall e: TERM,
    measure2 e > 0.
  Proof.
    intros.
    dependent induction e; simpl.
    - auto.
    - lia.
    - specialize (IHe _ eq_refl JMeq_refl).
      lia.
    - lia.
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

  Lemma measure1_slash_unfolding:
    forall y,
    measure1 (subst_slash y) = measure1 (subst_app [y] subst_ids).
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

  Lemma measure2_slash_unfolding:
    forall y,
    measure2 (subst_slash y) = measure2 (subst_app [y] subst_ids).
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
    induction x; simpl; try lia;
    cbv; try lia.
    admit.
  Admitted.

  Lemma measure3_vec_pos:
    forall v: VECTOR,
    measure3 v > 1.
  Proof.
    intros.
    dependent induction v; simpl.
    - unfold X15; lia.
    - unfold X16; lia.
    - specialize (IHv2 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHv1 _ eq_refl JMeq_refl).
      lia.
    - admit.
  Admitted.

  Lemma measure3_num_pos:
    forall n: NUMBER,
    measure3 n > 1.
  Proof.
    intros.
    dependent induction n; simpl.
    - unfold X19.
      lia.
    - unfold X20.
      lia.
    - specialize (IHn _ eq_refl JMeq_refl).
      lia.
    - apply measure3_vec_pos.
    - specialize (IHn1 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHn1 _ eq_refl JMeq_refl).
      lia.
  Qed.

  Lemma decreasing:
    forall s x y,
    @step s x y ->
    @LT s y x.
  Proof.
    (* induction 1; intros.
    (* Structural... *)
    - constructor 2; simpl.
      + lia.
      + ring_simplify.
        assert (measure2 e > 0) by apply measure2_term_pos.
        assert (measure2 f > 0) by apply measure2_term_pos.
        assert (measure2 s > 0) by apply measure2_subst_pos.
        lia.
    - constructor 1; simpl.
      ring_simplify.
      assert (measure1 s > 1) by apply measure1_subst_pos.
      lia.
    (* Classical... *)
    - constructor 3.
      + rewrite measure1_lift_unfolding.
        reflexivity.
      + rewrite measure2_lift_unfolding.
        reflexivity.
      + simpl; ring_simplify.
        lia.
    - constructor 3.
      + rewrite measure1_subst_unfolding.
        reflexivity.
      + rewrite measure2_subst_unfolding.
        reflexivity.
      + simpl; unfold X10, X16; ring_simplify.
        lia.
    - constructor 3.
      + rewrite measure1_traverse_unfolding.
        reflexivity.
      + rewrite measure2_traverse_unfolding.
        reflexivity.
      + simpl; ring_simplify.
        lia.
    (* Congruence rules... *)
    - dependent destruction IHstep.
      + constructor 1; simpl.
        apply Nat.pow_lt_mono_r; auto.
      + constructor 2; simpl; auto.
        lia.
      + constructor 3; simpl; auto.
        lia.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - dependent destruction IHstep.
      + constructor 1; simpl; auto.
      + constructor 2; simpl; auto.
      + constructor 3; simpl; auto.
    - admit.
    - admit.
    - admit.
    - admit.
    (* Arithmetic rules... *)
    - constructor 3; simpl; auto.
      ring_simplify.
      assert (measure3 m > 0) by apply measure3_pos.
      lia.
    - constructor 3; simpl; auto.
      ring_simplify.
      assert (measure3 n > 1) by apply measure3_num_pos.
      lia.
    - constructor 3; simpl; auto.
      lia.
    - admit.
    - constructor 3; simpl; auto.
    - constructor 1; simpl.
      rewrite sumup0_measure1_simpl.
      assert (measure1 x > 0) by apply measure1_term_pos.
      lia.
    - constructor 3; simpl.
      + do 2 rewrite sumup0_measure1_simpl.
        reflexivity.
      + do 2 rewrite sumup1_measure2_simpl.
        reflexivity.
      + ring_simplify.
        lia.
    (* Vector rules... *)
    - constructor 3; simpl.
      + do 2 rewrite sumup0_measure1_simpl.
        lia.
      + do 2 rewrite sumup1_measure2_simpl.
        lia.
      + ring_simplify.
        assert (measure3 ys > 0) by apply measure3_pos.
        lia.
    - constructor 3; simpl.
      + do 2 rewrite sumup0_measure1_simpl.
        lia.
      + do 2 rewrite sumup1_measure2_simpl.
        lia.
      + ring_simplify.
        assert (measure3 zs > 1) by apply measure3_vec_pos.
        nia.
    (* Axioms... *)
    - constructor 2; simpl.
      + lia.
      + rename t0 into t.
        assert (measure2 e > 0) by apply measure2_term_pos.
        assert (measure2 s > 0) by apply measure2_subst_pos.
        assert (measure2 t > 0) by apply measure2_subst_pos.
        lia.
    - constructor 1; simpl.
      assert (measure1 e > 0) by apply measure1_term_pos.
      lia.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - constructor 1; simpl.
      assert (measure1 s > 1) by apply measure1_subst_pos.
      lia.
    - admit. *)
  Admitted.

  Ltac boundscheck :=
    repeat match goal with
    | H: @step NUMBER ?n ?m |- _ => apply interpretation_consistent_num in H
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

  (* TODO: fix this... *)
  Axiom FORCE: forall n m, interpretation n = interpretation m -> n = m.

  Ltac force :=
    match goal with
    | |- @clos_refl_trans (T _) _ ?a ?b => replace b with a; try reflexivity
    | |- @eq (T TERM) ?a ?b => f_equal
    | |- @eq (T SUBST) ?a ?b => f_equal
    | |- @eq (T VECTOR) ?a ?b => f_equal
    | |- @eq (T NUMBER) ?a ?b =>
          idtac "forcing equality between" a "and" b;
          reflexivity
    end.

  Ltac work :=
    try solve [ join; try easy; repeat force; boundscheck ].

  Ltac wonder i j :=
    destruct (lt_eq_lt_dec (interpretation i) (interpretation j)) as
      [ [ ? | ? ] | ? ].

  Tactic Notation "just" "do" "it" :=
    repeat break;
    try solve [ work | eauto with sigma ].

  Local Notation one := (succ zero).

  (* This one is for debugging... *)
  Local Tactic Notation "why ?" :=
    eexists; repeat reduce.

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
    (* Structural... *)
    - admit.
    - admit.
    (* Congruence... *)
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    (* Arithmetic... *)
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    (* Vectors... *)
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    (* Axioms... *)
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
    - just do it.
      + admit.
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
    just do it.
  Qed.

  (* (VarShift1)  n[!] = 1+n *)
  Example VarShift1:
    forall n,
    joinable (inst (subst_lift 1) (var n))
             (var (1 + n)).
  Proof.
    admit.
  Admitted.

  (* (VarShift2)  n[! o s] = (1+n)[s] *)
  Example VarShift2:
    forall n s,
    joinable (inst (subst_comp (subst_lift 1) s) (var n))
             (inst s (var (1 + n))).
  Proof.
    admit.
  Admitted.

  (* (FVarCons)   0[a, s] = a *)
  Example FVarCons:
    forall a s,
    joinable (inst (subst_app [a] s) (var 0))
             a.
  Proof.
    admit.
  Admitted.

  (* (FVarLift1)  0[U(s)] = 0 *)
  Example FVarLift1:
    forall s,
    joinable (inst (subst_upn 1 s) (var 0))
             (var 0).
  Proof.
    admit.
  Admitted.

  (* (FVarLift2)  0[U(s) o t] = 0[t] *)
  Example FVarLift2:
    forall s t,
    joinable (inst (subst_comp (subst_upn 1 s) t) (var 0))
             (inst t (var 0)).
  Proof.
    admit.
  Admitted.

  (* (RVarCons)   (1+n)[a, s] = n[s] *)
  Example RVarCons:
    forall n a s,
    joinable (inst (subst_app [a] s) (var (1 + n)))
             (inst s (var n)).
  Proof.
    admit.
  Admitted.

  (* (RVarLift1)  (1+n)[U(s)] = n[s o !] *)
  Example RVarLift1:
    forall n s,
    joinable (inst (subst_upn 1 s) (var (1 + n)))
             (inst (subst_comp s (subst_lift 1)) (var n)).
  Proof.
    admit.
  Admitted.

  (* (RVarLift2)  (1+n)[U(s) o t] = n[s o ! o t] *)
  Example RVarLift2:
    forall n s t,
    joinable (inst (subst_comp (subst_upn 1 s) t) (var (1 + n)))
             (inst (subst_comp s (subst_comp (subst_lift 1) t)) (var n)).
  Proof.
    admit.
  Admitted.

  (* (AssEnv)     (s o t) o u = s o (t o u) *)
  Example AssEnv:
    forall s t u,
    joinable (subst_comp (subst_comp s t) u)
             (subst_comp s (subst_comp t u)).
  Proof.
    just do it.
  Qed.

  (* (MapEnv)     (a, s) o t = (a[t], s o t) *)
  Example MapEnv:
    forall a s t,
    joinable (subst_comp (subst_app [a] s) t)
             (subst_app [inst t a] (subst_comp s t)).
  Proof.
    just do it.
  Qed.

  (* (ShiftCons)  ! o (a, s) = s *)
  Example ShiftCons:
    forall a s,
    joinable (subst_comp (subst_lift 1) (subst_app [a] s))
             s.
  Proof.
    admit.
  Admitted.

  (* (ShiftLift1) ! o U(s) = s o ! *)
  Example ShiftLift1:
    forall s,
    joinable (subst_comp (subst_lift 1) (subst_upn 1 s))
             (subst_comp s (subst_lift 1)).
  Proof.
    admit.
  Admitted.

  (* (ShiftLift2) ! o U(s) o t = s o ! o t *)
  Example ShiftLift2:
    forall s t,
    joinable (subst_comp (subst_lift 1) (subst_comp (subst_upn 1 s) t))
             (subst_comp s (subst_comp (subst_lift 1) t)).
  Proof.
    admit.
  Admitted.

  (* (Lift1)      U(s) o U(t) = U(s o t) *)
  Example Lift1:
    forall s t,
    joinable (subst_comp (subst_upn 1 s) (subst_upn 1 t))
             (subst_upn 1 (subst_comp s t)).
  Proof.
    just do it.
  Qed.

  (* (Lift2)      U(s) o U(t) o u = U(s o t) o u *)
  Example Lift2:
    forall s t u,
    joinable (subst_comp (subst_upn 1 s) (subst_comp (subst_upn 1 t) u))
             (subst_comp (subst_upn 1 (subst_comp s t)) u).
  Proof.
    just do it.
  Qed.

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

  Open Scope sigma.

  Example Lift0:
    forall k e,
    joinable (lift 0 k e) e.
  Proof.
    just do it.
  Qed.

  Example InstLiftComm:
    forall e s i k j,
    interpretation k <= interpretation j ->
    joinable (lift i k (traverse s j e)) (traverse s (i + j) (lift i k e)).
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  Example LiftSubstComm:
    forall e f i k j,
    interpretation k <= interpretation j ->
    joinable (lift i k (subst f j e))
             (subst f (i + j) (lift i k e)).
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  Example LiftPerm:
    forall e i j k l,
    interpretation k <= interpretation l ->
    joinable (lift i k (lift j l e))
             (lift j (i + l) (lift i k e)).
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  Example LiftSimpl:
    forall e i j k l,
    interpretation k <= interpretation (l + j) ->
    interpretation l <= interpretation k ->
    joinable (lift i k (lift j l e))
             (lift (i + j) l e).
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  Example SubstSimpl:
    forall e f p i k,
    interpretation p <= interpretation (i + k) ->
    interpretation k <= interpretation p ->
    joinable (subst f p (lift (1 + i) k e))
             (lift i k e).
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  Example SubstLiftPerm:
    forall e f i p k,
    joinable (lift i (p + k) (subst f p e))
             (subst (lift i k f) p (lift i (1 + p + k) e)).
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  Example SubstSubstPerm:
    forall e f g p k,
    joinable (subst f (p + k) (subst g p e))%sigma
             (subst (subst f k g) p (subst f (1 + p + k) e))%sigma.
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  (* ---------------------------------------------------------------------- *)

  Goal
    forall n e,
    joinable (subst (subst (var 1) n (var 0)) 0 (lift (2 + n) 1 e))%sigma
             (subst (var 1) n (lift (2 + n) 1 e))%sigma.
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  Example InstVarShift:
    forall s p k n,
    joinable (traverse s (p + k) (var (p + n)))
             (lift p 0 (traverse s k (var n))).
  Proof.
    intros; why?.
    - admit.
    - admit.
  Admitted.

  (* ---------------------------------------------------------------------- *)

  Hint Resolve clos_rt_rt1n: sigma.
  Hint Resolve clos_rt1n_rt: sigma.

  Arguments clos_refl_sym_trans {A}.

  Notation conv s :=
    (clos_refl_sym_trans (@step s)).

  Theorem normalization:
    forall s: sort,
    (* Recall that for steps, the RHS is smaller, thus transp. *)
    well_founded (transp (T s) step).
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
    induction (normalization s x); intros.
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
