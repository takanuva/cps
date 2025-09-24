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
    | dbsubst (e: t TERM) (k: t NUM) (f: t TERM): t TERM
    | dbtraverse (s: t SUBST) (k: t NUM) (e: t TERM): t TERM
    | instantiation (s: t SUBST) (e: t TERM): t TERM
    (* Substitution syntax: *)
    | metas (n: nat): t SUBST
    | iota: t SUBST
    | slift (n: t NUM): t SUBST
    | concatenate (v: t VECTOR) (s: t SUBST): t SUBST
    | compose (s: t SUBST) (r: t SUBST): t SUBST
    | uplift (n: t NUM) (s: t SUBST): t SUBST
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
    | MIN (n: t NUM) (m: t NUM): t NUM
    | MAX (n: t NUM) (m: t NUM): t NUM.

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
    | MIN n m =>
      min (interpretation n) (interpretation m)
    | MAX n m =>
      max (interpretation n) (interpretation m)
    end.

  Definition DIF n m :=
    SUB (MAX n m) (MIN n m).

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
  Notation subst := dbsubst.
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

  Notation subst_drop i :=
    (subst_comp (subst_lift i))
    (only parsing).

  Notation subst_cons y :=
    (subst_app [y])
    (only parsing).

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
    | A4 y k e:
      step (subst y k e)
           (traverse (subst_cons y subst_ids) k e)
    | A5 s k e:
      step (traverse s k e)
           (inst (subst_upn k s) e)
    (* RULES FOR LIFT *)
    | L1 n:
      interpretation n = 0 ->
      step (subst_lift n)
           subst_ids
    (* RULES FOR CONS *)

    (* RULES FOR COMP *)
    | Y1 s t u:
      step (subst_comp (subst_comp s t) u)
           (subst_comp s (subst_comp t u))
    (* RULES FOR UPLIFT *)
    | U1 n s:
      interpretation n = 0 ->
      step (subst_upn n s)
           s
    | U2 k j s:
      step (subst_upn k (subst_upn j s))
           (subst_upn (ADD j k) s)













    (* ITERACTIONS *)
    | II1 e:
      step (inst subst_ids e)
           e
    | UI1 n:
      step (subst_upn n subst_ids)
           subst_ids
    | XI1 s:
      step (subst_comp s subst_ids)
           s
    | XI2 s:
      step (subst_comp subst_ids s)
           s
    | IY1 s t e:
      step (inst t (inst s e))
           (inst (subst_comp s t) e)
    (* SIMPLIFICATION *)

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
    | C7 y1 y2 k e:
      step y1 y2 -> step (subst y1 k e) (subst y2 k e)
    | C8 y k1 k2 e:
      step k1 k2 -> step (subst y k1 e) (subst y k2 e)
    | C9 y k e1 e2:
      step e1 e2 -> step (subst y k e1) (subst y k e2)
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
    | C22 e1 e2 x:
      step e1 e2 -> step (e1 :: x) (e2 :: x)
    | C23 e x1 x2:
      step x1 x2 -> step (e :: x1) (e :: x2)
    | C24 x1 x2 y:
      step x1 x2 -> step (x1 ++ y) (x2 ++ y)
    | C25 x y1 y2:
      step y1 y2 -> step (x ++ y1) (x ++ y2)
    (* TODO: congruence rules for numbers! *).

  Create HintDb sigma.

  Hint Constructors step: sigma.
  Hint Extern 1 => lia: sigma.

  Notation star s :=
    (clos_refl_trans _ (@step s)).

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

  Lemma interpretation_min:
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
  Qed.

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
  Hint Rewrite interpretation_min: interpretation.
  Hint Rewrite interpretation_max: interpretation.
  Hint Rewrite interpretation_cons_length: interpretation.
  Hint Rewrite interpretation_nil_length: interpretation.
  Hint Rewrite interpretation_app_length: interpretation.

  Lemma interpretation_consistent_num:
    forall n m,
    @step NUM n m ->
    interpretation n = interpretation m.
  Proof.
    intros.
    dependent destruction H.
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
  Proof.
    intros n1 n2 (n3, ?, ?).
    assert (n1 = n3 /\ n2 = n3) as (?, ?).
    - split.
      + clear H0.
        induction H; subst; easy.
      + clear H.
        induction H0; subst; easy.
    - subst.
      apply joinable_refl.
  Qed.

  Lemma C1_join:
    forall e1 e2,
    joinable e1 e2 ->
    joinable (abs e1) (abs e2).
  Proof.
    intros e1 e2 (e3, ?, ?).
    exists (abs e3).
    - clear H0.
      induction H; eauto with sigma.
    - clear H.
      induction H0; eauto with sigma.
  Qed.

  Lemma C2_join:
    forall e1 e2 f1 f2,
    joinable e1 e2 ->
    joinable f1 f2 ->
    joinable (app e1 f1) (app e2 f2).
  Proof.
    intros e1 e2 f1 f2 (e3, ?, ?) (f3, ?, ?).
    exists (app e3 f3).
    - clear H0 H2.
      apply rt_trans with (app e3 f1).
      + clear H1.
        induction H; eauto with sigma.
      + clear H.
        induction H1; eauto with sigma.
    - clear H H1.
      apply rt_trans with (app e3 f2).
      + clear H2.
        induction H0; eauto with sigma.
      + clear H0.
        induction H2; eauto with sigma.
  Qed.

  Lemma C3_join:
    forall i1 i2 k1 k2 e1 e2,
    joinable i1 i2 ->
    joinable k1 k2 ->
    joinable e1 e2 ->
    joinable (lift i1 k1 e1) (lift i2 k2 e2).
  Proof.
    admit.
  Admitted.

  Lemma C4_join:
    forall y1 y2 k1 k2 e1 e2,
    joinable y1 y2 ->
    joinable k1 k2 ->
    joinable e1 e2 ->
    joinable (subst y1 k1 e1) (subst y2 k2 e2).
  Proof.
    admit.
  Admitted.

  Lemma C5_join:
    forall s1 s2 k1 k2 e1 e2,
    joinable s1 s2 ->
    joinable k1 k2 ->
    joinable e1 e2 ->
    joinable (traverse s1 k1 e1) (traverse s2 k2 e2).
  Proof.
    admit.
  Admitted.

  Lemma C6_join:
    forall s1 s2 e1 e2,
    joinable s1 s2 ->
    joinable e1 e2 ->
    joinable (inst s1 e1) (inst s2 e2).
  Proof.
    admit.
  Admitted.

  Lemma C7_join:
    forall n1 n2,
    joinable n1 n2 ->
    joinable (subst_lift n1) (subst_lift n2).
  Proof.
    admit.
  Admitted.

  Lemma C8_join:
    forall v1 v2 s1 s2,
    joinable v1 v2 ->
    joinable s1 s2 ->
    joinable (subst_app v1 s1) (subst_app v2 s2).
  Proof.
    admit.
  Admitted.

  Lemma C9_join:
    forall s1 s2 r1 r2,
    joinable s1 s2 ->
    joinable (subst_comp s1 r1) (subst_comp s2 r2).
  Proof.
    admit.
  Admitted.

  Lemma C10_join:
    forall n1 n2 s1 s2,
    joinable n1 n2 ->
    joinable s1 s2 ->
    joinable (subst_upn n1 s1) (subst_upn n2 s2).
  Proof.
    admit.
  Admitted.

  Lemma C11_join:
    forall e1 e2 x1 x2,
    joinable e1 e2 ->
    joinable x1 x2 ->
    joinable (e1 :: x1) (e2 :: x2).
  Proof.
    admit.
  Admitted.

  Lemma C12_join:
    forall x1 x2 y1 y2,
    joinable x1 x2 ->
    joinable y1 y2 ->
    joinable (x1 ++ y1) (x2 ++ y2).
  Proof.
    admit.
  Admitted.

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
    | index n => 2 ^ measure1 n
    | abstraction e => 2 + measure1 e
    | application e f => measure1 e + measure1 f
    | dblift i k e => max 2 (2 ^ measure1 i) * measure1 e
    | dbsubst y k e => (2 + measure1 y) * measure1 e
    | dbtraverse s k e => measure1 s * measure1 e
    | instantiation s e => measure1 s * measure1 e
    (* SUBST *)
    | metas _ => 2
    | iota => 2
    | slift n => max 2 (2 ^ interpretation n)
    | concatenate v s => sumup 0 measure1 v + measure1 s
    | compose s t => measure1 s * measure1 t
    | uplift n s => measure1 s
    (* VECTOR *)
    | metav _ => 0
    | nil => 0
    | cons e v => measure1 e + sumup 0 measure1 v
    | join v u => sumup 0 measure1 v + sumup 0 measure1 u
    (* NUMBER *)
    | metan n => interpretation (metan n)
    | zero => interpretation zero
    | succ n => interpretation (succ n)
    | length v => interpretation (length v)
    | SUB n m => interpretation (SUB n m)
    | ADD n m => interpretation (ADD n m)
    | MIN n m => interpretation (MIN n m)
    | MAX n m => interpretation (MAX n m)
    end.

  Lemma measure1_NUM:
    forall n: NUM,
    measure1 n = interpretation n.
  Proof.
    intros.
    dependent induction n; simpl; auto.
  Qed.

  (* ---------------------------------------------------------------------- *)

  Fixpoint measure2 {s: sort} (expr: s) {struct expr}: nat :=
    match expr with
    (* TERM *)
    | metat _ => 1
    | index n => 1
    | abstraction e => 2 * measure2 e
    | application e f => 1 + measure2 e + measure2 f
    | dblift i k e => measure2 e * (1 + 4 ^ measure2 k * max 1 (measure2 i))
    | dbsubst y k e => measure2 e * (1 + 4 ^ measure2 k * (2 + measure2 y))
    | dbtraverse s k e => measure2 e * (1 + 4 ^ measure2 k * measure2 s)
    | instantiation s e => measure2 e * (1 + measure2 s)
    (* SUBST *)
    | metas _ => 1
    | iota => 1
    | slift n => max 1 (measure2 n)
    | concatenate v s => sumup 1 measure2 v + measure2 s
    | compose s t => measure2 s * (1 + measure2 t)
    | uplift n s => 4 ^ measure2 n * measure2 s
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
    | MIN n m => interpretation (MIN n m)
    | MAX n m => interpretation (MAX n m)
    end.

  Lemma measure2_NUM:
    forall n: NUM,
    measure2 n = interpretation n.
  Proof.
    intros.
    dependent induction n; simpl; auto.
  Qed.

  (* ---------------------------------------------------------------------- *)

  (* TODO: check that these number are actually the smallest possible ones. *)

  Fixpoint measure3 {s: sort} (expr: s) {struct expr}: nat :=
    match expr with
    (* TERM *)
    | metat _ => 1
    | index n => 1 + measure3 n
    | abstraction e => 1 + measure3 e
    | application e f => 1 + measure3 e + measure3 f
    | dblift i k e => 10 + measure3 i + measure3 k + measure3 e
    | dbsubst y k e => 13 + measure3 y + measure3 k + measure3 e
    | dbtraverse s k e => 8 + measure3 s + measure3 k + measure3 e
    | instantiation s e => 5 + measure3 s + measure3 e
    (* SUBST *)
    | metas _ => 1
    | iota => 1
    | slift n => 1 + measure3 n
    | concatenate v s => 1 + measure3 v + measure3 s
    | compose s t => 1 + measure3 s + measure3 t
    | uplift n s => 2 + measure3 n + measure3 s
    (* VECTOR *)
    | metav _ => 1
    | nil => 1
    | cons e v => 1 + measure3 e + measure3 v
    | join v u => 1 + measure3 v + measure3 u
    (* NUMBER *)
    | metan n => 1
    | zero => 1
    | succ n => 1 + measure3 n
    | length v => 1 + measure3 v
    | SUB n m => 1 + measure3 n + measure3 m
    | ADD n m => 1 + measure3 n + measure3 m
    | MIN n m => 1 + measure3 n + measure3 m
    | MAX n m => 1 + measure3 n + measure3 m
    end.

  Lemma measure1_subst_pos:
    forall e: SUBST,
    measure1 e > 1.
  Proof.
    intros.
    dependent induction e; simpl.
    - auto.
    - auto.
    - remember (2 ^ interpretation e) as n.
      destruct n.
      + auto.
      + destruct n; lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHe1 _ eq_refl JMeq_refl).
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      assumption.
  Qed.

  Lemma measure1_term_pos:
    forall e: TERM,
    measure1 e > 0.
  Proof.
    intros.
    dependent induction e; simpl.
    - auto.
    - clear IHe; generalize (measure1 e) as n.
      induction n; simpl.
      + auto.
      + lia.
    - lia.
    - specialize (IHe1 _ eq_refl JMeq_refl).
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - clear IHe1 IHe2.
      specialize (IHe3 _ eq_refl JMeq_refl).
      remember (2 ^ measure1 e1) as n.
      destruct n; simpl; intros.
      + lia.
      + lia.
    - clear IHe2.
      specialize (IHe1 _ eq_refl JMeq_refl).
      specialize (IHe3 _ eq_refl JMeq_refl).
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
      destruct (measure2 e).
      + auto.
      + lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      lia.
    - specialize (IHe1 _ eq_refl JMeq_refl).
      lia.
    - clear IHe1.
      specialize (IHe2 _ eq_refl JMeq_refl).
      assert (4 ^ measure2 e1 > 0).
      + generalize (measure2 e1) as n.
        induction n; simpl.
        * auto.
        * lia.
      + lia.
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
    now rewrite measure1_NUM.
  Qed.

  Lemma measure1_subst_unfolding:
    forall y k e,
    measure1 (subst y k e) = measure1 (traverse (subst_cons y subst_ids) k e).
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
    forall y k e,
    measure2 (subst y k e) = measure2 (traverse (subst_cons y subst_ids) k e).
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

  Lemma num_step_measure3:
    forall n m,
    @step NUM n m ->
    measure3 n > measure3 m.
  Proof.
    intros.
    dependent induction H.
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
    induction x; simpl; nia.
  Qed.

  Lemma decreasing:
    forall s x y,
    @step s x y ->
    @LT s y x.
  Proof.
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
      + simpl; nia.
    - constructor 3.
      + now rewrite measure1_subst_unfolding.
      + now rewrite measure2_subst_unfolding.
      + simpl; nia.
    - constructor 3.
      + now rewrite measure1_traverse_unfolding.
      + now rewrite measure2_traverse_unfolding.
      + simpl.
        ring_simplify.
        simpl; nia.
    - constructor 3; simpl.
      + rewrite H; simpl.
        reflexivity.
      + rewrite measure2_NUM.
        rewrite H.
        reflexivity.
      + simpl.
        assert (measure3 n > 0) by apply measure3_pos.
        nia.
    - constructor 2; simpl.
      + nia.
      + rename t0 into t.
        assert (measure2 s > 0) by apply measure2_subst_pos.
        assert (measure2 t > 0) by apply measure2_subst_pos.
        assert (measure2 u > 0) by apply measure2_subst_pos.
        nia.
    - constructor 3; simpl.
      + reflexivity.
      + rewrite measure2_NUM.
        rewrite H.
        simpl; nia.
      + nia.
    - constructor 3; simpl.
      + reflexivity.
      + rewrite Nat.mul_assoc.
        do 2 rewrite measure2_NUM.
        now rewrite Nat.add_comm, Nat.pow_add_r.
      + nia.
    - constructor 1; simpl.
      assert (measure1 e > 0) by apply measure1_term_pos.
      nia.
    - remember (measure2 n) as m.
      destruct m.
      + constructor 3; simpl.
        * reflexivity.
        * rewrite <- Heqm; simpl.
          reflexivity.
        * nia.
      + constructor 2; simpl.
        * reflexivity.
        * rewrite <- Heqm; simpl.
          ring_simplify.
          assert (4 ^ m > 0); try nia.
          clear Heqm.
          induction m; simpl; nia.
    - constructor 1; simpl.
      assert (measure1 s > 1) by apply measure1_subst_pos.
      nia.
    - constructor 1; simpl.
      assert (measure1 s > 1) by apply measure1_subst_pos.
      nia.
    - constructor 2; simpl.
      + nia.
      + rename t0 into t.
        assert (measure2 e > 0) by apply measure2_term_pos.
        assert (measure2 s > 0) by apply measure2_subst_pos.
        assert (measure2 t > 0) by apply measure2_subst_pos.
        nia.
    (* From this point forward, congruences... *)
    - constructor 3; simpl.
      + do 2 rewrite measure1_NUM.
        now rewrite interpretation_consistent_num with n1 n2.
      + reflexivity.
      + apply -> Nat.succ_lt_mono.
        now apply num_step_measure3.
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
    - constructor 3; simpl.
      + do 2 rewrite measure1_NUM.
        now rewrite interpretation_consistent_num with i1 i2.
      + do 3 rewrite measure2_NUM.
        now rewrite interpretation_consistent_num with i1 i2.
      + simpl; ring_simplify.
        apply num_step_measure3 in H.
        nia.
    - constructor 3; simpl.
      + reflexivity.
      + do 3 rewrite measure2_NUM.
        now rewrite interpretation_consistent_num with k1 k2.
      + simpl; ring_simplify.
        apply num_step_measure3 in H.
        nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 x > 0) by apply measure1_term_pos.
        remember (2 ^ measure1 i) as m.
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
        * now rewrite H0.
        * assert (measure2 e > 0) by apply measure2_term_pos.
          apply Mult.mult_lt_compat_l_stt; auto.
          apply -> Nat.succ_lt_mono.
          ring_simplify.
          remember (4 ^ measure2 k) as n.
          assert (n * measure2 x < n * measure2 y); try lia.
          apply Mult.mult_lt_compat_l_stt; auto.
          subst; generalize (measure2 k) as n.
          induction n; simpl; lia.
      + constructor 3; simpl.
        * now rewrite H0.
        * now rewrite H1.
        * nia.
    - constructor 3; simpl.
      + reflexivity.
      + do 2 rewrite measure2_NUM.
        now rewrite interpretation_consistent_num with k1 k2.
      + ring_simplify.
        apply num_step_measure3 in H.
        nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        nia.
      + constructor 2; simpl.
        * nia.
        * nia.
      + constructor 3; simpl.
        * nia.
        * nia.
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
          generalize (measure2 k) as n.
          induction n; simpl; nia.
      + constructor 3; simpl.
        * nia.
        * nia.
        * nia.
    - constructor 3; simpl.
      + reflexivity.
      + do 2 rewrite measure2_NUM.
        now rewrite interpretation_consistent_num with k1 k2.
      + ring_simplify.
        apply num_step_measure3 in H.
        lia.
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
        * ring_simplify.
          nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 e > 0) by apply measure1_term_pos.
        nia.
      + constructor 2; simpl.
        * nia.
        * assert (measure2 e > 0) by apply measure2_term_pos.
          nia.
      + constructor 3; simpl.
        * nia.
        * nia.
        * nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assert (measure1 s > 1) by apply measure1_subst_pos.
        nia.
      + constructor 2; simpl.
        * nia.
        * nia.
      + constructor 3; simpl.
        * nia.
        * nia.
        * nia.
    - constructor 3; simpl.
      * rewrite interpretation_consistent_num with n1 n2; auto.
      * do 2 rewrite measure2_NUM.
        now rewrite interpretation_consistent_num with n1 n2.
      * apply -> Nat.succ_lt_mono.
        now apply num_step_measure3.
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
      + constructor 1; simpl; lia.
      + constructor 2; simpl.
        * nia.
        * nia.
      + constructor 3; simpl.
        * nia.
        * nia.
        * nia.
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
    - constructor 3; simpl.
      + reflexivity.
      + do 2 rewrite measure2_NUM.
        now rewrite interpretation_consistent_num with n1 n2.
      + apply num_step_measure3 in H.
        nia.
    - dependent destruction IHstep.
      + constructor 1; simpl.
        assumption.
      + constructor 2; simpl.
        * assumption.
        * apply Mult.mult_lt_compat_l_stt; auto.
          generalize (measure2 n) as m.
          induction m; auto.
          simpl; nia.
      + constructor 3; simpl.
        * assumption.
        * now rewrite H1.
        * nia.
    - dependent induction IHstep.
      + constructor 1; simpl.
        nia.
      + constructor 2; simpl.
        * nia.
        * nia.
      + constructor 3; simpl.
        * nia.
        * nia.
        * nia.
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
  Qed.

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

  Tactic Notation "just" "do" "it" :=
    repeat break;
    try solve [ work | eauto with sigma ].

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
      + join.
        admit.
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
    - admit.
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

  Hint Resolve clos_rt_rt1n: sigma.
  Hint Resolve clos_rt1n_rt: sigma.

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

  Arguments clos_refl_sym_trans {A}.

  Notation conv s :=
    (clos_refl_sym_trans (@step s)).

  Corollary church_rosser:
    forall {s} x y,
    conv s x y ->
    joinable x y.
  Proof.
    (* Confluence implies the Church-Rosser property. *)
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

  Print Assumptions normalization.
  Print Assumptions church_rosser.

End Sigma.
