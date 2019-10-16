Require Import Arith.

(* *)
Inductive level: Prop :=
  | sort
  | value
  | command.

(* *)
Inductive pseudoterm: level -> Set :=
  | type: pseudoterm sort
  | prop: pseudoterm sort
  | void: pseudoterm sort
  | base: pseudoterm sort
  | bound:
    forall n: nat,
    pseudoterm value
  | negation:
    forall xs: list (pseudoterm sort),
    pseudoterm sort
  | jump:
    forall f: pseudoterm value,
    forall xs: list (pseudoterm value),
    pseudoterm command
  | bind:
    forall b: pseudoterm command,
    forall ts: list (pseudoterm sort),
    forall c: pseudoterm command,
    pseudoterm command.

Coercion bound: nat >-> pseudoterm.
Coercion pseudoterm: level >-> Sortclass.

Fixpoint lift (i: nat) (k: nat) {l: level} (e: l): l :=
  match e with
  | type =>
    type
  | prop =>
    prop
  | void =>
    void
  | base =>
    base
  | bound n =>
    if le_gt_dec k n then
      bound (i + n)
    else
      bound n
  | negation xs =>
    negation (List.map (lift i k) xs)
  | jump f xs =>
    jump (lift i k f) (List.map (lift i k) xs)
  | bind b ts c =>
    bind (lift i (S k) b) (List.map (lift i k) ts) (lift i (k + length ts) c)
  end.
