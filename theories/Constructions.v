(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import List.
Require Local.Constructions.Calculus.
Require Local.Constructions.Conversion.
Require Local.Constructions.Confluence.
Require Local.Constructions.TypeSystem.
Require Local.Constructions.Inversion.
(* Require Local.Constructions.TermModel.
Require Local.Constructions.DPresheafModel. *)
Require Local.Constructions.Normalization.
Require Local.Constructions.Stratification.
Require Local.Constructions.Reduction.
Require Local.Constructions.Observational.

Import ListNotations.

Include Calculus.
Include Conversion.
Include Confluence.
Include TypeSystem.
Include Inversion.
(* Include TermModel.
Include DPresheafModel. *)
Include Normalization.
Include Stratification.
Include Reduction.
Include Observational.

Local Coercion bound: nat >-> term.

(* fun (T: Set) (U: T -> Set) (f: (Pi x: T.U x)) (y: T): U y => f y *)

Example dependent_example1: term :=
  abstraction iset
    (abstraction (pi 0 iset)
      (abstraction (pi 1 (application 1 0))
        (abstraction 2
          (application 1 0)))).

Example dependent_example1_type: term :=
  pi iset
    (pi (pi 0 iset)
      (pi (pi 1 (application 1 0))
        (pi 2
          (application 2 0)))).

Example dependent_example1_typed:
  typing [] dependent_example1 dependent_example1_type conv.
Proof.
  unfold dependent_example1.
  unfold dependent_example1_type.
  eapply typing_abs.
  eapply typing_abs.
  eapply typing_abs.
  eapply typing_abs.
  eapply typing_app.
  - eapply typing_bound.
    + repeat econstructor; vm_compute; reflexivity.
    + repeat constructor.
    + now simpl.
    + now vm_compute.
  - eapply typing_bound.
    + repeat econstructor; vm_compute; reflexivity.
    + constructor.
    + now simpl.
    + now vm_compute.
  - now vm_compute.
Qed.

(* fun (T: Set) (U: T -> Set) (x: T) (y: U x): Sigma z: T, U z => (x, y) *)

(* Example dependent_example2: term :=
  abstraction iset
    (abstraction (pi 0 iset)
      (abstraction 1
        (abstraction (application 1 0)
          (pair 1 0 (sigma 3 (application 3 0)))))).

Example dependent_example2_type: term :=
  pi iset
    (pi (pi 0 iset)
      (pi 1
        (pi (application 1 0)
          (sigma 3 (application 3 0))))).

Example dependent_example2_typed:
  typing [] dependent_example2 dependent_example2_type conv.
Proof.
  unfold dependent_example2.
  unfold dependent_example2_type.
  eapply typing_abs.
  eapply typing_abs.
  eapply typing_abs.
  eapply typing_abs.
  eapply typing_pair.
  - eapply typing_bound.
    + repeat econstructor; vm_compute; reflexivity.
    + repeat constructor.
    + now simpl.
    + now vm_compute.
  - eapply typing_bound.
    + repeat econstructor; vm_compute; reflexivity.
    + constructor.
    + now simpl.
    + now vm_compute.
Qed.

(* Eval cbv in let f: (forall T: Type, T -> T) :=
                 fun (T: Type) (x: T) =>
                   x
               in fun (x: f Set bool) =>
                 f bool x. *)

Example dependent_example3a: term :=
  abstraction (type 0) (abstraction 0 0).

Example dependent_example3b: term :=
  pi (type 0) (pi 0 1).

Example dependent_example3c: term :=
  application (application 0 iset) boolean.

Example dependent_example3d: term :=
  application (application 1 boolean) 0.

Example dependent_example3: term :=
  definition
    dependent_example3a
    dependent_example3b
    (abstraction dependent_example3c dependent_example3d).

Example dependent_example3_type: term :=
  pi boolean boolean.

Example dependent_example3_typed:
  typing [] dependent_example3 dependent_example3_type conv.
Proof.
  (* This will need cumulativity and conversion. Oh boy! *)
  admit.
Admitted. *)
