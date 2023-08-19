(******************************************************************************)
(*   Copyright (c) 2019--2023 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Program.
Require Import Equality.
Require Import Local.Prelude.
Require Import Local.Syntax.
Require Import Local.Metatheory.
Require Import Local.Context.
Require Import Local.Machine.

(* Since Kennedy's machine semantics is sound and complete, we should write a
   version of Appel's interpreter, which is the denotational semantics of his IR
   into ML, by using the partiality monad and prove it correct with regard to
   the machine semantics as well. This would allow us to extract an executable
   interpreter for the CPS-calculus which is verified to be correct. *)

(*
  datatype dvalue = RECORD of dvalue list * nat
                  | INT of int
                  | REAL of real
                  | FUNC of dvalue list ->
                     (loc*(loc->dvalue)*(loc->int))->
                     answer
                  | STRING of string
                  | ...

  type env = CPS.var -> dvalue

  E : CPS.expr -> env -> store -> answe

  ...
  | E (CPS.APP(f,vl)) env =
                   let val FUNC g = V env f
                    in g (map (V env) vl)
                   end
  | E (CPS.FIX(fl,e)) env =
            let fun h r1 (f,vl,b) =
                   FUNC(fn al => E b (bindn(g r1,vl,al)))
                and g r = bindn(r, map #1 fl, map (h r) fl)
             in E e (g env)
            end
  ...

  fun bind(env:env, v:CPS.var, d) =
                  fn w => if v=w then d else env w

  fun bindn(env, v::vl, d::dl) = bindn(bind(env,v,d),vl,dl)
    | bindn(env, nil, nil) = env

*)

Section Appel.

  Variable answer: Type.
  Variable carrier: Type.

  Hypothesis intro: (list carrier -> answer) -> carrier.
  Hypothesis elim: carrier -> (list carrier -> answer).

  Hypothesis beta: forall l x, elim (intro l) x = l x.
  Hypothesis eta: forall y, intro (elim y) = y.

  Notation env := (nat -> carrier).

  Notation var := { e | exists n, e = bound n }.

  Program Fixpoint get (g: env) (e: var): carrier :=
    match e with
    | bound n =>
      g n
    | _ =>
      False_rect carrier _
    end.

  Next Obligation.
    eapply n; auto.
  Defined.

  (*
  Program Fixpoint eval (e: pseudoterm) (g: env): answer :=
    match e with
    | jump k xs =>
      elim (get g k) (map (get g) xs)
    | _ =>
      (* This case will be an absurd and will not be part of the code. *)
      _
    end.

  let val FUNC g = V env f
                      in g (map (V env) vl)
                     end
  *)

End Appel.
