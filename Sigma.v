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

  Variable interpretation: NUM -> nat.

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
    (*
    (* Instantiation rules: *)
    | A6 x:
      step (inst subst_ids x)
           x
    | A7 n y ys s:
      interpretation n = 0 ->
      step (inst (subst_app (y :: ys) s) (var n))
           y
    | A8 n y ys s:
      interpretation n > 0 ->
      step (inst (subst_app (y :: ys) s) (var n))
           (inst (subst_app ys s) (var (n - 1)))
    | A9 n ys s:
      interpretation n >= interpretation (length ys) ->
      step (inst (subst_app ys s) (var n))
           (inst s (var (n - length ys)))
    | A10 i n:
      step (inst (subst_lift i) (var n))
           (var (i + n))
    | A11 i s n:
      step (inst (subst_drop i s) (var n))
           (inst s (var (i + n)))
    | A12 i s n:
      interpretation i > interpretation n ->
      step (inst (subst_upn i s) (var n))
           (var n)
    | A13 i n s t:
      interpretation i > interpretation n ->
      step (inst (subst_comp (subst_upn i s) t) (var n))
           (inst t (var n))
    | A14 i s n:
      interpretation i <= interpretation n ->
      step (inst (subst_upn i s) (var n))
           (inst (subst_comp s (subst_lift i)) (var (n - i)))
    | A15 i n s t:
      interpretation i <= interpretation n ->
      step (inst (subst_comp (subst_upn i s) t) (var n))
           (inst (subst_comp s (subst_drop i t)) (var (n - i)))
    | A16 t s x:
      step (inst t (inst s x))
           (inst (subst_comp s t) x)

    (* NEW RULE!!! *)
    | AXX j s i n:
      step (inst (subst_comp (subst_upn j s) (subst_lift i)) (var n))
           (inst (subst_upn (i + j) s) (var (i + n)))

    (* NEW RULE!!! *)
    | AYY j s i n t:
      step (inst (subst_comp (subst_upn j s) (subst_comp (subst_lift i) t)) (var n))
           (inst (subst_comp (subst_upn (i + j) s) t) (var (i + n)))









    (* Algebraic rules: *)
    | A17 n:
      interpretation n = 0 ->
      step (subst_lift n)
           subst_ids
    | A18 n s:
      interpretation n = 0 ->
      step (subst_upn n s)
           s
    | A19 i y ys s:
      interpretation i > 0 ->
       step (subst_drop i (subst_app (y :: ys) s))
            (subst_drop (i - 1) (subst_app ys s))
    | A20 i ys s:
       interpretation i >= interpretation (length ys) ->
       step (subst_drop i (subst_app ys s))
            (subst_drop (i - length ys) s)
    | A21 s:
      step (subst_comp subst_ids s)
           s
    | A22 s:
      step (subst_comp s subst_ids)
           s
    | A23 s t u:
      step (subst_comp (subst_comp s t) u)
           (subst_comp s (subst_comp t u))
    (* WE MIGHT WANT TO CHANGE THE FOLLOWING!!! *)
    | A24 ys s t:
      step (subst_comp (subst_app ys s) t)
           (subst_app (smap t 0 ys) (subst_comp s t))
    (* ------------------- *)
    | A25 m n s:
      interpretation m = interpretation (number 1 + n) ->
      step (subst_cons (inst s (var n)) (subst_drop m s)) (subst_drop n s)
    | A26 i j s:
      interpretation i >= interpretation j ->
      step (subst_drop i (subst_upn j s))
           (subst_drop (i - j) (subst_comp s (subst_lift j)))
    | A27 i j s:
      interpretation i <= interpretation j ->
      step (subst_drop i (subst_upn j s))
           (subst_comp (subst_upn (j - i) s) (subst_lift i))
    | A28 i j s t:
      interpretation i >= interpretation j ->
      step (subst_drop i (subst_comp (subst_upn j s) t))
           (subst_drop (i - j) (subst_comp s (subst_drop j t)))
    | A29 i j s t:
      interpretation i <= interpretation j ->
      step (subst_drop i (subst_comp (subst_upn j s) t))
           (subst_comp (subst_upn (j - i) s) (subst_drop i t))
    | A30 k j s t:
      interpretation k >= interpretation j ->
      step (subst_comp (subst_upn k s) (subst_upn j t))
           (subst_upn j (subst_comp (subst_upn (k - j) s) t))
    | A31 j k s t:
      interpretation j >= interpretation k ->
      step (subst_comp (subst_upn k s) (subst_upn j t))
           (subst_upn k (subst_comp s (subst_upn (j - k) t)))
    | A32 j k s t u:
      interpretation k >= interpretation j ->
      step (subst_comp (subst_upn k s) (subst_comp (subst_upn j t) u))
           (subst_comp (subst_upn j (subst_comp (subst_upn (k - j) s) t)) u)
    | A33 j k s t u:
      interpretation j >= interpretation k ->
      step (subst_comp (subst_upn k s) (subst_comp (subst_upn j t) u))
           (subst_comp (subst_upn k (subst_comp s (subst_upn (j - k) t))) u)
    | A34 n y ys s t:
      interpretation n > 0 ->
      step (subst_comp (subst_upn n s) (subst_app (y :: ys) t))
           (subst_cons y (subst_comp (subst_upn (n - 1) s) (subst_app ys t)))
    | A35 n ys s t:
      interpretation n >= interpretation (length ys) ->
      step (subst_comp (subst_upn n s) (subst_app ys t))
           (subst_app ys (subst_comp (subst_upn (n - length ys) s) t))
    | A36 n ys zs s t:
       interpretation n >= interpretation (length ys) ->
       step (subst_comp (subst_upn n s) (subst_app (ys ++ zs) t))
            (subst_app ys (subst_comp (subst_upn (n - length ys) s) (subst_app zs t)))
    | A37 i:
      step (subst_upn i subst_ids)
           subst_ids
    | A38 i j:
      (* SMALL CHANGE IN HERE! *)
      step (subst_drop i (subst_lift j))
           (subst_lift (j + i))
    | A39 i j s:
      step (subst_upn i (subst_upn j s))
           (subst_upn (i + j) s)
    | A40 s:
      step (subst_app [] s)
           s
    | A41 xs ys s:
      (* WE INVERTED THIS RULE!!! *)
      step (subst_app (xs ++ ys) s)
           (subst_app xs (subst_app ys s))
    *)













    (* ---------------------------------------------------------------------- *)
    (* 1. (Closure) inst s (inst t e) = inst (subst_comp s t) e *)
    | A6 s t x:
      step (inst t (inst s x))
           (inst (subst_comp s t) x)
    (* 2. (VarShift1) inst (subst_lift 1) (var n) = var (1 + n) *)
    | A7 i n:
      step (inst (subst_lift i) (var n))
           (var (i + n))
    (* 3. (VarShift2) inst (subst_comp (subst_lift 1) s)
                                                       = inst s (var (1 + n)) *)
    | A8 i s n:
      step (inst (subst_comp (subst_lift i) s) (var n))
           (inst s (var (i + n)))
    (* 4. (FVar) inst (subst_cons y s) (var 0) = y *)
    | A9 y ys s:
      step (inst (subst_app (y :: ys) s) (var 0))
           y
    (* 5. (FVarLift1) inst (subst_upn 1 s) (var 0) = var 0 *)
    | A10 i s n:
      interpretation i > interpretation n ->
      step (inst (subst_upn i s) (var n))
           (var n)
    (* 6. (FvarLift2) inst (subst_comp (subst_upn 1 s) t) (var 0)
                                                             = inst t (var 0) *)
    | A11 i s t n:
      interpretation i > interpretation n ->
      step (inst (subst_comp (subst_upn i s) t) (var n))
           (inst t (var n))
    (* 7. (RVar) inst (subst_cons y s) (var (1 + n)) = inst s (var n) *)
    | A12 y ys s n:
      interpretation n > 0 ->
      step (inst (subst_app (y :: ys) s) (var n))
           (inst (subst_app ys s) (var (n - 1)))
    | A13 ys s n:
      interpretation n >= interpretation (length ys) ->
      step (inst (subst_app ys s) (var n))
           (inst s (var (n - length ys)))
    (* Sometimes app and comp can't commute, so we need to consider it here. *)
    | AAA y ys s t n:
      interpretation n > 0 ->
      step (inst (subst_comp (subst_app (y :: ys) s) t) (var n))
           (inst (subst_comp (subst_app ys s) t) (var (n - 1)))
    | AAB ys s t n:
      interpretation n >= interpretation (length ys) ->
      step (inst (subst_comp (subst_app ys s) t) (var n))
           (inst (subst_comp s t) (var (n - length ys)))




    (* 8. (RVarLift1) inst (subst_upn 1 s) (var (1 + n))
                                 = inst (subst_comp s (subst_lift 1)) (var n) *)
    | A14 i s n:
      interpretation i <= interpretation n ->
      step (inst (subst_upn i s) (var n))
           (inst (subst_comp s (subst_lift i)) (var (n - i)))
    (* 9. (RVarLift2) inst (subst_comp (subst_upn 1 s) t) (var (1 + n))
                  = inst (subst_comp s (subst_comp (subst_lift 1) t)) (var n) *)
    | A15 i s t n:
      interpretation i <= interpretation n ->
      step (inst (subst_comp (subst_upn i s) t) (var n))
           (inst (subst_comp s (subst_comp (subst_lift i) t)) (var (n - i)))












    (* 21. (IdEnv) inst subst_ids x = x *)
    | A16 x:
      step (inst subst_ids x)
           x
    (* ---------------------------------------------------------------------- *)
    (* 10. (AssEnv) subst_comp (subst_comp s t) u
                                              = subst_comp s (subst_comp t u) *)
    | A17 s t u:
      step (subst_comp (subst_comp s t) u)
           (subst_comp s (subst_comp t u))
    (* 11. (MapEnv) subst_comp (subst_cons y s) t
                                     = subst_cons (inst t y) (subst_comp s t) *)
    | A18 y ys s t:
      step (subst_comp (subst_app (y :: ys) s) t)
           (subst_cons (inst t y) (subst_comp (subst_app ys s) t))
    (* 12. (Shift) subst_comp (subst_lift 1) (subst_cons y s) = s *)
    | A19 i y ys s:
      interpretation i > interpretation 0 ->
      step (subst_comp (subst_lift i) (subst_app (y :: ys) s))
           (subst_comp (subst_lift (i - 1)) (subst_app ys s))
    | A20 i ys s:
      interpretation i >= interpretation (length ys) ->
      step (subst_comp (subst_lift i) (subst_app ys s))
           (subst_comp (subst_lift (i - length ys)) s)



    | A19' i y ys s t:
      interpretation i > interpretation 0 ->
      step (subst_comp (subst_lift i) (subst_comp (subst_app (y :: ys) s) t))
           (subst_comp (subst_lift (i - 1)) (subst_comp (subst_app ys s) t))
    | A20' i ys s t:
      interpretation i >= interpretation (length ys) ->
      step (subst_comp (subst_lift i) (subst_comp (subst_app ys s) t))
           (subst_comp (subst_lift (i - length ys)) (subst_comp s t))





    (* 13. (ShiftLift1) subst_comp (subst_lift 1) (subst_upn 1 s)
                                                = subst_comp s (subst_lift 1) *)
    | A21 i j s:
      interpretation i >= interpretation j ->
      step (subst_comp (subst_lift i) (subst_upn j s))
           (subst_comp (subst_lift (i - j)) (subst_comp s (subst_lift j)))
    | A22 i j s:
      interpretation i <= interpretation j ->
      step (subst_comp (subst_lift i) (subst_upn j s))
           (subst_comp (subst_upn (j - i) s) (subst_lift i))








    (* 14. (ShiftLift2) subst_comp (subst_lift 1) (subst_comp (subst_upn 1 s) t)
                                 = subst_comp s (subst_comp (subst_lift 1) t) *)
    | A23 i j s t:
      interpretation i >= interpretation j ->
      step (subst_comp (subst_lift i) (subst_comp (subst_upn j s) t))
           (subst_comp (subst_lift (i - j)) (subst_comp s (subst_comp (subst_lift j) t)))
    | A24 i j s t:
      interpretation i <= interpretation j ->
      step (subst_comp (subst_lift i) (subst_comp (subst_upn j s) t))
           (subst_comp (subst_upn (j - i) s) (subst_comp (subst_lift i) t))





    (* 15. (Lift1) subst_comp (subst_upn 1 s) (subst_upn 1 t)
                                               = subst_upn 1 (subst_comp s t) *)
    | A25 i j s t:
      interpretation i >= interpretation j ->
      step (subst_comp (subst_upn i s) (subst_upn j t))
           (subst_upn j (subst_comp (subst_upn (i - j) s) t))
    | A26 i j s t:
      interpretation i <= interpretation j ->
        step (subst_comp (subst_upn i s) (subst_upn j t))
             (subst_upn i (subst_comp s (subst_upn (j - i) t)))
    (* 16. (Lift2) subst_comp (subst_upn 1 s) (subst_comp (subst_upn 1 t) u)
                                = subst_comp (subst_upn 1 (subst_comp s t)) u *)
    | A27 i j s t u:
      interpretation i >= interpretation j ->
      step (subst_comp (subst_upn i s) (subst_comp (subst_upn j t) u))
           (subst_comp (subst_upn j (subst_comp (subst_upn (i - j) s) t)) u)
    | A28 i j s t u:
      interpretation i <= interpretation j ->
      step (subst_comp (subst_upn i s) (subst_comp (subst_upn j t) u))
           (subst_comp (subst_upn i (subst_comp s (subst_upn (j - i) t))) u)





    (* 17. (LiftEnv) subst_comp (subst_upn 1 s) (subst_cons y t)
                                              = subst_cons y (subst_comp s t) *)
    | A29 i s y ys t:
      interpretation i > interpretation 0 ->
      step (subst_comp (subst_upn i s) (subst_app (y :: ys) t))
           (subst_cons y (subst_comp (subst_upn (i - 1) s) (subst_app ys t)))
    | A30 i s ys t:
      interpretation i >= interpretation (length ys) ->
      step (subst_comp (subst_upn i s) (subst_app ys t))
           (subst_app ys (subst_comp (subst_upn (i - length ys) s) t))

    | A29' i s y ys t u:
      interpretation i > interpretation 0 ->
      (* TODO: check if this is normal form!!! *)
      step (subst_comp (subst_upn i s) (subst_comp (subst_app (y :: ys) t) u))
           (subst_cons (inst u y)
             (subst_comp (subst_upn (i - 1) s) (subst_comp (subst_app ys t) u)))
    | A30' i s ys t u:
      interpretation i >= interpretation (length ys) ->
      step (subst_comp (subst_upn i s) (subst_comp (subst_app ys t) u))
           (subst_comp (subst_app ys (subst_comp (subst_upn (i - length ys) s) t)) u)



    (* 18. (IdL) subst_comp subst_ids s = s *)
    | AY1 s:
      step (subst_comp subst_ids s)
           s
    (* 19. (IdR) subst_comp s subst_ids = s *)
    | AY2 s:
      step (subst_comp s subst_ids)
           s
    (* 20. (LiftId) subst_upn 1 subst_ids = subst_ids *)
    | AY3 i:
      step (subst_upn i subst_ids)
           subst_ids
    (* ---------------------------------------------------------------------- *)
    | AX1 i: (* Remove useless lift. *)
      interpretation i = interpretation 0 ->
      step (subst_lift i)
           (subst_ids)
    | AX2 i s: (* Remove useless uplift. *)
      interpretation i = interpretation 0 ->
      step (subst_upn i s)
           s
    | AX3 i j: (* Join lifts. *)
      step (subst_comp (subst_lift i) (subst_lift j))
           (subst_lift (j + i))
    | AX4 i j s:
      step (subst_comp (subst_lift i) (subst_comp (subst_lift j) s))
           (subst_comp (subst_lift (j + i)) s)
    | AX5 i j s: (* Join uplifts. *)
      step (subst_upn i (subst_upn j s))
           (subst_upn (j + i) s)
    | AX6 ys s:
      interpretation (length ys) = interpretation 0 ->
      step (subst_app ys s)
           s
    | AX7 y ys zs s: (* Join cons and app... *)
      interpretation (length ys) = interpretation 0 ->
      step (subst_app (y :: ys) (subst_app zs s))
           (subst_app (y :: zs) s)
    (* ---------------------------------------------------------------------- *)

    | ABA i k s n:
      step (inst (subst_comp (subst_upn k s) (subst_lift i)) (var n))
           (inst (subst_upn (i + k) s) (var (i + n)))

    | ABB i k s t n:
      step (inst (subst_comp (subst_upn k s) (subst_comp (subst_lift i) t)) (var n))
           (inst (subst_comp (subst_upn (i + k) s) t) (var (i + n)))

    (* | ABC i j s t n:
      interpretation (i + j)%sigma > interpretation n ->
      step (inst (subst_upn i (subst_comp (subst_upn j s) t)) (var n))
           (inst (subst_upn i t) (var n))

    | ABD i j s t u n:
      interpretation (i + j)%sigma > interpretation n ->
      step (inst (subst_comp (subst_upn i (subst_comp (subst_upn j s) t)) u) (var n))
           (inst (subst_comp (subst_upn i t) u) (var n)) *)

    | ABE ys i s t n:
      interpretation (i + length ys) > interpretation n ->
      step (inst (subst_app ys (subst_comp (subst_upn i s) t)) (var n))
           (inst (subst_app ys t) (var n))

    | ABF ys i s t u n:
      interpretation (i + length ys) > interpretation n ->
      step (inst (subst_comp (subst_app ys (subst_comp (subst_upn i s) t)) u) (var n))
           (inst (subst_comp (subst_app ys t) u) (var n))

    (* ---------------------------------------------------------------------- *)
    (* Congruence rules: *)
    | C0 n1 n2:
      step n1 n2 -> step (index n1) (index n2)
    | C1 e1 e2:
      step e1 e2 -> step (abs e1) (abs e2)
    | C3 e1 e2 f:
      step e1 e2 -> step (app e1 f) (app e2 f)
    | C4 e f1 f2:
      step f1 f2 -> step (app e f1) (app e f2)
    | C5 i1 i2 k e:
      step i1 i2 -> step (lift i1 k e) (lift i2 k e)
    | C6 i k1 k2 e:
      step k1 k2 -> step (lift i k1 e) (lift i k2 e)
    | C7 i k e1 e2:
      step e1 e2 -> step (lift i k e1) (lift i k e2)
    | C8 y1 y2 k e:
      step y1 y2 -> step (subst y1 k e) (subst y2 k e)
    | C9 y k1 k2 e:
      step k1 k2 -> step (subst y k1 e) (subst y k2 e)
    | C10 y k e1 e2:
      step e1 e2 -> step (subst y k e1) (subst y k e2)
    | C11 s1 s2 k e:
      step s1 s2 -> step (traverse s1 k e) (traverse s2 k e)
    | C12 s k1 k2 e:
      step k1 k2 -> step (traverse s k1 e) (traverse s k2 e)
    | C13 s k e1 e2:
      step e1 e2 -> step (traverse s k e1) (traverse s k e2)
    | C14 s1 s2 e:
      step s1 s2 -> step (inst s1 e) (inst s2 e)
    | C15 s e1 e2:
      step e1 e2 -> step (inst s e1) (inst s e2)
    | C16 n1 n2:
      step n1 n2 -> step (subst_lift n1) (subst_lift n2)
    | C17 v1 v2 s:
      step v1 v2 -> step (subst_app v1 s) (subst_app v2 s)
    | C18 v s1 s2:
      step s1 s2 -> step (subst_app v s1) (subst_app v s2)
    | C19 s1 s2 r:
      step s1 s2 -> step (subst_comp s1 r) (subst_comp s2 r)
    | C20 s r1 r2:
      step r1 r2 -> step (subst_comp s r1) (subst_comp s r2)
    | C21 n1 n2 s:
      step n1 n2 -> step (subst_upn n1 s) (subst_upn n2 s)
    | C22 n s1 s2:
      step s1 s2 -> step (subst_upn n s1) (subst_upn n s2)
    | C23 e1 e2 x:
      step e1 e2 -> step (e1 :: x) (e2 :: x)
    | C24 e x1 x2:
      step x1 x2 -> step (e :: x1) (e :: x2)
    | C25 x1 x2 y:
      step x1 x2 -> step (x1 ++ y) (x2 ++ y)
    | C26 x y1 y2:
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
    admit.
  Admitted.

  Lemma interpretation_succ:
    forall n,
    interpretation (succ n) = S (interpretation n).
  Proof.
    admit.
  Admitted.

  Lemma interpretation_number:
    forall n,
    interpretation (number n) = n.
  Proof.
    admit.
  Admitted.

  Lemma interpretation_add:
    forall a b,
    interpretation (a + b) = interpretation a + interpretation b.
  Proof.
    admit.
  Admitted.

  Lemma interpretation_sub:
    forall a b,
    interpretation (a - b) = interpretation a - interpretation b.
  Proof.
    admit.
  Admitted.

  Lemma interpretation_cons_length:
    forall y ys,
    interpretation (length (y :: ys)) = interpretation (1 + length ys).
  Proof.
    admit.
  Admitted.

  Lemma interpretation_nil_length:
    interpretation (length []) = interpretation 0.
  Proof.
    admit.
  Admitted.

  Lemma interpretation_app_length:
    forall xs ys,
    interpretation (length (xs ++ ys)) =
      interpretation (length xs) + interpretation (length ys).
  Proof.
    admit.
  Admitted.

  Lemma interpretation_min:
    forall n m,
    interpretation (MIN n m) = min (interpretation n) (interpretation m).
  Proof.
    admit.
  Admitted.

  Lemma interpretation_max:
    forall n m,
    interpretation (MAX n m) = max (interpretation n) (interpretation m).
  Proof.
    admit.
  Admitted.

  Create HintDb interpretation.

  Hint Rewrite interpretation_zero: interpretation.
  Hint Rewrite interpretation_succ: interpretation.
  Hint Rewrite interpretation_number: interpretation.
  Hint Rewrite interpretation_add: interpretation.
  Hint Rewrite interpretation_sub: interpretation.
  Hint Rewrite interpretation_cons_length: interpretation.
  Hint Rewrite interpretation_nil_length: interpretation.
  Hint Rewrite interpretation_app_length: interpretation.
  Hint Rewrite interpretation_min: interpretation.
  Hint Rewrite interpretation_max: interpretation.

  Lemma interpretation_consistent_num:
    forall n m,
    @step NUM n m ->
    interpretation n = interpretation m.
  Proof.
    intros.
    dependent induction H;
    autorewrite with interpretation in *.
  Qed.

  Lemma interpretation_consistent_len:
    forall xs ys,
    @step VECTOR xs ys ->
    interpretation (length xs) = interpretation (length ys).
  Proof.
    intros.
    dependent induction H;
    autorewrite with interpretation in *.
    - lia.
    - f_equal.
      now apply IHstep.
    - f_equal.
      now apply IHstep.
    - f_equal.
      now apply IHstep.
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

  Definition equivalent {s} (y: t s) (z: t s): Prop :=
    exists2 w,
    @star s y w & @star s z w.

  Lemma equivalent_refl:
    forall {s} x,
    @equivalent s x x.
  Proof.
    repeat intro.
    exists x; eauto with sigma.
  Qed.

  Hint Resolve equivalent_refl: core.

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

  Theorem locally_confluent:
    forall s x y,
    let origX := x in
    let origY := y in
    forall X: @step s x y,
    forall z,
    let origZ := z in
    forall Y: @step s x z,
    equivalent y z.
  Proof.
    induction 3; intros.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
      + wonder j n.
        * work.
        * work.
      + wonder j n.
        * work.
        * work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
      + rename j0 into k, s0 into s.
        wonder (SUB i j) k.
        * work.
        * work.
    - repeat break; work.
    - repeat break; work.
      + rename j0 into k, s0 into s, t0 into t.
        wonder (SUB i j) k.
        * work.
        * work.
    - repeat break; work.
      + rename j0 into k, t1 into t.
        wonder i k.
        * work.
        * work.
      + rename j0 into k, t1 into t.
        wonder i k.
        * work.
        * work.
      + wonder i 0.
        * work.
        * work.
      + wonder i (length ys).
        * admit.
        * work.
      + wonder i 0.
        * work.
        * work.
      + wonder i (length ys).
        * admit.
        * work.
    - repeat break; work.
      + rename j0 into k, s0 into t.
        wonder i (ADD k j).
        * work.
        * work.
    - repeat break; work.
      + rename j0 into k, s0 into s, t0 into t.
        wonder (ADD k i) j.
        * work.
        * work.
    - repeat break; work.
      + rename j0 into k, s0 into t.
        wonder (SUB i j) k.
        * work.
        * work.
    - repeat break; work.
      + rename j0 into k, s0 into s, t0 into t.
        wonder (ADD k i) j.
        * work.
        * work.
      + rename j0 into k, t1 into t.
        wonder i k.
        * work.
        * work.
      + rename j0 into k, t1 into t, u0 into u.
        wonder i k.
        * work.
        * work.
      + wonder i 0.
        * work.
        * work.
      + admit.
      + wonder i 0.
        * work.
        * work.
      + rename t0 into t1, t1 into t2, u0 into u.
        wonder i (length ys).
        * admit.
        * work.
    - repeat break; work.
    - repeat break; work.
      + replace ys0 with [] by admit.
        work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
      + rename j0 into k, s0 into s.
        wonder (ADD j i) k.
        * work.
        * work.
      + rename j0 into k, s0 into s.
        wonder (ADD j i) k.
        * work.
        * work.
    - repeat break; work.
    - repeat break; work.
    - repeat break; work.
      + replace zs with [] by admit.
        replace ys with [] by admit.
        work.
      + rename ys0 into zs.
        replace ys with [] by admit.
        replace zs with [] by admit.
        admit.
    - repeat break; work.
    - repeat break; work.
      + rename s0 into t.
        wonder (ADD i k) j.
        * work.
        * work.
      + rename s0 into t, t1 into u.
        wonder (ADD i k) j.
        * work.
        * work.
    - admit.
    - admit.
    (* .................................................................. *)
  Admitted.

End Sigma.
