(******************************************************************************)
(*   Copyright (c) 2019--2026 - Paulo Torrens <paulotorrens AT gnu DOT org>   *)
(******************************************************************************)

Require Import Local.Setoid.
Require Import Local.Category.Theory.

Set Primitive Projections.
(* TODO: we might want to make these monomorphic. *)
Set Universe Polymorphism.

(* -------------------------------------------------------------------------- *)

(* We define the notion of a category with families, which forms a model of
   basic dependent type theory. This is a category C, such that:

   - we call the objects of C contexts (environments), and they model such;
   - we call the morphisms of C substitutions, and they model such;
   - an empty context, which is a terminal object of C;
   - ...

   TODO: properly document this, specially the relationship to explicit
   substitution and to the sigma-calculus, which is quite evident!
*)

Structure CwF := {
  (* ... *)
  cwf_cat: Category;
  (* ... *)
  cwf_env :=
    obj cwf_cat;
  (* ... *)
  cwf_sub: cwf_cat -> cwf_cat -> Setoid :=
    hom cwf_cat;
  (* ... *)
  cwf_empty: Terminal cwf_cat;
  (* ... *)
  cwf_ty: cwf_env -> Setoid;
  cwf_tsub {G D}:
    cwf_sub D G ~> cwf_ty G ~> cwf_ty D;
  (* ... *)
  cwf_el G: SetoidFamily (cwf_ty G);
  cwf_esub {G D A}:
    forall s: cwf_sub D G,
    cwf_el G A ~> cwf_el D (cwf_tsub s A);
  (* ... *)
  cwf_transp {G A B} (H: A == B) :=
    setoid_transport (cwf_el G) H;
  (* ... *)
  cwf_u {G}: nat -> cwf_ty G;
  cwf_t {G n}:
    forall X: cwf_el G (cwf_u n),
    cwf_ty G;
  cwf_lift {G n l}:
    forall H: n < l,
    forall X: cwf_el G (cwf_u n),
    cwf_el G (cwf_u l);
  (* ... *)
  cwf_ucoh {G n l}:
    forall H: n < l,
    forall X: cwf_el G (cwf_u n),
    cwf_t (cwf_lift H X) == cwf_t X
}.

(*

(* TODO: temporary...! *)
Coercion Domain: PartialSetoid >-> Sortclass.

Coercion domain_cast: partial_path >-> Funclass.

Structure CwF: Type := {
  (* TODO: can we enforce that this is small? Check later! *)
  cwf_cat: Category;
  cwf_env := obj cwf_cat;
  cwf_sub := hom cwf_cat;
  cwf_empty: Terminal cwf_cat;
  (* ... *)
  cwf_ty: cwf_env -> PartialSetoid;
  cwf_tsub {G D}:
    cwf_sub D G -> cwf_ty G -> cwf_ty D;
  (* ... *)
  cwf_el G: cwf_ty G ~> PartialSetoid;
  cwf_esub {G D A}:
    forall s: cwf_sub D G,
    cwf_el G A -> cwf_el D (cwf_tsub s A);
  cwf_transp {G A B} (H: A == B) :=
    cong (cwf_el G) H;
  (* ... *)
  cwf_ext G: cwf_ty G -> cwf_env;
  cwf_cons {G D}:
    forall s: cwf_sub D G,
    forall A: cwf_ty G,
    cwf_el D (cwf_tsub s A) ->
    cwf_sub D (cwf_ext G A);
  cwf_proj {G A}:
    cwf_sub (cwf_ext G A) G;
  cwf_zero {G A}:
    cwf_el (cwf_ext G A) (cwf_tsub cwf_proj A);
  (* ... *)
  cwf_tsub_respectful {G D}:
    Proper (setoid_equiv ==> setoid_equiv ==> setoid_equiv) (@cwf_tsub G D);
  cwf_tsub_id {G}:
    forall {A: cwf_ty G},
    cwf_tsub id A == A;
  cwf_tsub_comp {G D E}:
    forall {s: cwf_sub D G},
    forall {r: cwf_sub E D},
    forall {A: cwf_ty G},
    cwf_tsub r (cwf_tsub s A) == cwf_tsub (post r s) A;
  (* TODO: we need to check that esub is respectful, but that is a form of
     heterogeneous equality; figure it out how to do that later, please? *)
  (* TODO: cwf_esub_id, same reason... *)
  (* TODO: cwf_esub_comp, same reason... *)
  (* TODO: should cwf_ext be respectful? Cause it doesn't make much sense that
     there would be an isomorphism between the resulting contexts afterwards, as
     morphisms are meant to be substitutions! *)
  (* TODO: show that snoc, proj and zero need to be respectful. *)
  (* TODO: law for p o (a, s) = s *)
  (* TODO: law for q[a, s] = a *)
  (* TODO: law for (a, s) o r = (a[r], s o r) *)
  (* TODO: law for (q, p) = id *)
  (* TODO: do we need eta? I.e., (q[s], p o s) = s? This derives the above... *)
  (* ... *)
  (* Given e: El(G, A), we take (e/) = (e[id], id) : G -> (G, A). This is just
     the subst/slash substitution built out of cons and identity. *)
  cwf_slash {G A} (e: cwf_el G A) :=
    cwf_cons id A (cwf_esub id e);
  (* Given a substitution s: D -> G, we want to lift it into another scope by
     defining up s = (0, (s o proj)) : (D, A[s]) -> (G, A). *)
  cwf_up {G D A} (s: cwf_sub D G) :=
    cwf_cons (post cwf_proj s) A (cwf_transp cwf_tsub_comp cwf_zero)
}.

*)

(* -------------------------------------------------------------------------- *)

(* A pseudomorphism is just a mapping between two CwFs M and N such that it is
   strict on the base category structure, i.e., things are preserved by setoid
   equality here, but it is weak in the terminal object and on environment
   extension, i.e., those are only preserved up to isomorphism.

   A good reference for this: "Gluing for Type Theory", by Kaposi et al. *)

Structure pseudomorphism (M: CwF) (N: CwF): Type := {
  psm_con:
    cwf_cat M -> cwf_cat N;
  psm_sub G D:
    cwf_cat M G D ~> cwf_cat N (psm_con G) (psm_con D);
  psm_ty G:
    cwf_ty M G ~> cwf_ty N (psm_con G);
  psm_el G A:
    cwf_el M G A ~> cwf_el N (psm_con G) (psm_ty G A)
}.

Arguments psm_con {M} {N}.
Arguments psm_sub {M} {N}.
Arguments psm_ty {M} {N}.
Arguments psm_el {M} {N}.

Program Definition pseudomorphism_id {M: CwF}: pseudomorphism M M := {|
  psm_con G :=
    G;
  psm_sub G D :=
    map s => s;
  psm_ty G :=
    map A => A;
  psm_el G A :=
    map e => e
|}.

Section PseudomorphismPost.

  Variable M: CwF.
  Variable N: CwF.
  Variable O: CwF.

  Variable X: pseudomorphism M N.
  Variable Y: pseudomorphism N O.

  Program Definition pseudomorphism_post: pseudomorphism M O := {|
    psm_con G := psm_con Y (psm_con X G);
    psm_sub G D :=
      map (s: cwf_cat M G D) =>
        psm_sub Y (psm_con X G) (psm_con X D) (psm_sub X G D s);
    psm_ty G :=
      map (A: cwf_ty M G) =>
        psm_ty Y (psm_con X G) (psm_ty X G A);
    psm_el G A :=
      map (e: cwf_el M G A) =>
        psm_el Y (psm_con X G) (psm_ty X G A) (psm_el X G A e)
  |}.

  Next Obligation of pseudomorphism_post.
    now rewrite H.
  Qed.

  Next Obligation of pseudomorphism_post.
    now rewrite H.
  Qed.

  Next Obligation of pseudomorphism_post.
    now rewrite H.
  Qed.

End PseudomorphismPost.

(* TODO: define the CwF category... if needed, of course. *)
