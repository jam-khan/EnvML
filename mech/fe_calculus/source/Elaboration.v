Require Import LibTactics.
From Stdlib Require Import Arith Lia.
From Stdlib Require Import Strings.String.
Require Import Top.source.Syntax.
Set Implicit Arguments.

(* -------------------------//-------------------------- *)
(* Elaboration, G |- M ~> e : A.  The judgment doubles as EnvML's type
   system, so G and A are FE types and each rule is discharged by one
   has_type rule; the rule that does it is named at each case. *)

(* Term entries (`&`) in T's left spine.  `&=` and `&s` do not move a de
   Bruijn index, they only put a tshift on the looked-up type.  The match
   is on the mode, so simpl is stuck until destruct m. *)
Fixpoint numv (T : typ) : nat :=
  match T with
  | and T1 non _ => S (numv T1)
  | and T1 rt  _ => numv T1
  | ands T1      => numv T1
  | _            => 0
  end.

(* expands Amb k Gsrc Gtodo dIn GIn dOut GOut: in ambient Amb, with the
   operand at index k and signature Gsrc, the entries of Gtodo extend the
   environment dIn : GIn to dOut : GOut.  Mirrors projectEntry in Elab.hs:
   a labelled entry is rebuilt by projection, a transparent one is written
   down, and an abstract one cannot be rebuilt at all -- which is why
   sig_shape excludes it.

   The projected index is numv GIn + k, not a constant: each labelled
   entry already emitted pushes a term binder, so the operand recedes. *)
Inductive expands : typ -> nat -> typ -> typ -> exp -> typ -> exp -> typ -> Prop :=
  | ex_nil : forall Amb k Gsrc d Gd,
      expands Amb k Gsrc top d Gd d Gd
  (* lt_conse, t_rec, trproj, t_var *)
  | ex_lbl : forall Amb k Gsrc G l A d Gd d1 Gd1 B,
      expands Amb k Gsrc G d Gd d1 Gd1 ->
      rlk Gsrc l B ->
      expands Amb k Gsrc (G & (rcd l A)) d Gd
              (d1 ,, rec l (rproj (var (numv Gd1 + k)) l)) (Gd1 & (rcd l B))
  (* lt_const *)
  | ex_typ : forall Amb k Gsrc G A d Gd d1 Gd1,
      expands Amb k Gsrc G d Gd d1 Gd1 ->
      wft (Amb +++ Gd1) A ->
      expands Amb k Gsrc (G &= A) d Gd (d1 ;; A) (Gd1 &= A).

(* -------------------------//-------------------------- *)

Inductive elab : typ -> smod -> exp -> typ -> Prop :=
  (* t_var, trproj *)
  | e_var : forall G n l A B,
      wfe G ->
      get_var G n A ->
      rlk A l B ->
      elab G (s_var n l) (rproj (var n) l) B
  (* t_lam *)
  | e_fun : forall G A M e B,
      elab (G & A) M e B ->
      elab G (s_fun A M) (lam e) (arr A B)
  (* t_blam *)
  | e_tfun : forall G M e B,
      elab (G &s) M e B ->
      elab G (s_tfun M) (blam e) (all B)
  (* t_app *)
  | e_app : forall G M1 M2 e1 e2 A B,
      elab G M1 e1 (arr A B) ->
      elab G M2 e2 A ->
      elab G (s_app M1 M2) (app e1 e2) B
  (* t_tapp.  No meta-substitution: state mani A B and leave the rest to
     e_eq, as t_tapp does. *)
  | e_tapp : forall G M e A B,
      elab G M e (all B) ->
      wft G A ->
      elab G (s_tapp M A) (tapp e A) (mani A B)
  (* t_eq.  Where a computed signature meets a written one; teq_dec
     (Decide.v) discharges the premise for a concrete program. *)
  | e_eq : forall G M e A B,
      elab G M e A ->
      teq G A B G ->
      elab G M e B
  (* t_box, rigidity from rigid_of_wft at T = top.  Elab.hs's box0 around a
     struct or functor is s_box (s_struct D) / s_box (s_fun ...). *)
  | e_box : forall G M e A,
      elab top M e A ->
      wfe G ->
      elab G (s_box M) (box unit e) (boxt top A)
  (* elabBodyRaw: a declaration block with no surrounding box *)
  | e_struct : forall G D d Gd,
      elabd G D d Gd ->
      elab G (s_struct D) d Gd
  (* expandMerge: ((lam (lam BODY)) e1) e2, both operands outside both
     binders so neither is exposed to capture.  Inside, operand 1 is at
     index 1 and operand 2 at index 0, and BODY emits operand 1's entries
     first.  sig_shape and unique_labels are checkComposable's conditions;
     closedness is the sandbox discipline, ++ flattening two
     independently-typed modules. *)
  | e_merge : forall G M1 M2 e1 e2 G1 G2 d1 Gd1 body Gout,
      elab G M1 e1 G1 ->
      elab G M2 e2 G2 ->
      wft top G1 -> wft top G2 ->
      sig_shape G1 -> sig_shape G2 ->
      unique_labels G1 -> unique_labels G2 ->
      expands ((G & G1) & G2) 1 G1 G1 unit top d1 Gd1 ->
      expands ((G & G1) & G2) 0 G2 G2 d1 Gd1 body Gout ->
      elab G (s_merge M1 M2) (app (app (lam (lam body)) e1) e2) Gout

with elabd : typ -> sdecl -> exp -> typ -> Prop :=
  (* lt_nil *)
  | ed_nil : forall G,
      wfe G ->
      elabd G d_nil unit top
  (* lt_conse, t_rec *)
  | ed_val : forall G D d Gd l e A,
      elabd G D d Gd ->
      has_type (G +++ Gd) e A ->
      elabd G (d_val D l e) (d ,, rec l e) (Gd & (rcd l A))
  (* lt_const *)
  | ed_typ : forall G D d Gd A,
      elabd G D d Gd ->
      wft (G +++ Gd) A ->
      elabd G (d_typ D A) (d ;; A) (Gd &= A)
  (* lt_conse, t_rec; the body sees what earlier declarations bound *)
  | ed_mod : forall G D d Gd l M e A,
      elabd G D d Gd ->
      elab (G +++ Gd) M e A ->
      elabd G (d_mod D l M) (d ,, rec l e) (Gd & (rcd l A)).

#[export] Hint Constructors expands elab elabd : core.

Scheme elab_mut  := Minimality for elab  Sort Prop
with   elabd_mut := Minimality for elabd Sort Prop.

Combined Scheme elab_elabd_mut from elab_mut, elabd_mut.
