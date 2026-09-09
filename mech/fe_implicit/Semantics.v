Require Import LibTactics.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Classes.EquivDec.
From Stdlib Require Import Strings.String.
Import ListNotations.
Require Export Teq ExpSyntax.
Set Implicit Arguments.

(* -------------------------//-------------------------- *)
Inductive lookupv : exp -> nat -> exp -> Prop :=
  | lvzero : forall v ve,
      lookupv (merge ve v) 0 v
  | lvsuccv : forall v v' n ve,
      lookupv ve n v' ->
      lookupv (merge ve v) (S n) v'.

Inductive rlookupv : exp -> string -> exp -> Prop :=
  | rvlzero : forall l v d,
      rlookupv (d ,, (rec l v)) l v
  | rvl_left : forall d v1 v l l1,
      rlookupv d l v ->
      ~ l = l1 ->
      rlookupv (d ,, (rec l1 v1)) l v
  | rvl_right : forall d1 d v l,
      rlookupv d1 l v ->
      rlookupv (d ,, d1) l v.

Fixpoint econcat (e1 e2: exp) : exp :=
  match e2 with
    | e3 ,, e4 => (econcat e1 e3) ,, e4
    | _ => e1
  end.

Notation "e1 ++- e2" := (econcat e1 e2) (at level 180).


Inductive step : exp -> exp -> exp -> Prop :=
  | svar : forall ve n v',
      value ve ->
      lookupv ve n v' ->
      step ve (var n) v'
  | sappl : forall ve e1 e2 e1',
      value ve ->
      step ve e1 e1' ->
      step ve (app e1 e2) (app e1' e2)
  | sappr : forall ve v1 e2 e2',
      value ve ->
      value v1 ->
      step ve e2 e2' ->
      step ve (app v1 e2) (app v1 e2')
  | sboxl : forall ve e1 e2 e1',
      value ve ->
      step ve e1 e1' ->
      step ve (box e1 e2) (box e1' e2)
  | sbox : forall ve e1 e2 e2',
      value ve ->
      value e1 ->
      step e1 e2 e2' ->
      step ve (box e1 e2) (box e1 e2')
  | sboxv : forall ve v1 v2,
      value ve ->
      value v1 ->
      value v2 ->
      step ve (box v1 v2) v2
  | sclos: forall ve e,
      value ve ->
      step ve (lam e) (clos ve e)
  | sbeta : forall ve v1 v2 e,
      value v1 ->
      value ve ->
      value v2 ->
      step ve (app (clos v1 e) v2) (box (v1 ,, v2) e)
  | ls_mrgl: forall ve e1 d1 d1',
      value ve ->
      step ve d1 d1' ->
      step ve (d1 ,, e1) (d1' ,, e1)
  | ls_mrgr: forall ve e1 e2 d1,
      value ve ->
      value d1 ->
      step (ve ++- d1) e1 e2 ->
      step ve (d1 ,, e1) (d1 ,, e2)
  | s_rec: forall ve l e e',
      value ve ->
      step ve e e' ->
      step ve (rec l e) (rec l e')
  | s_proj: forall ve l e e',
      value ve ->
      step ve e e' ->
      step ve (rproj e l) (rproj e' l)
  | srprojv : forall ve l dv v2,
      value ve ->
      value dv ->
      rlookupv dv l v2 ->
      step ve (rproj dv l) v2.

#[export]
Hint Constructors lookupv rlookupv step: core.


Lemma lookupv_value: forall v n v',
  lookupv v n v' ->
  value v ->
  value v'.
Proof.
  introv Hl. inductions Hl; introv Hv; inverts* Hv.
Qed.

Lemma rl_value: forall dv l v',
  rlookupv dv l v' ->
  value dv ->
  value v'.
Proof.
  introv Hr. inductions Hr; introv Hv; try solve [inverts* Hv].
  - inverts Hv. inverts* H2.
Qed.

Inductive mstep : exp -> exp -> exp -> Prop :=
  | mstep_base : forall ve e, value ve -> mstep ve e e
  | mstep_step : forall ve e e' e'', step ve e e' -> mstep ve e' e'' -> mstep ve e e''.

#[export]
Hint Constructors mstep: core.


Lemma value_app: forall E2,
  value E2 -> forall E1,
  value E1 ->
  value (E1 ++- E2).
Proof.
  introv Hv2. inductions Hv2; introv Hv1; try solve [simpl; eauto].
Qed.
