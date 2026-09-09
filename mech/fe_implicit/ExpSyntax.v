Require Import LibTactics.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Classes.EquivDec.
From Stdlib Require Import Strings.String.
Import ListNotations.
Require Export Teq.
Set Implicit Arguments.


(* -------------------------//-------------------------- *)
Inductive exp :=
  | lit : nat -> exp
  | var : nat -> exp
  | lam : exp -> exp
  | box : exp -> exp -> exp
  | app : exp -> exp -> exp
  | clos: exp -> exp -> exp
  | rec: string -> exp -> exp
  | rproj: exp -> string -> exp
  | unit: exp
  | merge: exp -> exp -> exp.

Notation "e1 ,, e2" := (merge e1 e2) (at level 80).

Inductive value : exp -> Prop :=
  | vlit: forall i, value (lit i)
  | vclos: forall E e,
      value E ->
      value (clos E e)
  | vrec: forall l v,
      value v ->
      value (rec l v)
  | lvnil: value unit
  | lvconsv: forall E v,
      value E ->
      value v ->
      value (E ,, v).

#[export]
Hint Constructors exp value : core.
