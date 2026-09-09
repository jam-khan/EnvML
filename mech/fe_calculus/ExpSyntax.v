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
  | blam: exp -> exp
  | clos: exp -> exp -> exp
  | bclos: exp -> exp -> exp
  | tapp : exp -> typ -> exp
  | rec: string -> exp -> exp
  | rproj: exp -> string -> exp
  | unit: exp
  | merge: exp -> exp -> exp
  | tmerge: exp -> typ -> exp.

Notation "e1 ,, e2" := (merge e1 e2) (at level 80).
Notation "e1 ;; A" := (tmerge e1 A) (at level 80).

Inductive value : exp -> Prop :=
  | vlit: forall i, value (lit i)
  | vclos: forall E e, 
      value E ->
      value (clos E e)
  | vbclos: forall E e,
      value E ->
      value (bclos E e)
  | vrec: forall l v,
      value v ->
      value (rec l v)
  | lvnil: value unit
  | lvconsv: forall E v,
      value E ->
      value v ->
      value (E ,, v)
  | lvconst: forall E T A,
      value E ->
      value (E ;; boxt T A).

#[export]
Hint Constructors exp value : core.
